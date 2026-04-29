// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `watch` subcommand: file watcher with incremental re-check.
//!
//! Watches a TLA+ spec file (and its .cfg) for changes, then re-runs
//! the model checker automatically. Similar to `cargo watch` or `jest --watch`.
//!
//! Also discovers and watches EXTENDS/INSTANCE dependency files so that
//! changes to imported modules trigger a re-check.
//!
//! Part of #3797.

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use notify::{Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};

use crate::cli_schema::{LivenessModeArg, OutputFormat, SoundnessGate, TraceFormat};
use crate::cmd_check::{cmd_check, CheckConfig};

/// Configuration for the watch command, bundling check flags plus watch-specific options.
pub(crate) struct WatchConfig {
    // Spec file and config
    pub(crate) file: PathBuf,
    pub(crate) config_path: Option<PathBuf>,

    // Watch-specific options
    pub(crate) on_error_only: bool,
    pub(crate) debounce_ms: u64,
    pub(crate) clear: bool,

    // Inherited check flags
    pub(crate) workers: usize,
    pub(crate) no_deadlock: bool,
    pub(crate) max_states: usize,
    pub(crate) max_depth: usize,
}

/// Run the watch loop: watch files, re-run check on changes.
pub(crate) fn cmd_watch(cfg: WatchConfig) -> Result<()> {
    let spec_path = cfg
        .file
        .canonicalize()
        .with_context(|| format!("cannot resolve spec file: {}", cfg.file.display()))?;

    // Determine .cfg path to watch (either explicit or derived).
    let config_path = resolve_config_path(&cfg.file, cfg.config_path.as_deref());

    // Collect all paths to watch: spec file, config, and EXTENDS/INSTANCE deps.
    let mut watch_paths: Vec<PathBuf> = vec![spec_path.clone()];
    if let Some(ref cp) = config_path {
        if cp.exists() {
            if let Ok(canonical) = cp.canonicalize() {
                watch_paths.push(canonical);
            }
        }
    }

    // Discover EXTENDS/INSTANCE dependency files and add them to watch list.
    let dep_paths = discover_dependency_files(&cfg.file);
    for dep in &dep_paths {
        if let Ok(canonical) = dep.canonicalize() {
            if !watch_paths.contains(&canonical) {
                watch_paths.push(canonical);
            }
        }
    }

    // Collect unique parent directories to watch.
    let watch_dirs: Vec<PathBuf> = {
        let mut dirs: Vec<PathBuf> = watch_paths
            .iter()
            .filter_map(|p| p.parent().map(Path::to_path_buf))
            .collect();
        dirs.sort();
        dirs.dedup();
        dirs
    };

    eprintln!("Watching {} for changes...", cfg.file.display());
    if let Some(ref cp) = config_path {
        if cp.exists() {
            eprintln!("  config: {}", cp.display());
        }
    }
    for dep in &dep_paths {
        eprintln!("  dependency: {}", dep.display());
    }
    eprintln!("Press Ctrl+C to stop.\n");

    // Run initial check.
    let mut total_runs: u64 = 0;
    let mut cumulative_time = Duration::ZERO;

    run_check_cycle(&cfg, &mut total_runs, &mut cumulative_time);

    // Set up file watcher.
    let (tx, rx) = mpsc::channel::<notify::Result<Event>>();
    let mut watcher: RecommendedWatcher = Watcher::new(
        tx,
        notify::Config::default().with_poll_interval(Duration::from_millis(100)),
    )
    .context("failed to create file watcher")?;

    for dir in &watch_dirs {
        watcher
            .watch(dir, RecursiveMode::NonRecursive)
            .with_context(|| format!("failed to watch directory: {}", dir.display()))?;
    }

    let debounce_duration = Duration::from_millis(cfg.debounce_ms);

    // Event loop with debouncing.
    loop {
        // Block until we get a relevant event.
        let event = match rx.recv() {
            Ok(Ok(event)) => event,
            Ok(Err(e)) => {
                eprintln!("Watch error: {e}");
                continue;
            }
            Err(_) => {
                // Channel closed (watcher dropped). Exit gracefully.
                break;
            }
        };

        if !is_relevant_event(&event, &watch_paths) {
            continue;
        }

        // Debounce: drain additional events within the debounce window.
        let deadline = Instant::now() + debounce_duration;
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                break;
            }
            match rx.recv_timeout(remaining) {
                Ok(_) => {} // Absorb event; keep draining.
                Err(mpsc::RecvTimeoutError::Timeout) => break,
                Err(mpsc::RecvTimeoutError::Disconnected) => return Ok(()),
            }
        }

        // Clear screen if requested, otherwise print separator.
        if cfg.clear {
            print!("\x1B[2J\x1B[1;1H");
        } else {
            eprintln!("\n{}", "=".repeat(60));
        }

        run_check_cycle(&cfg, &mut total_runs, &mut cumulative_time);

        eprintln!("\nWatching for changes... (Ctrl+C to stop)");
    }

    Ok(())
}

/// Determine the config path: explicit > derived from spec name.
fn resolve_config_path(spec: &Path, explicit: Option<&Path>) -> Option<PathBuf> {
    if let Some(p) = explicit {
        return Some(p.to_path_buf());
    }
    // Derive: Spec.tla -> Spec.cfg
    let mut cfg_path = spec.to_path_buf();
    cfg_path.set_extension("cfg");
    if cfg_path.exists() {
        Some(cfg_path)
    } else {
        None
    }
}

/// Discover EXTENDS/INSTANCE dependency `.tla` files by parsing the spec.
///
/// Uses `ModuleLoader` to resolve module names found via EXTENDS and INSTANCE
/// declarations. Returns paths to all discovered dependency files (excluding
/// stdlib modules which have no on-disk `.tla`).
fn discover_dependency_files(spec_file: &Path) -> Vec<PathBuf> {
    let mut result = Vec::new();

    // Parse the main module to get its AST.
    let source = match std::fs::read_to_string(spec_file) {
        Ok(s) => s,
        Err(_) => return result,
    };
    let tree = tla_core::parse_to_syntax_tree(&source);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return result,
    };

    // Use the module loader to resolve dependencies.
    let mut loader = tla_core::ModuleLoader::new(spec_file);

    // Collect EXTENDS dependencies.
    let mut seen = HashSet::new();
    if let Ok(extends) = loader.load_extends(&module) {
        for name in extends {
            if seen.insert(name.clone()) {
                if let Some(path) = loader.get(&name).map(|m| m.path.clone()) {
                    result.push(path);
                }
            }
        }
    }

    // Collect INSTANCE dependencies.
    if let Ok(instances) = loader.load_instances(&module) {
        for name in instances {
            if seen.insert(name.clone()) {
                if let Some(path) = loader.get(&name).map(|m| m.path.clone()) {
                    result.push(path);
                }
            }
        }
    }

    result
}

/// Check if a notify event is relevant (modification of a watched file).
fn is_relevant_event(event: &Event, watch_paths: &[PathBuf]) -> bool {
    match event.kind {
        EventKind::Modify(_) | EventKind::Create(_) | EventKind::Remove(_) => {}
        _ => return false,
    }

    // Check if any event path matches our watched files.
    for event_path in &event.paths {
        let canonical = event_path
            .canonicalize()
            .unwrap_or_else(|_| event_path.clone());
        if watch_paths.iter().any(|wp| *wp == canonical) {
            return true;
        }
    }
    false
}

/// Run one check cycle, updating stats.
fn run_check_cycle(cfg: &WatchConfig, total_runs: &mut u64, cumulative_time: &mut Duration) {
    *total_runs += 1;
    let start = Instant::now();

    eprintln!(
        "--- Run #{} | {} ---\n",
        total_runs,
        chrono::Local::now().format("%H:%M:%S"),
    );

    let check_cfg = build_check_config(cfg);
    let result = cmd_check(check_cfg);

    let elapsed = start.elapsed();
    *cumulative_time += elapsed;

    match result {
        Ok(()) => {
            if cfg.on_error_only {
                // In on-error-only mode, suppress passing output.
                eprintln!("\n(pass) Elapsed: {:.2}s", elapsed.as_secs_f64());
            }
        }
        Err(e) => {
            eprintln!("\nError: {e:#}");
        }
    }

    eprintln!(
        "\n--- Total: {} run(s), cumulative {:.2}s ---",
        total_runs,
        cumulative_time.as_secs_f64(),
    );
}

/// Build a `CheckConfig` from the watch config, using sensible defaults
/// for the many check-specific fields.
fn build_check_config(cfg: &WatchConfig) -> CheckConfig {
    CheckConfig {
        file: cfg.file.clone(),
        config_path: cfg.config_path.clone(),
        compiled: false,
        quint: false,
        random_walks: 0,
        walk_depth: 10_000,
        workers: cfg.workers,
        no_deadlock: cfg.no_deadlock,
        max_states: cfg.max_states,
        max_depth: cfg.max_depth,
        memory_limit: 0,
        disk_limit: 0,
        soundness_gate: SoundnessGate::Sound,
        require_exhaustive: false,
        bmc_depth: 0,
        bmc_incremental: false,
        pdr_enabled: false,
        kinduction_enabled: false,
        kinduction_max_k: 20,
        kinduction_incremental: false,
        por_enabled: false,
        show_coverage: false,
        coverage_guided: false,
        coverage_mix_ratio: 8,
        estimate: false,
        estimate_only: None,
        no_trace: false,
        store_states: false,
        initial_capacity: None,
        mmap_fingerprints: None,
        huge_pages: false,
        disk_fingerprints: None,
        mmap_dir: None,
        trace_file_path: None,
        mmap_trace_locations: None,
        collision_check: String::new(),
        checkpoint_dir: None,
        checkpoint_interval: 300,
        resume_from: None,
        output_format: OutputFormat::Human,
        trace_format: TraceFormat::Text,
        difftrace: false,
        explain_trace: false,
        continue_on_error: false,
        allow_incomplete: false,
        force: true, // Always re-run, skip cache.
        profile_enum: false,
        profile_enum_detail: false,
        profile_eval: false,
        liveness_mode: LivenessModeArg::Full,
        strict_liveness: false,
        jit: false,
        jit_verify: false,
        no_preprocess: false,
        partial_eval: false,
        pipeline: false,
        strategy: None,
        fused: false,
        portfolio: false,
        portfolio_strategies: Vec::new(),
        cli_init: None,
        cli_next: None,
        cli_invariants: Vec::new(),
        cli_properties: Vec::new(),
        cli_constants: Vec::new(),
        trace_invariants: Vec::new(),
        inductive_check_invariant: None,
        no_config: false,
        allow_io: false,
        symbolic_sim: false,
        symbolic_sim_runs: 0,
        symbolic_sim_length: 0,
        incremental: None,
        distributed: false,
        distributed_nodes: Vec::new(),
        distributed_node_id: 0,
        show_tiers: false,
        type_specialize: crate::cli_schema::TypeSpecializeArg::Auto,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_resolve_config_path_explicit_overrides_derived() {
        let explicit = PathBuf::from("/tmp/custom.cfg");
        let result = resolve_config_path(Path::new("Spec.tla"), Some(&explicit));
        assert_eq!(result, Some(PathBuf::from("/tmp/custom.cfg")));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_resolve_config_path_none_when_no_cfg_exists() {
        // Use a spec path where no .cfg exists.
        let result = resolve_config_path(Path::new("/tmp/nonexistent_spec.tla"), None);
        assert_eq!(result, None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_is_relevant_event_modify() {
        let watch_paths = vec![PathBuf::from("/tmp/test.tla")];
        let event = Event {
            kind: EventKind::Modify(notify::event::ModifyKind::Data(
                notify::event::DataChange::Content,
            )),
            paths: vec![PathBuf::from("/tmp/test.tla")],
            attrs: Default::default(),
        };
        assert!(is_relevant_event(&event, &watch_paths));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_is_relevant_event_unrelated_path() {
        let watch_paths = vec![PathBuf::from("/tmp/test.tla")];
        let event = Event {
            kind: EventKind::Modify(notify::event::ModifyKind::Data(
                notify::event::DataChange::Content,
            )),
            paths: vec![PathBuf::from("/tmp/other.tla")],
            attrs: Default::default(),
        };
        assert!(!is_relevant_event(&event, &watch_paths));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_is_relevant_event_access_ignored() {
        let watch_paths = vec![PathBuf::from("/tmp/test.tla")];
        let event = Event {
            kind: EventKind::Access(notify::event::AccessKind::Read),
            paths: vec![PathBuf::from("/tmp/test.tla")],
            attrs: Default::default(),
        };
        assert!(!is_relevant_event(&event, &watch_paths));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_build_check_config_force_always_true() {
        let cfg = WatchConfig {
            file: PathBuf::from("test.tla"),
            config_path: None,
            on_error_only: false,
            debounce_ms: 500,
            clear: false,
            workers: 0,
            no_deadlock: false,
            max_states: 0,
            max_depth: 0,
        };
        let check_cfg = build_check_config(&cfg);
        // Watch mode always bypasses cache.
        assert!(check_cfg.force);
    }
}
