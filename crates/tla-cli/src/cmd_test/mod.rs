// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `test` subcommand: property-based testing of TLA+ specifications.
//!
//! Runs N random walks through the state space, checking invariants along each
//! trace. Reports results in a test-framework style with per-invariant pass/fail
//! and trace statistics. Exit code 0 on all-pass, 1 on any failure.
//!
//! Unlike `check` (exhaustive BFS) or `simulate` (exploration-oriented), `test`
//! is designed for quick feedback during development: clean output, fast random
//! exploration, and deterministic replay via `--seed`.
//!
//! Supports `--workers N` for parallel trace generation: each worker thread
//! gets its own `ModelChecker` and runs an independent slice of the walks.

use std::path::Path;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use anyhow::{bail, Context, Result};
use tla_check::{
    resolve_spec_from_config_with_extends, Config, ModelChecker, RandomWalkConfig,
    RandomWalkResult, ResolvedSpec,
};
use tla_core::ast::Module;
use tla_core::{lower_error_diagnostic, lower_main_module, FileId, ModuleLoader};

use crate::{parse_or_report, read_source};

/// Configuration for the `tla2 test` subcommand, built from CLI args.
pub(crate) struct TestConfig {
    pub file: std::path::PathBuf,
    pub config_path: Option<std::path::PathBuf>,
    pub runs: usize,
    pub depth: usize,
    pub seed: u64,
    pub workers: usize,
    pub no_deadlock: bool,
}

pub(crate) fn cmd_test(cfg: TestConfig) -> Result<()> {
    let file = &cfg.file;
    let start = Instant::now();

    // Parse the TLA+ source file.
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    // Load extended and instanced modules.
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);

    let _extended_names = loader
        .load_extends(&module)
        .context("failed to load extended modules")?;
    let _instance_names = loader
        .load_instances(&module)
        .context("failed to load instanced modules")?;

    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules = loader.modules_for_model_checking(&module);

    // Resolve config.
    let config_path = resolve_config_path(file, cfg.config_path.as_deref())?;
    let config_source = std::fs::read_to_string(&config_path)
        .with_context(|| format!("read config {}", config_path.display()))?;

    let mut config = Config::parse(&config_source).map_err(|errors| {
        for err in &errors {
            eprintln!("{}:{}: {}", config_path.display(), err.line(), err);
        }
        anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
    })?;

    if config.specification_conflicts_with_init_next() {
        bail!("SPECIFICATION and INIT/NEXT are mutually exclusive");
    }

    // Resolve SPECIFICATION if needed.
    let spec_scope_module_names: Vec<&str> = extended_modules_for_resolve
        .iter()
        .chain(instanced_modules_for_resolve.iter())
        .map(|m| m.name.node.as_str())
        .collect();
    let extended_syntax_trees: Vec<_> = spec_scope_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.syntax_tree))
        .collect();

    let mut resolved_spec = None;
    if (config.init.is_none() || config.next.is_none()) && config.specification.is_some() {
        match resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees) {
            Ok(resolved) => {
                if config.init.is_none() {
                    config.init = Some(resolved.init.clone());
                }
                if config.next.is_none() {
                    config.next = Some(resolved.next.clone());
                }
                resolved_spec = Some(resolved);
            }
            Err(e) => bail!("Failed to resolve SPECIFICATION: {}", e),
        }
    }
    config.normalize_resolved_specification();

    // Build invariant list for reporting.
    let invariant_names: Vec<String> = config.invariants.clone();
    let has_invariants = !invariant_names.is_empty();
    let check_deadlock = !cfg.no_deadlock && config.check_deadlock;

    // Determine effective worker count. Fall back to sequential if the spec
    // uses an inline NEXT expression (ResolvedSpec with next_node), because
    // SyntaxNode is !Send and cannot be shared across threads.
    let has_inline_next = resolved_spec
        .as_ref()
        .is_some_and(|r| r.next_node.is_some());

    let effective_workers = if has_inline_next {
        // SyntaxNode is !Send — force sequential.
        1
    } else if cfg.workers == 0 {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    } else {
        cfg.workers
    };

    // Print test header.
    println!();
    println!("tla2 test  {}", file.display());
    println!(
        "  config:    {}",
        config_path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
    );
    if let Some(ref init) = config.init {
        println!("  init:      {init}");
    }
    if let Some(ref next) = config.next {
        println!("  next:      {next}");
    }
    if has_invariants {
        println!("  invariants: {}", invariant_names.join(", "));
    }
    if check_deadlock {
        println!("  deadlock:  checked");
    }
    println!(
        "  runs:      {}  depth: {}  seed: {}  workers: {}",
        cfg.runs,
        cfg.depth,
        if cfg.seed == 0 {
            "random".to_string()
        } else {
            cfg.seed.to_string()
        },
        effective_workers,
    );
    println!();

    // Build runtime config for checker construction.
    let runtime_config = config.runtime_model_config();

    // Run walks: sequential if 1 worker, parallel otherwise.
    let walk_result = if effective_workers <= 1 {
        run_sequential(
            &module,
            &checker_modules,
            &runtime_config,
            check_deadlock,
            resolved_spec.as_ref(),
            cfg.runs,
            cfg.depth,
            cfg.seed,
        )
    } else {
        // Parallel path: no inline NEXT (guaranteed by the check above).
        run_parallel(
            &module,
            &checker_modules,
            &runtime_config,
            check_deadlock,
            cfg.runs,
            cfg.depth,
            cfg.seed,
            effective_workers,
        )
    };

    let elapsed = start.elapsed();

    // Report results in test-framework style.
    match walk_result {
        RandomWalkResult::NoViolationFound {
            walks_completed,
            total_steps,
        } => {
            // All invariants passed across all walks.
            if has_invariants {
                for inv_name in &invariant_names {
                    println!("  PASS  {inv_name}");
                }
            }
            if check_deadlock {
                println!("  PASS  (deadlock freedom)");
            }
            if !has_invariants && !check_deadlock {
                println!("  PASS  (no invariant violations, no deadlocks)");
            }
            println!();
            print_stats(walks_completed, total_steps, cfg.depth, elapsed);
            println!();
            println!("ok  -- {} run(s), no violations", walks_completed);
            Ok(())
        }
        RandomWalkResult::InvariantViolation {
            invariant,
            trace,
            walk_id,
            depth,
        } => {
            // Report which invariants passed and which failed.
            for inv_name in &invariant_names {
                if *inv_name == invariant {
                    println!("  FAIL  {inv_name}  (walk {walk_id}, depth {depth})");
                } else {
                    println!("  --    {inv_name}");
                }
            }
            if check_deadlock {
                println!("  --    (deadlock freedom)");
            }
            println!();
            println!("Counterexample trace ({} states):", trace.len());
            println!("{trace}");
            print_stats(walk_id + 1, depth, cfg.depth, elapsed);
            println!();
            bail!("FAILED -- invariant `{invariant}` violated at depth {depth} (walk {walk_id})");
        }
        RandomWalkResult::Deadlock {
            trace,
            walk_id,
            depth,
        } => {
            if has_invariants {
                for inv_name in &invariant_names {
                    println!("  --    {inv_name}");
                }
            }
            println!("  FAIL  (deadlock freedom)  (walk {walk_id}, depth {depth})");
            println!();
            println!("Deadlock trace ({} states):", trace.len());
            println!("{trace}");
            print_stats(walk_id + 1, depth, cfg.depth, elapsed);
            println!();
            bail!("FAILED -- deadlock at depth {depth} (walk {walk_id})");
        }
        RandomWalkResult::Error(e) => {
            bail!("test run failed: {e}");
        }
    }
}

// ---------------------------------------------------------------------------
// Sequential execution: single ModelChecker, batched for progress reporting
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn run_sequential(
    module: &Module,
    checker_modules: &[&Module],
    runtime_config: &Config,
    check_deadlock: bool,
    resolved_spec: Option<&ResolvedSpec>,
    num_runs: usize,
    max_depth: usize,
    seed: u64,
) -> RandomWalkResult {
    let mut checker =
        ModelChecker::new_with_extends(module, checker_modules, runtime_config);
    checker.set_deadlock_check(check_deadlock);

    if let Some(resolved) = resolved_spec {
        if let Err(e) = checker.register_inline_next(resolved) {
            return RandomWalkResult::Error(e);
        }
    }

    // Run walks in batches of 10 for progress reporting.
    let batch_size = 10;
    let mut total_walks: usize = 0;
    let mut total_steps: usize = 0;

    while total_walks < num_runs {
        let remaining = num_runs - total_walks;
        let this_batch = remaining.min(batch_size);

        let walk_config = RandomWalkConfig {
            num_walks: this_batch,
            max_depth,
            seed: if seed == 0 {
                None
            } else {
                Some(seed.wrapping_add(total_walks as u64))
            },
        };

        let result = checker.random_walk(&walk_config);
        match result {
            RandomWalkResult::NoViolationFound {
                walks_completed,
                total_steps: steps,
            } => {
                total_walks += walks_completed;
                total_steps += steps;
                eprint!("\r  progress: {total_walks}/{num_runs} runs completed");
            }
            RandomWalkResult::InvariantViolation {
                invariant,
                trace,
                walk_id,
                depth,
            } => {
                eprintln!();
                return RandomWalkResult::InvariantViolation {
                    invariant,
                    trace,
                    walk_id: total_walks + walk_id,
                    depth,
                };
            }
            RandomWalkResult::Deadlock {
                trace,
                walk_id,
                depth,
            } => {
                eprintln!();
                return RandomWalkResult::Deadlock {
                    trace,
                    walk_id: total_walks + walk_id,
                    depth,
                };
            }
            RandomWalkResult::Error(e) => {
                eprintln!();
                return RandomWalkResult::Error(e);
            }
        }
    }
    eprintln!();

    RandomWalkResult::NoViolationFound {
        walks_completed: total_walks,
        total_steps,
    }
}

// ---------------------------------------------------------------------------
// Parallel execution: one ModelChecker per thread, first-violation-wins
// ---------------------------------------------------------------------------

/// Run walks in parallel. Callers must ensure `resolved_spec` has no inline
/// NEXT node (i.e., `next_node.is_none()`) — this is enforced at the call
/// site by falling back to sequential when `next_node.is_some()`.
#[allow(clippy::too_many_arguments)]
fn run_parallel(
    module: &Module,
    checker_modules: &[&Module],
    runtime_config: &Config,
    check_deadlock: bool,
    num_runs: usize,
    max_depth: usize,
    seed: u64,
    num_workers: usize,
) -> RandomWalkResult {
    // Divide runs across workers.
    let runs_per_worker = num_runs / num_workers;
    let remainder = num_runs % num_workers;

    // Shared progress counter.
    let completed_walks = Arc::new(AtomicUsize::new(0));
    let total_steps = Arc::new(AtomicUsize::new(0));

    // First violation found by any worker.
    let first_violation: Arc<Mutex<Option<RandomWalkResult>>> = Arc::new(Mutex::new(None));
    let stop_flag = Arc::new(AtomicBool::new(false));

    std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(num_workers);

        for worker_id in 0..num_workers {
            let worker_runs = runs_per_worker + if worker_id < remainder { 1 } else { 0 };
            if worker_runs == 0 {
                continue;
            }

            // Compute global walk-ID offset for this worker.
            let walk_offset: usize = (0..worker_id)
                .map(|w| runs_per_worker + if w < remainder { 1 } else { 0 })
                .sum();

            let completed = Arc::clone(&completed_walks);
            let steps_counter = Arc::clone(&total_steps);
            let violation = Arc::clone(&first_violation);
            let stop = Arc::clone(&stop_flag);

            let handle = s.spawn(move || {
                // Each thread gets its own ModelChecker (borrows module/config from scope).
                let mut checker = ModelChecker::new_with_extends(
                    module,
                    checker_modules,
                    runtime_config,
                );
                checker.set_deadlock_check(check_deadlock);

                // No register_inline_next needed: callers guarantee no inline NEXT.

                // Run walks one at a time so we can check the stop flag.
                for local_walk in 0..worker_runs {
                    if stop.load(Ordering::Relaxed) {
                        return;
                    }

                    let walk_config = RandomWalkConfig {
                        num_walks: 1,
                        max_depth,
                        seed: if seed == 0 {
                            None
                        } else {
                            Some(seed.wrapping_add((walk_offset + local_walk) as u64))
                        },
                    };

                    let result = checker.random_walk(&walk_config);
                    match result {
                        RandomWalkResult::NoViolationFound {
                            total_steps: steps, ..
                        } => {
                            steps_counter.fetch_add(steps, Ordering::Relaxed);
                            let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
                            if done % 10 == 0 || done == num_runs {
                                eprint!("\r  progress: {done}/{num_runs} runs completed");
                            }
                        }
                        RandomWalkResult::InvariantViolation {
                            invariant,
                            trace,
                            depth,
                            ..
                        } => {
                            stop.store(true, Ordering::Relaxed);
                            let mut guard = violation.lock().expect("lock poisoned");
                            if guard.is_none() {
                                *guard = Some(RandomWalkResult::InvariantViolation {
                                    invariant,
                                    trace,
                                    walk_id: walk_offset + local_walk,
                                    depth,
                                });
                            }
                            return;
                        }
                        RandomWalkResult::Deadlock { trace, depth, .. } => {
                            stop.store(true, Ordering::Relaxed);
                            let mut guard = violation.lock().expect("lock poisoned");
                            if guard.is_none() {
                                *guard = Some(RandomWalkResult::Deadlock {
                                    trace,
                                    walk_id: walk_offset + local_walk,
                                    depth,
                                });
                            }
                            return;
                        }
                        RandomWalkResult::Error(e) => {
                            stop.store(true, Ordering::Relaxed);
                            let mut guard = violation.lock().expect("lock poisoned");
                            if guard.is_none() {
                                *guard = Some(RandomWalkResult::Error(e));
                            }
                            return;
                        }
                    }
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().expect("worker thread panicked");
        }
    });

    eprintln!();

    // Check if any violation was found.
    let taken = Arc::try_unwrap(first_violation)
        .expect("all threads joined")
        .into_inner()
        .expect("lock poisoned");

    if let Some(v) = taken {
        return v;
    }

    RandomWalkResult::NoViolationFound {
        walks_completed: completed_walks.load(Ordering::Relaxed),
        total_steps: total_steps.load(Ordering::Relaxed),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Resolve the .cfg config file path: explicit path or default `<file>.cfg`.
fn resolve_config_path(spec_file: &Path, explicit: Option<&Path>) -> Result<std::path::PathBuf> {
    match explicit {
        Some(p) => Ok(p.to_path_buf()),
        None => {
            let mut cfg_path = spec_file.to_path_buf();
            cfg_path.set_extension("cfg");
            if !cfg_path.exists() {
                bail!(
                    "No config file specified and {} does not exist.\n\
                     Use --config to specify a configuration file.",
                    cfg_path.display()
                );
            }
            Ok(cfg_path)
        }
    }
}

fn print_stats(walks: usize, total_steps: usize, max_depth: usize, elapsed: std::time::Duration) {
    let secs = elapsed.as_secs_f64();
    let steps_per_sec = if secs > 0.0 {
        total_steps as f64 / secs
    } else {
        0.0
    };
    println!("  walks:     {walks}");
    println!("  steps:     {total_steps}");
    println!("  max depth: {max_depth}");
    println!("  time:      {secs:.3}s");
    println!("  steps/sec: {steps_per_sec:.0}");
}
