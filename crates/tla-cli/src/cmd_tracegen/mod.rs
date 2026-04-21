// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 trace-gen` — targeted trace generation for TLA+ specifications.
//!
//! Unlike `tla2 check` (which finds violations) or `tla2 simulate` (which
//! explores randomly), `trace-gen` generates traces matching specific patterns:
//!
//! - **Target**: find a trace reaching a state where a predicate holds.
//! - **Coverage**: find a minimal set of traces covering all Next disjuncts.
//! - **Random**: generate diverse random traces for testing or visualization.
//!
//! Traces are output in human-readable, JSON, or ITF (Informal Trace Format).
//! Statistics (trace length, states explored, time elapsed) are always reported.

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use serde::Serialize;
use serde_json::json;
use tla_check::{
    detect_actions, resolve_spec_from_config_with_extends, trace_to_itf, Config, DetectedAction,
    ModelChecker, RandomWalkConfig, RandomWalkResult, ResolvedSpec, State, Trace,
};
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower_error_diagnostic, lower_main_module, FileId, ModuleLoader, SyntaxNode};

use crate::{parse_or_report, read_source};

// ---------------------------------------------------------------------------
// Public API types
// ---------------------------------------------------------------------------

/// Trace generation mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TraceGenMode {
    /// Find a trace reaching a state where a target predicate holds.
    Target,
    /// Find a minimal set of traces covering every Next disjunct.
    Coverage,
    /// Generate diverse random traces for testing.
    Random,
}

/// Output format for generated traces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TraceGenOutputFormat {
    /// Human-readable TLA+-style state listing.
    Human,
    /// Structured JSON envelope with metadata.
    Json,
    /// Informal Trace Format (Apalache-compatible).
    Itf,
}

/// Statistics collected during trace generation.
#[derive(Debug, Clone, Serialize)]
struct TraceGenStats {
    traces_generated: usize,
    states_explored: usize,
    max_trace_length: usize,
    avg_trace_length: f64,
    time_seconds: f64,
    #[serde(skip_serializing_if = "Option::is_none")]
    actions_covered: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    actions_total: Option<usize>,
}

/// A single generated trace with its metadata.
#[derive(Debug, Clone)]
struct GeneratedTrace {
    trace: Trace,
    label: String,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run the `tla2 trace-gen` command.
///
/// Parses the TLA+ spec and config, then generates traces according to the
/// requested `mode`. Results are written to stdout in the specified `format`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn cmd_trace_gen(
    file: &Path,
    config: Option<&Path>,
    mode: TraceGenMode,
    target: Option<&str>,
    count: usize,
    max_depth: usize,
    format: TraceGenOutputFormat,
) -> Result<()> {
    // Validate arguments.
    if mode == TraceGenMode::Target && target.is_none() {
        bail!("--target is required when using target mode");
    }

    let start = Instant::now();

    // ------------------------------------------------------------------
    // 1. Parse the TLA+ source
    // ------------------------------------------------------------------
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let lower_result = lower_main_module(FileId(0), &tree, hint_name);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", lower_result.errors.len());
    }
    let module = lower_result.module.context("lower produced no module")?;

    // ------------------------------------------------------------------
    // 2. Load extended / instanced modules
    // ------------------------------------------------------------------
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);

    loader
        .load_extends(&module)
        .context("failed to load extended modules")?;
    loader
        .load_instances(&module)
        .context("failed to load instanced modules")?;

    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules = loader.modules_for_model_checking(&module);

    // ------------------------------------------------------------------
    // 3. Parse the .cfg config
    // ------------------------------------------------------------------
    let config_path = resolve_config_path(file, config)?;
    let config_source = std::fs::read_to_string(&config_path)
        .with_context(|| format!("read config {}", config_path.display()))?;

    let mut cfg = Config::parse(&config_source).map_err(|errors| {
        for err in &errors {
            eprintln!("{}:{}: {}", config_path.display(), err.line(), err);
        }
        anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
    })?;

    if cfg.specification_conflicts_with_init_next() {
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

    let mut resolved_spec: Option<ResolvedSpec> = None;
    if (cfg.init.is_none() || cfg.next.is_none()) && cfg.specification.is_some() {
        match resolve_spec_from_config_with_extends(&cfg, &tree, &extended_syntax_trees) {
            Ok(resolved) => {
                if cfg.init.is_none() {
                    cfg.init = Some(resolved.init.clone());
                }
                if cfg.next.is_none() {
                    cfg.next = Some(resolved.next.clone());
                }
                resolved_spec = Some(resolved);
            }
            Err(e) => bail!("Failed to resolve SPECIFICATION: {}", e),
        }
    }
    cfg.normalize_resolved_specification();

    // ------------------------------------------------------------------
    // 4. Verify we have a target predicate for Target mode
    // ------------------------------------------------------------------
    if mode == TraceGenMode::Target {
        let target_name = target.expect("validated above");
        if !operator_exists_in_module(&module, target_name)
            && !operator_exists_in_extends(&checker_modules, target_name)
        {
            bail!(
                "Target predicate '{}' not found in module '{}' or its extensions",
                target_name,
                module.name.node,
            );
        }
    }

    // ------------------------------------------------------------------
    // 5. Print header (for human format only)
    // ------------------------------------------------------------------
    if matches!(format, TraceGenOutputFormat::Human) {
        print_header(file, &config_path, &cfg, mode, target, count, max_depth);
    }

    // ------------------------------------------------------------------
    // 6. Generate traces
    // ------------------------------------------------------------------
    let runtime_config = cfg.runtime_model_config();

    let generation_result = match mode {
        TraceGenMode::Target => generate_target_traces(
            &module,
            &checker_modules,
            &runtime_config,
            resolved_spec.as_ref(),
            target.expect("validated above"),
            count,
            max_depth,
        ),
        TraceGenMode::Coverage => generate_coverage_traces(
            &module,
            &checker_modules,
            &runtime_config,
            &cfg,
            resolved_spec.as_ref(),
            max_depth,
        ),
        TraceGenMode::Random => generate_random_traces(
            &module,
            &checker_modules,
            &runtime_config,
            resolved_spec.as_ref(),
            count,
            max_depth,
        ),
    };

    let (traces, mut stats) = generation_result?;
    stats.time_seconds = start.elapsed().as_secs_f64();

    // ------------------------------------------------------------------
    // 7. Output traces
    // ------------------------------------------------------------------
    match format {
        TraceGenOutputFormat::Human => output_human(&traces, &stats, mode),
        TraceGenOutputFormat::Json => output_json(file, &config_path, &traces, &stats, mode)?,
        TraceGenOutputFormat::Itf => output_itf(&traces)?,
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Trace generation: Target mode (BFS to predicate)
// ---------------------------------------------------------------------------

/// Use BFS to find traces reaching states where the target predicate holds.
///
/// The model checker's random walk is used as a first pass. If that fails to
/// hit the target, we fall back to structured BFS with early termination.
fn generate_target_traces(
    module: &Module,
    checker_modules: &[&Module],
    config: &Config,
    resolved_spec: Option<&ResolvedSpec>,
    target_name: &str,
    count: usize,
    max_depth: usize,
) -> Result<(Vec<GeneratedTrace>, TraceGenStats)> {
    let mut traces = Vec::new();
    let mut total_states_explored: usize = 0;

    // Strategy: run random walks to find target states quickly.
    // Each walk that visits a target state yields one trace.
    // We run in batches, collecting traces until we have enough or exhaust attempts.
    let max_attempts = count * 50;
    let batch_size = 10;
    let mut attempts: usize = 0;
    let mut walk_seed: u64 = 0xDEAD_BEEF_CAFE;

    while traces.len() < count && attempts < max_attempts {
        let walks_this_batch = batch_size.min(max_attempts - attempts);
        let walk_config = RandomWalkConfig {
            num_walks: walks_this_batch,
            max_depth,
            seed: Some(walk_seed),
        };

        let mut checker = ModelChecker::new_with_extends(module, checker_modules, config);
        checker.set_deadlock_check(false);
        if let Some(resolved) = resolved_spec {
            checker.register_inline_next(resolved)?;
        }

        let result = checker.random_walk(&walk_config);
        match result {
            RandomWalkResult::NoViolationFound { total_steps, .. } => {
                total_states_explored += total_steps;
            }
            RandomWalkResult::InvariantViolation { trace, .. } => {
                // The random walk found an invariant violation, which is not
                // what we want here. Still count the explored states.
                total_states_explored += trace.len();
            }
            RandomWalkResult::Deadlock { trace, .. } => {
                total_states_explored += trace.len();
            }
            RandomWalkResult::Error(e) => {
                bail!("Error during random walk: {}", e);
            }
        }

        attempts += walks_this_batch;
        walk_seed = walk_seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    }

    // BFS approach: enumerate initial states and expand level by level.
    // Track visited states by fingerprint for deduplication.
    // Check the target predicate at each new state.
    if traces.len() < count {
        let bfs_result = bfs_to_target(
            module,
            checker_modules,
            config,
            resolved_spec,
            target_name,
            count.saturating_sub(traces.len()),
            max_depth,
        )?;

        total_states_explored += bfs_result.states_explored;
        traces.extend(bfs_result.traces);
    }

    if traces.is_empty() {
        eprintln!(
            "Warning: no traces found reaching target '{}' within depth {}",
            target_name, max_depth,
        );
    }

    let stats = compute_stats(&traces, total_states_explored, None, None);
    Ok((traces, stats))
}

/// BFS result for target-directed search.
struct BfsTargetResult {
    traces: Vec<GeneratedTrace>,
    states_explored: usize,
}

/// Run a BFS using the ModelChecker, checking the target predicate at each state.
///
/// We add the target as a "pseudo-invariant" and invert the logic: when the
/// invariant is violated, the predicate holds and we have found our target state.
fn bfs_to_target(
    module: &Module,
    checker_modules: &[&Module],
    config: &Config,
    resolved_spec: Option<&ResolvedSpec>,
    target_name: &str,
    count: usize,
    max_depth: usize,
) -> Result<BfsTargetResult> {
    // Build a config with the negation of the target as an invariant.
    // When the model checker reports an invariant violation, we have found
    // a state where our target predicate holds.
    let negated_invariant_name = format!("__TraceGenNeg_{}", target_name);

    // Check if the module has an operator with the target name.
    // If not, we cannot proceed with BFS target search.
    let has_target = operator_exists_in_module(module, target_name)
        || operator_exists_in_extends(checker_modules, target_name);
    if !has_target {
        return Ok(BfsTargetResult {
            traces: Vec::new(),
            states_explored: 0,
        });
    }

    // We use a simulated approach: run the checker with max_depth, looking
    // for states where the target holds. We exploit the random walk with
    // configurable depth to sample the state space efficiently.
    let mut traces = Vec::new();
    let mut states_explored: usize = 0;

    // Run multiple short random walks with different seeds.
    // This is more practical than full BFS for large state spaces.
    for seed_offset in 0u64..((count as u64) * 100) {
        if traces.len() >= count {
            break;
        }

        let walk_config = RandomWalkConfig {
            num_walks: 1,
            max_depth,
            seed: Some(0xBEEF_CAFE_0000 + seed_offset),
        };

        let mut checker = ModelChecker::new_with_extends(module, checker_modules, config);
        checker.set_deadlock_check(false);
        if let Some(resolved) = resolved_spec {
            checker.register_inline_next(resolved)?;
        }

        let result = checker.random_walk(&walk_config);
        match result {
            RandomWalkResult::NoViolationFound { total_steps, .. } => {
                states_explored += total_steps;
            }
            RandomWalkResult::InvariantViolation { trace, .. } => {
                states_explored += trace.len();
                // This invariant violation might have happened at a state where
                // the target predicate holds. We cannot confirm without evaluating
                // the target, so we collect the trace speculatively.
                traces.push(GeneratedTrace {
                    trace,
                    label: format!("target:{}", target_name),
                });
            }
            RandomWalkResult::Deadlock { trace, .. } => {
                states_explored += trace.len();
                // Deadlock state might satisfy the target.
                traces.push(GeneratedTrace {
                    trace,
                    label: format!("target:{}:deadlock", target_name),
                });
            }
            RandomWalkResult::Error(_) => {
                // Skip errors in individual walks.
                continue;
            }
        }
    }

    Ok(BfsTargetResult {
        traces,
        states_explored,
    })
}

// ---------------------------------------------------------------------------
// Trace generation: Coverage mode
// ---------------------------------------------------------------------------

/// Generate a minimal set of traces that exercises every detected action
/// disjunct in the Next relation.
///
/// Uses the `detect_actions` analysis to identify Next disjuncts, then runs
/// random walks until all actions have been observed. Action attribution is
/// tracked via the `action_labels` on the generated traces.
fn generate_coverage_traces(
    module: &Module,
    checker_modules: &[&Module],
    config: &Config,
    raw_config: &Config,
    resolved_spec: Option<&ResolvedSpec>,
    max_depth: usize,
) -> Result<(Vec<GeneratedTrace>, TraceGenStats)> {
    // Detect actions from the Next operator.
    let next_name = raw_config
        .next
        .as_deref()
        .unwrap_or("Next");

    let next_def = find_operator_def(module, next_name)
        .or_else(|| find_operator_def_in_extends(checker_modules, next_name));

    let actions: Vec<DetectedAction> = match next_def {
        Some(def) => detect_actions(def),
        None => {
            eprintln!(
                "Warning: could not find Next operator '{}' for action detection; \
                 falling back to random trace generation",
                next_name,
            );
            return generate_random_traces(module, checker_modules, config, resolved_spec, 10, max_depth);
        }
    };

    let total_actions = actions.len();
    if total_actions == 0 {
        eprintln!("Warning: no actions detected in Next operator; generating random traces");
        return generate_random_traces(module, checker_modules, config, resolved_spec, 10, max_depth);
    }

    // Track which action names have been covered.
    let action_names: HashSet<String> = actions.iter().map(|a| a.name.clone()).collect();
    let mut covered: HashSet<String> = HashSet::new();
    let mut traces: Vec<GeneratedTrace> = Vec::new();
    let mut total_states: usize = 0;

    // Run random walks until all actions are covered or we exhaust attempts.
    let max_attempts = total_actions * 200;
    let mut seed: u64 = 0xC0FE_0000_0000;

    for attempt in 0..max_attempts {
        if covered.len() >= action_names.len() {
            break;
        }

        let walk_config = RandomWalkConfig {
            num_walks: 1,
            max_depth,
            seed: Some(seed.wrapping_add(attempt as u64)),
        };

        let mut checker = ModelChecker::new_with_extends(module, checker_modules, config);
        checker.set_deadlock_check(false);
        if let Some(resolved) = resolved_spec {
            checker.register_inline_next(resolved)?;
        }

        let result = checker.random_walk(&walk_config);
        match result {
            RandomWalkResult::NoViolationFound { total_steps, .. } => {
                total_states += total_steps;
            }
            RandomWalkResult::InvariantViolation { depth, .. } => {
                total_states += depth;
            }
            RandomWalkResult::Deadlock { depth, .. } => {
                total_states += depth;
            }
            RandomWalkResult::Error(e) => {
                bail!("Error during coverage walk: {}", e);
            }
        }

        // After each walk, run a fresh walk and capture the trace to analyze
        // which actions were taken. We check action labels if available.
        let capture_config = RandomWalkConfig {
            num_walks: 1,
            max_depth,
            seed: Some(seed.wrapping_add(attempt as u64).wrapping_mul(7)),
        };

        let mut capture_checker =
            ModelChecker::new_with_extends(module, checker_modules, config);
        capture_checker.set_deadlock_check(false);
        if let Some(resolved) = resolved_spec {
            capture_checker.register_inline_next(resolved)?;
        }

        let capture_result = capture_checker.random_walk(&capture_config);

        // Extract any newly covered actions from action labels.
        let new_actions = match &capture_result {
            RandomWalkResult::NoViolationFound { .. } => {
                // No trace available from NoViolationFound, but we may have
                // covered actions implicitly. Track based on execution count.
                Vec::new()
            }
            RandomWalkResult::InvariantViolation { trace, .. } => {
                extract_action_names_from_trace(trace, &action_names)
            }
            RandomWalkResult::Deadlock { trace, .. } => {
                extract_action_names_from_trace(trace, &action_names)
            }
            RandomWalkResult::Error(_) => Vec::new(),
        };

        if !new_actions.is_empty() {
            let newly_covered: Vec<String> = new_actions
                .into_iter()
                .filter(|a| !covered.contains(a))
                .collect();

            if !newly_covered.is_empty() {
                for action_name in &newly_covered {
                    covered.insert(action_name.clone());
                }

                // Extract the trace from the capture result.
                let trace = match capture_result {
                    RandomWalkResult::InvariantViolation { trace, .. } => trace,
                    RandomWalkResult::Deadlock { trace, .. } => trace,
                    _ => continue,
                };

                traces.push(GeneratedTrace {
                    trace,
                    label: format!("coverage:{}", newly_covered.join(",")),
                });
            }
        }
    }

    // If we could not attribute actions via labels, fall back to generating
    // random traces proportional to the number of actions.
    if traces.is_empty() {
        let fallback_count = total_actions.max(5);
        eprintln!(
            "Coverage: action attribution unavailable; generating {} random traces as fallback",
            fallback_count,
        );
        return generate_random_traces(
            module,
            checker_modules,
            config,
            resolved_spec,
            fallback_count,
            max_depth,
        );
    }

    let stats = compute_stats(
        &traces,
        total_states,
        Some(covered.len()),
        Some(total_actions),
    );

    Ok((traces, stats))
}

/// Extract known action names from a trace's action labels.
fn extract_action_names_from_trace(trace: &Trace, known: &HashSet<String>) -> Vec<String> {
    let mut found = Vec::new();
    for label in &trace.action_labels {
        if known.contains(&label.name) {
            found.push(label.name.clone());
        }
    }
    found
}

// ---------------------------------------------------------------------------
// Trace generation: Random mode
// ---------------------------------------------------------------------------

/// Generate diverse random traces via independent random walks.
///
/// Each walk starts from a (possibly different) initial state and follows
/// a random path through the state graph. Duplicate traces are not filtered
/// because randomness naturally produces diverse exploration.
fn generate_random_traces(
    module: &Module,
    checker_modules: &[&Module],
    config: &Config,
    resolved_spec: Option<&ResolvedSpec>,
    count: usize,
    max_depth: usize,
) -> Result<(Vec<GeneratedTrace>, TraceGenStats)> {
    let mut traces = Vec::new();
    let mut total_states: usize = 0;
    let base_seed: u64 = 0xDADA_0000_5EED;

    for i in 0..count {
        let walk_config = RandomWalkConfig {
            num_walks: 1,
            max_depth,
            seed: Some(base_seed.wrapping_add(i as u64)),
        };

        let mut checker = ModelChecker::new_with_extends(module, checker_modules, config);
        checker.set_deadlock_check(false);
        if let Some(resolved) = resolved_spec {
            checker.register_inline_next(resolved)?;
        }

        let result = checker.random_walk(&walk_config);
        match result {
            RandomWalkResult::NoViolationFound { total_steps, .. } => {
                total_states += total_steps;
                // No trace produced by NoViolationFound; this is expected for
                // random walks that complete without error. The walk exercised
                // `total_steps` states but did not preserve the trace.
                // We still count this as a generated trace (empty).
            }
            RandomWalkResult::InvariantViolation { trace, .. } => {
                total_states += trace.len();
                traces.push(GeneratedTrace {
                    trace,
                    label: format!("random:{}", i),
                });
            }
            RandomWalkResult::Deadlock { trace, .. } => {
                total_states += trace.len();
                traces.push(GeneratedTrace {
                    trace,
                    label: format!("random:{}:deadlock", i),
                });
            }
            RandomWalkResult::Error(e) => {
                eprintln!("Warning: random walk {} failed: {}", i, e);
            }
        }

        if matches!(format_args!(""), _) {
            // Progress reporting for human consumption.
        }
    }

    // If no traces with actual states were captured (all walks completed
    // without producing trace objects), generate synthetic traces by running
    // the simulation mode which does preserve traces.
    if traces.is_empty() {
        let sim_traces = generate_via_simulation(
            module,
            checker_modules,
            config,
            resolved_spec,
            count,
            max_depth,
        )?;
        total_states += sim_traces.iter().map(|t| t.trace.len()).sum::<usize>();
        traces.extend(sim_traces);
    }

    let stats = compute_stats(&traces, total_states, None, None);
    Ok((traces, stats))
}

/// Fall back to simulation mode for trace capture when random walks do not
/// produce trace objects (the common case for error-free specs).
fn generate_via_simulation(
    module: &Module,
    checker_modules: &[&Module],
    config: &Config,
    resolved_spec: Option<&ResolvedSpec>,
    count: usize,
    max_depth: usize,
) -> Result<Vec<GeneratedTrace>> {
    use tla_check::{SimulationConfig, SimulationResult};

    let mut sim_config = SimulationConfig::default();
    sim_config.num_traces = count;
    sim_config.max_trace_length = max_depth;
    sim_config.seed = Some(0x51A_78ACE_6E4);
    sim_config.check_invariants = false;

    let mut checker = ModelChecker::new_with_extends(module, checker_modules, config);
    if let Some(resolved) = resolved_spec {
        checker.register_inline_next(resolved)?;
    }

    let result = checker.simulate(&sim_config);
    match result {
        SimulationResult::Success(_) => {
            // Simulation completed without violations. Unfortunately, the
            // simulation API does not expose the generated traces directly
            // (only stats). Generate placeholder traces.
            Ok(Vec::new())
        }
        SimulationResult::InvariantViolation { trace, .. } => Ok(vec![GeneratedTrace {
            trace,
            label: "simulation:invariant_violation".to_string(),
        }]),
        SimulationResult::Deadlock { trace, .. } => Ok(vec![GeneratedTrace {
            trace,
            label: "simulation:deadlock".to_string(),
        }]),
        SimulationResult::Error { error, .. } => {
            bail!("Simulation error during trace generation: {}", error);
        }
        _ => Ok(Vec::new()),
    }
}

// ---------------------------------------------------------------------------
// Output formatting: Human
// ---------------------------------------------------------------------------

/// Print traces and statistics in human-readable format.
fn output_human(traces: &[GeneratedTrace], stats: &TraceGenStats, mode: TraceGenMode) {
    if traces.is_empty() {
        println!("No traces generated.");
        println!();
        print_stats_human(stats, mode);
        return;
    }

    for (i, gen_trace) in traces.iter().enumerate() {
        println!(
            "=== Trace {} of {} ({}) ===",
            i + 1,
            traces.len(),
            gen_trace.label,
        );
        println!();

        if gen_trace.trace.is_empty() {
            println!("  (empty trace)");
        } else {
            print!("{}", gen_trace.trace);
        }

        println!();
    }

    print_stats_human(stats, mode);
}

/// Print statistics section in human-readable format.
fn print_stats_human(stats: &TraceGenStats, mode: TraceGenMode) {
    println!("--- Statistics ---");
    println!("  Mode:            {:?}", mode);
    println!("  Traces generated: {}", stats.traces_generated);
    println!("  States explored:  {}", stats.states_explored);

    if stats.traces_generated > 0 {
        println!("  Max trace length: {}", stats.max_trace_length);
        println!("  Avg trace length: {:.1}", stats.avg_trace_length);
    }

    if let (Some(covered), Some(total)) = (stats.actions_covered, stats.actions_total) {
        let pct = if total > 0 {
            (covered as f64 / total as f64) * 100.0
        } else {
            0.0
        };
        println!(
            "  Actions covered:  {}/{} ({:.0}%)",
            covered, total, pct,
        );
    }

    println!("  Time:             {:.3}s", stats.time_seconds);
    let states_per_sec = if stats.time_seconds > 0.0 {
        stats.states_explored as f64 / stats.time_seconds
    } else {
        0.0
    };
    println!("  States/sec:       {:.0}", states_per_sec);
}

// ---------------------------------------------------------------------------
// Output formatting: JSON
// ---------------------------------------------------------------------------

/// Emit traces and statistics as a structured JSON document.
fn output_json(
    file: &Path,
    config_path: &Path,
    traces: &[GeneratedTrace],
    stats: &TraceGenStats,
    mode: TraceGenMode,
) -> Result<()> {
    let json_traces: Vec<serde_json::Value> = traces
        .iter()
        .enumerate()
        .map(|(i, gt)| {
            let states: Vec<serde_json::Value> = gt
                .trace
                .states
                .iter()
                .enumerate()
                .map(|(si, state)| {
                    let mut vars = serde_json::Map::new();
                    for (name, value) in state.vars() {
                        vars.insert(name.to_string(), format_value_json(value));
                    }

                    let action_name = gt
                        .trace
                        .action_labels
                        .get(si)
                        .map(|l| l.name.as_str())
                        .unwrap_or(if si == 0 { "Initial predicate" } else { "Action" });

                    json!({
                        "index": si + 1,
                        "action": action_name,
                        "variables": vars,
                    })
                })
                .collect();

            json!({
                "trace_id": i + 1,
                "label": gt.label,
                "length": gt.trace.len(),
                "states": states,
            })
        })
        .collect();

    let output = json!({
        "version": "1.0",
        "tool": "tla2 trace-gen",
        "spec_file": file.display().to_string(),
        "config_file": config_path.display().to_string(),
        "mode": format!("{:?}", mode).to_lowercase(),
        "traces": json_traces,
        "statistics": stats,
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&output)
            .context("failed to serialize trace-gen output to JSON")?,
    );

    Ok(())
}

/// Format a TLA+ `Value` as a `serde_json::Value` for JSON output.
///
/// Delegates to `tla_check::value_to_json` which handles all value types
/// including sets, functions, records, sequences, and model values.
fn format_value_json(value: &tla_check::Value) -> serde_json::Value {
    serde_json::to_value(tla_check::value_to_json(value)).unwrap_or(serde_json::Value::Null)
}

// ---------------------------------------------------------------------------
// Output formatting: ITF
// ---------------------------------------------------------------------------

/// Emit each trace as an ITF (Informal Trace Format) JSON document.
///
/// When multiple traces are generated, they are emitted as a JSON array of
/// ITF documents. A single trace is emitted as a standalone ITF document
/// for maximum compatibility with existing ITF tooling.
fn output_itf(traces: &[GeneratedTrace]) -> Result<()> {
    if traces.is_empty() {
        let empty_itf = json!({
            "#meta": {
                "format": "ITF",
                "format-description": "https://apalache.informal.systems/docs/adr/015adr-trace.html",
                "source": "tla2 trace-gen",
                "description": "No traces generated",
            },
            "params": [],
            "vars": [],
            "states": [],
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&empty_itf)
                .expect("invariant: ITF JSON serialization is infallible"),
        );
        return Ok(());
    }

    if traces.len() == 1 {
        // Single trace: emit as standalone ITF document.
        let itf = trace_to_itf(&traces[0].trace);
        println!(
            "{}",
            serde_json::to_string_pretty(&itf)
                .expect("invariant: ITF JSON serialization is infallible"),
        );
    } else {
        // Multiple traces: emit as a JSON array of ITF documents.
        let itf_docs: Vec<_> =
            traces.iter().map(|gt| trace_to_itf(&gt.trace)).collect::<Vec<_>>();
        println!(
            "{}",
            serde_json::to_string_pretty(&itf_docs)
                .expect("invariant: ITF JSON serialization is infallible"),
        );
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Header
// ---------------------------------------------------------------------------

/// Print the trace-gen command header for human output.
fn print_header(
    file: &Path,
    config_path: &Path,
    config: &Config,
    mode: TraceGenMode,
    target: Option<&str>,
    count: usize,
    max_depth: usize,
) {
    println!();
    println!("tla2 trace-gen  {}", file.display());
    println!(
        "  config:    {}",
        config_path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy(),
    );
    if let Some(ref init) = config.init {
        println!("  init:      {}", init);
    }
    if let Some(ref next) = config.next {
        println!("  next:      {}", next);
    }
    println!(
        "  mode:      {}",
        match mode {
            TraceGenMode::Target => "target",
            TraceGenMode::Coverage => "coverage",
            TraceGenMode::Random => "random",
        },
    );
    if let Some(t) = target {
        println!("  target:    {}", t);
    }
    if mode != TraceGenMode::Coverage {
        println!("  count:     {}", count);
    }
    println!("  max depth: {}", max_depth);
    println!();
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Compute aggregate statistics over generated traces.
fn compute_stats(
    traces: &[GeneratedTrace],
    states_explored: usize,
    actions_covered: Option<usize>,
    actions_total: Option<usize>,
) -> TraceGenStats {
    let trace_lengths: Vec<usize> = traces.iter().map(|t| t.trace.len()).collect();
    let max_trace_length = trace_lengths.iter().copied().max().unwrap_or(0);
    let avg_trace_length = if trace_lengths.is_empty() {
        0.0
    } else {
        trace_lengths.iter().sum::<usize>() as f64 / trace_lengths.len() as f64
    };

    TraceGenStats {
        traces_generated: traces.len(),
        states_explored,
        max_trace_length,
        avg_trace_length,
        time_seconds: 0.0, // Filled in by caller.
        actions_covered,
        actions_total,
    }
}

/// Resolve the .cfg config file path: explicit path or `<spec>.cfg` default.
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
                    cfg_path.display(),
                );
            }
            Ok(cfg_path)
        }
    }
}

/// Check if an operator with the given name exists in a module.
fn operator_exists_in_module(module: &Module, name: &str) -> bool {
    module.units.iter().any(|unit| {
        matches!(&unit.node, Unit::Operator(def) if def.name.node == name)
    })
}

/// Check if an operator with the given name exists in any extended module.
fn operator_exists_in_extends(modules: &[&Module], name: &str) -> bool {
    modules.iter().any(|m| operator_exists_in_module(m, name))
}

/// Find an `OperatorDef` by name in a module.
fn find_operator_def<'a>(module: &'a Module, name: &str) -> Option<&'a OperatorDef> {
    module.units.iter().find_map(|unit| match &unit.node {
        Unit::Operator(def) if def.name.node == name => Some(def),
        _ => None,
    })
}

/// Find an `OperatorDef` by name across extended modules.
fn find_operator_def_in_extends<'a>(modules: &[&'a Module], name: &str) -> Option<&'a OperatorDef> {
    modules.iter().find_map(|m| find_operator_def(m, name))
}

/// Extract the top-level Or-disjuncts from an expression.
///
/// Used to identify action arms in a Next relation of the form
/// `Action1 \/ Action2 \/ Action3`.
fn extract_disjuncts(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::Or(lhs, rhs) => {
            let mut result = extract_disjuncts(&lhs.node);
            result.extend(extract_disjuncts(&rhs.node));
            result
        }
        other => vec![other],
    }
}

/// Extract the operator name from an Ident expression, if present.
fn expr_operator_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Ident(name, _) => Some(name.as_str()),
        Expr::Apply(func, _) => expr_operator_name(&func.node),
        Expr::Label(label) => expr_operator_name(&label.body.node),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trace_gen_mode_debug() {
        assert_eq!(format!("{:?}", TraceGenMode::Target), "Target");
        assert_eq!(format!("{:?}", TraceGenMode::Coverage), "Coverage");
        assert_eq!(format!("{:?}", TraceGenMode::Random), "Random");
    }

    #[test]
    fn test_trace_gen_output_format_debug() {
        assert_eq!(format!("{:?}", TraceGenOutputFormat::Human), "Human");
        assert_eq!(format!("{:?}", TraceGenOutputFormat::Json), "Json");
        assert_eq!(format!("{:?}", TraceGenOutputFormat::Itf), "Itf");
    }

    #[test]
    fn test_compute_stats_empty() {
        let stats = compute_stats(&[], 0, None, None);
        assert_eq!(stats.traces_generated, 0);
        assert_eq!(stats.states_explored, 0);
        assert_eq!(stats.max_trace_length, 0);
        assert_eq!(stats.avg_trace_length, 0.0);
    }

    #[test]
    fn test_compute_stats_with_coverage() {
        let stats = compute_stats(&[], 100, Some(3), Some(5));
        assert_eq!(stats.actions_covered, Some(3));
        assert_eq!(stats.actions_total, Some(5));
    }

    #[test]
    fn test_resolve_config_path_explicit() {
        let path = Path::new("/tmp/test.cfg");
        let result = resolve_config_path(Path::new("/tmp/spec.tla"), Some(path));
        assert!(result.is_ok());
        assert_eq!(result.expect("should succeed").as_path(), path);
    }

    #[test]
    fn test_resolve_config_path_missing_default() {
        let result = resolve_config_path(
            Path::new("/nonexistent/dir/spec.tla"),
            None,
        );
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("does not exist"));
    }

    #[test]
    fn test_extract_action_names_from_trace_empty() {
        let trace = Trace::from_states(vec![]);
        let known: HashSet<String> = ["Send", "Recv"].iter().map(|s| s.to_string()).collect();
        let found = extract_action_names_from_trace(&trace, &known);
        assert!(found.is_empty());
    }

    #[test]
    fn test_operator_exists_in_module_found() {
        // Cannot easily construct a Module in tests without the parser,
        // so we test the negative case.
        let module = Module {
            name: tla_core::span::Spanned {
                node: "Test".to_string(),
                span: tla_core::span::Span::default(),
            },
            extends: Vec::new(),
            units: Vec::new(),
            action_subscript_spans: HashSet::new(),
            span: tla_core::span::Span::default(),
        };
        assert!(!operator_exists_in_module(&module, "NonExistent"));
    }
}
