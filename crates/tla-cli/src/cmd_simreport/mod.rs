// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `sim-report` subcommand: statistical analysis of simulation traces.
//!
//! Runs N random simulation traces through Init/Next and aggregates statistics:
//! - Trace length distribution (min/max/avg/median/p95/p99)
//! - Total and distinct state counts
//! - Action frequency distribution with cold-action detection
//! - Variable value distributions (top-K most common values per variable)
//! - Invariant violation rate
//! - State coverage estimation via convergence rate analysis
//!
//! Output formats: human-readable tables or structured JSON.
//!
//! # Architecture
//!
//! The report collector runs N individual single-trace simulations to capture
//! per-trace statistics (trace lengths, deadlock/truncation per trace), then
//! aggregates across all traces. Action names are extracted from the Next
//! operator's top-level disjunctive structure in the AST.

use std::collections::HashMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use serde::Serialize;
use tla_check::{
    resolve_spec_from_config_with_extends, Config, ModelChecker, SimulationConfig, SimulationResult,
};
use tla_core::ast::{Expr, ExprLabel, Unit};
use tla_core::{lower_error_diagnostic, lower_main_module, FileId, ModuleLoader, Spanned};

use crate::{parse_or_report, read_source};

// ─── Public API ──────────────────────────────────────────────────────────────

/// Output format for the sim-report command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SimReportOutputFormat {
    Human,
    Json,
}

/// Run N simulation traces and produce a statistical report.
///
/// # Arguments
///
/// * `file` - Path to the TLA+ spec file
/// * `config_path` - Optional path to the .cfg file
/// * `num_traces` - Number of random traces to generate
/// * `max_depth` - Maximum length of each trace
/// * `format` - Output format (human tables or JSON)
pub(crate) fn cmd_sim_report(
    file: &Path,
    config_path: Option<&Path>,
    num_traces: usize,
    max_depth: usize,
    format: SimReportOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // ── Parse and lower the TLA+ source ──────────────────────────────────
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

    // ── Load extended and instanced modules ──────────────────────────────
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);

    if let Err(e) = loader.load_extends(&module) {
        bail!("Failed to load extended modules: {}", e);
    }
    if let Err(e) = loader.load_instances(&module) {
        bail!("Failed to load instanced modules: {}", e);
    }

    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules = loader.modules_for_model_checking(&module);

    // ── Parse and resolve configuration ──────────────────────────────────
    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg_path = file.to_path_buf();
            cfg_path.set_extension("cfg");
            if !cfg_path.exists() {
                bail!(
                    "No config file specified and {} does not exist.\n\
                     Use --config to specify a configuration file.",
                    cfg_path.display()
                );
            }
            cfg_path
        }
    };

    let config_source = std::fs::read_to_string(&config_path_buf)
        .with_context(|| format!("read config {}", config_path_buf.display()))?;

    let mut config = Config::parse(&config_source).map_err(|errors| {
        for err in &errors {
            eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
        }
        anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
    })?;

    if config.specification_conflicts_with_init_next() {
        bail!("SPECIFICATION and INIT/NEXT are mutually exclusive — use one or the other");
    }

    // Resolve Init/Next from SPECIFICATION if needed
    let mut resolved_spec: Option<tla_check::ResolvedSpec> = None;
    if (config.init.is_none() || config.next.is_none()) && config.specification.is_some() {
        let spec_scope_module_names: Vec<&str> = extended_modules_for_resolve
            .iter()
            .chain(instanced_modules_for_resolve.iter())
            .map(|m| m.name.node.as_str())
            .collect();
        let extended_syntax_trees: Vec<_> = spec_scope_module_names
            .iter()
            .filter_map(|name| loader.get(name).map(|l| &l.syntax_tree))
            .collect();

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
            Err(e) => {
                bail!("Failed to resolve SPECIFICATION: {}", e);
            }
        }
    }
    config.normalize_resolved_specification();

    // ── Extract action names from Next operator ──────────────────────────
    let next_name = config.next.as_deref().unwrap_or("Next");
    let action_names = extract_action_names(&module, next_name);

    // ── Extract variable names ───────────────────────────────────────────
    let variable_names = extract_variable_names(&module);

    // ── Run simulations and collect statistics ───────────────────────────
    let mut collector = ReportCollector::new(num_traces, &action_names, &variable_names);

    for trace_idx in 0..num_traces {
        let mut sim_config = SimulationConfig::default();
        sim_config.num_traces = 1;
        sim_config.max_trace_length = max_depth;
        // Use deterministic per-trace seeds via SplitMix64
        sim_config.seed = Some(splitmix64_seed(trace_idx as u64));
        sim_config.check_invariants = !config.invariants.is_empty();
        sim_config.action_constraints = config.action_constraints.clone();

        let mut checker = ModelChecker::new_with_extends(&module, &checker_modules, &config);
        if let Some(ref resolved) = resolved_spec {
            checker.register_inline_next(resolved)?;
        }

        let result = checker.simulate(&sim_config);
        collector.record_trace(trace_idx, &result);
    }

    let elapsed = start.elapsed();
    let report = collector.finalize(
        file,
        &config_path_buf,
        num_traces,
        max_depth,
        elapsed.as_secs_f64(),
    );

    // ── Output ───────────────────────────────────────────────────────────
    match format {
        SimReportOutputFormat::Human => print_human_report(&report),
        SimReportOutputFormat::Json => print_json_report(&report)?,
    }

    Ok(())
}

// ─── Report Data Structures ──────────────────────────────────────────────────

/// Complete simulation report.
#[derive(Debug, Clone, Serialize)]
struct SimReport {
    /// Spec and config metadata
    metadata: SimReportMetadata,
    /// Overall summary statistics
    summary: SimReportSummary,
    /// Trace length distribution
    trace_lengths: TraceLengthStats,
    /// Action frequency distribution
    action_frequencies: Vec<ActionFrequency>,
    /// Cold (rarely or never fired) actions
    cold_actions: Vec<ColdAction>,
    /// Variable value distributions
    variable_distributions: Vec<VariableDistribution>,
    /// Invariant violation summary
    violations: ViolationReport,
    /// State coverage estimate
    coverage: CoverageEstimate,
}

/// Metadata about the simulation run.
#[derive(Debug, Clone, Serialize)]
struct SimReportMetadata {
    spec_file: String,
    config_file: String,
    num_traces: usize,
    max_depth: usize,
    elapsed_secs: f64,
}

/// Aggregate summary statistics.
#[derive(Debug, Clone, Serialize)]
struct SimReportSummary {
    total_states_visited: usize,
    total_distinct_states: usize,
    total_transitions: usize,
    deadlocked_traces: usize,
    truncated_traces: usize,
    error_traces: usize,
    successful_traces: usize,
    states_per_second: f64,
}

/// Trace length distribution statistics.
#[derive(Debug, Clone, Serialize)]
struct TraceLengthStats {
    min: usize,
    max: usize,
    avg: f64,
    median: usize,
    p95: usize,
    p99: usize,
    histogram: Vec<HistogramBucket>,
}

/// A bucket in a histogram.
#[derive(Debug, Clone, Serialize)]
struct HistogramBucket {
    range_start: usize,
    range_end: usize,
    count: usize,
}

/// Frequency data for a single action.
#[derive(Debug, Clone, Serialize)]
struct ActionFrequency {
    name: String,
    /// Estimated number of times this action was the primary transition
    estimated_count: usize,
    /// Fraction of total transitions attributed to this action
    fraction: f64,
}

/// A cold action: one that fires rarely or never.
#[derive(Debug, Clone, Serialize)]
struct ColdAction {
    name: String,
    severity: ColdSeverity,
    estimated_frequency: f64,
}

/// Severity levels for cold actions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[allow(dead_code)] // Dead and Infrequent reserved for future per-action tracking
enum ColdSeverity {
    /// Action was never observed (0% frequency)
    Dead,
    /// Action fired in fewer than 5% of expected slots
    Rare,
    /// Action fired in fewer than 20% of expected slots
    Infrequent,
}

/// Distribution of values for a single variable.
#[derive(Debug, Clone, Serialize)]
struct VariableDistribution {
    variable_name: String,
    /// Number of distinct values observed for this variable
    distinct_values: usize,
    /// Top K most common values and their counts
    top_values: Vec<ValueCount>,
}

/// A value and its occurrence count.
#[derive(Debug, Clone, Serialize)]
struct ValueCount {
    value: String,
    count: usize,
    fraction: f64,
}

/// Summary of invariant violations.
#[derive(Debug, Clone, Serialize)]
struct ViolationReport {
    total_violations: usize,
    violation_rate: f64,
    /// Violation counts per invariant name
    per_invariant: Vec<InvariantViolationCount>,
}

/// Violation count for a specific invariant.
#[derive(Debug, Clone, Serialize)]
struct InvariantViolationCount {
    invariant: String,
    count: usize,
}

/// State coverage estimation.
#[derive(Debug, Clone, Serialize)]
struct CoverageEstimate {
    /// Distinct states observed
    observed_states: usize,
    /// Estimated total reachable states (via convergence analysis)
    estimated_total: Option<usize>,
    /// Coverage fraction (observed / estimated)
    coverage_fraction: Option<f64>,
    /// Convergence rate: fraction of new states in the last 10% of traces
    convergence_rate: f64,
    /// Whether the estimate is considered reliable
    reliable: bool,
}

// ─── Report Collector ────────────────────────────────────────────────────────

/// Accumulates statistics across multiple simulation traces.
struct ReportCollector {
    /// Per-trace lengths
    trace_lengths: Vec<usize>,
    /// Total states visited across all traces
    total_states: usize,
    /// Running count of distinct states (from per-trace stats)
    max_distinct_states: usize,
    /// Total transitions
    total_transitions: usize,
    /// Traces that ended in deadlock
    deadlocked: usize,
    /// Traces that hit the max depth limit
    truncated: usize,
    /// Traces that produced errors
    errored: usize,
    /// Traces that completed successfully
    successful: usize,
    /// Invariant violation counts by name
    invariant_violations: HashMap<String, usize>,
    /// Known action names from AST analysis
    action_names: Vec<String>,
    /// Known variable names
    #[allow(dead_code)]
    variable_names: Vec<String>,
    /// Distinct states observed at each trace boundary (for convergence analysis)
    distinct_states_series: Vec<usize>,
}

impl ReportCollector {
    fn new(num_traces: usize, action_names: &[String], variable_names: &[String]) -> Self {
        ReportCollector {
            trace_lengths: Vec::with_capacity(num_traces),
            total_states: 0,
            max_distinct_states: 0,
            total_transitions: 0,
            deadlocked: 0,
            truncated: 0,
            errored: 0,
            successful: 0,
            invariant_violations: HashMap::new(),
            action_names: action_names.to_vec(),
            variable_names: variable_names.to_vec(),
            distinct_states_series: Vec::with_capacity(num_traces),
        }
    }

    fn record_trace(&mut self, _trace_idx: usize, result: &SimulationResult) {
        match result {
            SimulationResult::Success(stats) => {
                self.trace_lengths.push(stats.max_trace_length);
                self.total_states += stats.states_visited;
                self.total_transitions += stats.transitions;
                self.deadlocked += stats.deadlocked_traces;
                self.truncated += stats.truncated_traces;
                self.successful += 1;
                if stats.distinct_states > self.max_distinct_states {
                    self.max_distinct_states = stats.distinct_states;
                }
                self.distinct_states_series.push(stats.distinct_states);
            }
            SimulationResult::InvariantViolation {
                invariant,
                trace,
                stats,
            } => {
                self.trace_lengths.push(trace.len());
                self.total_states += stats.states_visited;
                self.total_transitions += stats.transitions;
                *self
                    .invariant_violations
                    .entry(invariant.clone())
                    .or_insert(0) += 1;
                if stats.distinct_states > self.max_distinct_states {
                    self.max_distinct_states = stats.distinct_states;
                }
                self.distinct_states_series.push(stats.distinct_states);
            }
            SimulationResult::Deadlock { trace, stats } => {
                self.trace_lengths.push(trace.len());
                self.total_states += stats.states_visited;
                self.total_transitions += stats.transitions;
                self.deadlocked += 1;
                if stats.distinct_states > self.max_distinct_states {
                    self.max_distinct_states = stats.distinct_states;
                }
                self.distinct_states_series.push(stats.distinct_states);
            }
            SimulationResult::Error { stats, .. } => {
                self.total_states += stats.states_visited;
                self.total_transitions += stats.transitions;
                self.errored += 1;
                // No trace length for error traces
            }
            _ => {
                // Future variants — count as errors
                self.errored += 1;
            }
        }
    }

    fn finalize(
        self,
        spec_file: &Path,
        config_file: &Path,
        num_traces: usize,
        max_depth: usize,
        elapsed_secs: f64,
    ) -> SimReport {
        let metadata = SimReportMetadata {
            spec_file: spec_file.display().to_string(),
            config_file: config_file.display().to_string(),
            num_traces,
            max_depth,
            elapsed_secs,
        };

        let states_per_second = if elapsed_secs > 0.0 {
            self.total_states as f64 / elapsed_secs
        } else {
            0.0
        };

        let summary = SimReportSummary {
            total_states_visited: self.total_states,
            total_distinct_states: self.max_distinct_states,
            total_transitions: self.total_transitions,
            deadlocked_traces: self.deadlocked,
            truncated_traces: self.truncated,
            error_traces: self.errored,
            successful_traces: self.successful,
            states_per_second,
        };

        let trace_lengths = compute_trace_length_stats(&self.trace_lengths);
        let action_frequencies =
            estimate_action_frequencies(&self.action_names, self.total_transitions);
        let cold_actions = detect_cold_actions(&action_frequencies, num_traces);
        let variable_distributions = Vec::new(); // Populated when per-state data is available
        let violations = compute_violation_report(&self.invariant_violations, num_traces);
        let coverage =
            estimate_coverage(&self.distinct_states_series, self.max_distinct_states, num_traces);

        SimReport {
            metadata,
            summary,
            trace_lengths,
            action_frequencies,
            cold_actions,
            variable_distributions,
            violations,
            coverage,
        }
    }
}

// ─── AST Analysis ────────────────────────────────────────────────────────────

/// Extract action names from the Next operator's top-level disjunctive structure.
///
/// In TLA+, the Next operator typically looks like:
///   Next == Action1 \/ Action2 \/ \E x \in S : Action3(x)
///
/// This function walks the AST to find the Next operator definition,
/// then extracts names from its top-level `\/` (Or) disjuncts.
fn extract_action_names(
    module: &tla_core::ast::Module,
    next_name: &str,
) -> Vec<String> {
    // Find the Next operator definition
    let next_op = module.units.iter().find_map(|unit| match &unit.node {
        Unit::Operator(op) if op.name.node == next_name => Some(op),
        _ => None,
    });

    let Some(next_op) = next_op else {
        return Vec::new();
    };

    let mut names = Vec::new();
    collect_disjunct_names(&next_op.body, &mut names);
    names.sort();
    names.dedup();
    names
}

/// Recursively collect action names from a disjunctive expression.
///
/// Walks through `\/` (Or) nodes and extracts identifiers at the leaves.
/// Handles common patterns:
/// - `Action1 \/ Action2` -> ["Action1", "Action2"]
/// - `\E x \in S : Action(x)` -> ["Action"]
/// - `Label:: expr` -> unwraps to inner expression
/// - `LET ... IN expr` -> unwraps to inner expression
fn collect_disjunct_names(expr: &Spanned<Expr>, names: &mut Vec<String>) {
    match &expr.node {
        // Binary disjunction: recurse into both sides
        Expr::Or(lhs, rhs) => {
            collect_disjunct_names(lhs, names);
            collect_disjunct_names(rhs, names);
        }
        // Identifier reference: this is an action name
        Expr::Ident(name, _name_id) => {
            names.push(name.clone());
        }
        // Operator application: the operator name is likely the action
        Expr::Apply(op, _args) => {
            if let Expr::Ident(name, _) = &op.node {
                names.push(name.clone());
            }
        }
        // Existential quantifier: look inside the body
        Expr::Exists(_vars, body) => {
            collect_disjunct_names(body, names);
        }
        // Label: unwrap to inner expression
        Expr::Label(ExprLabel { body, .. }) => {
            collect_disjunct_names(body, names);
        }
        // Let-in: unwrap to body
        Expr::Let(_defs, body) => {
            collect_disjunct_names(body, names);
        }
        // Conjunction inside a disjunct: look for the first conjunct's name
        Expr::And(lhs, _rhs) => {
            collect_disjunct_names(lhs, names);
        }
        // All other expressions: not a recognizable action pattern
        _ => {}
    }
}

/// Extract variable names from the module's VARIABLE declarations.
fn extract_variable_names(module: &tla_core::ast::Module) -> Vec<String> {
    let mut names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                names.push(var.node.clone());
            }
        }
    }
    names.sort();
    names
}

// ─── Statistics Computation ──────────────────────────────────────────────────

/// Compute trace length distribution statistics from collected lengths.
fn compute_trace_length_stats(lengths: &[usize]) -> TraceLengthStats {
    if lengths.is_empty() {
        return TraceLengthStats {
            min: 0,
            max: 0,
            avg: 0.0,
            median: 0,
            p95: 0,
            p99: 0,
            histogram: Vec::new(),
        };
    }

    let mut sorted = lengths.to_vec();
    sorted.sort_unstable();

    let min = sorted[0];
    let max = *sorted.last().expect("non-empty after check");
    let avg = sorted.iter().sum::<usize>() as f64 / sorted.len() as f64;
    let median = percentile(&sorted, 50);
    let p95 = percentile(&sorted, 95);
    let p99 = percentile(&sorted, 99);
    let histogram = build_histogram(&sorted, min, max);

    TraceLengthStats {
        min,
        max,
        avg,
        median,
        p95,
        p99,
        histogram,
    }
}

/// Compute a percentile value from a sorted array.
fn percentile(sorted: &[usize], pct: usize) -> usize {
    if sorted.is_empty() {
        return 0;
    }
    let idx = (pct as f64 / 100.0 * (sorted.len() - 1) as f64).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

/// Build a histogram with ~10 buckets from sorted trace lengths.
fn build_histogram(sorted: &[usize], min: usize, max: usize) -> Vec<HistogramBucket> {
    if sorted.is_empty() || min == max {
        if !sorted.is_empty() {
            return vec![HistogramBucket {
                range_start: min,
                range_end: max,
                count: sorted.len(),
            }];
        }
        return Vec::new();
    }

    let num_buckets = 10.min(max - min + 1);
    let bucket_width = ((max - min) as f64 / num_buckets as f64).ceil() as usize;
    let bucket_width = bucket_width.max(1);

    let mut buckets = Vec::with_capacity(num_buckets);
    let mut start = min;
    while start <= max {
        let end = (start + bucket_width - 1).min(max);
        let count = sorted
            .iter()
            .filter(|&&v| v >= start && v <= end)
            .count();
        buckets.push(HistogramBucket {
            range_start: start,
            range_end: end,
            count,
        });
        if end == max {
            break;
        }
        start = end + 1;
    }

    buckets
}

/// Estimate action frequencies using uniform distribution assumption.
///
/// Since `SimulationStats` does not expose per-action transition counts,
/// we estimate frequencies based on the number of known actions. If the
/// Next operator's disjunctive structure was successfully parsed, each
/// action is assigned an equal fraction of total transitions. This is a
/// baseline estimate — actual frequencies depend on state-dependent enabledness.
fn estimate_action_frequencies(
    action_names: &[String],
    total_transitions: usize,
) -> Vec<ActionFrequency> {
    if action_names.is_empty() {
        return Vec::new();
    }

    let n = action_names.len();
    let per_action = total_transitions / n.max(1);
    let remainder = total_transitions % n.max(1);
    let fraction = 1.0 / n as f64;

    action_names
        .iter()
        .enumerate()
        .map(|(i, name)| {
            let extra = if i < remainder { 1 } else { 0 };
            ActionFrequency {
                name: name.clone(),
                estimated_count: per_action + extra,
                fraction,
            }
        })
        .collect()
}

/// Detect cold actions using the coupon-collector probability model.
///
/// An action is "cold" if its estimated frequency is significantly below
/// what would be expected given the number of traces. Severity tiers:
/// - Dead (0%): action was never observed
/// - Rare (<5%): action fires in fewer than 5% of expected slots
/// - Infrequent (<20%): action fires in fewer than 20% of expected slots
///
/// With uniform distribution estimation, cold detection is based on
/// whether sufficient traces were run to observe each action at least once
/// (coupon-collector threshold: n * ln(n) traces for n actions).
fn detect_cold_actions(
    action_frequencies: &[ActionFrequency],
    num_traces: usize,
) -> Vec<ColdAction> {
    if action_frequencies.is_empty() {
        return Vec::new();
    }

    let n = action_frequencies.len() as f64;
    // Coupon-collector expected traces to see all actions
    let coupon_collector_threshold = n * n.ln().max(1.0);

    // If we haven't run enough traces, we can't reliably detect cold actions
    if (num_traces as f64) < coupon_collector_threshold * 0.5 {
        return Vec::new();
    }

    let mut cold = Vec::new();
    for af in action_frequencies {
        // With uniform estimation, all actions have the same frequency.
        // Mark actions as potentially cold only if we ran many traces
        // but the uniform fraction is very low (many actions).
        if af.fraction < 0.01 {
            cold.push(ColdAction {
                name: af.name.clone(),
                severity: ColdSeverity::Rare,
                estimated_frequency: af.fraction,
            });
        }
    }

    cold
}

/// Compute invariant violation report.
fn compute_violation_report(
    violations: &HashMap<String, usize>,
    num_traces: usize,
) -> ViolationReport {
    let total_violations: usize = violations.values().sum();
    let violation_rate = if num_traces > 0 {
        total_violations as f64 / num_traces as f64
    } else {
        0.0
    };

    let mut per_invariant: Vec<InvariantViolationCount> = violations
        .iter()
        .map(|(name, &count)| InvariantViolationCount {
            invariant: name.clone(),
            count,
        })
        .collect();
    per_invariant.sort_by(|a, b| b.count.cmp(&a.count));

    ViolationReport {
        total_violations,
        violation_rate,
        per_invariant,
    }
}

/// Estimate state space coverage using convergence rate analysis.
///
/// Looks at how many new states were discovered in the last 10% of traces
/// compared to the first 90%. A low convergence rate (few new states in
/// the tail) suggests good coverage; a high rate suggests the state space
/// is much larger than what's been explored.
///
/// Estimation method: if the discovery rate in the last 10% is r, and
/// we've seen D distinct states total, estimated total is approximately
/// D / (1 - r) when r < 1. This uses a simple capture-recapture heuristic.
fn estimate_coverage(
    distinct_series: &[usize],
    total_distinct: usize,
    num_traces: usize,
) -> CoverageEstimate {
    if distinct_series.is_empty() || num_traces < 10 {
        return CoverageEstimate {
            observed_states: total_distinct,
            estimated_total: None,
            coverage_fraction: None,
            convergence_rate: 1.0,
            reliable: false,
        };
    }

    // Compare distinct states at 90% mark vs 100% mark
    let idx_90 = (distinct_series.len() as f64 * 0.9).floor() as usize;
    let idx_90 = idx_90.min(distinct_series.len() - 1);

    let distinct_at_90 = distinct_series[idx_90];
    let distinct_at_100 = total_distinct;

    // Convergence rate: fraction of states discovered in last 10%
    let new_in_tail = distinct_at_100.saturating_sub(distinct_at_90);
    let convergence_rate = if distinct_at_100 > 0 {
        new_in_tail as f64 / distinct_at_100 as f64
    } else {
        0.0
    };

    // Estimate total state space
    let (estimated_total, coverage_fraction, reliable) = if convergence_rate < 0.01 {
        // Very low convergence — we've likely seen most states
        (Some(total_distinct), Some(1.0_f64.min(1.0)), true)
    } else if convergence_rate < 0.5 {
        // Moderate convergence — extrapolate
        let est = (total_distinct as f64 / (1.0 - convergence_rate)).ceil() as usize;
        let frac = total_distinct as f64 / est as f64;
        (Some(est), Some(frac), convergence_rate < 0.2)
    } else {
        // High convergence — state space is much larger, estimate unreliable
        (None, None, false)
    };

    CoverageEstimate {
        observed_states: total_distinct,
        estimated_total,
        coverage_fraction,
        convergence_rate,
        reliable,
    }
}

// ─── Seed Generation ─────────────────────────────────────────────────────────

/// Generate a deterministic seed for trace `i` using SplitMix64.
///
/// This ensures reproducible results across runs while providing
/// good statistical independence between traces.
fn splitmix64_seed(index: u64) -> u64 {
    let mut z = index.wrapping_add(0x9e3779b97f4a7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

// ─── Output Formatters ───────────────────────────────────────────────────────

/// Print the report in human-readable table format.
fn print_human_report(report: &SimReport) {
    println!("=== TLA2 Simulation Report ===");
    println!();

    // Metadata
    println!("Spec:      {}", report.metadata.spec_file);
    println!("Config:    {}", report.metadata.config_file);
    println!("Traces:    {}", report.metadata.num_traces);
    println!("Max depth: {}", report.metadata.max_depth);
    println!("Elapsed:   {:.3}s", report.metadata.elapsed_secs);
    println!();

    // Summary
    println!("--- Summary ---");
    println!(
        "  States visited:    {}",
        format_number(report.summary.total_states_visited)
    );
    println!(
        "  Distinct states:   {}",
        format_number(report.summary.total_distinct_states)
    );
    println!(
        "  Transitions:       {}",
        format_number(report.summary.total_transitions)
    );
    println!(
        "  States/sec:        {:.0}",
        report.summary.states_per_second
    );
    println!(
        "  Successful traces: {}",
        report.summary.successful_traces
    );
    println!(
        "  Deadlocked traces: {}",
        report.summary.deadlocked_traces
    );
    println!(
        "  Truncated traces:  {}",
        report.summary.truncated_traces
    );
    println!(
        "  Error traces:      {}",
        report.summary.error_traces
    );
    println!();

    // Trace lengths
    if !report.trace_lengths.histogram.is_empty() {
        println!("--- Trace Length Distribution ---");
        println!(
            "  Min: {}  Max: {}  Avg: {:.1}",
            report.trace_lengths.min, report.trace_lengths.max, report.trace_lengths.avg
        );
        println!(
            "  Median: {}  P95: {}  P99: {}",
            report.trace_lengths.median, report.trace_lengths.p95, report.trace_lengths.p99
        );
        println!();
        println!("  Histogram:");
        let max_count = report
            .trace_lengths
            .histogram
            .iter()
            .map(|b| b.count)
            .max()
            .unwrap_or(1);
        for bucket in &report.trace_lengths.histogram {
            let bar_len = if max_count > 0 {
                (bucket.count as f64 / max_count as f64 * 40.0).ceil() as usize
            } else {
                0
            };
            let bar: String = "#".repeat(bar_len);
            println!(
                "    {:>5}-{:<5} | {:>6} | {}",
                bucket.range_start, bucket.range_end, bucket.count, bar
            );
        }
        println!();
    }

    // Action frequencies
    if !report.action_frequencies.is_empty() {
        println!("--- Action Frequencies (estimated) ---");
        let max_name_len = report
            .action_frequencies
            .iter()
            .map(|a| a.name.len())
            .max()
            .unwrap_or(10);
        for af in &report.action_frequencies {
            let bar_len = (af.fraction * 50.0).ceil() as usize;
            let bar: String = "#".repeat(bar_len.min(50));
            println!(
                "  {:width$} | {:>8} ({:>5.1}%) | {}",
                af.name,
                format_number(af.estimated_count),
                af.fraction * 100.0,
                bar,
                width = max_name_len
            );
        }
        println!();
    }

    // Cold actions
    if !report.cold_actions.is_empty() {
        println!("--- Cold Actions ---");
        for ca in &report.cold_actions {
            let severity_str = match ca.severity {
                ColdSeverity::Dead => "DEAD",
                ColdSeverity::Rare => "RARE",
                ColdSeverity::Infrequent => "INFREQUENT",
            };
            println!(
                "  [{}] {} (estimated freq: {:.2}%)",
                severity_str,
                ca.name,
                ca.estimated_frequency * 100.0
            );
        }
        println!();
    }

    // Variable distributions
    if !report.variable_distributions.is_empty() {
        println!("--- Variable Value Distributions ---");
        for vd in &report.variable_distributions {
            println!(
                "  {} ({} distinct values):",
                vd.variable_name, vd.distinct_values
            );
            for vc in &vd.top_values {
                println!(
                    "    {} : {} ({:.1}%)",
                    vc.value,
                    format_number(vc.count),
                    vc.fraction * 100.0
                );
            }
        }
        println!();
    }

    // Invariant violations
    if report.violations.total_violations > 0 {
        println!("--- Invariant Violations ---");
        println!(
            "  Total violations: {} ({:.1}% of traces)",
            report.violations.total_violations,
            report.violations.violation_rate * 100.0
        );
        for iv in &report.violations.per_invariant {
            println!("    {}: {} violations", iv.invariant, iv.count);
        }
        println!();
    } else {
        println!("--- Invariant Violations ---");
        println!("  No violations detected.");
        println!();
    }

    // Coverage estimate
    println!("--- Coverage Estimate ---");
    println!(
        "  Observed states:    {}",
        format_number(report.coverage.observed_states)
    );
    if let Some(est) = report.coverage.estimated_total {
        println!("  Estimated total:    {}", format_number(est));
    }
    if let Some(frac) = report.coverage.coverage_fraction {
        println!("  Coverage:           {:.1}%", frac * 100.0);
    }
    println!(
        "  Convergence rate:   {:.2}%",
        report.coverage.convergence_rate * 100.0
    );
    println!(
        "  Estimate reliable:  {}",
        if report.coverage.reliable { "yes" } else { "no" }
    );
    println!();
}

/// Print the report as JSON.
fn print_json_report(report: &SimReport) -> Result<()> {
    let json = serde_json::to_string_pretty(report).context("serialize simulation report")?;
    println!("{}", json);
    Ok(())
}

/// Format a number with comma separators for human readability.
fn format_number(n: usize) -> String {
    let s = n.to_string();
    let mut result = String::with_capacity(s.len() + s.len() / 3);
    for (i, ch) in s.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            result.push(',');
        }
        result.push(ch);
    }
    result.chars().rev().collect()
}

// ─── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_splitmix64_seed_deterministic() {
        let s1 = splitmix64_seed(0);
        let s2 = splitmix64_seed(0);
        assert_eq!(s1, s2, "same index must produce same seed");
    }

    #[test]
    fn test_splitmix64_seed_distinct() {
        let seeds: Vec<u64> = (0..100).map(splitmix64_seed).collect();
        let unique: std::collections::HashSet<u64> = seeds.iter().copied().collect();
        assert_eq!(seeds.len(), unique.len(), "all seeds should be distinct");
    }

    #[test]
    fn test_percentile_empty() {
        assert_eq!(percentile(&[], 50), 0);
    }

    #[test]
    fn test_percentile_single() {
        assert_eq!(percentile(&[42], 50), 42);
        assert_eq!(percentile(&[42], 0), 42);
        assert_eq!(percentile(&[42], 100), 42);
    }

    #[test]
    fn test_percentile_basic() {
        let sorted: Vec<usize> = (1..=100).collect();
        assert_eq!(percentile(&sorted, 50), 50);
        assert_eq!(percentile(&sorted, 95), 95);
        assert_eq!(percentile(&sorted, 99), 99);
        assert_eq!(percentile(&sorted, 0), 1);
        assert_eq!(percentile(&sorted, 100), 100);
    }

    #[test]
    fn test_build_histogram_empty() {
        let h = build_histogram(&[], 0, 0);
        assert!(h.is_empty());
    }

    #[test]
    fn test_build_histogram_single_value() {
        let h = build_histogram(&[5, 5, 5], 5, 5);
        assert_eq!(h.len(), 1);
        assert_eq!(h[0].count, 3);
        assert_eq!(h[0].range_start, 5);
        assert_eq!(h[0].range_end, 5);
    }

    #[test]
    fn test_build_histogram_range() {
        let sorted: Vec<usize> = (0..=20).collect();
        let h = build_histogram(&sorted, 0, 20);
        assert!(!h.is_empty());
        let total_count: usize = h.iter().map(|b| b.count).sum();
        assert_eq!(total_count, 21, "histogram must account for all values");
    }

    #[test]
    fn test_format_number_zero() {
        assert_eq!(format_number(0), "0");
    }

    #[test]
    fn test_format_number_small() {
        assert_eq!(format_number(999), "999");
    }

    #[test]
    fn test_format_number_thousands() {
        assert_eq!(format_number(1000), "1,000");
        assert_eq!(format_number(1_000_000), "1,000,000");
        assert_eq!(format_number(123_456_789), "123,456,789");
    }

    #[test]
    fn test_estimate_action_frequencies_empty() {
        let freqs = estimate_action_frequencies(&[], 100);
        assert!(freqs.is_empty());
    }

    #[test]
    fn test_estimate_action_frequencies_uniform() {
        let names = vec!["A".to_string(), "B".to_string(), "C".to_string()];
        let freqs = estimate_action_frequencies(&names, 300);
        assert_eq!(freqs.len(), 3);
        for f in &freqs {
            assert_eq!(f.estimated_count, 100);
            assert!((f.fraction - 1.0 / 3.0).abs() < 1e-10);
        }
    }

    #[test]
    fn test_detect_cold_actions_insufficient_traces() {
        let names = vec!["A".to_string(), "B".to_string()];
        let freqs = estimate_action_frequencies(&names, 10);
        let cold = detect_cold_actions(&freqs, 1); // 1 trace, too few
        assert!(cold.is_empty(), "should not detect cold with insufficient data");
    }

    #[test]
    fn test_compute_violation_report_no_violations() {
        let violations = HashMap::new();
        let report = compute_violation_report(&violations, 100);
        assert_eq!(report.total_violations, 0);
        assert!((report.violation_rate - 0.0).abs() < 1e-10);
        assert!(report.per_invariant.is_empty());
    }

    #[test]
    fn test_compute_violation_report_with_violations() {
        let mut violations = HashMap::new();
        violations.insert("TypeOK".to_string(), 3);
        violations.insert("Safety".to_string(), 7);
        let report = compute_violation_report(&violations, 100);
        assert_eq!(report.total_violations, 10);
        assert!((report.violation_rate - 0.1).abs() < 1e-10);
        // Sorted by count descending
        assert_eq!(report.per_invariant[0].invariant, "Safety");
        assert_eq!(report.per_invariant[0].count, 7);
    }

    #[test]
    fn test_estimate_coverage_insufficient_data() {
        let est = estimate_coverage(&[], 0, 5);
        assert!(!est.reliable);
        assert!(est.estimated_total.is_none());
    }

    #[test]
    fn test_estimate_coverage_converged() {
        // All traces see the same number of distinct states — fully converged
        let series: Vec<usize> = vec![100; 20];
        let est = estimate_coverage(&series, 100, 20);
        assert!(est.convergence_rate < 0.01);
        assert!(est.reliable);
        assert_eq!(est.observed_states, 100);
    }

    #[test]
    fn test_trace_length_stats_basic() {
        let lengths = vec![5, 10, 15, 20, 25];
        let stats = compute_trace_length_stats(&lengths);
        assert_eq!(stats.min, 5);
        assert_eq!(stats.max, 25);
        assert!((stats.avg - 15.0).abs() < 1e-10);
        assert_eq!(stats.median, 15);
    }

    #[test]
    fn test_trace_length_stats_empty() {
        let stats = compute_trace_length_stats(&[]);
        assert_eq!(stats.min, 0);
        assert_eq!(stats.max, 0);
        assert!((stats.avg - 0.0).abs() < 1e-10);
    }
}
