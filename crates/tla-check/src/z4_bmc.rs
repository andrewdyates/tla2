// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z4-based bounded model checking (BMC) for symbolic bug finding.
//!
//! This module wires `tla-z4`'s `BmcTranslator` into `tla-check` so callers can
//! run incremental deepening over a TLA+ `Init`/`Next`/`INVARIANT` spec.

use std::sync::Arc;
use std::time::Duration;

use tla_core::ast::Module;
use tla_z4::{BmcState, BmcTranslator, SolveResult, UnknownReason, Z4Error};

use crate::check::CheckError;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::shared_verdict::SharedVerdict;
use crate::z4_pdr::expand_operators_for_chc;
use crate::z4_shared;

/// Result of BMC-based symbolic bug finding.
#[derive(Debug)]
pub enum BmcResult {
    /// A counterexample exists within the requested bound.
    Violation {
        /// Minimal depth bound `k` at which the solver found a violation.
        depth: usize,
        /// Counterexample trace from step 0 through `depth`.
        trace: Vec<BmcState>,
    },
    /// No counterexample exists up to and including `max_depth`.
    BoundReached {
        /// Maximum depth checked exhaustively by BMC.
        max_depth: usize,
    },
    /// Solver could not determine a result at `depth`.
    Unknown {
        /// Depth at which the unknown result occurred.
        depth: usize,
        /// Human-readable explanation of the unknown result.
        reason: String,
    },
}

/// Errors specific to BMC checking.
#[derive(Debug, thiserror::Error)]
pub enum BmcError {
    /// Missing Init or Next definition.
    #[error("Missing specification: {0}")]
    MissingSpec(String),
    /// No invariants configured.
    #[error("No invariants configured for BMC checking")]
    NoInvariants,
    /// Failed to translate the TLA+ expression into BMC constraints.
    #[error("BMC translation failed: {0}")]
    TranslationError(String),
    /// Solver setup or execution failed.
    #[error("BMC solver failed: {0}")]
    SolverFailed(String),
    /// General checker error.
    #[error("Check error: {0:?}")]
    CheckError(#[from] CheckError),
}

impl From<Z4Error> for BmcError {
    fn from(err: Z4Error) -> Self {
        match err {
            Z4Error::Solver(inner) => BmcError::SolverFailed(inner.to_string()),
            other => BmcError::TranslationError(other.to_string()),
        }
    }
}

/// Configuration for bounded model checking.
#[derive(Debug, Clone)]
pub struct BmcConfig {
    /// Maximum depth to check with incremental deepening.
    pub max_depth: usize,
    /// Timeout applied to each per-depth solver invocation.
    pub solve_timeout: Option<Duration>,
    /// Enable lightweight debug logging to stderr.
    pub debug: bool,
    /// Use incremental solving: keep one solver instance across all depths,
    /// retaining learned clauses via `push`/`pop` scoping. Part of #3724.
    pub incremental: bool,
}

impl BmcConfig {
    /// Construct a config for a specific maximum depth with default timeouts.
    pub fn with_max_depth(max_depth: usize) -> Self {
        Self {
            max_depth,
            ..Self::default()
        }
    }
}

impl Default for BmcConfig {
    fn default() -> Self {
        let timeout_secs: u64 = std::env::var("TLA2_BMC_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(300);

        // Allow env-var opt-in for non-CLI callers (pipeline, portfolio).
        // Part of #3724.
        let incremental = std::env::var("TLA2_BMC_INCREMENTAL")
            .ok()
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);

        Self {
            max_depth: 0,
            solve_timeout: Some(Duration::from_secs(timeout_secs)),
            debug: debug_z4_bmc_enabled(),
            incremental,
        }
    }
}

debug_flag!(debug_z4_bmc_enabled, "TLA2_DEBUG_Z4_BMC");

/// When the wavefront starvation gap (sent - consumed) exceeds this threshold,
/// BMC drains intermediate wavefronts and skips to the latest one. This prevents
/// unbounded memory growth from wavefronts accumulating faster than BMC can
/// process them under high BFS throughput.
///
/// Part of #4004.
const STARVATION_THRESHOLD: u64 = 4;

/// Number of seeds (wavefronts + frontier samples) processed before the
/// persistent BMC translator is recreated to clear accumulated learned clauses.
/// Without periodic refresh, the translator's internal solver state grows
/// unboundedly, degrading solving performance over time.
///
/// Part of #4006.
const TRANSLATOR_REFRESH_INTERVAL: u64 = 64;

/// Create a BMC translator with the appropriate logic for the given variable sorts.
///
/// Delegates to [`z4_shared::make_translator`] for logic selection.
fn make_translator(
    var_sorts: &[(String, tla_z4::TlaSort)],
    depth: usize,
) -> Result<BmcTranslator, BmcError> {
    Ok(z4_shared::make_translator(var_sorts, depth)?)
}

/// Run BMC-based symbolic bug finding on a TLA+ spec.
pub fn check_bmc(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    bmc_config: BmcConfig,
) -> Result<BmcResult, BmcError> {
    check_bmc_with_portfolio(module, config, ctx, bmc_config, None)
}

/// Run BMC with portfolio verdict for early termination.
///
/// When `portfolio_verdict` is `Some`, each depth iteration checks whether
/// another lane has already resolved before starting the solver call.
/// If resolved, returns `BmcResult::Unknown` immediately.
///
/// Part of #3717.
pub fn check_bmc_with_portfolio(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    bmc_config: BmcConfig,
    portfolio_verdict: Option<Arc<SharedVerdict>>,
) -> Result<BmcResult, BmcError> {
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(BmcError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(BmcError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }

    if config.invariants.is_empty() {
        return Err(BmcError::NoInvariants);
    }

    let resolved =
        z4_shared::resolve_init_next(config, &symbolic_ctx).map_err(BmcError::MissingSpec)?;

    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(BmcError::MissingSpec)?;
    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(BmcError::MissingSpec)?;
    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(|e| BmcError::TranslationError(e))?;

    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);

    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    if bmc_config.debug {
        eprintln!(
            "[z4-bmc] checking {} vars up to depth {}{}",
            var_sorts.len(),
            bmc_config.max_depth,
            if bmc_config.incremental {
                " (incremental)"
            } else {
                ""
            }
        );
    }

    if bmc_config.incremental {
        check_bmc_incremental(
            &var_sorts,
            &init_expanded,
            &next_expanded,
            &safety_expanded,
            &bmc_config,
            portfolio_verdict.as_deref(),
        )
    } else {
        check_bmc_per_depth(
            &var_sorts,
            &init_expanded,
            &next_expanded,
            &safety_expanded,
            &bmc_config,
            portfolio_verdict.as_deref(),
        )
    }
}

/// Per-depth BMC: creates a fresh solver for each depth bound.
///
/// This is the original approach. Each depth discards the solver and starts fresh,
/// losing any learned clauses from previous depths.
fn check_bmc_per_depth(
    var_sorts: &[(String, tla_z4::TlaSort)],
    init_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    next_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    safety_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    bmc_config: &BmcConfig,
    portfolio_verdict: Option<&SharedVerdict>,
) -> Result<BmcResult, BmcError> {
    for depth in 0..=bmc_config.max_depth {
        // Portfolio early-exit: another lane resolved (Part of #3717).
        if let Some(sv) = portfolio_verdict {
            if sv.is_resolved() {
                return Ok(BmcResult::Unknown {
                    depth,
                    reason: String::from("portfolio verdict resolved by another lane"),
                });
            }
        }

        if bmc_config.debug {
            eprintln!("[z4-bmc] depth {}", depth);
        }

        let mut translator = make_translator(var_sorts, depth)?;
        translator.set_timeout(bmc_config.solve_timeout);

        for (name, sort) in var_sorts {
            translator.declare_var(name, sort.clone())?;
        }

        let init_term = translator.translate_init(init_expanded)?;
        translator.assert(init_term);

        for step in 0..depth {
            let next_term = translator.translate_next(next_expanded, step)?;
            translator.assert(next_term);
        }

        let not_safety = translator.translate_not_safety_all_steps(safety_expanded, depth)?;
        translator.assert(not_safety);

        match translator.try_check_sat()? {
            SolveResult::Sat => {
                let model = translator.try_get_model()?;
                let trace = translator.extract_trace(&model);
                return Ok(BmcResult::Violation { depth, trace });
            }
            SolveResult::Unsat(_) => {}
            SolveResult::Unknown => {
                let reason = match translator.last_unknown_reason() {
                    Some(UnknownReason::Timeout) => {
                        format!("solver timed out at depth {}", depth)
                    }
                    Some(other) => {
                        format!("solver returned unknown at depth {}: {:?}", depth, other)
                    }
                    None => format!("solver returned unknown at depth {}", depth),
                };
                return Ok(BmcResult::Unknown { depth, reason });
            }
            _ => {
                return Ok(BmcResult::Unknown {
                    depth,
                    reason: format!("solver returned unexpected result at depth {}", depth),
                });
            }
        }
    }

    Ok(BmcResult::BoundReached {
        max_depth: bmc_config.max_depth,
    })
}

/// Incremental BMC: keeps one solver instance across all depths. Part of #3724.
///
/// Uses `push_scope`/`pop_scope` to retract per-depth safety negation queries
/// while retaining Init + accumulated Next transition assertions. This allows
/// the solver to carry forward learned clauses across depth iterations.
///
/// Formula at depth k:
/// ```text
/// [persistent] Init(s0)
/// [persistent] Next(s0,s1), Next(s1,s2), ..., Next(sk-1,sk)
/// [scoped]     ¬Safety(s0) ∨ ... ∨ ¬Safety(sk)
/// ```
fn check_bmc_incremental(
    var_sorts: &[(String, tla_z4::TlaSort)],
    init_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    next_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    safety_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    bmc_config: &BmcConfig,
    portfolio_verdict: Option<&SharedVerdict>,
) -> Result<BmcResult, BmcError> {
    // Create a single translator for the maximum depth. All k+1 step variables
    // are declared up front so transitions can be added incrementally.
    let mut translator = make_translator(var_sorts, bmc_config.max_depth)?;
    translator.set_timeout(bmc_config.solve_timeout);

    for (name, sort) in var_sorts {
        translator.declare_var(name, sort.clone())?;
    }

    // Assert Init(s0) once — this persists across all depths.
    let init_term = translator.translate_init(init_expanded)?;
    translator.assert(init_term);

    for depth in 0..=bmc_config.max_depth {
        // Portfolio early-exit: another lane resolved (Part of #3717).
        if let Some(sv) = portfolio_verdict {
            if sv.is_resolved() {
                return Ok(BmcResult::Unknown {
                    depth,
                    reason: String::from("portfolio verdict resolved by another lane"),
                });
            }
        }

        if bmc_config.debug {
            eprintln!("[z4-bmc-incr] depth {}", depth);
        }

        // Add the transition for the new step (persistent, not retracted by pop).
        // At depth 0 there is no transition to add.
        if depth > 0 {
            let next_term = translator.translate_next(next_expanded, depth - 1)?;
            translator.assert(next_term);
        }

        // Push a scope for the per-depth safety negation query.
        // Use a scoped-result pattern: run the query inside a closure, then
        // ALWAYS pop the scope before propagating errors. Fixes push/pop
        // scope leak on `?` error propagation (same class of bug as #4000).
        translator.push_scope()?;
        let scoped_result: Result<Option<BmcResult>, BmcError> = (|| {
            let not_safety = translator.translate_not_safety_all_steps(safety_expanded, depth)?;
            translator.assert(not_safety);

            match translator.try_check_sat()? {
                SolveResult::Sat => {
                    let model = translator.try_get_model()?;
                    let trace = translator.extract_trace(&model);
                    Ok(Some(BmcResult::Violation { depth, trace }))
                }
                SolveResult::Unsat(_) => Ok(None),
                SolveResult::Unknown => {
                    let reason = match translator.last_unknown_reason() {
                        Some(UnknownReason::Timeout) => {
                            format!("solver timed out at depth {} (incremental)", depth)
                        }
                        Some(other) => {
                            format!(
                                "solver returned unknown at depth {} (incremental): {:?}",
                                depth, other
                            )
                        }
                        None => {
                            format!("solver returned unknown at depth {} (incremental)", depth)
                        }
                    };
                    Ok(Some(BmcResult::Unknown { depth, reason }))
                }
                _ => Ok(Some(BmcResult::Unknown {
                    depth,
                    reason: format!(
                        "solver returned unexpected result at depth {} (incremental)",
                        depth
                    ),
                })),
            }
        })();

        // ALWAYS pop the scope, regardless of whether the inner block
        // succeeded or failed. Prevents scope leak on error propagation.
        translator.pop_scope()?;

        match scoped_result {
            Ok(Some(result)) => return Ok(result),
            Ok(None) => { /* Unsat — continue to next depth */ }
            Err(e) => return Err(e),
        }
    }

    Ok(BmcResult::BoundReached {
        max_depth: bmc_config.max_depth,
    })
}

/// Run BMC seeded from BFS frontier states instead of Init.
///
/// Polls `cooperative.frontier_rx` for concrete states and compressed wavefront
/// formulas. Uses a **persistent translator** across all seeds — variable
/// declarations and solver configuration are done once, and each seed
/// (frontier sample or wavefront formula) is wrapped in a `push_scope`/`pop_scope`
/// pair so seed-specific assertions are retracted without rebuilding the solver.
/// This preserves learned clauses across iterations, enabling incremental solving.
///
/// Part of #3766, Epic #3762 (CDEMC).
/// Part of #3834: incremental wavefront BMC with translator reuse.
pub fn check_bmc_cooperative(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    bmc_config: BmcConfig,
    cooperative: Arc<crate::cooperative_state::SharedCooperativeState>,
) -> Result<BmcResult, BmcError> {
    use std::time::Duration;
    use tla_z4::BmcValue;

    // Same setup as check_bmc_with_portfolio.
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(BmcError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(BmcError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }
    if config.invariants.is_empty() {
        return Err(BmcError::NoInvariants);
    }

    let resolved =
        z4_shared::resolve_init_next(config, &symbolic_ctx).map_err(BmcError::MissingSpec)?;
    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(BmcError::MissingSpec)?;
    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(|e| BmcError::TranslationError(e))?;

    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);

    // Infer sorts for Init expression (needed for var_sorts even though we don't translate Init).
    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(BmcError::MissingSpec)?;
    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);
    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    if bmc_config.debug {
        eprintln!(
            "[z4-bmc-coop] waiting for frontier states, {} vars, max depth {}",
            var_sorts.len(),
            bmc_config.max_depth,
        );
    }

    // Lemma cursor: tracks how many learned lemmas BMC has already consumed
    // from the cooperative state. Part of #3835.
    let mut lemma_cursor: usize = 0;
    // Cached expanded lemma expressions, ready for BMC translation.
    let mut expanded_lemmas: Vec<tla_core::Spanned<tla_core::ast::Expr>> = Vec::new();

    // Helper closure: deepen from a seeded translator, checking safety at each
    // depth. Returns Ok(Some(result)) on violation or cooperative resolution,
    // Ok(None) if max_depth exhausted without finding a violation.
    //
    // Part of #3823: extracted so both frontier-sample and wavefront-formula
    // code paths share the same deepening logic.
    //
    // Enhanced: reports depth progress to SharedCooperativeState at each step
    // so that other lanes (BFS, PDR) can observe live BMC deepening activity.
    // Tracks per-seed completion metrics for average depth analysis.
    //
    // NOTE: Lemmas are NOT asserted here. PDR-learned lemmas are universal
    // invariants that hold at every reachable state. They are asserted
    // persistently at the base translator level (outside seed push/pop
    // scopes) so they are shared across all seeds without redundant
    // re-assertion. See `assert_lemmas_persistent` below. Fixes #4003.
    let deepen_from_seed =
        |translator: &mut tla_z4::BmcTranslator,
         cooperative: &crate::cooperative_state::SharedCooperativeState|
         -> Result<Option<BmcResult>, BmcError> {
            // Signal that a new seed is being processed.
            cooperative.bmc_start_seed();

            // Inner helper that does the actual deepening work. Returns
            // `(max_unsat_depth, result)` so the outer closure can pass the
            // accurate depth to `bmc_complete_seed` on ALL exit paths (success
            // or error), fixing #4005. Scope-level cleanup (pop after push) is
            // handled within this helper using a scoped-result pattern, fixing
            // #4000.
            let inner = |translator: &mut tla_z4::BmcTranslator|
         -> (u64, Result<Option<BmcResult>, BmcError>) {
            let mut max_unsat_depth: u64 = 0;

            for depth in 0..=bmc_config.max_depth {
                // Report live depth progress to the cooperative state.
                cooperative.bmc_report_depth_progress(depth as u64);

                if cooperative.is_resolved() {
                    return (max_unsat_depth, Ok(Some(BmcResult::Unknown {
                        depth,
                        reason: String::from("cooperative verdict resolved during BMC deepening"),
                    })));
                }

                if depth > 0 {
                    let next_term = match translator.translate_next(&next_expanded, depth - 1) {
                        Ok(t) => t,
                        Err(e) => return (max_unsat_depth, Err(e.into())),
                    };
                    translator.assert(next_term);
                }

                // Push a scope for the per-depth safety negation query.
                // Use a scoped-result pattern: capture the result of the
                // push/query/check block, then ALWAYS pop before propagating
                // any error. This prevents scope leaks on `?` errors (#4000).
                match translator.push_scope() {
                    Ok(()) => {}
                    Err(e) => return (max_unsat_depth, Err(e.into())),
                }
                let scoped_result: Result<Option<BmcResult>, BmcError> = (|| {
                    let not_safety =
                        translator.translate_not_safety_all_steps(&safety_expanded, depth)?;
                    translator.assert(not_safety);

                    match translator.try_check_sat()? {
                        tla_z4::SolveResult::Sat => {
                            let model = translator.try_get_model()?;
                            let trace = translator.extract_trace(&model);
                            cooperative
                                .verdict
                                .publish(crate::shared_verdict::Verdict::Violated);
                            Ok(Some(BmcResult::Violation { depth, trace }))
                        }
                        tla_z4::SolveResult::Unsat(_) => Ok(None),
                        _ => Ok(Some(BmcResult::Unknown {
                            depth,
                            reason: format!(
                                "solver returned unexpected result at depth {} (cooperative)",
                                depth
                            ),
                        })),
                    }
                })();

                // ALWAYS pop the scope, regardless of whether the inner block
                // succeeded or failed. This is the key fix for #4000.
                match translator.pop_scope() {
                    Ok(()) => {}
                    Err(e) => return (max_unsat_depth, Err(e.into())),
                }

                match scoped_result {
                    Ok(Some(result)) => return (max_unsat_depth, Ok(Some(result))),
                    Ok(None) => {
                        // Unsat at this depth — record and continue deepening.
                        max_unsat_depth = depth as u64;
                    }
                    Err(e) => return (max_unsat_depth, Err(e)),
                }
            }
            (max_unsat_depth, Ok(None))
        };

            // Run the inner helper and ensure bmc_complete_seed is called on ALL
            // exit paths — both success and error. This fixes #4005.
            let (max_unsat_depth, result) = inner(translator);
            cooperative.bmc_complete_seed(max_unsat_depth);
            result
        };

    // Assert PDR-learned lemmas persistently at the base translator level.
    //
    // PDR lemmas are universal invariants — they hold at every reachable state,
    // not just at specific seeds. Asserting them outside seed push/pop scopes
    // means they persist across all seeds, avoiding:
    // (a) Redundant re-assertion of the same lemmas for every seed
    // (b) The misleading "persistent constraints" comment from the old code
    //     where lemmas were actually scoped to seeds (inside push/pop)
    //
    // Lemmas must be asserted at every BMC step (0..=max_depth) because the
    // invariant holds at each reachable state along the trace.
    //
    // Returns the number of successfully asserted lemma-step pairs.
    //
    // Fixes #4003: lemmas are now truly persistent (base level), not falsely
    // labeled "persistent" while being scoped inside seed push/pop brackets.
    // Part of #3835: PDR lemma sharing to BMC.
    // Part of #4001: log translation failures instead of silently swallowing.
    let assert_lemmas_persistent = |translator: &mut tla_z4::BmcTranslator,
                                    lemmas: &[tla_core::Spanned<tla_core::ast::Expr>],
                                    debug: bool|
     -> usize {
        let mut asserted: usize = 0;
        let mut failures: usize = 0;
        for lemma in lemmas {
            for step in 0..=bmc_config.max_depth {
                match translator.translate_safety_at_step(lemma, step) {
                    Ok(lemma_term) => {
                        translator.assert(lemma_term);
                        asserted += 1;
                    }
                    Err(e) => {
                        failures += 1;
                        if debug {
                            eprintln!(
                                "[z4-bmc-coop] lemma translation failed at step {}: {}",
                                step, e,
                            );
                        }
                    }
                }
            }
        }
        if failures > 0 && debug {
            eprintln!(
                "[z4-bmc-coop] {}/{} lemma-step assertions failed (persistent)",
                failures,
                lemmas.len() * (bmc_config.max_depth + 1),
            );
        }
        asserted
    };

    // Helper: create a fresh persistent translator with variable declarations.
    // Extracted so we can recreate it periodically to clear learned clause
    // accumulation (Part of #4006).
    let create_translator = |var_sorts: &[(String, tla_z4::TlaSort)],
                             bmc_config: &BmcConfig|
     -> Result<tla_z4::BmcTranslator, BmcError> {
        let mut t = make_translator(var_sorts, bmc_config.max_depth)?;
        t.set_timeout(bmc_config.solve_timeout);
        for (name, sort) in var_sorts {
            t.declare_var(name, sort.clone())?;
        }
        Ok(t)
    };

    // Create ONE persistent translator for the cooperative poll loop.
    // Variable declarations and solver configuration are done once. Each seed
    // (frontier sample or wavefront formula) uses push_scope/pop_scope to add
    // sample-specific assertions without rebuilding the translator, preserving
    // any learned clauses across iterations.
    //
    // Part of #3834: incremental wavefront BMC with translator reuse.
    // Part of #4006: periodically recreated to clear accumulated learned clauses.
    let mut translator = create_translator(&var_sorts, &bmc_config)?;

    // Track seeds processed since last translator refresh for clause eviction.
    // Part of #4006.
    let mut seeds_since_refresh: u64 = 0;

    if bmc_config.debug {
        eprintln!(
            "[z4-bmc-coop] persistent translator created, {} vars declared",
            var_sorts.len(),
        );
    }

    // Poll cooperative channels for concrete frontier states and compressed
    // wavefront formulas. Individual samples are seeded via assert_concrete_state;
    // wavefront formulas are seeded via assert_wavefront_formula, encoding the
    // entire compressed frontier as a single disjunctive constraint.
    //
    // Each seed is wrapped in a push/pop scope so the base translator state
    // (variable declarations, solver config) persists across seeds.
    //
    // Part of #3823: close the feedback loop so wavefront formulas are consumed.
    // Part of #3834: persistent translator with incremental solving.
    // Part of #4004: starvation prevention via backpressure and wavefront skipping.
    let poll_timeout = Duration::from_millis(500);
    let wavefront_timeout = Duration::from_millis(50);
    loop {
        // Early exit: another lane resolved.
        if cooperative.is_resolved() {
            return Ok(BmcResult::Unknown {
                depth: 0,
                reason: String::from("cooperative verdict resolved by another lane"),
            });
        }

        // Early exit: BFS completed without publishing a resolved verdict.
        // Without this check, the cooperative loop spins forever waiting for
        // wavefronts that will never arrive. Part of #4002.
        if cooperative.is_bfs_complete() && !cooperative.is_resolved() {
            return Ok(BmcResult::Unknown {
                depth: 0,
                reason: String::from("BFS completed without resolved verdict, BMC exiting"),
            });
        }

        // Periodic translator refresh: recreate the solver to clear accumulated
        // learned clauses and internal state. Without this, the persistent
        // translator's memory grows unboundedly over long runs.
        // Part of #4006.
        if seeds_since_refresh >= TRANSLATOR_REFRESH_INTERVAL {
            if bmc_config.debug {
                eprintln!(
                    "[z4-bmc-coop] refreshing translator after {} seeds to clear learned clauses",
                    seeds_since_refresh,
                );
            }
            translator = create_translator(&var_sorts, &bmc_config)?;
            seeds_since_refresh = 0;
            cooperative.record_translator_refresh();

            // Re-assert all accumulated lemmas on the fresh translator.
            // Lemmas are persistent base-level constraints that must survive
            // translator refresh. Fixes #4003.
            if !expanded_lemmas.is_empty() {
                let n =
                    assert_lemmas_persistent(&mut translator, &expanded_lemmas, bmc_config.debug);
                if bmc_config.debug {
                    eprintln!(
                        "[z4-bmc-coop] re-asserted {} lemma-step pairs after translator refresh",
                        n,
                    );
                }
            }
        }

        // Poll for new PDR lemmas before processing the next seed.
        // New lemmas are asserted persistently at the base translator level
        // (outside any push/pop scope) so they apply to all future seeds.
        // Fixes #4003: lemmas are no longer re-asserted redundantly inside
        // each seed's push/pop scope.
        let (new_lemmas, new_cursor) = cooperative.poll_learned_lemmas(lemma_cursor);
        if !new_lemmas.is_empty() {
            let mut new_expanded = Vec::with_capacity(new_lemmas.len());
            for lemma in new_lemmas {
                new_expanded.push(expand_operators_for_chc(&symbolic_ctx, &lemma, false));
            }

            // Assert the new lemmas persistently at base solver level.
            let n = assert_lemmas_persistent(&mut translator, &new_expanded, bmc_config.debug);

            if bmc_config.debug {
                eprintln!(
                    "[z4-bmc-coop] consumed {} new PDR lemmas ({} step-assertions, total: {})",
                    new_expanded.len(),
                    n,
                    new_cursor,
                );
            }

            expanded_lemmas.extend(new_expanded);
            lemma_cursor = new_cursor;
        }

        // Starvation detection: if BFS is producing wavefronts much faster
        // than BMC can consume them, drain intermediate wavefronts and skip
        // to the most recent one. This bounds memory growth and keeps BMC
        // working on the current frontier rather than falling permanently behind.
        // Part of #4004.
        let starvation_gap = cooperative.wavefront_starvation_gap();
        if starvation_gap > STARVATION_THRESHOLD {
            let (drained_wf, latest_wf) = cooperative.drain_stale_wavefronts();
            let (drained_fs, _latest_fs) = cooperative.drain_stale_frontier_samples();

            if drained_wf > 0 {
                for _ in 0..drained_wf {
                    cooperative.record_wavefront_dropped_backpressure();
                    // Count drained wavefronts as consumed to keep gap accurate.
                    cooperative.record_wavefront_consumed();
                }
            }
            if drained_fs > 0 {
                for _ in 0..drained_fs {
                    cooperative.record_frontier_sample_dropped_backpressure();
                }
            }

            if bmc_config.debug && (drained_wf > 0 || drained_fs > 0) {
                eprintln!(
                    "[z4-bmc-coop] backpressure: starvation gap {}, drained {} wavefronts + {} samples",
                    starvation_gap, drained_wf, drained_fs,
                );
            }

            // Process the latest wavefront if we got one from the drain.
            if let Some(wavefront) = latest_wf {
                cooperative.record_wavefront_consumed();
                seeds_since_refresh += 1;

                translator.push_scope()?;

                let shared: Vec<(String, BmcValue)> = wavefront
                    .shared
                    .iter()
                    .map(|s| (s.name.clone(), s.value.clone()))
                    .collect();
                let disjuncts: Vec<Vec<(String, BmcValue)>> = wavefront
                    .disjuncts
                    .iter()
                    .map(|d| d.assignments.clone())
                    .collect();
                translator.assert_wavefront_formula(&shared, &disjuncts, 0)?;

                let result = deepen_from_seed(&mut translator, &cooperative)?;

                translator.pop_scope()?;
                // Evict Skolem constants and other temporary variables
                // accumulated during seed translation. Part of #4006.
                translator.clear_temporary_vars();

                if let Some(result) = result {
                    if matches!(result, BmcResult::Violation { .. }) {
                        cooperative.record_wavefront_induced_violation();
                    }
                    return Ok(result);
                }

                continue;
            }
        }

        // Prefer wavefront formulas over individual samples: wavefronts
        // encode many states at once (higher coverage per solver call).
        // Fall back to individual frontier samples when no wavefront is ready.
        //
        // BFS frontier hint prioritization: when the BFS lane has explored
        // several levels, seeds from shallow (already-checked) BFS depths are
        // less likely to find new violations. We still process them but log
        // when a seed is deprioritized for diagnostics.

        // Try compressed wavefront formula from the compressor thread first.
        // Wavefronts encode many frontier states in a single disjunctive formula,
        // giving higher coverage per solver invocation than individual samples.
        // Part of #3823: close the feedback loop so wavefront formulas are consumed.
        if let Some(wavefront) = cooperative.recv_wavefront(wavefront_timeout) {
            let wavefront_depth = wavefront.depth;
            let prioritized = cooperative.should_prioritize_seed(wavefront_depth);

            if bmc_config.debug {
                eprintln!(
                    "[z4-bmc-coop] got wavefront at depth {}, {} shared, {} disjuncts{}",
                    wavefront_depth,
                    wavefront.shared.len(),
                    wavefront.disjuncts.len(),
                    if prioritized { "" } else { " (deprioritized)" },
                );
            }

            if !prioritized {
                cooperative.record_bmc_seed_deprioritized();
            }

            cooperative.record_wavefront_consumed();
            seeds_since_refresh += 1;

            // Push an outer scope for this wavefront seed. Use a scoped-result
            // pattern to ensure pop_scope is always called, even if seed
            // assertion or deepening fails via `?`. Fixes #4000.
            translator.push_scope()?;
            let seed_result: Result<Option<BmcResult>, BmcError> = (|| {
                // Convert WavefrontFormula types to the (String, BmcValue) format
                // expected by assert_wavefront_formula.
                let shared: Vec<(String, BmcValue)> = wavefront
                    .shared
                    .iter()
                    .map(|s| (s.name.clone(), s.value.clone()))
                    .collect();
                let disjuncts: Vec<Vec<(String, BmcValue)>> = wavefront
                    .disjuncts
                    .iter()
                    .map(|d| d.assignments.clone())
                    .collect();
                translator.assert_wavefront_formula(&shared, &disjuncts, 0)?;
                deepen_from_seed(&mut translator, &cooperative)
            })();

            // ALWAYS pop the wavefront seed scope. Fixes #4000.
            translator.pop_scope()?;
            // Evict Skolem constants and other temporary variables
            // accumulated during seed translation. Part of #4006.
            translator.clear_temporary_vars();

            let seed_result = seed_result?;
            if let Some(result) = seed_result {
                // Track wavefront-induced violations for diagnostics.
                if matches!(result, BmcResult::Violation { .. }) {
                    cooperative.record_wavefront_induced_violation();
                }
                return Ok(result);
            }

            // Wavefront processed — skip individual sample polling this iteration
            // to avoid starvation of wavefront consumption.
            continue;
        }

        // Fall back to individual frontier sample when no wavefront is ready.
        if let Some(sample) = cooperative.recv_frontier_sample(poll_timeout) {
            let sample_depth = sample.depth;
            let prioritized = cooperative.should_prioritize_seed(sample_depth);

            if bmc_config.debug {
                eprintln!(
                    "[z4-bmc-coop] got frontier state at depth {}, {} vars{}",
                    sample_depth,
                    sample.assignments.len(),
                    if prioritized { "" } else { " (deprioritized)" },
                );
            }

            if !prioritized {
                cooperative.record_bmc_seed_deprioritized();
            }

            seeds_since_refresh += 1;

            // Push an outer scope for this seed — all seed assertions and
            // deepening transitions will be retracted on pop. Use a
            // scoped-result pattern to ensure pop_scope is always called,
            // even if assertion or deepening fails via `?`. Fixes #4000.
            translator.push_scope()?;
            let seed_result: Result<Option<BmcResult>, BmcError> = (|| {
                let bmc_assignments: Vec<(String, BmcValue)> = sample.assignments;
                translator.assert_concrete_state(&bmc_assignments, 0)?;
                deepen_from_seed(&mut translator, &cooperative)
            })();

            // ALWAYS pop the seed scope. Fixes #4000.
            translator.pop_scope()?;
            // Evict Skolem constants and other temporary variables
            // accumulated during seed translation. Part of #4006.
            translator.clear_temporary_vars();

            let seed_result = seed_result?;
            if let Some(result) = seed_result {
                return Ok(result);
            }
        }
    }
}

#[cfg(test)]
mod tests;
