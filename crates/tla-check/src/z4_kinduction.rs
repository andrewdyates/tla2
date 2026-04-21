// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z4-based k-induction for proving TLA+ safety properties.
//!
//! k-Induction extends bounded model checking (BMC) to *prove* safety properties
//! that BMC alone can only *bound-check*. The algorithm works in two phases:
//!
//! 1. **Base case** (handled by BMC): verify that no counterexample exists
//!    within the first `k` steps from Init.
//! 2. **Inductive step** (this module): assume the safety property holds for
//!    `k` consecutive states, then check whether it can be violated at the
//!    next step. If the inductive query is UNSAT, the property is proved for
//!    ALL reachable states (not just bounded depth).
//!
//! # k-Induction Formula
//!
//! For depth bound k and safety property S, the inductive step checks:
//! ```text
//! Next(s0,s1) /\ Next(s1,s2) /\ ... /\ Next(sk-1,sk)
//! /\ S(s0) /\ S(s1) /\ ... /\ S(sk-1)
//! /\ ¬S(sk)
//! ```
//!
//! Note: there is NO Init constraint. The states s0..sk are arbitrary.
//!
//! - If UNSAT: the property is k-inductive, hence holds for all reachable states.
//! - If SAT: the counterexample may be spurious (unreachable from Init).
//!   Increment k and retry.
//!
//! Ported from `tla-petri/src/examinations/kinduction.rs` and adapted for
//! TLA+ expressions via `BmcTranslator`. Part of #3722.

use std::sync::Arc;
use std::time::Duration;

use tla_core::ast::Module;
use tla_z4::{BmcTranslator, SolveResult, UnknownReason, Z4Error};

use crate::check::CheckError;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::shared_verdict::SharedVerdict;
use crate::z4_pdr::expand_operators_for_chc;
use crate::z4_shared;

/// Result of k-induction-based safety verification.
#[derive(Debug)]
pub enum KInductionResult {
    /// The property is k-inductive: it holds for ALL reachable states.
    Proved {
        /// The depth `k` at which the inductive step succeeded.
        k: usize,
    },
    /// k-Induction could not prove the property within the given bound.
    ///
    /// This does NOT mean the property is false -- the counterexamples to
    /// induction may all be spurious (unreachable from Init). A stronger
    /// technique (PDR, explicit-state, or higher k) may still prove it.
    Unknown {
        /// Maximum depth attempted.
        max_k: usize,
        /// Human-readable reason for the inconclusive result.
        reason: String,
    },
    /// BMC found a real counterexample at the base case.
    Counterexample {
        /// Depth at which the violation was found.
        depth: usize,
        /// Counterexample trace from Init through the violation.
        trace: Vec<tla_z4::BmcState>,
    },
}

/// Errors specific to k-induction checking.
#[derive(Debug, thiserror::Error)]
pub enum KInductionError {
    /// Missing Init or Next definition.
    #[error("Missing specification: {0}")]
    MissingSpec(String),
    /// No invariants configured.
    #[error("No invariants configured for k-induction checking")]
    NoInvariants,
    /// Failed to translate the TLA+ expression into BMC constraints.
    #[error("k-induction translation failed: {0}")]
    TranslationError(String),
    /// Solver setup or execution failed.
    #[error("k-induction solver failed: {0}")]
    SolverFailed(String),
    /// General checker error.
    #[error("Check error: {0:?}")]
    CheckError(#[from] CheckError),
}

impl From<Z4Error> for KInductionError {
    fn from(err: Z4Error) -> Self {
        match err {
            Z4Error::Solver(inner) => KInductionError::SolverFailed(inner.to_string()),
            other => KInductionError::TranslationError(other.to_string()),
        }
    }
}

/// Configuration for k-induction checking.
#[derive(Debug, Clone)]
pub struct KInductionConfig {
    /// Maximum induction depth to attempt.
    pub max_k: usize,
    /// Starting depth for the inductive step.
    ///
    /// Set this to the BMC bound that already passed the base case to avoid
    /// redundant base-case work. For example, if BMC verified the base case
    /// up to depth 5, set `start_k = 1` and the algorithm will try k=1..max_k.
    pub start_k: usize,
    /// Timeout applied to each per-depth solver invocation.
    pub solve_timeout: Option<Duration>,
    /// Enable lightweight debug logging to stderr.
    pub debug: bool,
    /// Use incremental solving for the inductive step.
    ///
    /// When enabled, the inductive step keeps a single solver instance across
    /// all depth iterations, using `push`/`pop` scoping to retract per-depth
    /// safety assertions while retaining accumulated transition constraints
    /// and learned clauses. This can significantly speed up the inductive step
    /// for specs where each depth builds on the previous one.
    pub incremental: bool,
}

impl Default for KInductionConfig {
    fn default() -> Self {
        let timeout_secs: u64 = std::env::var("TLA2_KINDUCTION_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(300);

        Self {
            max_k: 20,
            start_k: 1,
            solve_timeout: Some(Duration::from_secs(timeout_secs)),
            debug: debug_z4_kinduction_enabled(),
            incremental: false,
        }
    }
}

debug_flag!(debug_z4_kinduction_enabled, "TLA2_DEBUG_Z4_KINDUCTION");

/// Run k-induction on a TLA+ spec.
///
/// First runs BMC as the base case (depth 0..max_k), then attempts the
/// inductive step at increasing depths. If BMC finds a violation, returns
/// `Counterexample`. If the inductive step succeeds, returns `Proved`.
/// Otherwise returns `Unknown`.
pub fn check_kinduction(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    kind_config: KInductionConfig,
) -> Result<KInductionResult, KInductionError> {
    check_kinduction_with_portfolio(module, config, ctx, kind_config, None)
}

/// Run k-induction with portfolio verdict for early termination.
///
/// When `portfolio_verdict` is `Some`, each depth iteration checks whether
/// another lane has already resolved before starting the solver call.
/// If resolved, returns `KInductionResult::Unknown` immediately.
///
/// Part of #3717.
pub fn check_kinduction_with_portfolio(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    kind_config: KInductionConfig,
    portfolio_verdict: Option<Arc<SharedVerdict>>,
) -> Result<KInductionResult, KInductionError> {
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(KInductionError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(KInductionError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }

    if config.invariants.is_empty() {
        return Err(KInductionError::NoInvariants);
    }

    let resolved = z4_shared::resolve_init_next(config, &symbolic_ctx)
        .map_err(KInductionError::MissingSpec)?;

    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(KInductionError::MissingSpec)?;
    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(KInductionError::MissingSpec)?;
    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(KInductionError::TranslationError)?;

    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);

    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    if kind_config.debug {
        eprintln!(
            "[z4-kind] checking {} vars, k={}..{}",
            var_sorts.len(),
            kind_config.start_k,
            kind_config.max_k,
        );
    }

    // Phase 1: BMC base case — check for real counterexamples.
    let bmc_result = run_bmc_base_case(
        &var_sorts,
        &init_expanded,
        &next_expanded,
        &safety_expanded,
        &kind_config,
        portfolio_verdict.as_deref(),
    )?;

    match bmc_result {
        BmcBaseResult::Violation { depth, trace } => {
            return Ok(KInductionResult::Counterexample { depth, trace });
        }
        BmcBaseResult::Unknown { depth, reason } => {
            return Ok(KInductionResult::Unknown {
                max_k: depth,
                reason: format!("BMC base case inconclusive: {reason}"),
            });
        }
        BmcBaseResult::BoundReached { max_depth } => {
            if kind_config.debug {
                eprintln!("[z4-kind] BMC base case passed up to depth {max_depth}");
            }
        }
    }

    // Phase 2: Inductive step — try to prove the property.
    if kind_config.incremental {
        run_inductive_step_incremental(
            &var_sorts,
            &next_expanded,
            &safety_expanded,
            &kind_config,
            portfolio_verdict.as_deref(),
        )
    } else {
        run_inductive_step(
            &var_sorts,
            &next_expanded,
            &safety_expanded,
            &kind_config,
            portfolio_verdict.as_deref(),
        )
    }
}

/// BMC base case result (internal).
enum BmcBaseResult {
    Violation {
        depth: usize,
        trace: Vec<tla_z4::BmcState>,
    },
    BoundReached {
        max_depth: usize,
    },
    Unknown {
        depth: usize,
        reason: String,
    },
}

/// Run BMC base case: check Init -> Next^k -> not Safety for each k.
fn run_bmc_base_case(
    var_sorts: &[(String, tla_z4::TlaSort)],
    init_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    next_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    safety_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    kind_config: &KInductionConfig,
    portfolio_verdict: Option<&SharedVerdict>,
) -> Result<BmcBaseResult, KInductionError> {
    for depth in 0..=kind_config.max_k {
        // Portfolio early-exit: another lane resolved (Part of #3717).
        if let Some(sv) = portfolio_verdict {
            if sv.is_resolved() {
                return Ok(BmcBaseResult::Unknown {
                    depth,
                    reason: String::from("portfolio verdict resolved by another lane"),
                });
            }
        }

        if kind_config.debug {
            eprintln!("[z4-kind] BMC base depth {depth}");
        }

        let mut translator = z4_shared::make_translator(var_sorts, depth)?;
        translator.set_timeout(kind_config.solve_timeout);

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
                return Ok(BmcBaseResult::Violation { depth, trace });
            }
            SolveResult::Unsat(_) => {} // base case holds at this depth
            SolveResult::Unknown => {
                let reason = match translator.last_unknown_reason() {
                    Some(UnknownReason::Timeout) => {
                        format!("solver timed out at BMC depth {depth}")
                    }
                    Some(other) => format!("solver unknown at BMC depth {depth}: {other:?}"),
                    None => format!("solver unknown at BMC depth {depth}"),
                };
                return Ok(BmcBaseResult::Unknown { depth, reason });
            }
            _ => {
                return Ok(BmcBaseResult::Unknown {
                    depth,
                    reason: format!("unexpected result at BMC depth {depth}"),
                });
            }
        }
    }

    Ok(BmcBaseResult::BoundReached {
        max_depth: kind_config.max_k,
    })
}

/// Run the inductive step: for each k, check if Safety is k-inductive.
///
/// The formula is:
/// ```text
/// Next(s0,s1) /\ ... /\ Next(sk-1,sk)
/// /\ Safety(s0) /\ Safety(s1) /\ ... /\ Safety(sk-1)
/// /\ ¬Safety(sk)
/// ```
///
/// No Init constraint — the states are arbitrary.
fn run_inductive_step(
    var_sorts: &[(String, tla_z4::TlaSort)],
    next_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    safety_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    kind_config: &KInductionConfig,
    portfolio_verdict: Option<&SharedVerdict>,
) -> Result<KInductionResult, KInductionError> {
    for k in kind_config.start_k..=kind_config.max_k {
        // Portfolio early-exit: another lane resolved (Part of #3717).
        if let Some(sv) = portfolio_verdict {
            if sv.is_resolved() {
                return Ok(KInductionResult::Unknown {
                    max_k: k,
                    reason: String::from("portfolio verdict resolved by another lane"),
                });
            }
        }

        if kind_config.debug {
            eprintln!("[z4-kind] inductive step k={k}");
        }

        let mut translator = z4_shared::make_translator(var_sorts, k)?;
        translator.set_timeout(kind_config.solve_timeout);

        for (name, sort) in var_sorts {
            translator.declare_var(name, sort.clone())?;
        }

        // Transition relation: Next(s0,s1) /\ ... /\ Next(sk-1,sk)
        for step in 0..k {
            let next_term = translator.translate_next(next_expanded, step)?;
            translator.assert(next_term);
        }

        // Induction hypothesis: Safety(s0) /\ ... /\ Safety(sk-1)
        for step in 0..k {
            let safety_term = translator.translate_safety_at_step(safety_expanded, step)?;
            translator.assert(safety_term);
        }

        // Induction check: ¬Safety(sk)
        let not_safety_k = translator.translate_not_safety_at_step(safety_expanded, k)?;
        translator.assert(not_safety_k);

        match translator.try_check_sat()? {
            SolveResult::Unsat(_) => {
                if kind_config.debug {
                    eprintln!("[z4-kind] PROVED: property is {k}-inductive");
                }
                return Ok(KInductionResult::Proved { k });
            }
            SolveResult::Sat => {
                // The counterexample to induction may be spurious (unreachable
                // from Init). Increment k and try again with a stronger hypothesis.
                if kind_config.debug {
                    eprintln!("[z4-kind] induction SAT at k={k} (may be spurious), trying deeper");
                }
            }
            SolveResult::Unknown => {
                let reason = match translator.last_unknown_reason() {
                    Some(UnknownReason::Timeout) => {
                        format!("solver timed out at induction depth {k}")
                    }
                    Some(other) => format!("solver unknown at induction depth {k}: {other:?}"),
                    None => format!("solver unknown at induction depth {k}"),
                };
                return Ok(KInductionResult::Unknown { max_k: k, reason });
            }
            _ => {
                return Ok(KInductionResult::Unknown {
                    max_k: k,
                    reason: format!("unexpected result at induction depth {k}"),
                });
            }
        }
    }

    Ok(KInductionResult::Unknown {
        max_k: kind_config.max_k,
        reason: format!(
            "property not {}-inductive (all depths had spurious counterexamples)",
            kind_config.max_k
        ),
    })
}

/// Incremental inductive step: keeps one solver instance across all depths.
///
/// Uses `push_scope`/`pop_scope` to retract per-depth safety hypothesis and
/// negation queries while retaining accumulated transition assertions and
/// learned clauses. At each depth k, the formula is:
///
/// ```text
/// [persistent] Next(s0,s1), Next(s1,s2), ..., Next(sk-1,sk)
/// [scoped]     Safety(s0) /\ ... /\ Safety(sk-1) /\ ¬Safety(sk)
/// ```
///
/// The key difference from the non-incremental version: transition assertions
/// from depth k are retained when checking depth k+1, and the solver carries
/// forward conflict clauses learned at shallower depths.
fn run_inductive_step_incremental(
    var_sorts: &[(String, tla_z4::TlaSort)],
    next_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    safety_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    kind_config: &KInductionConfig,
    portfolio_verdict: Option<&SharedVerdict>,
) -> Result<KInductionResult, KInductionError> {
    // Create a single translator for the maximum depth. All step variables
    // are declared up front so transitions can be added incrementally.
    let mut translator = z4_shared::make_translator(var_sorts, kind_config.max_k)?;
    translator.set_timeout(kind_config.solve_timeout);

    for (name, sort) in var_sorts {
        translator.declare_var(name, sort.clone())?;
    }

    // For start_k > 1, pre-assert transitions for steps 0..start_k-1
    // so they persist across all depth iterations.
    for step in 0..kind_config.start_k.saturating_sub(1) {
        let next_term = translator.translate_next(next_expanded, step)?;
        translator.assert(next_term);
    }

    for k in kind_config.start_k..=kind_config.max_k {
        // Portfolio early-exit: another lane resolved (Part of #3717).
        if let Some(sv) = portfolio_verdict {
            if sv.is_resolved() {
                return Ok(KInductionResult::Unknown {
                    max_k: k,
                    reason: String::from("portfolio verdict resolved by another lane"),
                });
            }
        }

        if kind_config.debug {
            eprintln!("[z4-kind-incr] inductive step k={k}");
        }

        // Add the new transition (persistent, not retracted by pop).
        // At k=start_k with start_k=1, this adds Next(s0,s1).
        // The transition for step k-1 connects state k-1 to state k.
        let new_step = k - 1;
        // Only add if not already added in the pre-assertion loop above.
        if new_step >= kind_config.start_k.saturating_sub(1) {
            let next_term = translator.translate_next(next_expanded, new_step)?;
            translator.assert(next_term);
        }

        // Push a scope for per-depth safety hypothesis + negation.
        translator.push_scope()?;

        // Induction hypothesis: Safety(s0) /\ ... /\ Safety(sk-1)
        for step in 0..k {
            let safety_term = translator.translate_safety_at_step(safety_expanded, step)?;
            translator.assert(safety_term);
        }

        // Induction check: ¬Safety(sk)
        let not_safety_k = translator.translate_not_safety_at_step(safety_expanded, k)?;
        translator.assert(not_safety_k);

        match translator.try_check_sat()? {
            SolveResult::Unsat(_) => {
                if kind_config.debug {
                    eprintln!("[z4-kind-incr] PROVED: property is {k}-inductive");
                }
                return Ok(KInductionResult::Proved { k });
            }
            SolveResult::Sat => {
                // Pop the safety hypothesis — the transitions remain.
                translator.pop_scope()?;
                if kind_config.debug {
                    eprintln!(
                        "[z4-kind-incr] induction SAT at k={k} (may be spurious), trying deeper"
                    );
                }
            }
            SolveResult::Unknown => {
                let reason = match translator.last_unknown_reason() {
                    Some(UnknownReason::Timeout) => {
                        format!("solver timed out at induction depth {k} (incremental)")
                    }
                    Some(other) => {
                        format!("solver unknown at induction depth {k} (incremental): {other:?}")
                    }
                    None => format!("solver unknown at induction depth {k} (incremental)"),
                };
                return Ok(KInductionResult::Unknown { max_k: k, reason });
            }
            _ => {
                return Ok(KInductionResult::Unknown {
                    max_k: k,
                    reason: format!("unexpected result at induction depth {k} (incremental)"),
                });
            }
        }
    }

    Ok(KInductionResult::Unknown {
        max_k: kind_config.max_k,
        reason: format!(
            "property not {}-inductive (incremental, all depths had spurious counterexamples)",
            kind_config.max_k
        ),
    })
}

/// Run k-induction cooperatively within the fused orchestrator.
///
/// Like `check_pdr_cooperative`, this function:
/// - Checks for early termination via the cooperative verdict
/// - Reports per-depth progress (current k) to `SharedCooperativeState`
/// - Delegates to the portfolio-aware entry point with the cooperative verdict arc
/// - Publishes results back to the cooperative state:
///   * On `Proved`: records proved k, marks all invariants proved, publishes `Satisfied`
///   * On `Counterexample`: publishes `Violated` (BMC base-case real counterexample)
///   * On `Unknown`: no verdict published (other lanes continue)
///
/// Part of #3844.
pub fn check_kinduction_cooperative(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    kind_config: KInductionConfig,
    cooperative: Arc<crate::cooperative_state::SharedCooperativeState>,
) -> Result<KInductionResult, KInductionError> {
    // Early exit: another lane already resolved.
    if cooperative.is_resolved() {
        return Ok(KInductionResult::Unknown {
            max_k: 0,
            reason: String::from("cooperative verdict already resolved"),
        });
    }

    // Run k-induction with cooperative progress reporting.
    // Unlike the plain portfolio path, this function reports per-depth progress
    // to the cooperative state so other lanes can observe k-induction's advancement.
    let result =
        check_kinduction_cooperative_inner(module, config, ctx, kind_config, &cooperative)?;

    // Publish cooperative results.
    match &result {
        KInductionResult::Proved { k } => {
            eprintln!(
                "[z4-kind] k-induction proved safety at k={k}, publishing to cooperative state"
            );
            cooperative.set_kinduction_proved_k(*k);
            cooperative.set_invariants_proved();
            cooperative
                .verdict
                .publish(crate::shared_verdict::Verdict::Satisfied);
        }
        KInductionResult::Counterexample { depth, .. } => {
            // The base case found a real counterexample from Init — this is definitive.
            eprintln!("[z4-kind] k-induction base case found counterexample at depth {depth}");
            cooperative
                .verdict
                .publish(crate::shared_verdict::Verdict::Violated);
        }
        KInductionResult::Unknown { max_k, reason } => {
            // Inconclusive — do NOT publish a verdict. Other lanes may still resolve.
            eprintln!("[z4-kind] k-induction inconclusive at max_k={max_k}: {reason}");
        }
    }

    Ok(result)
}

/// Inner cooperative k-induction that reports per-depth progress.
///
/// This is separated from `check_kinduction_cooperative` so that the progress
/// reporting hooks can be injected at each depth boundary without duplicating
/// the entire BMC base case + inductive step logic. We re-use the existing
/// `check_kinduction_with_portfolio` function for the actual solving, wrapping
/// it with progress updates.
fn check_kinduction_cooperative_inner(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    kind_config: KInductionConfig,
    cooperative: &Arc<crate::cooperative_state::SharedCooperativeState>,
) -> Result<KInductionResult, KInductionError> {
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(KInductionError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(KInductionError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }

    if config.invariants.is_empty() {
        return Err(KInductionError::NoInvariants);
    }

    let resolved = z4_shared::resolve_init_next(config, &symbolic_ctx)
        .map_err(KInductionError::MissingSpec)?;

    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(KInductionError::MissingSpec)?;
    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(KInductionError::MissingSpec)?;
    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(KInductionError::TranslationError)?;

    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);

    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    if kind_config.debug {
        eprintln!(
            "[z4-kind-coop] checking {} vars, k={}..{}",
            var_sorts.len(),
            kind_config.start_k,
            kind_config.max_k,
        );
    }

    // Phase 1: BMC base case — check for real counterexamples.
    // Report progress at each BMC depth.
    for depth in 0..=kind_config.max_k {
        if cooperative.is_resolved() {
            return Ok(KInductionResult::Unknown {
                max_k: depth,
                reason: String::from("cooperative verdict resolved by another lane"),
            });
        }

        cooperative.update_kinduction_current_k(depth);

        if kind_config.debug {
            eprintln!("[z4-kind-coop] BMC base depth {depth}");
        }

        let mut translator = z4_shared::make_translator(&var_sorts, depth)?;
        translator.set_timeout(kind_config.solve_timeout);

        for (name, sort) in &var_sorts {
            translator.declare_var(name, sort.clone())?;
        }

        let init_term = translator.translate_init(&init_expanded)?;
        translator.assert(init_term);

        for step in 0..depth {
            let next_term = translator.translate_next(&next_expanded, step)?;
            translator.assert(next_term);
        }

        let not_safety = translator.translate_not_safety_all_steps(&safety_expanded, depth)?;
        translator.assert(not_safety);

        match translator.try_check_sat()? {
            SolveResult::Sat => {
                let model = translator.try_get_model()?;
                let trace = translator.extract_trace(&model);
                return Ok(KInductionResult::Counterexample { depth, trace });
            }
            SolveResult::Unsat(_) => {} // base case holds at this depth
            SolveResult::Unknown => {
                let reason = match translator.last_unknown_reason() {
                    Some(UnknownReason::Timeout) => {
                        format!("solver timed out at BMC depth {depth}")
                    }
                    Some(other) => format!("solver unknown at BMC depth {depth}: {other:?}"),
                    None => format!("solver unknown at BMC depth {depth}"),
                };
                return Ok(KInductionResult::Unknown {
                    max_k: depth,
                    reason: format!("BMC base case inconclusive: {reason}"),
                });
            }
            _ => {
                return Ok(KInductionResult::Unknown {
                    max_k: depth,
                    reason: format!("unexpected result at BMC depth {depth}"),
                });
            }
        }
    }

    if kind_config.debug {
        eprintln!(
            "[z4-kind-coop] BMC base case passed up to depth {}",
            kind_config.max_k
        );
    }

    // Phase 2: Inductive step — try to prove the property.
    // Report progress at each induction depth.
    for k in kind_config.start_k..=kind_config.max_k {
        if cooperative.is_resolved() {
            return Ok(KInductionResult::Unknown {
                max_k: k,
                reason: String::from("cooperative verdict resolved by another lane"),
            });
        }

        cooperative.update_kinduction_current_k(k);

        if kind_config.debug {
            eprintln!("[z4-kind-coop] inductive step k={k}");
        }

        let mut translator = z4_shared::make_translator(&var_sorts, k)?;
        translator.set_timeout(kind_config.solve_timeout);

        for (name, sort) in &var_sorts {
            translator.declare_var(name, sort.clone())?;
        }

        // Transition relation: Next(s0,s1) /\ ... /\ Next(sk-1,sk)
        for step in 0..k {
            let next_term = translator.translate_next(&next_expanded, step)?;
            translator.assert(next_term);
        }

        // Induction hypothesis: Safety(s0) /\ ... /\ Safety(sk-1)
        for step in 0..k {
            let safety_term = translator.translate_safety_at_step(&safety_expanded, step)?;
            translator.assert(safety_term);
        }

        // Induction check: not Safety(sk)
        let not_safety_k = translator.translate_not_safety_at_step(&safety_expanded, k)?;
        translator.assert(not_safety_k);

        match translator.try_check_sat()? {
            SolveResult::Unsat(_) => {
                if kind_config.debug {
                    eprintln!("[z4-kind-coop] PROVED: property is {k}-inductive");
                }
                return Ok(KInductionResult::Proved { k });
            }
            SolveResult::Sat => {
                if kind_config.debug {
                    eprintln!(
                        "[z4-kind-coop] induction SAT at k={k} (may be spurious), trying deeper"
                    );
                }
            }
            SolveResult::Unknown => {
                let reason = match translator.last_unknown_reason() {
                    Some(UnknownReason::Timeout) => {
                        format!("solver timed out at induction depth {k}")
                    }
                    Some(other) => format!("solver unknown at induction depth {k}: {other:?}"),
                    None => format!("solver unknown at induction depth {k}"),
                };
                return Ok(KInductionResult::Unknown { max_k: k, reason });
            }
            _ => {
                return Ok(KInductionResult::Unknown {
                    max_k: k,
                    reason: format!("unexpected result at induction depth {k}"),
                });
            }
        }
    }

    Ok(KInductionResult::Unknown {
        max_k: kind_config.max_k,
        reason: format!(
            "property not {}-inductive (all depths had spurious counterexamples)",
            kind_config.max_k
        ),
    })
}

#[cfg(test)]
mod tests;
