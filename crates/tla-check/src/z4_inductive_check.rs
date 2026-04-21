// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inductive invariant convenience checker (Apalache Gap 8).
//!
//! Automates the two-step inductive invariant check pattern used by Apalache:
//!
//! 1. **Initiation**: `Init => IndInv` — every initial state satisfies the invariant.
//! 2. **Consecution**: `IndInv /\ Next => IndInv'` — the invariant is preserved
//!    by all transitions.
//!
//! This is equivalent to `--kinduction --kinduction-max-k 1 --inv <IndInv>`
//! (1-induction), but provides clearer diagnostics about which phase fails.
//!
//! # Relationship to k-Induction
//!
//! `--inductive-check IndInv` is semantically equivalent to
//! `--kinduction --kinduction-max-k 1 --inv IndInv` (1-induction).
//! The difference is UX: `--inductive-check` reports which of the two phases
//! (initiation or consecution) failed, matching the Apalache workflow.
//!
//! Part of #3756.

use std::time::Duration;

use tla_core::ast::Module;
use tla_z4::{BmcTranslator, SolveResult, UnknownReason, Z4Error};

use crate::config::Config;
use crate::eval::EvalCtx;
use crate::z4_pdr::expand_operators_for_chc;
use crate::z4_shared;

/// Result of an inductive invariant check.
#[derive(Debug)]
pub enum InductiveCheckResult {
    /// Both phases passed: the invariant is inductive.
    Proved,
    /// Phase 1 failed: some initial state violates the invariant.
    InitiationFailed {
        /// Human-readable description of the failure.
        reason: String,
    },
    /// Phase 2 failed: some transition from a state satisfying IndInv
    /// leads to a state violating IndInv'.
    ConsecutionFailed {
        /// Human-readable description of the failure.
        reason: String,
    },
    /// The solver could not determine the result for one of the phases.
    Unknown {
        /// Which phase was inconclusive.
        phase: InductivePhase,
        /// Human-readable reason.
        reason: String,
    },
}

/// Which phase of the inductive check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InductivePhase {
    /// Phase 1: Init => IndInv
    Initiation,
    /// Phase 2: IndInv /\ Next => IndInv'
    Consecution,
}

impl std::fmt::Display for InductivePhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Initiation => write!(f, "Initiation (Init => IndInv)"),
            Self::Consecution => write!(f, "Consecution (IndInv /\\ Next => IndInv')"),
        }
    }
}

/// Errors specific to inductive invariant checking.
#[derive(Debug, thiserror::Error)]
pub enum InductiveCheckError {
    /// Missing Init or Next definition.
    #[error("Missing specification: {0}")]
    MissingSpec(String),
    /// The specified invariant operator was not found.
    #[error("Inductive invariant operator not found: {0}")]
    InvariantNotFound(String),
    /// Failed to translate the TLA+ expression into constraints.
    #[error("Inductive check translation failed: {0}")]
    TranslationError(String),
    /// Solver setup or execution failed.
    #[error("Inductive check solver failed: {0}")]
    SolverFailed(String),
}

impl From<Z4Error> for InductiveCheckError {
    fn from(err: Z4Error) -> Self {
        match err {
            Z4Error::Solver(inner) => InductiveCheckError::SolverFailed(inner.to_string()),
            other => InductiveCheckError::TranslationError(other.to_string()),
        }
    }
}

/// Configuration for the inductive invariant check.
#[derive(Debug, Clone)]
pub struct InductiveCheckConfig {
    /// Name of the inductive invariant operator to check.
    pub invariant: String,
    /// Timeout applied to each solver invocation.
    pub solve_timeout: Option<Duration>,
    /// Enable lightweight debug logging to stderr.
    pub debug: bool,
}

impl InductiveCheckConfig {
    pub fn new(invariant: String) -> Self {
        let timeout_secs: u64 = std::env::var("TLA2_INDUCTIVE_CHECK_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(300);

        Self {
            invariant,
            solve_timeout: Some(Duration::from_secs(timeout_secs)),
            debug: debug_inductive_check_enabled(),
        }
    }
}

debug_flag!(debug_inductive_check_enabled, "TLA2_DEBUG_INDUCTIVE_CHECK");

/// Run a two-phase inductive invariant check on a TLA+ spec.
///
/// Phase 1 (Initiation): checks `Init /\ ¬IndInv` is UNSAT.
/// Phase 2 (Consecution): checks `IndInv /\ Next /\ ¬IndInv'` is UNSAT.
///
/// If both are UNSAT, the invariant is inductive.
pub fn check_inductive(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    ind_config: &InductiveCheckConfig,
) -> Result<InductiveCheckResult, InductiveCheckError> {
    let symbolic_ctx = z4_shared::symbolic_ctx_with_config(ctx, config)
        .map_err(InductiveCheckError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(InductiveCheckError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }

    let resolved = z4_shared::resolve_init_next(config, &symbolic_ctx)
        .map_err(InductiveCheckError::MissingSpec)?;

    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(InductiveCheckError::MissingSpec)?;
    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(InductiveCheckError::MissingSpec)?;

    // Resolve the inductive invariant operator.
    let inv_resolved = symbolic_ctx.resolve_op_name(&ind_config.invariant);
    let inv_expr = z4_shared::get_operator_body(&symbolic_ctx, inv_resolved)
        .map_err(|e| InductiveCheckError::InvariantNotFound(e))?;

    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);
    let inv_expanded = expand_operators_for_chc(&symbolic_ctx, &inv_expr, false);

    // Build config with the inductive invariant as the sole invariant for sort inference.
    let inv_names = vec![ind_config.invariant.clone()];
    let var_sorts = z4_shared::infer_var_sorts(&vars, &init_expanded, &inv_names, &symbolic_ctx);

    if ind_config.debug {
        eprintln!(
            "[inductive-check] checking {} vars, invariant={}",
            var_sorts.len(),
            ind_config.invariant,
        );
    }

    // Phase 1: Initiation — Init /\ ¬IndInv should be UNSAT.
    let phase1 = check_initiation(&var_sorts, &init_expanded, &inv_expanded, ind_config)?;
    match phase1 {
        PhaseResult::Pass => {
            if ind_config.debug {
                eprintln!("[inductive-check] Phase 1 (Initiation) PASSED");
            }
        }
        PhaseResult::Fail => {
            return Ok(InductiveCheckResult::InitiationFailed {
                reason: format!(
                    "Some initial state violates the invariant `{}`",
                    ind_config.invariant
                ),
            });
        }
        PhaseResult::Unknown(reason) => {
            return Ok(InductiveCheckResult::Unknown {
                phase: InductivePhase::Initiation,
                reason,
            });
        }
    }

    // Phase 2: Consecution — IndInv /\ Next /\ ¬IndInv' should be UNSAT.
    let phase2 = check_consecution(&var_sorts, &next_expanded, &inv_expanded, ind_config)?;
    match phase2 {
        PhaseResult::Pass => {
            if ind_config.debug {
                eprintln!("[inductive-check] Phase 2 (Consecution) PASSED");
            }
        }
        PhaseResult::Fail => {
            return Ok(InductiveCheckResult::ConsecutionFailed {
                reason: format!(
                    "The invariant `{}` is not preserved by some transition",
                    ind_config.invariant
                ),
            });
        }
        PhaseResult::Unknown(reason) => {
            return Ok(InductiveCheckResult::Unknown {
                phase: InductivePhase::Consecution,
                reason,
            });
        }
    }

    Ok(InductiveCheckResult::Proved)
}

/// Internal phase result.
enum PhaseResult {
    /// UNSAT — the phase passed.
    Pass,
    /// SAT — the phase failed (counterexample exists).
    Fail,
    /// Solver returned unknown.
    Unknown(String),
}

/// Phase 1: Check `Init /\ ¬IndInv` is UNSAT.
///
/// If UNSAT, all initial states satisfy the invariant.
/// If SAT, there exists an initial state that violates it.
fn check_initiation(
    var_sorts: &[(String, tla_z4::TlaSort)],
    init_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    inv_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    ind_config: &InductiveCheckConfig,
) -> Result<PhaseResult, InductiveCheckError> {
    // depth=0: only step 0, no transitions.
    let mut translator = z4_shared::make_translator(var_sorts, 0)?;
    translator.set_timeout(ind_config.solve_timeout);

    for (name, sort) in var_sorts {
        translator.declare_var(name, sort.clone())?;
    }

    // Assert Init(s0).
    let init_term = translator.translate_init(init_expanded)?;
    translator.assert(init_term);

    // Assert ¬IndInv(s0).
    let not_inv = translator.translate_not_safety_at_step(inv_expanded, 0)?;
    translator.assert(not_inv);

    match translator.try_check_sat()? {
        SolveResult::Unsat(_) => Ok(PhaseResult::Pass),
        SolveResult::Sat => Ok(PhaseResult::Fail),
        SolveResult::Unknown => {
            let reason = match translator.last_unknown_reason() {
                Some(UnknownReason::Timeout) => {
                    "solver timed out during initiation check".to_string()
                }
                Some(other) => format!("solver unknown during initiation: {other:?}"),
                None => "solver unknown during initiation check".to_string(),
            };
            Ok(PhaseResult::Unknown(reason))
        }
        _ => Ok(PhaseResult::Unknown(
            "unexpected solver result during initiation".to_string(),
        )),
    }
}

/// Phase 2: Check `IndInv /\ Next /\ ¬IndInv'` is UNSAT.
///
/// If UNSAT, the invariant is preserved by all transitions.
/// If SAT, there exists a transition from a state satisfying IndInv
/// to a state violating IndInv.
fn check_consecution(
    var_sorts: &[(String, tla_z4::TlaSort)],
    next_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    inv_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    ind_config: &InductiveCheckConfig,
) -> Result<PhaseResult, InductiveCheckError> {
    // depth=1: two step frames (s0 -> s1), one transition.
    let mut translator = z4_shared::make_translator(var_sorts, 1)?;
    translator.set_timeout(ind_config.solve_timeout);

    for (name, sort) in var_sorts {
        translator.declare_var(name, sort.clone())?;
    }

    // Assert IndInv(s0) — the induction hypothesis (no Init constraint).
    let inv_at_0 = translator.translate_safety_at_step(inv_expanded, 0)?;
    translator.assert(inv_at_0);

    // Assert Next(s0, s1).
    let next_term = translator.translate_next(next_expanded, 0)?;
    translator.assert(next_term);

    // Assert ¬IndInv(s1) — the negated conclusion.
    let not_inv_at_1 = translator.translate_not_safety_at_step(inv_expanded, 1)?;
    translator.assert(not_inv_at_1);

    match translator.try_check_sat()? {
        SolveResult::Unsat(_) => Ok(PhaseResult::Pass),
        SolveResult::Sat => Ok(PhaseResult::Fail),
        SolveResult::Unknown => {
            let reason = match translator.last_unknown_reason() {
                Some(UnknownReason::Timeout) => {
                    "solver timed out during consecution check".to_string()
                }
                Some(other) => format!("solver unknown during consecution: {other:?}"),
                None => "solver unknown during consecution check".to_string(),
            };
            Ok(PhaseResult::Unknown(reason))
        }
        _ => Ok(PhaseResult::Unknown(
            "unexpected solver result during consecution".to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::parse_module;

    /// Helper: run inductive check on a spec string.
    fn check_spec_inductive(
        src: &str,
        invariant: &str,
    ) -> Result<InductiveCheckResult, InductiveCheckError> {
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec![invariant.to_string()],
            ..Default::default()
        };

        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let ind_config = InductiveCheckConfig {
            invariant: invariant.to_string(),
            solve_timeout: Some(Duration::from_secs(30)),
            debug: false,
        };

        check_inductive(&module, &config, &ctx, &ind_config)
    }

    // ---- Test 1: Invariant that IS 1-inductive (both phases pass) ----
    //
    // Variable x starts at 0 and stays at 0 forever.
    // IndInv: x = 0.
    // Initiation: Init => x=0. TRUE (x=0 in Init).
    // Consecution: x=0 /\ x'=x => x'=0. TRUE.

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inductive_check_proves_stable_invariant() {
        let src = r#"
---- MODULE StableZero ----
VARIABLE x
Init == x = 0
Next == x' = x
IndInv == x = 0
====
"#;

        let result = check_spec_inductive(src, "IndInv").expect("should succeed");
        match result {
            InductiveCheckResult::Proved => {} // expected
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    // ---- Test 2: Initiation fails (Init does not imply IndInv) ----
    //
    // Variable x starts at 0 or 1.
    // IndInv: x = 0.
    // Initiation: Init /\ ¬(x=0) is SAT (x=1 satisfies Init but not IndInv).

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inductive_check_initiation_fails() {
        let src = r#"
---- MODULE BadInit ----
VARIABLE x
Init == x \in {0, 1}
Next == x' = x
IndInv == x = 0
====
"#;

        let result = check_spec_inductive(src, "IndInv").expect("should succeed");
        match result {
            InductiveCheckResult::InitiationFailed { reason } => {
                assert!(
                    reason.contains("IndInv"),
                    "reason should mention the invariant name: {reason}"
                );
            }
            other => panic!("expected InitiationFailed, got {other:?}"),
        }
    }

    // ---- Test 3: Consecution fails (IndInv is not preserved by Next) ----
    //
    // Variable x starts at 0. Next increments x.
    // IndInv: x >= 0.
    // Initiation: Init => x >= 0. TRUE (x=0 >= 0).
    // Consecution: x >= 0 /\ x'=x+1 => x' >= 0. TRUE (x+1 >= 0 when x >= 0).
    //
    // Wait, that's actually inductive. Let me use a different example.
    //
    // Variable x starts at 0. Next sets x' = x + 1.
    // IndInv: x <= 10.
    // Initiation: Init => x <= 10. TRUE (x=0 <= 10).
    // Consecution: x <= 10 /\ x'=x+1 => x' <= 10.
    //   Counterexample: x=10, x'=11, 11 > 10. SAT. FAILS.

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inductive_check_consecution_fails() {
        let src = r#"
---- MODULE BadConsecution ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
IndInv == x <= 10
====
"#;

        let result = check_spec_inductive(src, "IndInv").expect("should succeed");
        match result {
            InductiveCheckResult::ConsecutionFailed { reason } => {
                assert!(
                    reason.contains("IndInv"),
                    "reason should mention the invariant name: {reason}"
                );
            }
            other => panic!("expected ConsecutionFailed, got {other:?}"),
        }
    }

    // ---- Test 4: Two-variable inductive invariant ----
    //
    // Variables x, y. Init: x=0, y=0. Next: x'=y, y'=x (swap).
    // IndInv: x >= 0 /\ y >= 0.
    // Initiation: x=0 >= 0 /\ y=0 >= 0. TRUE.
    // Consecution: (x>=0 /\ y>=0) /\ (x'=y /\ y'=x) => (x'>=0 /\ y'>=0).
    //   x'=y >= 0 (from hypothesis). y'=x >= 0 (from hypothesis). TRUE.

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inductive_check_two_variable_proved() {
        let src = r#"
---- MODULE TwoVar ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = y /\ y' = x
IndInv == x >= 0 /\ y >= 0
====
"#;

        let result = check_spec_inductive(src, "IndInv").expect("should succeed");
        match result {
            InductiveCheckResult::Proved => {} // expected
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    // ---- Test 5: Invariant that holds in all reachable states but is NOT inductive ----
    //
    // x starts at 0, increments by 1. x <= 100 holds for the first 101 states
    // but is not inductive because consecution fails at x=100.
    // This is the classic example of a "safety property" vs "inductive invariant".

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inductive_check_safety_not_inductive() {
        let src = r#"
---- MODULE SafetyNotInductive ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
IndInv == x <= 100
====
"#;

        let result = check_spec_inductive(src, "IndInv").expect("should succeed");
        match result {
            InductiveCheckResult::ConsecutionFailed { .. } => {} // expected
            other => panic!("expected ConsecutionFailed, got {other:?}"),
        }
    }

    // ---- Test 6: Toggle spec — classic 1-inductive invariant ----
    //
    // x toggles between 0 and 1. IndInv: x \in {0,1} (as x>=0 /\ x<=1).
    // Initiation: x \in {0,1} => x>=0 /\ x<=1. TRUE.
    // Consecution: x>=0 /\ x<=1 /\ (IF x=0 THEN x'=1 ELSE x'=0) => x'>=0 /\ x'<=1.
    //   If x=0: x'=1, 1>=0 /\ 1<=1. TRUE.
    //   If x=1: x'=0, 0>=0 /\ 0<=1. TRUE.
    //   No other cases possible. UNSAT.

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inductive_check_toggle_proved() {
        let src = r#"
---- MODULE Toggle ----
VARIABLE x
Init == x \in {0, 1}
Next == IF x = 0 THEN x' = 1 ELSE x' = 0
IndInv == x >= 0 /\ x <= 1
====
"#;

        let result = check_spec_inductive(src, "IndInv").expect("should succeed");
        match result {
            InductiveCheckResult::Proved => {} // expected
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    // ---- Test 7: Error — invariant operator not found ----

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inductive_check_error_invariant_not_found() {
        let src = r#"
---- MODULE NoInv ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;

        let result = check_spec_inductive(src, "NonExistent");
        match result {
            Err(InductiveCheckError::InvariantNotFound(msg)) => {
                assert!(
                    msg.contains("NonExistent"),
                    "error should mention the missing invariant: {msg}"
                );
            }
            other => panic!("expected InvariantNotFound error, got {other:?}"),
        }
    }

    // ---- Test 8: Error — missing Init ----

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inductive_check_error_missing_init() {
        let src = r#"
---- MODULE MissingInit ----
VARIABLE x
Next == x' = x
IndInv == x >= 0
====
"#;

        let module = parse_module(src);
        let config = Config {
            init: None,
            next: Some("Next".to_string()),
            invariants: vec!["IndInv".to_string()],
            ..Default::default()
        };

        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let ind_config = InductiveCheckConfig {
            invariant: "IndInv".to_string(),
            solve_timeout: Some(Duration::from_secs(10)),
            debug: false,
        };

        let err = check_inductive(&module, &config, &ctx, &ind_config)
            .expect_err("should fail with missing Init");
        assert!(
            matches!(err, InductiveCheckError::MissingSpec(_)),
            "expected MissingSpec error, got {err:?}"
        );
    }

    // ---- Test 9: Both phases pass with arithmetic (x stays in bounded range) ----
    //
    // x starts at 5. Next: x' = IF x > 0 THEN x - 1 ELSE 0.
    // IndInv: x >= 0.
    // Initiation: 5 >= 0. TRUE.
    // Consecution: x>=0 /\ (IF x>0 THEN x'=x-1 ELSE x'=0) => x'>=0.
    //   If x>0: x'=x-1, x-1 >= 0 (since x >= 1). TRUE.
    //   If x=0: x'=0, 0>=0. TRUE.
    //   UNSAT.

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn test_inductive_check_decrement_to_zero() {
        let src = r#"
---- MODULE DecrToZero ----
VARIABLE x
Init == x = 5
Next == IF x > 0 THEN x' = x - 1 ELSE x' = 0
IndInv == x >= 0
====
"#;

        let result = check_spec_inductive(src, "IndInv").expect("should succeed");
        match result {
            InductiveCheckResult::Proved => {} // expected
            other => panic!("expected Proved, got {other:?}"),
        }
    }
}
