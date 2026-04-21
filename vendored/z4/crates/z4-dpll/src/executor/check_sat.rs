// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Check-sat pipeline: solve dispatch, interrupt handling, logic routing.
//!
//! Extracted from `executor.rs` for code health — the check-sat pipeline
//! is the largest cohesive unit in the executor.

use hashbrown::HashMap;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Instant;
use z4_core::TermId;

use super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::logic_detection::LogicCategory;

/// Red zone for `stacker::maybe_grow` at the executor check-sat entry point.
/// When remaining stack is below this threshold, stacker allocates a new
/// segment before entering the solve pipeline. This prevents repeated
/// mmap/munmap cycles from inner theory guards (e.g., NRA's 4 MiB red zone)
/// that cause extreme slowdown on small thread stacks in debug mode (#6783).
///
/// Must exceed NRA's own 4 MiB red zone so the outer grow covers the inner
/// check, eliminating the double-grow penalty.
const EXECUTOR_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    6 * 1024 * 1024 // 6 MiB in debug — exceeds NRA's 4 MiB red zone
} else {
    2 * 1024 * 1024 // 2 MiB in release
};

/// Stack segment size allocated by stacker when the red zone is reached.
/// 16 MiB provides ample room for the entire solve pipeline including
/// theory solvers, model validation, and proof checking in debug mode.
const EXECUTOR_STACK_SIZE: usize = 16 * 1024 * 1024;

impl Executor {
    /// Solve the current `ctx.assertions` with quantifier preprocessing enabled.
    ///
    /// Shared by `check_sat_internal` and the quantified `check_sat_assuming`
    /// fallback path. Handles E-matching/CEGQI preprocessing, logic detection,
    /// quantified-LIA div/mod bailout, solver dispatch, and result remapping.
    pub(super) fn solve_current_assertions_with_quantifier_support(
        &mut self,
    ) -> Result<SolveResult> {
        // Quantifier preprocessing: E-matching, CEGQI, promote-unsat, assertion filtering.
        // Reads last_model.euf_model for congruence-aware E-matching, then clears it.
        let qr = self.process_quantifiers();
        self.last_model = None;

        let (category, features) = self.detect_logic_category(&self.ctx.assertions);

        // Defer model validation when quantifier E-matching modified the assertion set.
        // The theory solver would validate against ground instances instead of the original
        // quantified assertions, causing false violations (#2862). Validation happens after
        // original_assertions are restored in map_quantifier_result.
        if qr.original_assertions.is_some() {
            self.defer_model_validation = true;
        }

        // Bail early on quantified LIA/LRA with div/mod: CEGQI refinement cannot
        // converge when div/mod creates opaque auxiliary variables in LIA preprocessing.
        // Each branch-and-bound iteration is expensive, causing debug-mode hangs (#6889).
        // Skip the initial solve entirely and return Unknown via map_quantifier_result.
        if qr.cegqi_has_forall
            && features.has_int_div_mod
            && matches!(category, LogicCategory::Lia | LogicCategory::Lra)
        {
            self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
            let result = Ok(SolveResult::Unknown);
            return self.map_quantifier_result(result, qr, category);
        }

        let result = self.route_to_solver(category, &features);

        // Map theory-solve result through quantifier/CEGQI semantics and restore assertions.
        self.map_quantifier_result(result, qr, category)
    }

    /// Run check-sat on current assertions.
    ///
    /// `pub(crate)`: External consumers MUST use `api::Solver::check_sat()` which
    /// returns `VerifiedSolveResult`. This method performs runtime validation
    /// (via `finalize_sat_model_validation`) but does not carry compile-time
    /// verification provenance. Part of #5787 (Phase 6).
    pub(crate) fn check_sat(&mut self) -> Result<SolveResult> {
        // Guard against small thread stacks: grow once here so inner theory
        // guards (NRA, model eval, proof checking) don't repeatedly mmap/munmap
        // their own segments. This fixes #6783 where repeated stacker growth
        // cycles caused extreme slowdown on 2 MiB threads in debug mode.
        stacker::maybe_grow(EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE, || {
            self.check_sat_guarded()
        })
    }

    /// Inner check-sat after stack guard. Separated to keep `check_sat` small.
    fn check_sat_guarded(&mut self) -> Result<SolveResult> {
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.skip_model_eval = false;
        let result = self.check_sat_internal()?;
        let result = if result == SolveResult::Sat && !self.last_model_validated {
            // Model validation expects a SAT marker in last_result.
            // Skip if map_quantifier_result already validated (deferred validation path).
            self.last_result = Some(SolveResult::Sat);
            self.finalize_sat_model_validation()?
        } else {
            result
        };
        self.last_result = Some(result);

        // Postcondition: SAT must produce a model (unless trivially SAT with no assertions)
        debug_assert!(
            result != SolveResult::Sat
                || self.last_model.is_some()
                || self.ctx.assertions.is_empty(),
            "BUG: check_sat returned SAT without populating last_model"
        );
        // Postcondition: UNSAT with proofs enabled must produce a proof
        debug_assert!(
            result != SolveResult::Unsat
                || self.last_proof.is_some()
                || !self.produce_proofs_enabled(),
            "BUG: check_sat returned UNSAT without populating last_proof (proofs enabled)"
        );
        // Observability: log when SAT is returned without model validation (#5973).
        // This is expected for Seq/SeqLia logics but should be visible for debugging.
        if result == SolveResult::Sat && !self.last_model_validated {
            tracing::debug!(
                skip_model_eval = self.skip_model_eval,
                "SAT result returned without model validation (skip_model_eval or deferred)"
            );
        }

        // #7912 postcondition: every SAT result has been validated at some level.
        // - last_model_validated: full SMT-level assertion validation passed
        // - skip_model_eval: theory can't evaluate models, but boolean skeleton
        //   was checked (debug_assert in finalize_sat_model_validation)
        // - empty assertions: trivially SAT, no validation needed
        debug_assert!(
            result != SolveResult::Sat
                || self.last_model_validated
                || self.skip_model_eval
                || self.ctx.assertions.is_empty(),
            "BUG: check_sat returned SAT without any model validation path — \
             last_model_validated={}, skip_model_eval={}, assertions={}",
            self.last_model_validated,
            self.skip_model_eval,
            self.ctx.assertions.len(),
        );

        Ok(result)
    }

    // ========================================================================
    // Interrupt / Deadline helpers
    // ========================================================================

    /// Set a persistent interrupt flag that is checked during every check-sat.
    ///
    /// When the flag is set to `true`, ongoing and future solves return
    /// `Unknown` with reason `Interrupted`. This is used by the CLI watchdog
    /// to cooperatively stop the solver on global timeout (#2971).
    pub fn set_interrupt(&mut self, flag: Arc<AtomicBool>) {
        self.solve_interrupt = Some(flag);
    }

    /// Propagate API-level timeout/interrupt controls into theory split loops.
    pub(crate) fn set_solve_controls(
        &mut self,
        interrupt: Option<Arc<AtomicBool>>,
        deadline: Option<Instant>,
    ) {
        self.solve_interrupt = interrupt;
        self.solve_deadline = deadline;
    }

    /// Clear solve controls after a check-sat call completes.
    pub(crate) fn clear_solve_controls(&mut self) {
        self.solve_interrupt = None;
        self.solve_deadline = None;
    }

    /// Build a `should_stop` closure for `solve_interruptible` that checks
    /// the executor's interrupt flag and deadline without borrowing `self`.
    ///
    /// The returned closure captures snapshots of the interrupt flag (Arc clone)
    /// and deadline (Copy), so it can be passed to SAT solver methods that
    /// require `Fn() -> bool` while `self` remains available for other use.
    pub(crate) fn make_should_stop(&self) -> impl Fn() -> bool {
        let interrupt_flag = self.solve_interrupt.clone();
        let deadline = self.solve_deadline;
        move || {
            if let Some(ref flag) = interrupt_flag {
                if flag.load(Ordering::Relaxed) {
                    return true;
                }
            }
            if let Some(dl) = deadline {
                if Instant::now() >= dl {
                    return true;
                }
            }
            false
        }
    }

    /// Check whether the current solve should abort due to interrupt/timeout.
    ///
    /// Returns `true` when the caller should return `Unknown` immediately.
    pub(crate) fn should_abort_theory_loop(&mut self) -> bool {
        if self
            .solve_interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            self.last_unknown_reason = Some(UnknownReason::Interrupted);
            self.last_result = Some(SolveResult::Unknown);
            return true;
        }

        if self.solve_deadline.is_some_and(|dl| Instant::now() >= dl) {
            self.last_unknown_reason = Some(UnknownReason::Timeout);
            self.last_result = Some(SolveResult::Unknown);
            return true;
        }

        false
    }

    // ========================================================================
    // Internal check-sat (logic routing)
    // ========================================================================

    /// Internal check-sat that also stores the model
    pub(super) fn check_sat_internal(&mut self) -> Result<SolveResult> {
        // Clear previous state. Defer last_model clear until after process_quantifiers()
        // which reads last_model.euf_model for congruence-aware E-matching (Phase B1b #3325).
        self.last_assumptions = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_proof = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_clause_trace = None;
        self.last_var_to_term = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.last_unknown_reason = None;
        self.proof_problem_assertion_provenance = None;
        self.last_statistics = crate::executor_types::Statistics::default();
        self.last_statistics.num_assertions = self.ctx.assertions.len() as u64;

        // Clear per-solve transient flags so they don't leak between (check-sat) calls
        self.bypass_string_tautology_guard = false;
        self.slia_accepted_unknown = false;
        self.array_axiom_scope = None;
        self.defer_model_validation = false;
        self.defer_counterexample_minimization = false;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.skip_model_eval = false;
        self.proof_check_result = None;

        // Sync proof tracker with :produce-proofs option
        if matches!(
            self.ctx.get_option("produce-proofs"),
            Some(z4_frontend::OptionValue::Bool(true))
        ) {
            self.proof_tracker.enable();
        }

        // Reset proof content for new solving session (keep scope tracking
        // for incremental push/pop balance) (#5992)
        self.proof_tracker.reset_session();

        if self.ctx.assertions.is_empty() {
            self.last_model = None;
            return Ok(SolveResult::Sat);
        }

        // Unsat core extraction: when produce-unsat-cores is enabled and there
        // are named assertions, redirect through check_sat_assuming with named
        // assertions as assumptions. The SAT solver's failed-assumption tracking
        // then gives us the minimal unsat core (MiniSat approach).
        if self.produce_unsat_cores_enabled() {
            let term_to_name: HashMap<TermId, String> = self
                .ctx
                .named_terms_iter()
                .map(|(name, tid)| (tid, name.to_string()))
                .collect();

            if !term_to_name.is_empty() {
                // Split assertions: named become assumptions, unnamed stay as base
                let mut named_assumptions = Vec::new();
                let mut unnamed_assertions = Vec::new();
                for &assertion in &self.ctx.assertions {
                    if term_to_name.contains_key(&assertion) {
                        named_assumptions.push(assertion);
                    } else {
                        unnamed_assertions.push(assertion);
                    }
                }

                // Only redirect if there are named assertions in the assertion set
                if !named_assumptions.is_empty() {
                    // Temporarily replace assertions with unnamed-only
                    let original_assertions =
                        std::mem::replace(&mut self.ctx.assertions, unnamed_assertions);

                    self.last_model = None;
                    let result = self.check_sat_assuming(&named_assumptions);

                    // Restore original assertions
                    self.ctx.assertions = original_assertions;

                    // Set the term-to-name mapping AFTER check_sat_assuming
                    // (which clears it as part of its own state reset).
                    self.last_core_term_to_name = Some(term_to_name);

                    return result;
                }
            }
        }

        let final_result = self.solve_current_assertions_with_quantifier_support();

        // SolveResult boundary postcondition contracts (#4642).
        // Every SAT must have a model, every proof-enabled UNSAT must have a proof.
        if let Ok(ref result) = final_result {
            match result {
                SolveResult::Sat => {
                    debug_assert!(
                        self.last_model.is_some(),
                        "BUG: check_sat_internal returned SAT without populating last_model"
                    );
                }
                SolveResult::Unsat => {
                    debug_assert!(
                        self.last_proof.is_some() || !self.produce_proofs_enabled(),
                        "BUG: check_sat_internal returned UNSAT without proof \
                         (produce-proofs is enabled)"
                    );
                }
                SolveResult::Unknown => {}
            }
        }

        final_result
    }

    /// Route to the appropriate theory solver based on detected logic category.
    ///
    /// Extracted from `check_sat_internal` for readability — the logic routing
    /// table is the largest single block in the check-sat pipeline.
    fn route_to_solver(
        &mut self,
        category: LogicCategory,
        features: &crate::features::StaticFeatures,
    ) -> Result<SolveResult> {
        match category {
            LogicCategory::Propositional => self.solve_propositional(),
            LogicCategory::QfUf => self.solve_euf(),
            LogicCategory::QfS => self.solve_strings(),
            LogicCategory::QfAx => self.solve_array_euf(),
            LogicCategory::QfLra => self.solve_lra(),
            LogicCategory::QfLia => self.solve_lia(),
            LogicCategory::QfNia => self.solve_nia(),
            LogicCategory::QfNra => self.solve_nra(),
            LogicCategory::QfNira => {
                if features.has_real {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_nia()
                }
            }
            // QF_UFNRA: UF + non-linear real arithmetic — combined via Nelson-Oppen (#6294).
            LogicCategory::QfUfnra => self.solve_uf_nra(),
            // QF_UFNIA/QF_UFNIRA: UF + non-linear integer arithmetic (#5984).
            // No combined UF+NIA solver exists yet. Without EUF congruence closure,
            // the NIA solver can assign inconsistent values to UF function
            // applications, producing unsound SAT results.
            LogicCategory::QfUfnia | LogicCategory::QfUfnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            // Use the more capable AufLia solver for UfLia - it handles theory
            // combination correctly with involves_int_arithmetic, while UfLia
            // has issues with equalities involving uninterpreted functions (#316).
            // Nonlinear terms upgraded to QfUfnia pre-dispatch (#6086).
            LogicCategory::QfUflia => self.solve_auf_lia(),
            LogicCategory::QfSeq => self.solve_seq(),
            LogicCategory::QfSeqBv => self.solve_seq(),
            LogicCategory::QfSeqlia => self.solve_seq_lia(),
            LogicCategory::QfSlia => self.solve_strings_lia(),
            // QF_SNIA: route linear formulas to strings+LIA (#3389).
            LogicCategory::QfSnia => {
                if features.has_nonlinear_int {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_strings_lia()
                }
            }
            // Nonlinear terms upgraded to QfUfnra pre-dispatch (#6086).
            LogicCategory::QfUflra => self.solve_uf_lra(),
            // Nonlinear terms upgraded to QfUfnia pre-dispatch (#6086).
            LogicCategory::QfAuflia => self.solve_auf_lia(),
            // Nonlinear terms upgraded to QfUfnra pre-dispatch (#6086).
            LogicCategory::QfAuflra => self.solve_auf_lra(),
            // Nonlinear terms upgraded to QfNira pre-dispatch (#6086).
            LogicCategory::QfLira => self.solve_lira(),
            // Nonlinear terms upgraded to QfUfnira pre-dispatch (#6086).
            LogicCategory::QfAuflira => self.solve_auflira(),
            LogicCategory::QfFp => self.solve_fp(),
            LogicCategory::QfBvfp => self.solve_bvfp(),
            LogicCategory::QfBv => self.solve_bv(),
            LogicCategory::QfAbv => self.solve_abv(),
            LogicCategory::QfUfbv => self.solve_ufbv(),
            LogicCategory::QfAufbv => self.solve_aufbv(),
            // BV + integer arithmetic with conversion functions: unsupported (#5503)
            LogicCategory::QfBvLia => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            // BV + Int without conversions: BV-first with AUFLIA fallback (#5356)
            LogicCategory::QfBvLiaIndep => self.solve_bv_lia_indep(),
            // Quantified logics: route to same solver as QF_ version.
            // Nonlinear terms upgraded to Nia/Nra pre-dispatch (#6086).
            LogicCategory::Lia => self.solve_lia(),
            LogicCategory::Lra => self.solve_lra(),
            // Quantified nonlinear: process_quantifiers() has already
            // stripped quantifiers and added ground instances via E-matching/
            // CEGQI/Skolemization. Route to ground solvers; map_quantifier_result
            // handles incompleteness (SAT→Unknown when quantifiers unhandled).
            LogicCategory::Nia => self.solve_nia(),
            LogicCategory::Nra => self.solve_nra(),
            LogicCategory::Ufnra => self.solve_uf_nra(),
            // Ufnia/Ufnira: no combined UF+NIA/UF+NIRA solver exists.
            // solve_nia()/solve_nra() would miss UF constraints, risking
            // unsound SAT. Return Unknown until a combined solver is built.
            LogicCategory::Ufnia | LogicCategory::Ufnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Uf => self.solve_euf(),
            // Nonlinear terms upgraded to Ufnia/Ufnra/Ufnira pre-dispatch (#6086).
            LogicCategory::Uflia => self.solve_auf_lia(),
            LogicCategory::Uflra => self.solve_uf_lra(),
            LogicCategory::Auflia => self.solve_auf_lia(),
            LogicCategory::Auflra => self.solve_auf_lra(),
            // Nonlinear terms upgraded to Nira pre-dispatch (#6086).
            LogicCategory::Lira => self.solve_lira(),
            LogicCategory::Auflira => self.solve_auflira(),
            LogicCategory::Nira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfDt => self.solve_dt(),
            // Combined DT + arithmetic: add DT axioms then route to arithmetic solver
            LogicCategory::DtAuflia => self.solve_dt_auflia(),
            LogicCategory::DtAuflra => self.solve_dt_auflra(),
            LogicCategory::DtAuflira => self.solve_dt_auflira(),
            // Combined DT + BV/Arrays: add DT axioms then route to BV/Array solver (#1766)
            LogicCategory::DtUfbv => self.solve_dt_ufbv(),
            LogicCategory::DtAufbv => self.solve_dt_aufbv(),
            LogicCategory::DtAx => self.solve_dt_ax(),
            // Quantified DT logics (#7150): quantifier preprocessing strips
            // quantifiers before reaching dispatch, so route to DT-combined solvers.
            LogicCategory::Ufdt | LogicCategory::Aufdt => self.solve_dt(),
            LogicCategory::Ufdtlia | LogicCategory::Aufdtlia => self.solve_dt_auflia(),
            LogicCategory::Ufdtlra => self.solve_dt_auflra(),
            LogicCategory::Ufdtlira | LogicCategory::Aufdtlira => self.solve_dt_auflira(),
            LogicCategory::Ufdtnia | LogicCategory::Ufdtnra | LogicCategory::Ufdtnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Other => Err(crate::executor_types::ExecutorError::UnsupportedLogic(
                self.ctx.logic().unwrap_or("<unspecified>").to_string(),
            )),
        }
    }
}
