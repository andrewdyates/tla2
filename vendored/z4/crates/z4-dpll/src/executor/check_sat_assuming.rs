// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! check-sat-assuming entry point extraction.

use hashbrown::HashSet;
use z4_core::{Sort, TermId};
use z4_frontend::OptionValue;

use super::dt_axioms::DtSolverDispatch;
use super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor_types::{ExecutorError, Result, SolveResult, Statistics, UnknownReason};
use crate::logic_detection::{LogicCategory, TheoryKind};

impl Executor {
    /// Run check-sat with assumptions.
    ///
    /// The assumptions are temporary - they are only used for this check-sat call
    /// and do not affect the assertion stack.
    ///
    /// `pub(crate)`: External consumers MUST use `api::Solver::check_sat_assuming()`
    /// which returns `VerifiedSolveResult`. Part of #5787 (Phase 6).
    pub(crate) fn check_sat_assuming(&mut self, assumptions: &[TermId]) -> Result<SolveResult> {
        // Clear any previous model/proof
        self.last_model = None;
        self.last_proof = None;
        self.last_lrat_certificate = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_clause_trace = None;
        self.last_var_to_term = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.last_unknown_reason = None;
        self.last_statistics = Statistics::default();
        self.last_statistics.num_assertions = self.ctx.assertions.len() as u64;
        self.proof_problem_assertion_provenance = None;
        // Clear per-solve transient flags (parity with check_sat_internal)
        self.skip_model_eval = false;
        self.defer_model_validation = false;
        self.defer_counterexample_minimization = false;
        self.bypass_string_tautology_guard = false;
        self.slia_accepted_unknown = false;
        self.array_axiom_scope = None;
        self.proof_check_result = None;

        // Store assumptions for potential get-unsat-assumptions call
        self.last_assumptions = Some(assumptions.to_vec());

        // Sync proof tracker with :produce-proofs option (matches check_sat_internal)
        if matches!(
            self.ctx.get_option("produce-proofs"),
            Some(OptionValue::Bool(true))
        ) {
            self.proof_tracker.enable();
        }

        // Reset proof content for new solving session (keep scope tracking
        // for incremental push/pop balance) (#5992)
        self.proof_tracker.reset_session();

        // Use the base assertions from context, assumptions are passed separately
        let base_assertions = self.ctx.assertions.clone();

        if base_assertions.is_empty() && assumptions.is_empty() {
            // SOUNDNESS: No assertions and no assumptions means the formula is
            // trivially satisfiable (empty conjunction = true). This fast path
            // bypasses check_sat_guarded() and finalize_sat_model_validation(),
            // which is correct because there are no assertions to validate against.
            // Part of #7912 (Gap A).
            debug_assert!(
                self.ctx.assertions.is_empty(),
                "BUG: base_assertions empty but ctx.assertions non-empty"
            );
            debug_assert!(
                assumptions.is_empty(),
                "BUG: entered empty-assertions fast path with non-empty assumptions"
            );
            self.last_result = Some(SolveResult::Sat);
            return Ok(SolveResult::Sat);
        }

        let mut all_assertions = base_assertions.clone();
        all_assertions.extend(assumptions.iter().copied());

        if all_assertions
            .iter()
            .copied()
            .any(|assertion| contains_quantifier(&self.ctx.terms, assertion))
        {
            let result = self.solve_quantified_assumptions(&base_assertions, assumptions)?;
            return Ok(self.finish_check_sat_assuming_result(assumptions, result));
        }

        let (category, features) = self.detect_logic_category(&all_assertions);

        // Use assumption-based solving for supported theories
        let result = match category {
            LogicCategory::Propositional => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Propositional,
            ),
            LogicCategory::QfUf => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Euf,
            ),
            LogicCategory::QfS => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Strings,
            ),
            LogicCategory::QfAx => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::ArrayEuf,
            ),
            LogicCategory::QfLra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Lra,
            ),
            LogicCategory::QfLia => self.solve_lia_with_assumptions(&base_assertions, assumptions),
            LogicCategory::QfNia => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Nia,
            ),
            LogicCategory::QfNra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Nra,
            ),
            LogicCategory::QfNira => {
                if features.has_real {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_with_assumptions_for_theory(
                        &base_assertions,
                        assumptions,
                        TheoryKind::Nia,
                    )
                }
            }
            LogicCategory::QfUfnra | LogicCategory::QfUfnia | LogicCategory::QfUfnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfUflia => {
                self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfSeq => self.solve_seq_with_assumptions(&base_assertions, assumptions),
            // Route Seq<BitVec> through the scoped-assertion Seq path so every
            // assumption participates in Seq axiom injection and BV comparison
            // transitivity before solving (#7656).
            LogicCategory::QfSeqBv => {
                self.solve_seq_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfSeqlia => {
                self.solve_seq_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfSlia => {
                self.solve_strings_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfSnia => {
                if features.has_nonlinear_int {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_strings_lia_with_assumptions(&base_assertions, assumptions)
                }
            }
            LogicCategory::QfUflra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::UfLra,
            ),
            LogicCategory::QfAuflia => {
                self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfAuflra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::AufLra,
            ),
            LogicCategory::QfLira => {
                self.solve_lira_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfAuflira => {
                self.solve_auflira_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfFp | LogicCategory::QfBvfp => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfBv => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Bv,
            ),
            LogicCategory::QfAbv => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::ArrayBv,
            ),
            LogicCategory::QfUfbv => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::UfBv,
            ),
            LogicCategory::QfAufbv => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::AufBv,
            ),
            LogicCategory::QfBvLia => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfBvLiaIndep => {
                self.solve_bv_lia_indep_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::Lia => {
                self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::Lra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Lra,
            ),
            LogicCategory::Nia | LogicCategory::Nra => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Ufnia | LogicCategory::Ufnra | LogicCategory::Ufnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Uf => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Euf,
            ),
            LogicCategory::Uflia | LogicCategory::Auflia => {
                self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::Auflra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::AufLra,
            ),
            LogicCategory::Uflra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::UfLra,
            ),
            LogicCategory::Lira => self.solve_lira_with_assumptions(&base_assertions, assumptions),
            LogicCategory::Auflira => {
                self.solve_auflira_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::Nira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfDt => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Dt,
            ),
            LogicCategory::DtAuflia => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                Some(Sort::Int),
                DtSolverDispatch::AufLia,
            ),
            LogicCategory::DtAuflra => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                Some(Sort::Real),
                DtSolverDispatch::Theory(TheoryKind::AufLra),
            ),
            LogicCategory::DtAuflira => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                Some(Sort::Int),
                DtSolverDispatch::AufLira,
            ),
            LogicCategory::DtUfbv => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                None,
                DtSolverDispatch::Theory(TheoryKind::UfBv),
            ),
            LogicCategory::DtAufbv => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                None,
                DtSolverDispatch::Theory(TheoryKind::AufBv),
            ),
            LogicCategory::DtAx => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                None,
                DtSolverDispatch::Theory(TheoryKind::ArrayEuf),
            ),
            // Quantified DT logics (#7150): route to DT-combined solvers
            LogicCategory::Ufdt | LogicCategory::Aufdt => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Dt,
            ),
            LogicCategory::Ufdtlia | LogicCategory::Aufdtlia => self
                .dt_combined_check_sat_assuming(
                    &base_assertions,
                    assumptions,
                    Some(Sort::Int),
                    DtSolverDispatch::AufLia,
                ),
            LogicCategory::Ufdtlra => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                Some(Sort::Real),
                DtSolverDispatch::Theory(TheoryKind::AufLra),
            ),
            LogicCategory::Ufdtlira | LogicCategory::Aufdtlira => self
                .dt_combined_check_sat_assuming(
                    &base_assertions,
                    assumptions,
                    Some(Sort::Int),
                    DtSolverDispatch::AufLira,
                ),
            LogicCategory::Ufdtnia | LogicCategory::Ufdtnra | LogicCategory::Ufdtnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Other => Err(ExecutorError::UnsupportedLogic(
                self.ctx.logic().unwrap_or("<unspecified>").to_string(),
            )),
        }?;

        let result = if result == SolveResult::Sat {
            self.last_result = Some(SolveResult::Sat);
            let validated = self.finalize_sat_model_validation()?;
            if validated == SolveResult::Sat {
                self.finalize_sat_assumption_validation(assumptions)?
            } else {
                validated
            }
        } else {
            result
        };

        if result == SolveResult::Sat {
            debug_assert!(
                self.last_model.is_some(),
                "BUG: check_sat_assuming returned SAT without populating last_model"
            );
        }
        if result == SolveResult::Unsat {
            debug_assert!(
                self.last_assumption_core.is_some(),
                "BUG: check_sat_assuming returned UNSAT without populating assumption core"
            );
        }

        Ok(self.finish_check_sat_assuming_result(assumptions, result))
    }

    /// Quantified `check-sat-assuming` fallback.
    ///
    /// The dedicated assumption solvers do not understand quantified formulas;
    /// routing quantified assertions there bypasses E-matching/CEGQI entirely
    /// and can return false SAT. For quantified assumption checks, temporarily
    /// solve over `base_assertions ∪ assumptions` using the regular quantifier
    /// pipeline, then restore the original assertion stack.
    ///
    /// UNSAT assumption cores are conservative: derived instantiations lose the
    /// SAT selector provenance of the assumptions that triggered them, so we
    /// report all active assumptions as the core rather than a potentially
    /// unsound subset.
    fn solve_quantified_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        let mut combined_assertions = base_assertions.to_vec();
        combined_assertions.extend(assumptions.iter().copied());

        let original_assertions = std::mem::replace(&mut self.ctx.assertions, combined_assertions);
        let solve_result = self.solve_current_assertions_with_quantifier_support();
        self.ctx.assertions = original_assertions;

        match solve_result? {
            SolveResult::Sat => {
                self.last_result = Some(SolveResult::Sat);
                self.finalize_sat_assumption_validation(assumptions)
            }
            SolveResult::Unsat => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::Unsat)
            }
            SolveResult::Unknown => Ok(SolveResult::Unknown),
        }
    }

    fn finish_check_sat_assuming_result(
        &mut self,
        assumptions: &[TermId],
        result: SolveResult,
    ) -> SolveResult {
        if result == SolveResult::Sat {
            debug_assert!(
                self.last_model.is_some(),
                "BUG: check_sat_assuming returned SAT without populating last_model"
            );
        }
        if result == SolveResult::Unsat {
            debug_assert!(
                self.last_assumption_core.is_some(),
                "BUG: check_sat_assuming returned UNSAT without populating last_assumption_core"
            );
        }

        self.last_result = Some(result);

        debug_assert!(
            result != SolveResult::Sat || self.last_model.is_some(),
            "BUG: check_sat_assuming returned SAT without populating last_model"
        );
        debug_assert!(
            result != SolveResult::Unsat || self.last_assumption_core.is_some(),
            "BUG: check_sat_assuming returned UNSAT without populating last_assumption_core"
        );
        debug_assert!(
            result != SolveResult::Unsat
                || self.last_assumption_core.as_ref().is_none_or(|core| {
                    let assumption_set: HashSet<TermId> = assumptions.iter().copied().collect();
                    core.iter().all(|t| assumption_set.contains(t))
                }),
            "BUG: UNSAT assumption core contains terms not in the original assumptions"
        );

        result
    }
}
