// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier result mapping: interprets SAT/UNSAT through CEGQI and E-matching semantics.
//!
//! `map_quantifier_result` translates the raw theory-solve result into the correct
//! quantified-formula answer by accounting for CEGQI forall/exists inversion,
//! E-matching incompleteness, interleaved refinement, and assertion restoration.

use z4_core::TermId;

use super::super::Executor;
use super::QuantifierProcessingResult;
use crate::cegqi::CegqiInstantiator;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::logic_detection::LogicCategory;

use super::super::MAX_INTERLEAVED_EMATCHING_ROUNDS;

/// Mutable state threaded through interleaved E-matching refinement.
struct InterleavedEmatchingState {
    result: Result<SolveResult>,
    reached_instantiation_limit: bool,
    ematching_added_instantiations: bool,
    unsat_from_interleaved: bool,
}

impl Executor {
    /// Map theory-solve result through quantifier/CEGQI semantics.
    ///
    /// Handles CEGQI forall/exists result inversion, E-matching incompleteness,
    /// and assertion restoration after quantifier preprocessing.
    pub(in crate::executor) fn map_quantifier_result(
        &mut self,
        result: Result<SolveResult>,
        qr: QuantifierProcessingResult,
        category: LogicCategory,
    ) -> Result<SolveResult> {
        let QuantifierProcessingResult {
            has_uninstantiated_quantifiers,
            reached_instantiation_limit,
            has_deferred,
            cegqi_has_forall,
            cegqi_has_exists,
            ematching_added_instantiations,
            refinement_assertions,
            cegqi_ce_lemma_ids,
            has_completely_unhandled_quantifiers,
            unhandled_quantifiers,
            ematching_has_exists,
            original_assertions,
            cegqi_state,
        } = qr;

        // Phase 1: Interleaved E-matching refinement (#5927).
        let ems = self.run_interleaved_ematching(
            result,
            &refinement_assertions,
            has_uninstantiated_quantifiers,
            ematching_added_instantiations,
            reached_instantiation_limit,
            category,
        );

        // Phase 2: Classify result through CEGQI/E-matching semantics.
        let mut final_result = self.classify_quantifier_result(
            ems.result,
            ems.ematching_added_instantiations,
            ems.reached_instantiation_limit,
            ems.unsat_from_interleaved,
            has_uninstantiated_quantifiers,
            has_deferred,
            cegqi_has_forall,
            cegqi_has_exists,
            &cegqi_ce_lemma_ids,
            has_completely_unhandled_quantifiers,
            &unhandled_quantifiers,
            ematching_has_exists,
            &cegqi_state,
            category,
        );

        // Phase 3: Restore original assertions after solve (#2844).
        self.restore_assertions(original_assertions, &mut final_result);

        final_result
    }

    /// DPLL(T)-interleaved E-matching (#5927): after the initial SAT solve,
    /// re-run E-matching with the fresh EUF model until fixpoint.
    fn run_interleaved_ematching(
        &mut self,
        result: Result<SolveResult>,
        refinement_assertions: &Option<Vec<TermId>>,
        has_uninstantiated_quantifiers: bool,
        ematching_added_instantiations: bool,
        reached_instantiation_limit: bool,
        category: LogicCategory,
    ) -> InterleavedEmatchingState {
        let mut state = InterleavedEmatchingState {
            result,
            reached_instantiation_limit,
            ematching_added_instantiations,
            unsat_from_interleaved: false,
        };
        let had_preprocessing_instances = ematching_added_instantiations;

        let orig = match (refinement_assertions, &state.result) {
            (Some(orig), Ok(SolveResult::Sat)) => orig,
            _ => return state,
        };
        if !state.ematching_added_instantiations && !has_uninstantiated_quantifiers {
            return state;
        }

        for _round in 0..MAX_INTERLEAVED_EMATCHING_ROUNDS {
            let added = self.try_ematching_refinement_round(orig);
            if added == 0 {
                break;
            }
            state.ematching_added_instantiations = true;

            let re_result = self.solve_for_category(category);
            match re_result {
                Ok(SolveResult::Sat) => {
                    state.result = re_result;
                }
                Ok(SolveResult::Unsat) => {
                    state.result = re_result;
                    state.reached_instantiation_limit = false;
                    if had_preprocessing_instances {
                        state.unsat_from_interleaved = true;
                    }
                    break;
                }
                other => {
                    state.result = other;
                    break;
                }
            }
        }
        state
    }

    /// Classify the solve result through CEGQI/E-matching semantics.
    #[allow(clippy::too_many_arguments)]
    fn classify_quantifier_result(
        &mut self,
        result: Result<SolveResult>,
        ematching_added_instantiations: bool,
        reached_instantiation_limit: bool,
        unsat_from_interleaved: bool,
        has_uninstantiated_quantifiers: bool,
        has_deferred: bool,
        cegqi_has_forall: bool,
        cegqi_has_exists: bool,
        cegqi_ce_lemma_ids: &[TermId],
        has_completely_unhandled_quantifiers: bool,
        unhandled_quantifiers: &[TermId],
        ematching_has_exists: bool,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
    ) -> Result<SolveResult> {
        let cegqi_mixed = cegqi_has_forall && cegqi_has_exists;

        match result {
            Ok(SolveResult::Sat) | Ok(SolveResult::Unknown) if cegqi_mixed => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
            Ok(SolveResult::Unsat) if unsat_from_interleaved && cegqi_ce_lemma_ids.is_empty() => {
                Ok(SolveResult::Unsat)
            }
            Ok(SolveResult::Unsat)
                if (cegqi_mixed || cegqi_has_forall) && !cegqi_ce_lemma_ids.is_empty() =>
            {
                self.disambiguate_cegqi_unsat(category, cegqi_ce_lemma_ids, cegqi_mixed)
            }
            Ok(SolveResult::Sat) if cegqi_has_forall && !ematching_added_instantiations => {
                let refinement_result =
                    self.try_cegqi_arith_refinement(cegqi_state, category, cegqi_ce_lemma_ids);
                if let Some(result) = refinement_result {
                    result
                } else {
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    Ok(SolveResult::Unknown)
                }
            }
            Ok(SolveResult::Sat) if cegqi_has_exists => Ok(SolveResult::Sat),
            Ok(SolveResult::Unsat) if cegqi_has_exists => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
            Ok(SolveResult::Sat)
                if (has_uninstantiated_quantifiers && !ematching_added_instantiations)
                    || reached_instantiation_limit
                    || has_deferred
                    || has_completely_unhandled_quantifiers =>
            {
                if !unhandled_quantifiers.is_empty() {
                    if let Some(mbqi_result) =
                        self.try_mbqi_refinement(unhandled_quantifiers, category)
                    {
                        mbqi_result
                    } else {
                        self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
                        Ok(SolveResult::Unknown)
                    }
                } else {
                    let reason = if reached_instantiation_limit {
                        UnknownReason::QuantifierRoundLimit
                    } else if has_deferred {
                        UnknownReason::QuantifierDeferred
                    } else {
                        UnknownReason::QuantifierUnhandled
                    };
                    self.last_unknown_reason = Some(reason);
                    Ok(SolveResult::Unknown)
                }
            }
            Ok(SolveResult::Unsat) if ematching_has_exists && !cegqi_has_exists => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierEmatchingExistsIncomplete);
                Ok(SolveResult::Unknown)
            }
            other => other,
        }
    }

    /// Restore original assertions after quantifier solving (#2844).
    fn restore_assertions(
        &mut self,
        original_assertions: Option<Vec<TermId>>,
        final_result: &mut Result<SolveResult>,
    ) {
        if self.defer_model_validation {
            self.defer_model_validation = false;
            self.ctx.assertions = original_assertions
                .expect("BUG: defer_model_validation set but original_assertions is None");
            if matches!(final_result, Ok(SolveResult::Sat)) {
                *final_result = self.finalize_sat_model_validation();
            }
        } else if let Some(original_assertions) = original_assertions {
            self.ctx.assertions = original_assertions;
        }
    }

    /// Disambiguate UNSAT from CEGQI refinement (#5975).
    ///
    /// Re-solves without CE lemmas to determine if UNSAT is genuine
    /// (from ground assertions alone) or CE-induced (forall is valid → SAT).
    pub(super) fn disambiguate_cegqi_unsat(
        &mut self,
        category: LogicCategory,
        ce_lemma_ids: &[TermId],
        is_mixed: bool,
    ) -> Result<SolveResult> {
        if ce_lemma_ids.is_empty() {
            return Ok(SolveResult::Unsat);
        }

        let ground_only: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|a| !ce_lemma_ids.contains(a))
            .collect();
        let saved = std::mem::replace(&mut self.ctx.assertions, ground_only);

        let saved_theory_state = self.incr_theory_state.take();
        let ground_result = self.solve_for_category(category);
        self.ctx.assertions = saved;
        self.incr_theory_state = saved_theory_state;

        match ground_result {
            Ok(SolveResult::Unsat) => Ok(SolveResult::Unsat),
            Ok(SolveResult::Sat) if !is_mixed => Ok(SolveResult::Sat),
            _ => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
        }
    }
}
