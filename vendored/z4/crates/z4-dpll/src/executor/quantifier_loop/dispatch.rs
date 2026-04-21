// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic-category dispatch and E-matching refinement for quantifier solving.
//!
//! `solve_for_category` mirrors the main dispatch table in `executor.rs` for
//! re-solving during CEGQI and E-matching refinement loops.
//! `try_ematching_refinement_round` runs one interleaved E-matching round
//! using the fresh EUF model after a SAT solve.

#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::TermId;

use super::super::model::EvalValue;
use super::super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::features::StaticFeatures;
use crate::logic_detection::LogicCategory;
use crate::quantifier_manager::QuantifierManager;

impl Executor {
    /// Dispatch to the appropriate theory solver for the given logic category.
    ///
    /// Must mirror the main dispatch table in `executor.rs` check_sat_internal.
    /// Missing categories here cause CEGQI refinement to silently return Unknown (#5989).
    pub(in crate::executor) fn solve_for_category(
        &mut self,
        category: LogicCategory,
    ) -> Result<SolveResult> {
        match category {
            LogicCategory::Propositional => self.solve_propositional(),
            LogicCategory::QfUf | LogicCategory::Uf => self.solve_euf(),
            LogicCategory::QfAx => self.solve_array_euf(),
            LogicCategory::QfLra | LogicCategory::Lra => self.solve_lra(),
            LogicCategory::QfLia | LogicCategory::Lia => self.solve_lia(),
            LogicCategory::QfNia | LogicCategory::Nia => self.solve_nia(),
            LogicCategory::QfNra | LogicCategory::Nra => self.solve_nra(),
            LogicCategory::QfLira | LogicCategory::Lira => self.solve_lira(),
            LogicCategory::QfNira | LogicCategory::Nira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfUfnra | LogicCategory::Ufnra => self.solve_uf_nra(),
            LogicCategory::QfUfnia
            | LogicCategory::QfUfnira
            | LogicCategory::Ufnia
            | LogicCategory::Ufnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfUflia | LogicCategory::Uflia => self.solve_auf_lia(),
            LogicCategory::QfUflra | LogicCategory::Uflra => self.solve_uf_lra(),
            LogicCategory::QfAuflia | LogicCategory::Auflia => self.solve_auf_lia(),
            LogicCategory::QfAuflra | LogicCategory::Auflra => self.solve_auf_lra(),
            LogicCategory::QfAuflira | LogicCategory::Auflira => self.solve_auflira(),
            LogicCategory::QfSeq => self.solve_seq(),
            LogicCategory::QfSeqBv => self.solve_seq(),
            LogicCategory::QfSeqlia => self.solve_seq_lia(),
            LogicCategory::QfS => self.solve_strings(),
            LogicCategory::QfSlia => self.solve_strings_lia(),
            LogicCategory::QfSnia => {
                let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
                if features.has_nonlinear_int {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_strings_lia()
                }
            }
            LogicCategory::QfBv => self.solve_bv(),
            LogicCategory::QfAbv => self.solve_abv(),
            LogicCategory::QfUfbv => self.solve_ufbv(),
            LogicCategory::QfAufbv => self.solve_aufbv(),
            LogicCategory::QfBvLia => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfBvLiaIndep => self.solve_bv_lia_indep(),
            LogicCategory::QfFp => self.solve_fp(),
            LogicCategory::QfBvfp => self.solve_bvfp(),
            LogicCategory::QfDt => self.solve_dt(),
            LogicCategory::DtAuflia => self.solve_dt_auflia(),
            LogicCategory::DtAuflra => self.solve_dt_auflra(),
            LogicCategory::DtAuflira => self.solve_dt_auflira(),
            LogicCategory::DtUfbv => self.solve_dt_ufbv(),
            LogicCategory::DtAufbv => self.solve_dt_aufbv(),
            LogicCategory::DtAx => self.solve_dt_ax(),
            // Quantified DT logics (#7150): route to DT-combined solvers
            LogicCategory::Ufdt | LogicCategory::Aufdt => self.solve_dt(),
            LogicCategory::Ufdtlia | LogicCategory::Aufdtlia => self.solve_dt_auflia(),
            LogicCategory::Ufdtlra => self.solve_dt_auflra(),
            LogicCategory::Ufdtlira | LogicCategory::Aufdtlira => self.solve_dt_auflira(),
            LogicCategory::Ufdtnia | LogicCategory::Ufdtnra | LogicCategory::Ufdtnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Other => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
        }
    }

    /// Phase B1c (#3325): Run one E-matching refinement round using the fresh EUF model.
    ///
    /// Returns the number of new instances added to `self.ctx.assertions`.
    /// Returns 0 if no model is available or no new instances were found.
    pub(in crate::executor) fn try_ematching_refinement_round(
        &mut self,
        original_assertions: &[TermId],
    ) -> usize {
        let euf_model_ref = self.last_model.as_ref().and_then(|m| m.euf_model.as_ref());
        if euf_model_ref.is_none() {
            return 0;
        }

        let mut combined_assertions: Vec<TermId> = self.ctx.assertions.clone();
        for &a in original_assertions {
            if contains_quantifier(&self.ctx.terms, a) && !combined_assertions.contains(&a) {
                combined_assertions.push(a);
            }
        }

        let qm = self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);

        let ematching_result =
            qm.run_ematching_round(&mut self.ctx.terms, &combined_assertions, euf_model_ref);

        let existing: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut added = 0usize;

        for inst in ematching_result.instantiations {
            if existing.contains(&inst) {
                continue;
            }
            if let Some(ref model) = self.last_model {
                if matches!(self.evaluate_term(model, inst), EvalValue::Bool(true)) {
                    continue;
                }
            }
            self.ctx.assertions.push(inst);
            added += 1;
        }

        added
    }
}
