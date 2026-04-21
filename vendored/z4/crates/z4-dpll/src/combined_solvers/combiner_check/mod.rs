// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen fixpoint check loop for TheoryCombiner.
//!
//! Separated from `combiner.rs` for file-size compliance (#6332 Wave 0).

// Wave 1: TheoryCombiner now used in production dispatch (#6332).
#![allow(clippy::result_large_err)]

use num_bigint::BigInt;
use z4_core::{Sort, TermId, TheoryResult, TheorySolver};
use z4_euf::EufSolver;
use z4_lia::LiaSolver;

use super::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, discover_model_equality, forward_non_sat,
    propagate_array_index_info, propagate_equalities_to, triage_lia_result,
    triage_lra_result_deferred,
};
use super::combiner::TheoryCombiner;
use super::interface_bridge::{
    evaluate_arith_term_with_reasons, evaluate_real_arith_term_with_reasons,
    lia_get_int_value_with_reasons, lra_get_real_value_with_reasons,
};

/// Result of the arithmetic check + propagation step.
pub(super) struct ArithStepResult {
    pub(super) is_unknown: bool,
    pub(super) deferred: Option<TheoryResult>,
    pub(super) new_equalities: bool,
}

impl TheoryCombiner<'_> {
    /// The full N-O fixpoint check loop.
    pub(super) fn nelson_oppen_check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen();
        const MAX_ITERATIONS: usize = 100;

        for iteration in 0..MAX_ITERATIONS {
            let arith = match self.check_arith_step(debug, iteration) {
                Ok(a) => a,
                Err(result) => return result,
            };
            let mut has_new_eqs = arith.new_equalities;

            let (bridge_eqs, bridge_speculative) = self.evaluate_bridge(debug);
            for eq in &bridge_eqs {
                self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                if let Some(lia) = &mut self.lia {
                    lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                }
            }
            has_new_eqs |= !bridge_eqs.is_empty();

            let euf_check = self.euf.check();
            if let Some(result) = forward_non_sat(euf_check) {
                return result;
            }

            let euf_eq_count = match self.propagate_euf_to_arith(debug, iteration) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };

            match self.check_arrays_step(debug, iteration) {
                Ok(arr_new) => {
                    has_new_eqs |= arr_new;
                }
                Err(result) => return result,
            }

            if !has_new_eqs && euf_eq_count == 0 {
                if debug && iteration > 0 {
                    safe_eprintln!(
                        "[N-O {}] Fixpoint reached after {} iterations",
                        self.label,
                        iteration + 1
                    );
                }
                match self.handle_fixpoint(
                    debug,
                    arith.is_unknown,
                    arith.deferred,
                    &bridge_speculative,
                ) {
                    Some(result) => return result,
                    None => continue,
                }
            }

            // Non-convergence is a solver bug — assert in all build modes.
            assert!(
                iteration < MAX_ITERATIONS - 1,
                "BUG: {} Nelson-Oppen loop did not converge in {MAX_ITERATIONS} iterations",
                self.label
            );
        }

        TheoryResult::Unknown
    }

    // --- Per-step helpers ---

    fn check_arith_step(
        &mut self,
        debug: bool,
        iteration: usize,
    ) -> Result<ArithStepResult, TheoryResult> {
        if let Some(lia) = &mut self.lia {
            let result = lia.check();
            let is_unknown = matches!(&result, TheoryResult::Unknown);
            let (deferred, early) = triage_lia_result(result);
            if let Some(early) = early {
                return Err(early);
            }
            let eq_count = propagate_equalities_to(
                lia,
                &mut self.euf,
                debug,
                self.arith_prop_label,
                iteration,
            )?;
            Ok(ArithStepResult {
                is_unknown,
                deferred,
                new_equalities: eq_count > 0,
            })
        } else if let Some(lra) = &mut self.lra {
            let result = lra.check();
            let is_unknown = matches!(&result, TheoryResult::Unknown);
            let (deferred, early) = triage_lra_result_deferred(result);
            if let Some(early) = early {
                return Err(early);
            }
            let eq_count = propagate_equalities_to(
                lra,
                &mut self.euf,
                debug,
                self.arith_prop_label,
                iteration,
            )?;
            Ok(ArithStepResult {
                is_unknown,
                deferred,
                new_equalities: eq_count > 0,
            })
        } else {
            Ok(ArithStepResult {
                is_unknown: false,
                deferred: None,
                new_equalities: false,
            })
        }
    }

    fn propagate_euf_to_arith(
        &mut self,
        debug: bool,
        iteration: usize,
    ) -> Result<usize, TheoryResult> {
        // Drain EUF equalities once and forward to both arithmetic AND arrays.
        // The array solver's `notify_equality` uses these to eagerly queue ROW2
        // axioms before `check()` runs — Z3's merge_eh equivalent (#6546).
        let eq_result = self.euf.propagate_equalities();
        if let Some(conflict) = eq_result.conflict {
            if !conflict.is_empty() {
                return Err(TheoryResult::Unsat(conflict));
            }
            tracing::warn!(
                "BUG: {} propagate_equalities returned conflict with 0 reasons — \
                 returning Unknown instead of crashing",
                self.euf_prop_label
            );
            return Err(TheoryResult::Unknown);
        }
        let count = eq_result.equalities.len();
        if debug && count > 0 {
            safe_eprintln!(
                "[N-O {}] Iteration {}: discovered {} equalities (→arith+arrays)",
                self.euf_prop_label,
                iteration,
                count
            );
        }
        for eq in &eq_result.equalities {
            debug_assert!(
                eq.lhs != eq.rhs,
                "BUG: {} propagated trivial self-equality ({:?} = {:?})",
                self.euf_prop_label,
                eq.lhs,
                eq.rhs
            );
        }
        // Forward to arithmetic solver.
        for eq in &eq_result.equalities {
            if let Some(lia) = &mut self.lia {
                lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            } else if let Some(lra) = &mut self.lra {
                lra.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }
        }
        // Forward to array solver via notify_equality for eager ROW2 axiom
        // queuing (#6546 Approach B). This fires the store×select cross-product
        // so that check() finds pre-queued axioms in pending_axioms.
        let mut arrays_changed = false;
        if let Some(arrays) = &mut self.arrays {
            for eq in &eq_result.equalities {
                arrays.notify_equality(eq.lhs, eq.rhs);
            }
            arrays_changed = !eq_result.equalities.is_empty();
        }
        if arrays_changed {
            self.mark_arrays_dirty();
        }
        Ok(count)
    }

    fn check_arrays_step(&mut self, debug: bool, iteration: usize) -> Result<bool, TheoryResult> {
        if self.array_quiescent_epoch == Some(self.array_epoch) {
            return Ok(false);
        }

        let mut new_eqs = false;
        if let Some(arrays) = &mut self.arrays {
            if let Some(result) = forward_non_sat(arrays.check()) {
                return Err(result);
            }
            let arr_eq_count = propagate_equalities_to(
                arrays,
                &mut self.euf,
                debug,
                self.arr_prop_label,
                iteration,
            )?;
            new_eqs = arr_eq_count > 0;
        }
        if self.lia.is_none() && self.lra.is_none() {
            let mut arrays_changed = false;
            if let Some(arrays) = &mut self.arrays {
                let euf_to_arr = propagate_equalities_to(
                    &mut self.euf,
                    arrays,
                    debug,
                    self.euf_prop_label,
                    iteration,
                )?;
                arrays_changed = euf_to_arr > 0;
                new_eqs |= euf_to_arr > 0;
            }
            if arrays_changed {
                self.mark_arrays_dirty();
            }
        }
        if new_eqs {
            self.array_quiescent_epoch = None;
        } else {
            self.array_quiescent_epoch = Some(self.array_epoch);
        }
        Ok(new_eqs)
    }

    // --- Bridge and fixpoint helpers ---

    pub(super) fn evaluate_bridge(
        &mut self,
        debug: bool,
    ) -> (Vec<z4_core::DiscoveredEquality>, Vec<(TermId, TermId)>) {
        let interface = match &mut self.interface {
            Some(i) => i,
            None => return (Vec::new(), Vec::new()),
        };
        if let Some(lia) = &self.lia {
            let euf_int_values = build_euf_int_value_map(&mut self.euf);
            interface.evaluate_and_propagate(
                self.terms,
                &|t| get_value_with_euf_fallback(lia, &euf_int_values, t),
                debug,
                self.label,
            )
        } else if let Some(lra) = &self.lra {
            interface.evaluate_and_propagate_real(
                self.terms,
                &|t| lra_get_real_value_with_reasons(lra, t),
                debug,
                self.label,
            )
        } else {
            (Vec::new(), Vec::new())
        }
    }

    pub(super) fn handle_fixpoint(
        &mut self,
        debug: bool,
        arith_is_unknown: bool,
        deferred_arith_result: Option<TheoryResult>,
        bridge_speculative: &[(TermId, TermId)],
    ) -> Option<TheoryResult> {
        if self.arrays.is_some() {
            match self.propagate_array_indices() {
                Some(TheoryResult::Sat) => {
                    self.mark_arrays_dirty();
                    return None;
                }
                Some(r) => return Some(r),
                None => {}
            }
        }
        if arith_is_unknown {
            return Some(TheoryResult::Unknown);
        }
        if let Some(split) = deferred_arith_result {
            return Some(split);
        }
        // #6846: discover_model_eq returns non-EUF-equivalent pairs with proven
        // arithmetic reasons. Terms with zero LIA reasons (UF applications with
        // arbitrary model values) are excluded to prevent the split loop from
        // diverging on constantly-shifting value groupings.
        if let Some(model_eq) = self.discover_model_eq(debug) {
            return Some(model_eq);
        }
        // #6846: Bridge speculative pairs are zero-reason equalities from LIA
        // model evaluation of UF applications. These terms have coincidentally
        // matching LIA values but no arithmetic proof of equality. Route them
        // through NeedModelEqualities so the split loop encodes them as SAT
        // decisions with triangle axioms. The split loop's global model-eq
        // iteration counter prevents divergence.
        let mut batch = Vec::new();
        for &(lhs, rhs) in bridge_speculative {
            if !self.euf.are_equal(lhs, rhs) {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] Bridge speculative model equality: {:?} = {:?} (no arithmetic reasons, not EUF-equal)",
                        self.label,
                        lhs,
                        rhs,
                    );
                }
                batch.push(z4_core::ModelEqualityRequest {
                    lhs,
                    rhs,
                    reason: Vec::new(),
                });
            }
        }
        match batch.len() {
            0 => {}
            1 => return Some(TheoryResult::NeedModelEquality(batch.pop().unwrap())),
            _ => return Some(TheoryResult::NeedModelEqualities(batch)),
        }
        if let Some(arrays) = &mut self.arrays {
            if let Some(result) = forward_non_sat(arrays.final_check()) {
                return Some(result);
            }
        }
        self.assert_convergence();
        Some(TheoryResult::Sat)
    }

    fn propagate_array_indices(&mut self) -> Option<TheoryResult> {
        let arrays = self.arrays.as_mut()?;
        let terms = self.terms;
        if let Some(lia) = &self.lia {
            propagate_array_index_info(terms, arrays, &mut self.euf, |t| {
                let mut reasons = Vec::new();
                let value = evaluate_arith_term_with_reasons(
                    terms,
                    &|var| lia_get_int_value_with_reasons(lia, var),
                    t,
                    &mut reasons,
                )?;
                Some((value, reasons))
            })
        } else if let Some(lra) = &self.lra {
            propagate_array_index_info(terms, arrays, &mut self.euf, |t| {
                let mut reasons = Vec::new();
                let value = evaluate_real_arith_term_with_reasons(
                    terms,
                    &|var| lra_get_real_value_with_reasons(lra, var),
                    t,
                    &mut reasons,
                )?;
                Some((value, reasons))
            })
        } else {
            None
        }
    }

    fn discover_model_eq(&mut self, debug: bool) -> Option<TheoryResult> {
        let sorted_terms = self.interface.as_ref()?.sorted_arith_terms();
        if let Some(lia) = &self.lia {
            // #6846: Evaluation-based model equality discovery.
            // Groups Int-sorted interface terms by LIA model value,
            // batches all non-EUF-equal pairs.
            discover_model_equality(
                sorted_terms.into_iter(),
                self.terms,
                &self.euf,
                &|t| {
                    let mut reasons = Vec::new();
                    evaluate_arith_term_with_reasons(
                        self.terms,
                        &|var| lia_get_int_value_with_reasons(lia, var),
                        t,
                        &mut reasons,
                    )
                },
                &[Sort::Int],
                debug,
                self.label,
            )
        } else if let Some(lra) = &self.lra {
            // #7462: Use evaluate_real_arith_term_with_reasons (recursive
            // expression evaluation) instead of direct variable lookup.
            // Without recursive evaluation, compound UF arguments like
            // (+ x 0.5) cannot be evaluated, so two UF args that simplify
            // to the same value are never grouped together.
            let terms = self.terms;
            discover_model_equality(
                sorted_terms.into_iter(),
                self.terms,
                &self.euf,
                &|t| {
                    let mut reasons = Vec::new();
                    evaluate_real_arith_term_with_reasons(
                        terms,
                        &|var| lra_get_real_value_with_reasons(lra, var),
                        t,
                        &mut reasons,
                    )
                },
                &[Sort::Real],
                debug,
                self.label,
            )
        } else {
            None
        }
    }

    fn assert_convergence(&mut self) {
        let mut solvers: Vec<&mut dyn TheorySolver> = Vec::new();
        if let Some(lia) = &mut self.lia {
            solvers.push(lia);
        }
        if let Some(lra) = &mut self.lra {
            solvers.push(lra);
        }
        solvers.push(&mut self.euf);
        if let Some(arrays) = &mut self.arrays {
            solvers.push(arrays);
        }
        assert_fixpoint_convergence(self.label, &mut solvers);
    }
}

/// Build EUF int-value lookup with pre-computed explain reasons (#5081).
pub(super) fn build_euf_int_value_map(
    euf: &mut EufSolver<'_>,
) -> hashbrown::HashMap<TermId, (BigInt, Vec<z4_core::TheoryLit>)> {
    let raw_map = euf.build_int_value_map();
    let mut explained: hashbrown::HashMap<TermId, (BigInt, Vec<z4_core::TheoryLit>)> =
        Default::default();
    for (tid, (val, const_tid)) in raw_map {
        let reasons = euf.explain(tid, const_tid);
        explained.insert(tid, (val, reasons));
    }
    explained
}

/// Get integer value for a term, trying LIA first then EUF fallback (#5081).
///
/// CRITICAL: When falling back to EUF reasons, we MUST use EUF's value too.
/// LIA's model value and EUF's reasons may be inconsistent — LIA can assign
/// `v = 0` (trivial model) while EUF's equality chain justifies `v = 42`.
/// Mixing LIA's value with EUF's reasons produces an unsound (value, reasons)
/// pair that causes false-UNSAT (#6930).
pub(super) fn get_value_with_euf_fallback(
    lia: &LiaSolver<'_>,
    euf_int_values: &hashbrown::HashMap<TermId, (BigInt, Vec<z4_core::TheoryLit>)>,
    t: TermId,
) -> Option<(BigInt, Vec<z4_core::TheoryLit>)> {
    if let Some((val, lia_reasons)) = lia_get_int_value_with_reasons(lia, t) {
        if !lia_reasons.is_empty() {
            return Some((val, lia_reasons));
        }
        // LIA returned a value with no reasons (unconstrained variable).
        // If EUF has a justified value for this term, prefer EUF's (value, reasons)
        // pair — they are guaranteed consistent since EUF's value comes from its
        // own equivalence class and the reasons justify that specific value.
        if let Some((euf_val, euf_reasons)) = euf_int_values.get(&t) {
            if !euf_reasons.is_empty() {
                return Some((euf_val.clone(), euf_reasons.clone()));
            }
        }
        return Some((val, lia_reasons));
    }
    euf_int_values
        .get(&t)
        .map(|(val, reasons)| (val.clone(), reasons.clone()))
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
