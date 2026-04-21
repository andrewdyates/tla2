// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen bridge methods for AUFLIRA combined solver.
//!
//! Cross-sort propagation, interface bridge evaluation, subsolver
//! checking, and fixpoint handling. The struct definition, constructor,
//! and `TheorySolver` trait impl are in `auf_lira.rs`.

use z4_core::{Constant, SplitRequest, TermData, TermId, TheoryLit, TheoryResult, TheorySolver};
use z4_lra::Bound;

use super::auf_lira::{AufLiraCrossSortTrailEntry, AufLiraSolver, SubsolverCheckResult};
use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, discover_model_equality, forward_non_sat,
    propagate_array_index_info, propagate_equalities_to, triage_lia_result,
    triage_lra_result_deferred,
};
use crate::combined_solvers::interface_bridge::{
    evaluate_arith_term_with_reasons, evaluate_real_arith_term_with_reasons,
    lia_get_int_value_with_reasons, lra_get_real_value_with_reasons,
};

impl AufLiraSolver<'_> {
    /// Returns `Ok((lia_is_unknown, lra_is_unknown, deferred_lia, deferred_lra))` or early-returns a conflict.
    ///
    /// Cross-sort propagation (#5955) runs at N-O loop level after sub-solver checks.
    ///
    /// #7448: Use triage_lra_result_deferred instead of triage_lra_result.
    /// triage_lra_result early-returns NeedModelEquality/NeedDisequalitySplit,
    /// which skips cross-sort propagation entirely. For Big-M patterns
    /// like (* 1000000.0 (to_real phase)), LRA discovers model equalities
    /// before cross-sort can bridge LIA's integer bounds to LRA. Without
    /// deferral, the loop cycles NeedModelEquality → encode → re-check
    /// without ever propagating phase's integrality, producing Unknown.
    pub(super) fn check_subsolvers(&mut self) -> SubsolverCheckResult {
        // LIA: defer splits to fixpoint so cross-sort, EUF, and interface bridge
        // propagation all run before the split escapes to the pipeline (#7448).
        // Without deferral, LIA NeedSplit bypasses all N-O propagation channels,
        // causing the outer split loop to oscillate on cross-sort variables.
        let lia_result = self.lia.check();
        let lia_is_unknown = matches!(&lia_result, TheoryResult::Unknown);
        let (deferred_lia_result, lia_early) = triage_lia_result(lia_result);
        if let Some(early) = lia_early {
            return Err(Box::new(early));
        }

        // LRA: continue N-O loop on Unknown — EUF/LIA equalities may help (#4945).
        //
        // #7448: Use triage_lra_result_deferred instead of triage_lra_result.
        // Deferring NeedModelEquality/NeedDisequalitySplit allows cross-sort
        // propagation to bridge LIA's integer bounds to LRA before the split
        // escapes to the pipeline.
        let lra_result = self.lra.check();
        let lra_is_unknown = matches!(&lra_result, TheoryResult::Unknown);
        let (deferred_lra_result, lra_early) = triage_lra_result_deferred(lra_result);
        if let Some(early) = lra_early {
            return Err(Box::new(early));
        }

        // EUF consistency check before cross-theory propagation.
        if let Some(result) = forward_non_sat(self.euf.check()) {
            return Err(Box::new(result));
        }

        Ok((
            lia_is_unknown,
            lra_is_unknown,
            deferred_lia_result,
            deferred_lra_result,
        ))
    }

    pub(super) fn propagate_theory_equalities(
        &mut self,
        debug: bool,
        iteration: usize,
    ) -> Result<(usize, usize, usize, usize), Box<TheoryResult>> {
        let lia_eq_count = propagate_equalities_to(
            &mut self.lia,
            &mut self.euf,
            debug,
            "AUFLIRA-LIA",
            iteration,
        )
        .map_err(Box::new)?;
        let lra_eq_count = propagate_equalities_to(
            &mut self.lra,
            &mut self.euf,
            debug,
            "AUFLIRA-LRA",
            iteration,
        )
        .map_err(Box::new)?;
        let euf_to_lia_count = propagate_equalities_to(
            &mut self.euf,
            &mut self.lia,
            debug,
            "AUFLIRA-EUF->LIA",
            iteration,
        )
        .map_err(Box::new)?;
        let euf_to_lra_count = propagate_equalities_to(
            &mut self.euf,
            &mut self.lra,
            debug,
            "AUFLIRA-EUF->LRA",
            iteration,
        )
        .map_err(Box::new)?;
        Ok((
            lia_eq_count,
            lra_eq_count,
            euf_to_lia_count,
            euf_to_lra_count,
        ))
    }

    /// Evaluate Int-sorted interface terms under LIA model and propagate to EUF (#5227).
    pub(super) fn propagate_int_interface_bridge(&mut self, debug: bool) -> usize {
        let lia = &self.lia;
        let (new_eqs, _speculative) = self.interface.evaluate_and_propagate(
            self.terms,
            &|t| lia_get_int_value_with_reasons(lia, t),
            debug,
            "AUFLIRA",
        );
        let count = new_eqs.len();
        for eq in &new_eqs {
            self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            self.lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
        }
        count
    }

    /// Evaluate Real-sorted interface terms under LRA model and propagate to EUF (#5227).
    pub(super) fn propagate_real_interface_bridge(&mut self, debug: bool) -> usize {
        let lra = &self.lra;
        let (new_eqs, _speculative) = self.interface.evaluate_and_propagate_real(
            self.terms,
            &|t| lra_get_real_value_with_reasons(lra, t),
            debug,
            "AUFLIRA",
        );
        let count = new_eqs.len();
        for eq in &new_eqs {
            self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
        }
        count
    }

    pub(super) fn propagate_array_index_relations(&mut self) -> Result<bool, Box<TheoryResult>> {
        let mut array_progress = false;
        {
            let terms = self.terms;
            let lia = &self.lia;
            if let Some(result) =
                propagate_array_index_info(terms, &mut self.arrays, &mut self.euf, |t| {
                    let mut reasons = Vec::new();
                    let value = evaluate_arith_term_with_reasons(
                        terms,
                        &|var| lia_get_int_value_with_reasons(lia, var),
                        t,
                        &mut reasons,
                    )?;
                    Some((value, reasons))
                })
            {
                match result {
                    TheoryResult::Sat => array_progress = true,
                    other => return Err(Box::new(other)),
                }
            }
        }
        {
            let terms = self.terms;
            let lra = &self.lra;
            if let Some(result) =
                propagate_array_index_info(terms, &mut self.arrays, &mut self.euf, |t| {
                    let mut reasons = Vec::new();
                    let value = evaluate_real_arith_term_with_reasons(
                        terms,
                        &|var| lra_get_real_value_with_reasons(lra, var),
                        t,
                        &mut reasons,
                    )?;
                    Some((value, reasons))
                })
            {
                match result {
                    TheoryResult::Sat => array_progress = true,
                    other => return Err(Box::new(other)),
                }
            }
        }
        Ok(array_progress)
    }

    /// Propagate LIA integer values to LRA for shared variables (#5955).
    ///
    /// Ported from `LiraSolver::propagate_cross_sort_values` (#4915, #5947).
    /// Returns `(propagation_count, optional_split_request)`.
    pub(super) fn propagate_cross_sort_values(
        &mut self,
        debug: bool,
    ) -> (usize, Option<TheoryResult>) {
        use num_rational::BigRational;

        let lia_lra = self.lia.lra_solver();
        let lra_vars = self.lra.term_to_var();
        // #6217: When to_int terms exist, suppress cross-sort splits to avoid
        // conflict with floor axiom handling in propagate_to_int_values.
        let has_to_int = !self.lra.to_int_terms().is_empty();

        let mut to_propagate: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();
        let mut to_propagate_bounds: Vec<(TermId, Option<Bound>, Option<Bound>)> = Vec::new();
        let mut need_split: Option<(TermId, BigRational)> = None;

        for (&term, _) in lia_lra.term_to_var() {
            // Only propagate for Int-sorted terms that also appear in a literal
            // actually asserted to the Real side (#6198, ported from #6290).
            if !matches!(self.terms.sort(term), z4_core::Sort::Int) {
                continue;
            }
            if !self.asserted_real_int_terms.contains(&term) || !lra_vars.contains_key(&term) {
                continue;
            }
            if let Some((value, reasons)) = lia_lra.get_value_with_reasons(term) {
                if !value.is_integer() {
                    continue;
                }
                let key = value.to_integer();
                if !self.propagated_cross_sort.insert((term, key.clone())) {
                    continue;
                }
                self.cross_sort_trail
                    .push(AufLiraCrossSortTrailEntry::Propagated(term, key));
                if reasons.is_empty() {
                    // #5947 soundness fix: bounds not tight. Propagate individual
                    // bounds (not the value) and request a split.
                    if let Some((lower, upper)) = lia_lra.get_bounds(term) {
                        if lower.is_none() && upper.is_none() {
                            // #6198: No direct bounds on this variable, but bounds
                            // may be implied through the simplex tableau (e.g., via
                            // an equality `select(a,0) = phase` where `phase` has
                            // direct bounds). In this case, we can't propagate bounds
                            // (no reason atoms available), but we still request a
                            // split so the DPLL solver explores the value.
                            if !has_to_int
                                && lia_lra.has_implied_bounds(term)
                                && need_split.is_none()
                            {
                                need_split = Some((term, value));
                            }
                            continue;
                        }
                        to_propagate_bounds.push((term, lower, upper));
                        if !has_to_int && need_split.is_none() {
                            need_split = Some((term, value));
                        }
                    }
                } else {
                    to_propagate.push((term, value, reasons));
                }
            }
        }

        let count = to_propagate.len() + to_propagate_bounds.len();
        self.apply_cross_sort_propagations(to_propagate, to_propagate_bounds, debug);
        let split = need_split.map(|s| Self::make_cross_sort_split(s.0, s.1, debug));
        (count, split)
    }

    /// Apply collected cross-sort propagations to LRA.
    fn apply_cross_sort_propagations(
        &mut self,
        tight: Vec<(TermId, num_rational::BigRational, Vec<TheoryLit>)>,
        bounds: Vec<(TermId, Option<Bound>, Option<Bound>)>,
        debug: bool,
    ) {
        for (term, value, reasons) in tight {
            if debug {
                safe_eprintln!(
                    "[N-O AUFLIRA] Cross-sort value: term {:?} = {} ({} reasons)",
                    term,
                    value,
                    reasons.len()
                );
            }
            self.lra.assert_tight_bound(term, &value, &reasons);
        }
        for (term, lower, upper) in bounds {
            if debug {
                safe_eprintln!(
                    "[N-O AUFLIRA] Cross-sort bounds: term {:?} lower={} upper={}",
                    term,
                    lower.is_some(),
                    upper.is_some()
                );
            }
            self.lra
                .assert_cross_sort_bounds(term, lower.as_ref(), upper.as_ref());
        }
    }

    /// Handle fixpoint: final result after N-O convergence.
    /// Returns `Some(result)` to return from check, `None` to continue the N-O loop.
    pub(super) fn handle_fixpoint(
        &mut self,
        debug: bool,
        lia_is_unknown: bool,
        lra_is_unknown: bool,
        deferred_lia_result: Option<TheoryResult>,
        deferred_lra_result: Option<TheoryResult>,
        pending_cross_sort_split: Option<TheoryResult>,
    ) -> Option<TheoryResult> {
        if lia_is_unknown || lra_is_unknown {
            return Some(TheoryResult::Unknown);
        }
        // #7448: return deferred LIA results (NeedSplit, NeedDisequalitySplit)
        // at fixpoint, after cross-sort, EUF, and interface bridge propagation
        // have all had a chance to run. Without deferral, LIA NeedSplit bypasses
        // all N-O propagation channels, causing the outer split loop to oscillate.
        if let Some(lia_deferred) = deferred_lia_result {
            return Some(lia_deferred);
        }
        // #7448: return deferred LRA results (NeedModelEquality,
        // NeedDisequalitySplit, NeedExpressionSplit) at fixpoint,
        // after cross-sort propagation has had a chance to run.
        if let Some(lra_deferred) = deferred_lra_result {
            return Some(lra_deferred);
        }
        // #5955: return cross-sort split at fixpoint for tight bounds.
        if let Some(split) = pending_cross_sort_split {
            return Some(split);
        }
        // Model equality discovery for non-convex theory combination (#4906).
        // #7462: Use evaluate_arith_term_with_reasons (recursive expression
        // evaluation) instead of lia_get_int_value_with_reasons (direct variable
        // lookup). Without recursive evaluation, compound expressions like (+ p 3)
        // that are arguments to UF applications cannot be evaluated, so two UF
        // args that simplify to the same value (e.g., p+3=5 and q+1=5) are never
        // grouped together, and the pairwise bridge misses the equality.
        // Int-sorted terms via LIA:
        {
            let lia = &self.lia;
            let terms = self.terms;
            if let Some(model_eq) = discover_model_equality(
                self.interface.sorted_arith_terms().into_iter(),
                self.terms,
                &self.euf,
                &|t| {
                    let mut reasons = Vec::new();
                    evaluate_arith_term_with_reasons(
                        terms,
                        &|var| lia_get_int_value_with_reasons(lia, var),
                        t,
                        &mut reasons,
                    )
                },
                &[z4_core::Sort::Int],
                debug,
                "AUFLIRA",
            ) {
                return Some(model_eq);
            }
        }
        // Real-sorted terms via LRA:
        {
            let lra = &self.lra;
            let terms = self.terms;
            if let Some(model_eq) = discover_model_equality(
                self.interface.sorted_arith_terms().into_iter(),
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
                &[z4_core::Sort::Real],
                debug,
                "AUFLIRA",
            ) {
                return Some(model_eq);
            }
        }
        // Deferred array checks at fixpoint (#6282 Packet 2).
        let final_result = self.arrays.final_check();
        if let Some(result) = forward_non_sat(final_result) {
            return Some(result);
        }
        assert_fixpoint_convergence(
            "AUFLIRA",
            &mut [
                &mut self.lia,
                &mut self.lra,
                &mut self.euf,
                &mut self.arrays,
            ],
        );
        Some(TheoryResult::Sat)
    }

    /// Build a split request for a non-tight shared variable (#5947).
    pub(super) fn make_cross_sort_split(
        term: TermId,
        value: num_rational::BigRational,
        debug: bool,
    ) -> TheoryResult {
        use num_bigint::BigInt;
        use num_rational::BigRational;
        let int_val = value.to_integer();
        let half = BigRational::new(1.into(), 2.into());
        let split_point = value + &half;
        if debug {
            safe_eprintln!(
                "[N-O AUFLIRA] Requesting split on shared var {:?} at {}",
                term,
                split_point
            );
        }
        TheoryResult::NeedSplit(SplitRequest {
            variable: term,
            value: split_point,
            floor: int_val.clone(),
            ceil: int_val + BigInt::from(1),
        })
    }

    pub(super) fn record_asserted_real_int_term(&mut self, term: TermId) {
        if self.asserted_real_int_terms.insert(term) {
            self.cross_sort_trail
                .push(AufLiraCrossSortTrailEntry::AssertedRealIntTerm(term));
        }
    }

    /// Track Int-sorted terms that occur in literals routed to the Real solver.
    /// Mirrors LiraSolver::track_asserted_real_int_terms (#6290).
    pub(super) fn track_asserted_real_int_terms(&mut self, literal: TermId) {
        let mut visited: hashbrown::HashSet<TermId> = hashbrown::HashSet::new();
        let mut stack = vec![literal];

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }

            if matches!(self.terms.sort(term), z4_core::Sort::Int)
                && !matches!(self.terms.get(term), TermData::Const(Constant::Int(_)))
            {
                self.record_asserted_real_int_term(term);
            }

            stack.extend(self.terms.children(term));
        }
    }
}
