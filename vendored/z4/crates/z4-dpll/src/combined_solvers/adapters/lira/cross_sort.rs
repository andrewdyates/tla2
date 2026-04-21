// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-sort value and bound propagation between LIA and LRA.
//!
//! When `to_real(x)` appears in a Real constraint, LRA shares the same TermId
//! for `x` as LIA. After LIA determines a tight bound (e.g., `x = 1`), this
//! value must be forwarded to LRA so it can detect conflicts with Real
//! constraints on the same variable.

use num_bigint::BigInt;
use num_rational::BigRational;
use z4_core::{SplitRequest, TermId, TheoryLit, TheoryResult};
use z4_lra::Bound;

use super::{CrossSortTrailEntry, LiraSolver};

impl LiraSolver<'_> {
    /// Propagate LIA integer values to LRA for shared variables (#4915, #5947).
    ///
    /// Returns `(propagation_count, optional_split_request)`.
    ///
    /// For each shared variable:
    /// - **Tight bounds** (lower == upper): propagate `x = value` with bound reasons (sound).
    /// - **Non-tight bounds**: propagate individual bounds to LRA (sound) AND
    ///   request a split so that branch-and-bound establishes tight bounds.
    ///   This avoids asserting `x = v` with reasons that only justify `l <= x <= u`,
    ///   which creates unsound conflict clauses (#5947 soundness fix).
    pub(super) fn propagate_cross_sort_values(
        &mut self,
        debug: bool,
    ) -> (usize, Option<TheoryResult>) {
        let lia_lra = self.lia.lra_solver();
        let lra_vars = self.lra.term_to_var();
        // #6217: When to_int terms exist, their values are propagated by
        // propagate_to_int_values which handles the floor axiom correctly.
        // Cross-sort splits on variables related to to_int equations never
        // converge because the DPLL solver can't find a stable assignment.
        // Suppress cross-sort splits when to_int terms are present.
        let has_to_int = !self.lra.to_int_terms().is_empty();

        let mut to_propagate: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();
        let mut to_propagate_bounds: Vec<(TermId, Option<Bound>, Option<Bound>)> = Vec::new();
        let mut need_split: Option<(TermId, BigRational)> = None;

        for (&term, _) in lia_lra.term_to_var() {
            // #6217: Only propagate cross-sort values for Int-sorted terms.
            // Real-sorted terms (e.g., the argument x in to_int(x)) appear in
            // both LIA's internal LRA and the main LRA but are not cross-sort
            // variables. Propagating their values and requesting integer-style
            // floor/ceil splits creates artificial gaps (e.g., x<=2 OR x>=3)
            // that exclude valid Real values like 2.5, causing false UNSAT.
            // Matches AUFLIRA adapter behavior (auf_lira.rs:286-288).
            if !matches!(self.terms.sort(term), z4_core::Sort::Int) {
                continue;
            }
            // `term_to_var()` is populated during `register_atom()`, so it contains
            // registration artifacts for Int-only literals. Only propagate terms
            // that also appeared in a literal actually asserted to the Real side.
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
                    .push(CrossSortTrailEntry::Propagated(term, key));
                if reasons.is_empty() {
                    // #5947 soundness fix: bounds not tight from SAT atoms.
                    // Propagate individual bounds and request a split.
                    if let Some((lower, upper)) = lia_lra.get_bounds(term) {
                        if lower.is_none() && upper.is_none() {
                            // #6198: No direct bounds, but implied bounds through
                            // the simplex tableau may exist. Request a split so
                            // the DPLL solver explores the value.
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
        tight: Vec<(TermId, BigRational, Vec<TheoryLit>)>,
        bounds: Vec<(TermId, Option<Bound>, Option<Bound>)>,
        debug: bool,
    ) {
        for (term, value, reasons) in tight {
            if debug {
                safe_eprintln!(
                    "[N-O LIRA] Cross-sort value: term {:?} = {} ({} reasons)",
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
                    "[N-O LIRA] Cross-sort bounds: term {:?} lower={} upper={}",
                    term,
                    lower.is_some(),
                    upper.is_some()
                );
            }
            self.lra
                .assert_cross_sort_bounds(term, lower.as_ref(), upper.as_ref());
        }
    }

    /// Build a split request for a non-tight shared variable (#5947).
    fn make_cross_sort_split(term: TermId, value: BigRational, debug: bool) -> TheoryResult {
        let int_val = value.to_integer();
        let half = BigRational::new(1.into(), 2.into());
        let split_point = value + &half;
        if debug {
            safe_eprintln!(
                "[N-O LIRA] Requesting split on shared var {:?} at {}",
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

    /// Propagate `to_int(x)` values from LRA to LIA (#5944).
    ///
    /// After LRA computes x's value, floor(x) is the correct value for to_int(x).
    /// Assert to_int(x) = floor(x) as tight bounds in LIA's internal LRA solver
    /// so LIA can propagate it through equalities like `y = to_int(x)`.
    pub(super) fn propagate_to_int_values(&mut self, debug: bool) -> usize {
        let to_int_terms = self.lra.to_int_terms().to_vec();
        if to_int_terms.is_empty() {
            return 0;
        }

        let var_to_term: hashbrown::HashMap<u32, TermId> = self
            .lra
            .term_to_var()
            .iter()
            .map(|(&t, &v)| (v, t))
            .collect();

        let lia_lra_vars = self.lia.lra_solver().term_to_var().clone();
        let mut count = 0;

        for (to_int_var, inner_arg_term) in to_int_terms {
            let Some(&to_int_term) = var_to_term.get(&to_int_var) else {
                continue;
            };
            // Only propagate if LIA knows about this to_int variable
            if !lia_lra_vars.contains_key(&to_int_term) {
                continue;
            }
            // Get x's value from LRA
            let Some(arg_val) = self.lra.get_value(inner_arg_term) else {
                continue;
            };
            let floored = BigRational::from(arg_val.floor().to_integer());
            // Check if already propagated
            let key = floored.numer().clone();
            if !self
                .propagated_cross_sort
                .insert((to_int_term, key.clone()))
            {
                continue;
            }
            self.cross_sort_trail
                .push(CrossSortTrailEntry::Propagated(to_int_term, key));

            // #6217: Collect the bound reasons for x from main LRA.
            // The floor axiom `to_int(x) = floor(x)` is justified by the
            // constraints on x (e.g., x >= 2.5 and x <= 2.9 justify floor = 2).
            // Passing these as reasons makes the tight bound "provable" from
            // SAT-level atoms, so cross-sort propagation treats it as tight
            // instead of requesting an integer-style split that never converges.
            let arg_reasons: Vec<TheoryLit> = self
                .lra
                .get_value_with_all_bound_reasons(inner_arg_term)
                .map(|(_, r)| r)
                .unwrap_or_default();

            if debug {
                safe_eprintln!(
                    "[N-O LIRA] to_int propagation: to_int(term {:?}) = floor({}) = {} ({} reasons)",
                    inner_arg_term,
                    arg_val,
                    floored,
                    arg_reasons.len()
                );
            }
            // Assert tight bound: to_int(x) = floor(x) in LIA's internal solver
            // with the reasons from x's bounds in main LRA.
            self.lia
                .lra_solver_mut()
                .assert_tight_bound(to_int_term, &floored, &arg_reasons);
            count += 1;
        }
        count
    }
}
