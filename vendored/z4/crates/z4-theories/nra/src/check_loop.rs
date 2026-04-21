// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NRA check loop: LRA check → sign → patch → tangent refinement.
//!
//! Contains the main iteration loop and its supporting methods:
//! tentative scope management, sign injection, division refinement,
//! monomial consistency checks, and sign checking.
//!
//! Extracted from lib.rs as part of #5970 code-health splits.

use num_rational::BigRational;
use num_traits::{One, Zero};
use z4_core::term::{Constant, TermData, TermId};
use z4_core::{TheoryLit, TheoryResult, TheorySolver};

use super::NraSolver;
use crate::sign;

impl NraSolver<'_> {
    /// Undo all tentative scopes (sign-cut + patch) if any are active.
    /// Both the sign-cut scope (pushed at lib.rs:322) and the patch scope
    /// (pushed at patch.rs:245) must be popped to prevent model-dependent
    /// bounds from leaking into future queries.
    pub(crate) fn undo_tentative_patch(&mut self) {
        while self.tentative_depth > 0 {
            self.lra.pop();
            self.tentative_depth -= 1;
        }
    }

    /// Inject model-derived sign bounds for original variables into a tentative
    /// LRA scope. Based on Z3's `nla_basics_lemmas.cpp:sign_lemma()`.
    fn inject_tentative_sign_cuts(&mut self) -> usize {
        use z4_lra::GomoryCut;
        let vars = sign::vars_needing_model_sign(
            &self.monomials,
            &self.aux_to_monomial,
            &self.var_sign_constraints,
        );
        let zero = BigRational::zero();
        let mut added = 0;
        for var_id in vars {
            let Some(val) = self.var_value(var_id) else {
                continue;
            };
            let is_lower = if val > zero {
                true
            } else if val < zero {
                false
            } else {
                continue; // val == 0: no cut needed
            };
            let lra_var = self.lra.ensure_var_registered(var_id);
            self.lra.add_gomory_cut(
                &GomoryCut {
                    coeffs: vec![(lra_var, BigRational::one())],
                    bound: zero.clone(),
                    is_lower,
                    reasons: Vec::new(),
                    source_term: None,
                },
                var_id,
            );
            added += 1;
        }
        added
    }

    /// Get the value of a term: tries LRA model first, then constant extraction.
    /// Handles rational and integer constants that may not have LRA variables (#6811).
    pub(crate) fn term_value(&self, term: TermId) -> Option<BigRational> {
        if let Some(val) = self.lra.get_value(term) {
            return Some(val);
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
            _ => None,
        }
    }

    /// Check if any tracked division has an inconsistent model value.
    /// Returns true if `model(denom) * model(div_term) != model(num)`.
    pub(crate) fn has_inconsistent_divisions(&self) -> bool {
        for purif in &self.div_purifications {
            let Some(denom_val) = self.var_value(purif.denominator) else {
                continue;
            };
            let Some(div_val) = self.var_value(purif.div_term) else {
                continue;
            };
            let Some(num_val) = self.term_value(purif.numerator) else {
                continue;
            };
            if &denom_val * &div_val != num_val {
                return true;
            }
        }
        false
    }

    /// Generate tangent-plane refinement lemmas for inconsistent divisions.
    ///
    /// For `(/ num denom)` with model values `d = model(denom)`, `k = model(div_term)`,
    /// the tangent plane of `f(denom, div_term) = denom * div_term` at `(d, k)` is:
    ///   `T = k * denom + d * div_term - d*k`
    ///
    /// We add the constraint `T [cmp] num_value` as a Gomory cut, where `cmp` is
    /// `>=` if the product is below `num` and `<=` if above.
    fn generate_division_refinement(&mut self) -> usize {
        use z4_lra::GomoryCut;

        let purifs: Vec<_> = self.div_purifications.clone();
        let mut added = 0;

        for purif in &purifs {
            let Some(d) = self.var_value(purif.denominator) else {
                continue;
            };
            let Some(k) = self.var_value(purif.div_term) else {
                continue;
            };
            let Some(num_val) = self.term_value(purif.numerator) else {
                continue;
            };

            let product = &d * &k;
            if product == num_val {
                continue; // consistent
            }

            // Tangent plane: k*denom + d*div_term - d*k [cmp] num_val
            // Rearranged: k*denom + d*div_term [cmp] num_val + d*k
            let denom_var = self.lra.ensure_var_registered(purif.denominator);
            let div_var = self.lra.ensure_var_registered(purif.div_term);

            let coeffs = vec![(denom_var, k.clone()), (div_var, d.clone())];
            let bound = &num_val + &product;
            let is_lower = product < num_val;

            self.lra.add_gomory_cut(
                &GomoryCut {
                    coeffs,
                    bound,
                    is_lower,
                    reasons: Vec::new(),
                    source_term: None,
                },
                purif.div_term,
            );
            added += 1;

            if self.debug {
                tracing::debug!(
                    "[NRA] division refinement: denom={:?}, div={:?}, d={}, k={}, num={}",
                    purif.denominator,
                    purif.div_term,
                    d,
                    k,
                    num_val
                );
            }
        }
        added
    }

    /// Check if a monomial's value is consistent with its factors
    fn check_monomial_consistency(&self, mon: &crate::monomial::Monomial) -> bool {
        let mut product = BigRational::one();
        for &var in &mon.vars {
            if let Some(val) = self.var_value(var) {
                product *= val;
            } else {
                return true;
            }
        }

        if let Some(aux_val) = self.var_value(mon.aux_var) {
            aux_val == product
        } else {
            true
        }
    }

    /// Generate refinement lemmas for inconsistent monomials.
    ///
    /// Uses McCormick envelopes (sound, globally valid for bounded variables)
    /// and tangent hyperplanes (model-point approximations) as Gomory cuts.
    ///
    /// Returns `(total_added, used_approximation)` where `used_approximation`
    /// is true if tangent hyperplanes (model-point approximations) were added.
    fn generate_refinement_lemmas(&mut self) -> (usize, bool) {
        // McCormick envelopes + tangent hyperplanes
        let (tangent_added, used_tangent) = self.add_tangent_constraints_for_incorrect_monomials();
        self.tangent_lemma_count += tangent_added as u64;

        (tangent_added, used_tangent)
    }

    /// Check sign consistency: propagate factor signs, then detect conflicts.
    fn check_signs(&mut self) -> Option<TheoryResult> {
        sign::propagate_monomial_signs(&self.monomials, &mut self.var_sign_constraints);
        if let Some(conflict) = sign::check_sign_consistency(
            &self.monomials,
            &self.sign_constraints,
            &self.var_sign_constraints,
            &self.asserted,
            self.debug,
        ) {
            self.conflict_count += 1;
            return Some(TheoryResult::Unsat(conflict));
        }
        None
    }

    /// Run the NRA check loop: LRA check -> sign -> patch -> tangent.
    ///
    /// Following Z3's NLA check sequence (nla_core.cpp):
    /// sign consistency, model patching, then tangent plane refinement.
    pub(crate) fn nra_check_loop(&mut self) -> TheoryResult {
        // In debug mode, unoptimized BigRational arithmetic and
        // debug_assert_tableau_consistency checks make each LRA call ~100x
        // slower. 50 iterations with a growing tableau causes multi-minute
        // hangs (#6785). 10 iterations is enough to validate convergence
        // patterns without blocking the test suite.
        #[cfg(debug_assertions)]
        const MAX_ITERATIONS: usize = 10;
        #[cfg(not(debug_assertions))]
        const MAX_ITERATIONS: usize = 50;
        // Track whether tangent hyperplane approximations were used (#5959).
        // Tangent planes are model-point linearizations that may exclude valid
        // NRA solutions (e.g., near irrational points like √2). When tangent
        // planes were used and LRA becomes UNSAT, the UNSAT is unreliable.
        // McCormick envelopes, even-power non-negativity, and sign cuts do NOT
        // set this flag — they provide sound bounds for bounded variables.
        let mut used_tangent_approximation = false;

        for iteration in 0..=MAX_ITERATIONS {
            let lra_result = self.lra.check();

            match &lra_result {
                TheoryResult::Sat | TheoryResult::Unknown => {
                    if self.debug {
                        tracing::debug!(
                            "[NRA] check iter={}, monomials={}, sign_constraints={}, var_sign_constraints={}",
                            iteration, self.monomials.len(), self.sign_constraints.len(),
                            self.var_sign_constraints.len()
                        );
                    }

                    if let Some(conflict) = self.check_signs() {
                        return conflict;
                    }

                    let monomial_ok = !self.has_inconsistent_monomials();
                    let division_ok = !self.has_inconsistent_divisions();
                    if monomial_ok && division_ok {
                        if matches!(lra_result, TheoryResult::Unknown) {
                            return TheoryResult::Unknown;
                        }
                        return TheoryResult::Sat;
                    }

                    // Step 5a: Tentative sign cuts for variables with unknown
                    // assertion-based sign. Push scope, add sign cuts, then
                    // proceed to tentative patch. If patch succeeds, sign cuts
                    // are kept. If not, undo_tentative_patch() pops everything.
                    // Based on Z3 nla_basics_lemmas.cpp:sign_lemma().
                    if self.tentative_depth == 0 {
                        self.lra.push();
                        self.tentative_depth += 1;
                    }
                    let sign_cuts = self.inject_tentative_sign_cuts();
                    self.sign_cut_count += sign_cuts as u64;

                    // Re-check consistency after sign cuts tightened LRA
                    if sign_cuts > 0
                        && !self.has_inconsistent_monomials()
                        && !self.has_inconsistent_divisions()
                    {
                        return TheoryResult::Sat;
                    }

                    // Model patching (Z3 nla_core.cpp:patch_monomials):
                    // tentative push/pop with Gomory cuts (#4125 soundness fix)
                    if self.try_tentative_patch() {
                        self.patch_count += 1;
                        if !self.has_inconsistent_divisions() {
                            return TheoryResult::Sat;
                        }
                    }

                    let (mut added, used_tangent) = self.generate_refinement_lemmas();
                    if used_tangent {
                        used_tangent_approximation = true;
                    }
                    // Division refinement: tangent planes for denom * div = num (#6811).
                    // These are model-point approximations (same class as tangent planes).
                    let div_added = self.generate_division_refinement();
                    if div_added > 0 {
                        added += div_added;
                        used_tangent_approximation = true;
                    }
                    if added == 0 || iteration == MAX_ITERATIONS {
                        return TheoryResult::Unknown;
                    }
                    continue;
                }
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                    self.conflict_count += 1;
                    if iteration == 0 {
                        // Pre-refinement: pure linear UNSAT is a genuine UNSAT.
                        return lra_result.clone();
                    }
                    if used_tangent_approximation {
                        // Tangent hyperplanes were used — UNSAT may be spurious
                        // (#5959). Recheck: pop refinements, re-add only exact
                        // lemmas (even-power nonneg, McCormick, sign cuts, and
                        // division refinement at fresh model point), then iterate
                        // to propagate bounds.
                        self.undo_tentative_patch();
                        self.lra.push();
                        self.tentative_depth += 1;
                        self.inject_tentative_sign_cuts();
                        let mons: Vec<_> = self.monomials.values().cloned().collect();
                        for mon in &mons {
                            self.add_even_power_nonneg(mon);
                            self.add_mccormick_constraints(mon);
                        }
                        // Re-add division refinement at fresh model point (#6811)
                        self.generate_division_refinement();
                        let mut recheck_proved = false;
                        // Multi-pass: McCormick on nested monomials may need
                        // LRA to propagate inner bounds before outer McCormick
                        // becomes effective (e.g., a*(b*c) needs bounds on b*c).
                        for _ in 0..3 {
                            let recheck = self.lra.check();
                            match &recheck {
                                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                                    recheck_proved = true;
                                    break;
                                }
                                _ => {
                                    // Re-add McCormick and division refinement
                                    // with potentially updated bounds/model
                                    let mut added_any = false;
                                    for mon in &mons {
                                        if self.add_mccormick_constraints(mon) > 0 {
                                            added_any = true;
                                        }
                                    }
                                    if self.generate_division_refinement() > 0 {
                                        added_any = true;
                                    }
                                    if !added_any {
                                        break;
                                    }
                                }
                            }
                        }
                        self.undo_tentative_patch();
                        if recheck_proved {
                            let conflict: Vec<TheoryLit> = self
                                .asserted
                                .iter()
                                .map(|&(t, v)| TheoryLit { term: t, value: v })
                                .collect();
                            return TheoryResult::Unsat(conflict);
                        }
                        return TheoryResult::Unknown;
                    }
                    // Only exact lemmas (McCormick envelopes, even-power
                    // non-negativity, sign cuts) were used. UNSAT is genuine.
                    let conflict: Vec<TheoryLit> = self
                        .asserted
                        .iter()
                        .map(|&(t, v)| TheoryLit { term: t, value: v })
                        .collect();
                    return TheoryResult::Unsat(conflict);
                }
                _ => return lra_result.clone(),
            }
        }

        TheoryResult::Unknown
    }

    /// Check if any tracked monomial has an inconsistent value
    pub(crate) fn has_inconsistent_monomials(&self) -> bool {
        self.monomials
            .values()
            .any(|m| !self.check_monomial_consistency(m))
    }
}
