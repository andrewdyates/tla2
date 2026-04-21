// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TheorySolver trait implementation for LIA.

use super::*;

impl TheorySolver for LiaSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        // Delegate to inner LRA solver so atom_index is populated.
        // Without this, LRA bound propagation cannot deduce implied atoms
        // for LIA problems (#4919).
        self.lra.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        debug_assert!(
            (literal.0 as usize) < self.terms.len(),
            "BUG: LIA assert_literal: term {} out of range (term store len={})",
            literal.0,
            self.terms.len()
        );

        // Any new assertion invalidates cached direct-enumeration models.
        self.direct_enum_witness = None;

        // Unwrap NOT: NOT(inner)=true means inner=false
        let (term, val) = unwrap_not(self.terms, literal, value);

        // Collect integer variables from this literal
        self.collect_integer_vars(term);

        // Track assertion for conflict generation
        self.asserted.push((term, val));

        // Forward to LRA solver (which also handles NOT unwrapping)
        self.lra.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        tracing::debug!(
            asserted = self.asserted.len(),
            integer_vars = self.integer_vars.len(),
            gomory_iter = self.gomory_iterations,
            hnf_iter = self.hnf_iterations,
            "LIA check"
        );
        let result = self.check_inner();
        if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            self.conflict_count += 1;
        }
        result
    }

    fn check_during_propagate(&mut self) -> TheoryResult {
        self.check_count += 1;
        tracing::debug!(
            asserted = self.asserted.len(),
            integer_vars = self.integer_vars.len(),
            "LIA check_during_propagate"
        );
        let result = self.check_during_propagate_inner();
        if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            self.conflict_count += 1;
        }
        result
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = self.lra.propagate();
        self.propagation_count += props.len() as u64;
        props
    }

    fn push(&mut self) {
        assert_eq!(
            self.scopes.len(),
            self.cut_scopes.len(),
            "BUG: LIA push: scope stack ({}) and cut_scope stack ({}) out of sync",
            self.scopes.len(),
            self.cut_scopes.len()
        );
        self.scopes.push(self.asserted.len());
        self.cut_scopes.push(self.learned_cuts.len());
        // Save cut-related state so pop() restores the outer scope's
        // iteration counters and seen-cut set (#3685).
        self.cut_state_scopes.push(CutScopeState {
            gomory_iterations: self.gomory_iterations,
            hnf_iterations: self.hnf_iterations,
            seen_hnf_cuts: self.seen_hnf_cuts.clone(),
            shared_eq_mark: self.shared_equalities.len(),
        });
        self.lra.push();
        self.direct_enum_witness = None;
    }

    fn pop(&mut self) {
        if let Some(mark) = self.scopes.pop() {
            debug_assert!(
                mark <= self.asserted.len(),
                "BUG: LIA pop: scope mark {} exceeds asserted length {}",
                mark,
                self.asserted.len()
            );
            self.asserted.truncate(mark);
            self.lra.pop();
            self.direct_enum_witness = None;
            let cut_mark = self.cut_scopes.pop().unwrap_or(0);
            self.learned_cuts.truncate(cut_mark);
            // Restore cut state from the outer scope (#3685).
            // Previously these were hard-reset to 0/empty, losing the outer
            // scope's iteration progress and seen-cut deduplication set.
            let saved = self.cut_state_scopes.pop().unwrap_or_default();
            self.gomory_iterations = saved.gomory_iterations;
            self.hnf_iterations = saved.hnf_iterations;
            self.seen_hnf_cuts = saved.seen_hnf_cuts;
            self.shared_equalities.truncate(saved.shared_eq_mark);
            // Clear Dioph caches on pop: equalities may be removed by backtracking,
            // making cached substitutions and reasons stale. The equality_key guard
            // in check() detects most staleness, but there is a window where
            // propagate_bounds_through_substitutions() could use stale data before
            // the key is re-validated. (#3736)
            self.dioph_equality_key.clear();
            self.dioph_safe_dependent_vars.clear();
            self.dioph_cached_substitutions.clear();
            self.dioph_cached_reasons.clear();

            // AUDIT FIX Clear propagated_equality_pairs on pop().
            // Without this, after backtracking, equalities that were previously propagated
            // won't be re-propagated even if they get re-established. This could cause
            // the N-O combination to miss conflicts in alternate search branches.
            self.propagated_equality_pairs.clear();
            self.pending_equalities.clear();
        }
    }

    fn reset(&mut self) {
        self.lra.reset();
        self.integer_vars.clear();
        self.int_constant_terms.clear();
        self.asserted.clear();
        self.scopes.clear();
        self.cut_scopes.clear();
        self.cut_state_scopes.clear();
        self.direct_enum_witness = None;
        self.gomory_iterations = 0;
        self.hnf_iterations = 0;
        self.seen_hnf_cuts.clear();
        self.learned_cuts.clear();
        self.dioph_equality_key.clear();
        self.dioph_safe_dependent_vars.clear();
        self.dioph_cached_substitutions.clear();
        self.dioph_cached_reasons.clear();
        self.pending_equalities.clear();
        self.propagated_equality_pairs.clear();
        self.shared_equalities.clear();
    }

    fn soft_reset(&mut self) {
        // Use clear_assertions which preserves learned HNF cuts
        self.clear_assertions();
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        let debug = self.debug_lia_nelson_oppen;

        // Phase 1: Detect algebraic equalities from equality assertions and
        // shared equalities (#3581). This also performs Gaussian elimination
        // on the shared equality system to derive tight bounds for variables
        // whose values are uniquely determined (e.g., f(1) = 0 from
        // f(0) = x, f(1) = f(0) - x).
        let derived_tight_bounds = self.detect_algebraic_equalities(debug);

        // Phase 2: Collect variables with tight bounds (lower == upper)
        // These are variables whose value is uniquely determined
        let mut tight_bound_vars: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();

        for &var_term in &self.integer_vars {
            if let Some((Some(lower), Some(upper))) = self.lra.get_bounds(var_term) {
                // Check if bounds are equal (tight)
                if lower.value == upper.value && !lower.strict && !upper.strict {
                    // Collect reasons from both bounds
                    let mut reasons = Vec::new();
                    for (reason, val) in lower.reasons.iter().zip(lower.reason_values.iter()) {
                        reasons.push(TheoryLit::new(*reason, *val));
                    }
                    for (reason, val) in upper.reasons.iter().zip(upper.reason_values.iter()) {
                        if !reasons.iter().any(|r| r.term == *reason) {
                            reasons.push(TheoryLit::new(*reason, *val));
                        }
                    }

                    if debug {
                        safe_eprintln!(
                            "[LIA N-O] Tight bound: term {} = {} (reasons: {:?})",
                            var_term.0,
                            lower.value,
                            reasons
                        );
                    }

                    tight_bound_vars.push((var_term, lower.value.to_big(), reasons));
                }
            }
        }

        // Include derived tight bounds from Gaussian elimination (#3581).
        // These are variables whose values were determined by the shared
        // equality system but are not stored as LRA bounds.
        for (var, value, reasons) in derived_tight_bounds {
            // Avoid duplicates: only add if not already in LRA tight bounds
            if !tight_bound_vars.iter().any(|(t, _, _)| *t == var) {
                if debug {
                    safe_eprintln!(
                        "[LIA N-O] Derived tight bound: term {} = {} (reasons: {:?})",
                        var.0,
                        value,
                        reasons
                    );
                }
                tight_bound_vars.push((var, value, reasons));
            }
        }

        // Include integer constant terms with trivial tight bounds (#3581).
        // Constants like 0, 1, 5 have fixed values by definition. Without
        // including them, propagate_tight_bound_equalities cannot pair a
        // derived tight bound (e.g., f(1) = 0) with the constant 0 term,
        // because grouping by value requires both sides to be present.
        for (int_val, &const_term) in &self.int_constant_terms {
            let value = BigRational::from(int_val.clone());
            if !tight_bound_vars.iter().any(|(t, _, _)| *t == const_term) {
                tight_bound_vars.push((const_term, value, Vec::new()));
            }
        }

        let mut equalities =
            propagate_tight_bound_equalities(tight_bound_vars, &mut self.propagated_equality_pairs);

        // Prepend any equalities from Phase 1 (algebraic detection)
        let mut algebraic = std::mem::take(&mut self.pending_equalities);
        algebraic.append(&mut equalities);

        EqualityPropagationResult {
            equalities: algebraic,
            conflict: None,
        }
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // Receive equality from another theory (EUF→LIA direction in Nelson-Oppen).
        // Add the equality constraint: lhs = rhs, which means lhs - rhs = 0.
        //
        // This allows LIA to use EUF-discovered equalities in its arithmetic reasoning.
        // For example, if EUF tells us (f 5) = -1, we add the constraint (f 5) - (-1) = 0,
        // which affects bounds on (f 5) in the simplex tableau.

        debug_assert!(
            (lhs.0 as usize) < self.terms.len(),
            "BUG: LIA assert_shared_equality: lhs term {} out of range (term store len={})",
            lhs.0,
            self.terms.len()
        );
        debug_assert!(
            (rhs.0 as usize) < self.terms.len(),
            "BUG: LIA assert_shared_equality: rhs term {} out of range (term store len={})",
            rhs.0,
            self.terms.len()
        );

        // #7451: Reject equalities involving non-arithmetic terms. In SLIA
        // problems, EUF can propagate String-sorted equalities (e.g., x = "hello")
        // to LIA. Without this guard, term_to_linear_coeffs treats String terms
        // as opaque LRA variables with value 0, causing propagate_equalities to
        // produce spurious cross-sort equalities (String = Int) → false UNSAT.
        let lhs_sort = self.terms.sort(lhs);
        let rhs_sort = self.terms.sort(rhs);
        if !matches!(lhs_sort, Sort::Int | Sort::Real)
            || !matches!(rhs_sort, Sort::Int | Sort::Real)
        {
            return;
        }

        // Register integer variables from both sides of the shared equality (#3581).
        // Without this, variables introduced only via shared equalities (e.g., UF
        // applications like f(0), f(1) and plain variables like x forwarded from
        // is_uf_int_equality) are not tracked in integer_vars. This means
        // propagate_equalities() never discovers their tight bounds, breaking
        // Nelson-Oppen equality propagation for chains like:
        //   f(0) = x, f(1) = f(0) - x → f(1) = 0
        self.collect_integer_vars(lhs);
        self.collect_integer_vars(rhs);

        // Store the shared equality for algebraic detection in propagate_equalities (#3581).
        self.shared_equalities.push((lhs, rhs, reason.to_vec()));

        // Invalidate the assertion view cache so that `detect_algebraic_equalities`
        // picks up the newly added shared equality.
        self.invalidate_assertion_view();

        let debug = self.debug_lia_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LIA N-O] Receiving shared equality: term {} = term {} (reason: {:?})",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // Parse both terms into linear expressions
        let lhs_coeffs = self.term_to_linear_coeffs(lhs);
        let rhs_coeffs = self.term_to_linear_coeffs(rhs);

        // Build linear expression: lhs - rhs = 0
        // coeffs: var_term -> coefficient
        let mut combined_coeffs: HashMap<TermId, BigRational> = HashMap::new();
        let mut constant = BigRational::zero();

        // Add lhs coefficients (positive)
        for (var, coeff) in lhs_coeffs.vars {
            *combined_coeffs.entry(var).or_insert_with(BigRational::zero) += &coeff;
        }
        constant += &lhs_coeffs.constant;

        // Subtract rhs coefficients
        for (var, coeff) in rhs_coeffs.vars {
            *combined_coeffs.entry(var).or_insert_with(BigRational::zero) -= &coeff;
        }
        constant -= &rhs_coeffs.constant;

        // Remove zero coefficients
        combined_coeffs.retain(|_, c| !c.is_zero());

        // If expression is just a constant, check if it's zero
        if combined_coeffs.is_empty() {
            if constant.is_zero() {
                // lhs = rhs is trivially true, no constraint needed
                if debug {
                    safe_eprintln!("[LIA N-O]   Equality is trivially true (constant 0)");
                }
            } else {
                // lhs = rhs is impossible (constant != 0)
                // This should be caught elsewhere, but log for debugging
                if debug {
                    safe_eprintln!(
                        "[LIA N-O]   Equality is impossible! Constant {} != 0",
                        constant
                    );
                }
            }
            return;
        }

        // Assert the equality constraint: Σ(coeff_i * var_i) + constant = 0
        // This means: Σ(coeff_i * var_i) = -constant
        // We add dual bounds: expr <= 0 AND expr >= 0
        //
        // Pass ALL reason literals so conflict explanations are complete.
        // Previously only the first reason was tracked, causing false UNSAT
        // when cross-disequality split atoms were dropped (#4891).
        let reasons: Vec<(TermId, bool)> = if reason.is_empty() {
            vec![(lhs, true)]
        } else {
            reason.iter().map(|r| (r.term, r.value)).collect()
        };

        // Use the underlying LRA solver to add bounds
        // The LRA solver tracks variables by TermId, so we need to convert our expression
        // Sort by TermId for deterministic registration order (#2681)
        let mut sorted_coeffs: Vec<_> = combined_coeffs.iter().collect();
        sorted_coeffs.sort_by_key(|(&var, _)| var);
        for (&var, _coeff) in &sorted_coeffs {
            // Ensure the variable is registered with LRA
            self.lra.ensure_var_registered(var);
        }

        // Add the constraint expr = 0 (where expr = Σ(coeff * var) + constant)
        // This is equivalent to: -constant <= Σ(coeff * var) <= -constant
        let neg_constant = -&constant;
        self.lra
            .assert_linear_equality_with_reasons(&combined_coeffs, &neg_constant, &reasons);

        if debug {
            safe_eprintln!(
                "[LIA N-O]   Added constraint: {} vars, constant={}",
                combined_coeffs.len(),
                constant
            );
        }
    }

    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // Receive disequality from another theory (EUF→LIA direction in Nelson-Oppen).
        // When EUF asserts (not (= (g x) 5)), LIA needs to know lhs != rhs so it can
        // detect violations: if the LIA model satisfies lhs = rhs, a split or conflict
        // is generated (#5228).

        let debug = self.debug_lia_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LIA N-O] Receiving shared disequality: term {} != term {} (reason: {} lits)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // Register integer variables from both sides for Nelson-Oppen tracking (#3581).
        self.collect_integer_vars(lhs);
        self.collect_integer_vars(rhs);

        // Invalidate the assertion view cache so modular arithmetic can see new terms.
        self.invalidate_assertion_view();

        // Forward to the inner LRA solver's shared disequality trail.
        // LRA's disequality checking infrastructure (post-simplex) will evaluate
        // lhs - rhs in the model and generate a split or conflict if lhs = rhs.
        self.lra.assert_shared_disequality(lhs, rhs, reason);
    }

    fn supports_theory_aware_branching(&self) -> bool {
        // LIA is an arithmetic theory — theory atoms should be decided before
        // Tseitin encoding variables. Delegate to inner LRA solver.
        self.lra.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        // Delegate to inner LRA solver for LP-model-consistent polarity.
        // Without this forwarding, UfLia/AufLia adapters get None (default)
        // for all atoms, causing polarity=true fallback instead of
        // model-consistent polarity (P1:122 finding 1).
        self.lra.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        // Forward to inner LRA solver to sort atoms by bound value for
        // O(log n) nearest-neighbor lookup in bound axiom generation.
        self.lra.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        // Forward to inner LRA solver for bound ordering axiom pairs.
        self.lra.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.lra.generate_incremental_bound_axioms(atom)
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("lia_checks", self.check_count),
            ("lia_conflicts", self.conflict_count),
            ("lia_propagations", self.propagation_count),
        ]
    }
}
