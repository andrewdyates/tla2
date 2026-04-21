// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    pub(crate) fn propagate_equalities_inner(&mut self) -> EqualityPropagationResult {
        let debug = self.debug_lra_nelson_oppen;

        // Collect variables with tight bounds (lower == upper, both non-strict)
        // These are variables whose value is uniquely determined.
        let mut tight_bound_vars: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();

        // Sort term_to_var entries by TermId for deterministic iteration (#2681).
        let mut sorted_term_vars: Vec<_> = self.term_to_var.iter().collect();
        sorted_term_vars.sort_by_key(|(&term, _)| term.0);

        for (&var_term, &var_id) in sorted_term_vars {
            if let Some(info) = self.vars.get(var_id as usize) {
                if let (Some(ref lower), Some(ref upper)) = (&info.lower, &info.upper) {
                    // Check if bounds are equal and non-strict (tight).
                    if lower.value == upper.value && !lower.strict && !upper.strict {
                        // Collect reasons from both bounds.
                        let mut reasons = Vec::new();
                        for (term, val) in lower.reason_pairs() {
                            if !term.is_sentinel() {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }
                        for (term, val) in upper.reason_pairs() {
                            if !term.is_sentinel() && !reasons.iter().any(|r| r.term == term) {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }

                        if debug {
                            safe_eprintln!(
                                "[LRA N-O] Tight bound: term {} = {} (reasons: {:?})",
                                var_term.0,
                                lower.value,
                                reasons
                            );
                        }

                        // Skip zero-reason tight bounds (#6282): these are variables
                        // whose value is only determined by simplex initialization
                        // (default model), not by asserted constraints. Propagating
                        // them as N-O equalities floods EUF with "all variables = 0"
                        // equalities that create spurious conflicts, preventing the
                        // N-O fixpoint from converging. Model-based equalities should
                        // go through discover_model_equality / NeedModelEquality
                        // instead, which lets the SAT solver explore both branches.
                        if reasons.is_empty() {
                            if self.debug_lra_nelson_oppen {
                                safe_eprintln!(
                                    "[LRA N-O] Skipping zero-reason tight bound: term {} = {}",
                                    var_term.0,
                                    lower.value,
                                );
                            }
                            continue;
                        }
                        if self.debug_lra_nelson_oppen {
                            safe_eprintln!(
                                "[LRA N-O] KEEPING tight bound: term {} = {} ({} reasons)",
                                var_term.0,
                                lower.value,
                                reasons.len(),
                            );
                        }
                        tight_bound_vars.push((var_term, lower.value_big(), reasons));
                    }
                }
            }
        }

        // Group variables by their value.
        let mut vars_by_value: HashMap<BigRational, Vec<(TermId, Vec<TheoryLit>)>> = HashMap::new();
        for (term, value, reasons) in tight_bound_vars {
            vars_by_value
                .entry(value)
                .or_default()
                .push((term, reasons));
        }

        // Sort groups by value for deterministic iteration (#2681).
        let mut sorted_groups: Vec<_> = vars_by_value.iter().collect();
        sorted_groups.sort_by(|(a, _), (b, _)| a.cmp(b));

        // For each group of variables with the same value, propagate equalities.
        for (_value, vars) in sorted_groups {
            if vars.len() < 2 {
                continue;
            }

            // Propagate pairwise equalities between all variables with same value.
            for i in 0..vars.len() {
                for j in (i + 1)..vars.len() {
                    let (lhs, lhs_reasons) = &vars[i];
                    let (rhs, rhs_reasons) = &vars[j];

                    // Canonicalize the pair to avoid duplicate propagations.
                    let pair = if lhs.0 < rhs.0 {
                        (*lhs, *rhs)
                    } else {
                        (*rhs, *lhs)
                    };

                    if !self.propagated_equality_pairs.contains(&pair) {
                        self.propagated_equality_pairs.insert(pair);

                        // Combine reasons from both variables.
                        // Use HashSet for O(1) dedup instead of Vec::contains().
                        let mut reason_seen: HashSet<TheoryLit> =
                            lhs_reasons.iter().copied().collect();
                        let mut combined_reasons = lhs_reasons.clone();
                        for r in rhs_reasons {
                            if reason_seen.insert(*r) {
                                combined_reasons.push(*r);
                            }
                        }

                        if debug {
                            safe_eprintln!(
                                "[LRA N-O] Propagating equality: term {} = term {} (reasons: {:?})",
                                lhs.0,
                                rhs.0,
                                combined_reasons
                            );
                        }

                        self.pending_equalities.push(DiscoveredEquality::new(
                            *lhs,
                            *rhs,
                            combined_reasons,
                        ));
                    }
                }
            }
        }

        // Return and clear pending equalities.
        let new_equalities = std::mem::take(&mut self.pending_equalities);
        if !new_equalities.is_empty() {
            info!(
                target: "z4::lra",
                propagated = new_equalities.len(),
                "Nelson-Oppen equality propagation"
            );
        }
        EqualityPropagationResult {
            equalities: new_equalities,
            conflict: None,
        }
    }

    pub(crate) fn assert_shared_equality_inner(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        // Receive equality from another theory (EUF→LRA direction in Nelson-Oppen).
        // Add the equality constraint: lhs = rhs, which means lhs - rhs = 0.
        //
        // This allows LRA to use EUF-discovered equalities in its arithmetic reasoning.
        // For example, if EUF tells us f(x) = y, we add the constraint f(x) - y = 0,
        // which affects bounds on both f(x) and y in the simplex tableau.

        let debug = self.debug_lra_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LRA N-O] Receiving shared equality: term {} = term {} (reason: {} lits)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // Parse both terms into linear expressions.
        // current_parsing_atom is None here, so parse_linear_expr won't mark
        // any atom as unsupported — shared equalities are cross-theory terms
        // handled by the other theory's semantics (#6167, #5511).
        debug_assert!(self.current_parsing_atom.is_none());
        let lhs_expr = self.parse_linear_expr(lhs);
        let rhs_expr = self.parse_linear_expr(rhs);

        // Build linear expression: lhs - rhs = 0.
        let mut diff_expr = lhs_expr;
        for &(var, ref coeff) in &rhs_expr.coeffs {
            diff_expr.add_term_rat(var, -coeff.clone());
        }
        diff_expr.constant = &diff_expr.constant - &rhs_expr.constant;

        // If expression is just a constant, check if it's zero.
        if diff_expr.is_constant() {
            if diff_expr.constant.is_zero() {
                if debug {
                    safe_eprintln!("[LRA N-O]   Equality is trivially true (constant 0)");
                }
            } else {
                // Constant is non-zero: lhs - rhs = c where c != 0, so lhs = rhs
                // is impossible. Record a trivial conflict using the reason literal
                // so DPLL(T) can backtrack. (#6157)
                if debug {
                    safe_eprintln!(
                        "[LRA N-O]   Equality is impossible! Constant {} != 0 — recording conflict",
                        diff_expr.constant
                    );
                }
                if self.trivial_conflict.is_none() {
                    // #8012: Store ALL reason literals so the blocking clause is
                    // complete. Previously only reason.first() was kept, producing
                    // overly-strong single-literal blocking clauses that eliminated
                    // valid SAT assignments when EUF propagated multi-literal
                    // equalities (e.g., f(a)=f(b) because a=b).
                    let conflict_lits: Vec<TheoryLit> = if reason.is_empty() {
                        vec![TheoryLit::new(lhs, true)]
                    } else {
                        reason.to_vec()
                    };
                    self.trivial_conflict = Some(conflict_lits);
                }
                self.dirty = true;
            }
            return;
        }

        // Assert the equality: diff_expr = 0, i.e., diff_expr <= 0 AND diff_expr >= 0.
        //
        // Pass ALL reason literals so conflict explanations are complete.
        // Previously only the first reason was tracked, causing false UNSAT
        // when cross-disequality split atoms were dropped (#4891).
        let reasons: Vec<(TermId, bool)> = if reason.is_empty() {
            vec![(lhs, true)]
        } else {
            reason.iter().map(|r| (r.term, r.value)).collect()
        };

        let zero = BigRational::zero();

        self.assert_bound_with_reasons(
            diff_expr.clone(),
            zero.clone(),
            BoundType::Upper,
            false,
            &reasons,
            None,
        );
        self.assert_bound_with_reasons(diff_expr, zero, BoundType::Lower, false, &reasons, None);

        // Mark as dirty to trigger re-check.
        self.dirty = true;
    }

    pub(crate) fn assert_shared_disequality_inner(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        // Receive disequality from another theory (EUF→LRA direction in Nelson-Oppen).
        // When EUF asserts (not (= (f x) y)), LRA needs to know lhs != rhs so it can
        // detect violations: if the LRA model satisfies lhs = rhs, a split or conflict
        // is generated (#5228).

        let debug = self.debug_lra_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LRA N-O] Receiving shared disequality: term {} != term {} (reason: {} lits)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // Parse both terms into linear expressions (same as assert_shared_equality).
        // current_parsing_atom is None here (#6167).
        debug_assert!(self.current_parsing_atom.is_none());
        let lhs_expr = self.parse_linear_expr(lhs);
        let rhs_expr = self.parse_linear_expr(rhs);

        // Build linear expression: lhs - rhs.
        let mut diff_expr = lhs_expr;
        for &(var, ref coeff) in &rhs_expr.coeffs {
            diff_expr.add_term_rat(var, -coeff.clone());
        }
        diff_expr.constant = &diff_expr.constant - &rhs_expr.constant;

        // If expression is just a constant, check if it's zero.
        if diff_expr.is_constant() {
            if diff_expr.constant.is_zero() {
                // lhs = rhs is forced but we have lhs != rhs — immediate conflict.
                // Record the conflict so DPLL(T) can backtrack. (#6157)
                if debug {
                    safe_eprintln!(
                        "[LRA N-O]   Shared disequality is trivially violated (constant 0 != 0) — recording conflict"
                    );
                }
                if self.trivial_conflict.is_none() {
                    // #8012: Store ALL reason literals (same fix as equality path).
                    let conflict_lits: Vec<TheoryLit> = if reason.is_empty() {
                        vec![TheoryLit::new(lhs, true)]
                    } else {
                        reason.to_vec()
                    };
                    self.trivial_conflict = Some(conflict_lits);
                }
                self.dirty = true;
            }
            // Non-zero constant: disequality is trivially satisfied, nothing to do.
            return;
        }

        // #6131: Extract the original equality term from the reason literals.
        // The first reason literal with value=false is the negated equality atom
        // (e.g., TheoryLit { term: (= a b), value: false }). This term is passed
        // to DisequalitySplitRequest so split clauses become conditional:
        // `(= a b) OR (x < c) OR (x > c)` instead of the unconditional
        // `(x < c) OR (x > c)` which survives backtracking and can cause false UNSAT.
        let eq_term = reason.iter().find(|lit| !lit.value).map(|lit| lit.term);

        // (#6131) Shared disequalities from EUF should always have a negated
        // equality in their reason. If not, the split will be unconditional
        // (fallback at apply_disequality_split) which can cause false UNSAT.
        debug_assert!(
            eq_term.is_some(),
            "BUG: shared disequality has no negated equality in reason ({} lits, all true)",
            reason.len()
        );

        // Store in the shared disequality trail for post-simplex checking.
        self.shared_disequality_trail
            .push((diff_expr, reason.to_vec(), eq_term));

        // Mark as dirty to trigger re-check.
        self.dirty = true;
    }
}
