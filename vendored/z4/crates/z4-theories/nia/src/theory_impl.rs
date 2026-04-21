// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `NiaSolver`.
//!
//! Implements the DPLL(T) theory interface for the nonlinear integer arithmetic theory.

use super::*;

impl TheorySolver for NiaSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // Unwrap NOT: NOT(inner)=true means inner=false
        let (term, val) = match self.terms.get(literal) {
            TermData::Not(inner) => (*inner, !value),
            _ => (literal, value),
        };

        // Track assertion for conflict generation
        self.asserted.push((term, val));

        // Collect integer variables for branch-and-bound
        self.collect_integer_vars(term);

        // Scan for and register nonlinear terms
        self.collect_nonlinear_terms(term);

        // Extract and record sign constraints from comparisons with zero
        if let Some((subject, constraint)) = self.extract_sign_constraint(term, val) {
            if self.debug {
                safe_eprintln!(
                    "[NIA] Recording sign constraint: subject={:?}, constraint={:?}, from assertion {:?}={}",
                    subject, constraint, term, val
                );
            }
            self.record_sign_constraint(subject, constraint, term);
        }

        // Delegate to LIA solver
        self.lia.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        tracing::debug!(
            asserted = self.asserted.len(),
            monomials = self.monomials.len(),
            "NIA check"
        );

        if self.debug {
            safe_eprintln!(
                "[NIA] check() called with {} assertions",
                self.asserted.len()
            );
        }

        // Maximum number of tangent plane refinement iterations
        const MAX_TANGENT_ITERATIONS: usize = 10;

        for iteration in 0..=MAX_TANGENT_ITERATIONS {
            // Check linear constraints
            let lia_result = self.lia.check();

            if self.debug {
                safe_eprintln!(
                    "[NIA] Iteration {}: LIA check result: {:?}",
                    iteration,
                    lia_result
                );
            }

            match &lia_result {
                TheoryResult::Sat | TheoryResult::Unknown => {
                    // Check sign consistency first (definitive conflicts)
                    if let Some(conflict) = self.check_sign_consistency() {
                        if self.debug {
                            safe_eprintln!("[NIA] Sign inconsistency detected");
                        }
                        self.conflict_count += 1;
                        return TheoryResult::Unsat(conflict);
                    }

                    // Check monomial value consistency and add tangent constraints
                    // Sort by key for deterministic consistency checking (#3060)
                    let mut sorted_mons: Vec<_> = self.monomials.iter().collect();
                    sorted_mons.sort_by(|(a, _), (b, _)| a.cmp(b));
                    let mons: Vec<_> = sorted_mons.into_iter().map(|(_, v)| v.clone()).collect();
                    let mut any_inconsistent = false;

                    for mon in &mons {
                        if !self.check_monomial_consistency(mon) {
                            any_inconsistent = true;
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] Monomial {:?} aux={:?} inconsistent",
                                    mon.vars,
                                    mon.aux_var
                                );
                            }
                        }
                    }

                    if any_inconsistent {
                        // Add tangent plane constraints to cut off bad model
                        let constraints_added =
                            self.add_tangent_constraints_for_incorrect_monomials();

                        if self.debug {
                            safe_eprintln!(
                                "[NIA] Added {} tangent plane constraints, re-checking",
                                constraints_added
                            );
                        }

                        if constraints_added == 0 || iteration == MAX_TANGENT_ITERATIONS {
                            // No progress possible or reached iteration limit
                            // Return Unknown (incomplete), NOT Unsat - the formula might still be satisfiable
                            // Tangent plane method not making progress doesn't prove infeasibility
                            if self.debug {
                                safe_eprintln!(
                                    "[NIA] No tangent progress (added={}, iter={}), returning unknown",
                                    constraints_added, iteration
                                );
                            }

                            return TheoryResult::Unknown;
                        }

                        // Continue to next iteration to re-check with new constraints
                        continue;
                    }

                    // All monomials are consistent
                    // If LIA said Unknown but we found no conflict, propagate Unknown
                    if matches!(lia_result, TheoryResult::Unknown) {
                        tracing::debug!("NIA check: unknown (LIA unknown, monomials consistent)");
                        return TheoryResult::Unknown;
                    } else {
                        tracing::debug!("NIA check: sat");
                        return TheoryResult::Sat;
                    }
                }
                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                    // LIA says the linear relaxation is unsatisfiable.
                    // But this could be due to tangent plane constraints that are
                    // too restrictive - they cut off valid nonlinear solutions.
                    // We can only trust LIA's Unsat if no tangent planes were added.
                    if iteration == 0 {
                        // First iteration: no tangent planes, LIA conflict is genuine
                        self.conflict_count += 1;
                        return lia_result.clone();
                    } else {
                        // Tangent planes may have made the linear relaxation infeasible
                        // even though the nonlinear problem is satisfiable
                        if self.debug {
                            safe_eprintln!(
                                "[NIA] LIA returned Unsat after {} tangent iterations - returning unknown (possibly too tight)",
                                iteration
                            );
                        }
                        return TheoryResult::Unknown;
                    }
                }
                _ => return lia_result.clone(),
            }
        }

        // Should not reach here, but safety fallback
        TheoryResult::Unknown
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = self.lia.propagate();
        self.propagation_count += props.len() as u64;
        props
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let mut stats = vec![
            ("nia_checks", self.check_count),
            ("nia_conflicts", self.conflict_count),
            ("nia_propagations", self.propagation_count),
        ];
        stats.extend(self.lia.collect_statistics());
        stats
    }

    fn push(&mut self) {
        self.scopes.push(self.asserted.len());
        // Save sign constraint state so pop() can restore it.
        self.sign_constraint_snapshots.push((
            self.sign_constraints.clone(),
            self.var_sign_constraints.clone(),
        ));
        // #3735: Start a new monomial trail scope. Monomials registered during
        // this scope will be removed on pop().
        self.monomial_trail.push(Vec::new());
        self.lia.push();
    }

    fn pop(&mut self) {
        if let Some(mark) = self.scopes.pop() {
            self.asserted.truncate(mark);
        }
        // Restore sign constraints to pre-push state. Without this, stale
        // constraints from the popped scope leak into the outer scope and
        // can cause incorrect sign lemmas / wrong UNSAT.
        if let Some((sc, vsc)) = self.sign_constraint_snapshots.pop() {
            self.sign_constraints = sc;
            self.var_sign_constraints = vsc;
        }
        // #3735: Remove monomials registered during the popped scope.
        if let Some(trail) = self.monomial_trail.pop() {
            for (vars_key, aux_var) in trail {
                self.monomials.remove(&vars_key);
                self.aux_to_monomial.remove(&aux_var);
            }
        }
        self.lia.pop();
    }

    fn reset(&mut self) {
        self.asserted.clear();
        self.scopes.clear();
        self.monomials.clear();
        self.aux_to_monomial.clear();
        self.sign_constraints.clear();
        self.var_sign_constraints.clear();
        self.sign_constraint_snapshots.clear();
        self.monomial_trail.clear();
        self.lia.reset();
    }
}
