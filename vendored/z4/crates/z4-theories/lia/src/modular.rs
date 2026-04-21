// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Modular constraint checking for LIA.
//!
//! Modular arithmetic-based infeasibility detection for integer linear
//! arithmetic. When an equality has a variable with coefficient ±1 and
//! other coefficients share a common GCD > 1, we derive modular
//! constraints that restrict the valid integer values.
//!
//! Bound propagation through substitutions, GCD tightening, and modular
//! conflict detection are in `modular_bounds`.

#[cfg(not(kani))]
use hashbrown::HashSet;
use num_bigint::BigInt;
use num_traits::{One, Signed};
use tracing::info;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::term::{Symbol, TermData};
use z4_core::{TermId, TheoryLit};

use crate::{gcd_of_abs, positive_mod, LiaSolver};

impl LiaSolver<'_> {
    fn extend_conflict_with_bound_reasons(conflict: &mut Vec<TheoryLit>, bound: &z4_lra::Bound) {
        for (&reason, &value) in bound.reasons.iter().zip(&bound.reason_values) {
            if !reason.is_sentinel() {
                conflict.push(TheoryLit::new(reason, value));
            }
        }
    }

    fn dedup_conflict_literals(conflict: &mut Vec<TheoryLit>) {
        let mut seen: HashSet<(TermId, bool)> = HashSet::new();
        conflict.retain(|lit| seen.insert((lit.term, lit.value)));
    }

    /// Check modular constraints from single equalities against bounds.
    ///
    /// For an equality like `r = 2*x - 2*y`, if variable `r` has coefficient ±1
    /// and all other coefficients have GCD > 1, then `r ≡ constant (mod GCD)`.
    ///
    /// Combined with bounds on `r`, this can detect infeasibility.
    pub(crate) fn check_single_equality_modular_constraints(&self) -> Option<Vec<TheoryLit>> {
        let debug = self.debug_mod;

        for &literal in &self.assertion_view().positive_equalities {
            // Check if this is an equality
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            // Parse the equality with variable tracking
            let (var_coeffs, constant) = self.parse_linear_expr_with_vars(args[0], args[1]);

            if var_coeffs.is_empty() {
                continue;
            }

            // Find variables with coefficient ±1
            for (&var_term, var_coeff) in &var_coeffs {
                if var_coeff.abs() != BigInt::one() {
                    continue;
                }

                // Compute GCD of all other coefficients
                let other_gcd = gcd_of_abs(
                    var_coeffs
                        .iter()
                        .filter(|(&t, _)| t != var_term)
                        .map(|(_, c)| c.clone()),
                );

                // If other coefficients have GCD > 1, we have a modular constraint
                if other_gcd > BigInt::one() {
                    // var ≡ ±constant (mod other_gcd), sign depends on var_coeff
                    let adj_const = if var_coeff.is_negative() {
                        -&constant
                    } else {
                        constant.clone()
                    };
                    let residue = positive_mod(&adj_const, &other_gcd);

                    if debug {
                        safe_eprintln!(
                            "[MOD] From equality {:?}: {:?} ≡ {} (mod {})",
                            literal,
                            var_term,
                            residue,
                            other_gcd
                        );
                    }

                    // Check bounds on var_term
                    if let Some((lb_opt, ub_opt)) = self.lra.get_bounds(var_term) {
                        let effective_lb = lb_opt.as_ref().map(Self::effective_int_lower);
                        let effective_ub = ub_opt.as_ref().map(Self::effective_int_upper);

                        if let (Some(lb), Some(ub)) = (&effective_lb, &effective_ub) {
                            if debug {
                                safe_eprintln!(
                                    "[MOD] Variable {:?} bounds: [{}, {}]",
                                    var_term,
                                    lb,
                                    ub
                                );
                            }

                            // Find first valid integer >= lb satisfying modular constraint
                            let diff = &residue - lb;
                            let adjustment = positive_mod(&diff, &other_gcd);
                            let first_valid = lb + adjustment;

                            if &first_valid > ub {
                                info!(
                                    target: "z4::lia",
                                    reason = "single_equality_modular",
                                    "Modular constraint UNSAT detected"
                                );
                                if debug {
                                    safe_eprintln!(
                                        "[MOD] UNSAT: no integer in [{}, {}] satisfies ≡ {} (mod {})",
                                        lb, ub, residue, other_gcd
                                    );
                                }
                                let mut conflict = vec![TheoryLit::new(literal, true)];
                                if let Some(lb) = lb_opt.as_ref() {
                                    Self::extend_conflict_with_bound_reasons(&mut conflict, lb);
                                }
                                if let Some(ub) = ub_opt.as_ref() {
                                    Self::extend_conflict_with_bound_reasons(&mut conflict, ub);
                                }
                                Self::dedup_conflict_literals(&mut conflict);

                                // If we cannot explain the bound contribution, skip this UNSAT.
                                // Returning only the equality literal would be unsound.
                                if conflict.len() <= 1 {
                                    if debug {
                                        safe_eprintln!(
                                            "[MOD] Skipping UNSAT: missing bound reason literals"
                                        );
                                    }
                                    continue;
                                }
                                return Some(conflict);
                            }
                        }
                    }
                }
            }
        }

        None
    }

    /// Check if a disequality split conflicts with modular constraints.
    ///
    /// When a disequality split is requested for variable V with excluded value E,
    /// check if modular constraints from equalities make E the only valid integer
    /// in V's bounds. If so, the disequality V != E makes the formula UNSAT.
    pub(crate) fn check_disequality_vs_modular(
        &self,
        split: &z4_core::DisequalitySplitRequest,
    ) -> Option<Vec<TheoryLit>> {
        let debug = self.debug_mod;

        if debug {
            safe_eprintln!(
                "[MOD] check_disequality_vs_modular: var={:?}, excluded={}",
                split.variable,
                split.excluded_value
            );
            safe_eprintln!("[MOD] Asserted literals: {}", self.asserted.len());
        }

        let excluded_int = if split.excluded_value.is_integer() {
            split.excluded_value.numer().clone()
        } else {
            if debug {
                safe_eprintln!("[MOD] Excluded value is not integer, skipping");
            }
            return None; // Non-integer excluded value
        };

        // DISABLED (#5970 soundness): Diophantine substitution-based modular
        // unique-value check. This check detects when a variable has exactly one
        // valid integer value in its bounds (given modular constraints from
        // Diophantine substitutions) and that value is excluded by a disequality.
        //
        // Root cause of false-Unsafe on const_mod_3: when the mod encoding
        // introduces auxiliary variables (q, r for v = 2*q + r, 0 <= r < 2),
        // the Diophantine substitution cache may contain stale or context-
        // dependent entries. The modular residue computed from these entries
        // can be wrong in the presence of ITE branching, causing a false
        // conflict that makes the SAT solver believe a satisfiable formula
        // is UNSAT. Since BMC relies on correct SAT results, this propagates
        // as a false counterexample.
        //
        // The check at single_equalities (below) is kept because it uses
        // direct equality coefficients, not cached substitutions.
        //
        // TODO(#5970): Re-enable after fixing substitution cache invalidation
        // for incremental ITE/mod interactions.
        if debug {
            safe_eprintln!(
                "[MOD] dioph_cached_substitutions count: {} (check DISABLED for soundness)",
                self.dioph_cached_substitutions.len()
            );
        }

        // Also check single equalities for modular constraints
        for &literal in &self.assertion_view().positive_equalities {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            // Parse the equality
            let (var_coeffs, constant) = self.parse_linear_expr_with_vars(args[0], args[1]);

            if debug {
                safe_eprintln!(
                    "[MOD] Equality {:?}: {} variables, constant={}",
                    literal,
                    var_coeffs.len(),
                    constant
                );
                for (var, coeff) in &var_coeffs {
                    safe_eprintln!("[MOD]   {:?} -> coeff {}", var, coeff);
                }
            }

            // Check if split.variable appears with coefficient ±1
            let Some(var_coeff) = var_coeffs.get(&split.variable) else {
                if debug {
                    safe_eprintln!(
                        "[MOD]   split.variable {:?} not found in equality",
                        split.variable
                    );
                }
                continue;
            };
            if var_coeff.abs() != BigInt::one() {
                continue;
            }

            // Compute GCD of other coefficients
            let other_gcd = gcd_of_abs(
                var_coeffs
                    .iter()
                    .filter(|(&t, _)| t != split.variable)
                    .map(|(_, c)| c.clone()),
            );

            if debug {
                safe_eprintln!("[MOD]   var_coeff={}, other_gcd={}", var_coeff, other_gcd);
            }

            if other_gcd <= BigInt::one() {
                if debug {
                    safe_eprintln!("[MOD]   other_gcd <= 1, skipping");
                }
                continue;
            }

            // Compute residue for the modular constraint
            let adj_const = if var_coeff.is_negative() {
                -&constant
            } else {
                constant.clone()
            };
            let residue = positive_mod(&adj_const, &other_gcd);

            if debug {
                safe_eprintln!("[MOD]   residue={}", residue);
            }

            // Get bounds on split.variable
            if let Some((lb_opt, ub_opt)) = self.lra.get_bounds(split.variable) {
                if debug {
                    safe_eprintln!("[MOD]   bounds: lb={:?}, ub={:?}", lb_opt, ub_opt);
                }
                // For integers, strict bounds need adjustment:
                // lb > v means lb >= ceil(v) for strict, lb >= ceil(v) for non-strict
                // ub < v means ub <= floor(v)-1 for strict integer if v is integer
                let effective_lb = lb_opt.as_ref().map(Self::effective_int_lower);
                let effective_ub = ub_opt.as_ref().map(Self::effective_int_upper);

                if let (Some(lb), Some(ub)) = (&effective_lb, &effective_ub) {
                    if debug {
                        safe_eprintln!("[MOD]   effective bounds: [{}, {}]", lb, ub);
                    }

                    // Find first valid integer in [lb, ub] satisfying modular constraint
                    let diff = &residue - lb;
                    let adjustment = positive_mod(&diff, &other_gcd);
                    let first_valid = lb + adjustment;

                    if debug {
                        safe_eprintln!(
                            "[MOD]   first_valid={}, excluded_int={}",
                            first_valid,
                            excluded_int
                        );
                    }

                    // Check if first_valid is the only valid integer and equals excluded_int
                    if &first_valid <= ub {
                        let second_valid = &first_valid + &other_gcd;
                        if debug {
                            safe_eprintln!("[MOD]   second_valid={}, checking if second > ub ({}) and first == excluded",
                                      second_valid, ub);
                        }
                        if &second_valid > ub && first_valid == excluded_int {
                            // The excluded value is the ONLY valid integer!
                            if debug {
                                safe_eprintln!(
                                    "[MOD] Disequality excludes unique valid value {} for {:?}",
                                    excluded_int,
                                    split.variable
                                );
                                safe_eprintln!(
                                    "[MOD] Bounds [{}, {}], residue {} (mod {})",
                                    lb,
                                    ub,
                                    residue,
                                    other_gcd
                                );
                            }
                            // Return conflict with the equality and any disequality literals
                            let mut conflict = vec![TheoryLit::new(literal, true)];
                            // Add any asserted disequality for this variable
                            for &diseq_lit in &self.assertion_view().negative_equalities {
                                if let TermData::App(Symbol::Named(n), a) =
                                    self.terms.get(diseq_lit)
                                {
                                    if n == "=" && a.len() == 2 {
                                        // Check if this is the disequality for our variable
                                        let has_var = a.contains(&split.variable);
                                        if has_var {
                                            conflict.push(TheoryLit::new(diseq_lit, false));
                                        }
                                    }
                                }
                            }
                            return Some(conflict);
                        }
                    }
                }
            }
        }

        None
    }
}
