// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen equality detection for LIA.
//!
//! Detects algebraic equalities between integer variables from tight bounds
//! and linear equations. Used for Nelson-Oppen theory combination.

use super::*;

impl LiaSolver<'_> {
    /// Detect algebraic equalities from asserted and shared equalities.
    ///
    /// Returns a list of `(term, value, reasons)` for variables whose values
    /// were uniquely determined by the system of shared equalities (Gaussian
    /// elimination). These are NOT stored in LRA's bounds, so the caller
    /// must feed them into `propagate_tight_bound_equalities` alongside
    /// LRA-derived tight bounds.
    pub(super) fn detect_algebraic_equalities(
        &mut self,
        debug: bool,
    ) -> Vec<(TermId, BigRational, Vec<TheoryLit>)> {
        // Collect tight-bound values from LRA for potential substitution
        let mut tight_bound_values: HashMap<TermId, BigRational> = HashMap::new();
        let mut initial_tight: HashSet<TermId> = HashSet::new();
        for &var_term in &self.integer_vars {
            if let Some((Some(lower), Some(upper))) = self.lra.get_bounds(var_term) {
                if lower.value == upper.value && !lower.strict && !upper.strict {
                    tight_bound_values.insert(var_term, lower.value.to_big());
                    initial_tight.insert(var_term);
                }
            }
        }
        // Track derived tight bounds with their reasons (#3581)
        let mut derived_tight_bounds: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();

        // Collect all equations: both from asserted literals and shared equalities (#3581).
        //
        // Each equation is (var_coeffs, constant, initial_reasons) where:
        //   Σ(coeff_i * var_i) = constant
        // Shared equalities come from EUF via assert_shared_equality and represent
        // constraints like f(0) = x or f(1) = f(0) - x. Without including these,
        // variables introduced only via shared equalities are invisible to the
        // algebraic detection, breaking theory combination for chains like:
        //   f(0) = x, f(1) = f(0) - x → f(1) = 0
        let mut equations: Vec<(HashMap<TermId, BigInt>, BigInt, Vec<TheoryLit>)> = Vec::new();

        // Equations from assertion view (positive equalities from assert_literal)
        for &literal in &self.assertion_view().positive_equalities {
            if let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) {
                if name != "=" || args.len() != 2 {
                    continue;
                }
                // #7451: Skip non-arithmetic equalities. In QF_SLIA, LIA receives
                // String-sorted equalities like `substr(x,0,1) = sk_res` because
                // they contain `str.substr` (a string-int bridge op). The Gaussian
                // elimination treats opaque non-Int terms as variables with
                // coefficient 1, producing spurious cross-sort equalities
                // (e.g., x:String = 0:Int) that cause false UNSAT via EUF.
                let lhs_sort = self.terms.sort(args[0]);
                let rhs_sort = self.terms.sort(args[1]);
                if !matches!(lhs_sort, Sort::Int | Sort::Real)
                    || !matches!(rhs_sort, Sort::Int | Sort::Real)
                {
                    continue;
                }
                let (var_coeffs, constant) = self.parse_linear_expr_with_vars(args[0], args[1]);
                let initial_reason = TheoryLit::new(literal, true);
                equations.push((var_coeffs, constant, vec![initial_reason]));
            }
        }

        // Equations from shared equalities (from assert_shared_equality, #3581)
        for &(lhs, rhs, ref reasons) in &self.shared_equalities {
            // #7451: Sort-guard shared equalities too. EUF→LIA propagation is
            // already filtered in StringsLiaSolver::check(), but apply the same
            // guard here defensively.
            let lhs_sort = self.terms.sort(lhs);
            let rhs_sort = self.terms.sort(rhs);
            if !matches!(lhs_sort, Sort::Int | Sort::Real)
                || !matches!(rhs_sort, Sort::Int | Sort::Real)
            {
                continue;
            }
            let (var_coeffs, constant) = self.parse_linear_expr_with_vars(lhs, rhs);
            equations.push((var_coeffs, constant, reasons.clone()));
        }

        if equations.is_empty() {
            return vec![];
        }

        // Iterative Gaussian-style elimination (#3581):
        //
        // Process all equations, substituting known tight-bound values and
        // deriving new ones. When a shared equality like f(0) = x reduces to
        // "f(0) - x = 0", we first learn that f(0) and x are equal. If another
        // shared equality then reduces a single variable (e.g., f(1) = 0 after
        // substituting f(0) = x into f(1) = f(0) - x), we add a tight bound.
        // Repeat until no new equalities or bounds are found.
        //
        // We also maintain a map of variable-to-variable equalities so we can
        // substitute equal variables (not just tight-bound constants).
        let mut var_equalities: HashMap<TermId, TermId> = HashMap::new();
        // Reasons for variable-to-variable equalities (for proof tracking).
        let mut var_eq_reasons: HashMap<(TermId, TermId), Vec<TheoryLit>> = HashMap::new();

        let mut new_equalities: Vec<DiscoveredEquality> = Vec::new();
        let mut new_pairs: HashSet<(TermId, TermId)> = HashSet::new();

        // Fixed-point loop: keep processing until no new substitutions
        let mut changed = true;
        let max_rounds = 10; // Prevent infinite loops
        let mut round = 0;
        while changed && round < max_rounds {
            changed = false;
            round += 1;

            for (eq_idx, (ref var_coeffs, ref constant, ref initial_reasons)) in
                equations.iter().enumerate()
            {
                let mut coeffs = var_coeffs.clone();
                let mut adj_constant = BigRational::from(constant.clone());
                let mut reasons: Vec<TheoryLit> = initial_reasons.clone();
                let mut reason_seen: HashSet<TheoryLit> = reasons.iter().copied().collect();

                // Substitute known tight-bound values
                let mut sorted_bounds: Vec<_> = tight_bound_values.iter().collect();
                sorted_bounds.sort_unstable_by_key(|(tid, _)| tid.0);
                for (var, val) in sorted_bounds {
                    if let Some(coeff) = coeffs.remove(var) {
                        let coeff_rat = BigRational::from(coeff);
                        adj_constant -= &coeff_rat * val;

                        if debug {
                            safe_eprintln!(
                                "[LIA N-O Algebraic]   Substituted {} = {} (tight bound)",
                                var.0,
                                val,
                            );
                        }

                        // Add tight bound reasons
                        if let Some((Some(lower), Some(upper))) = self.lra.get_bounds(*var) {
                            if lower.value == upper.value && !lower.strict && !upper.strict {
                                for (reason, val) in
                                    lower.reasons.iter().zip(lower.reason_values.iter())
                                {
                                    let lit = TheoryLit::new(*reason, *val);
                                    if reason_seen.insert(lit) {
                                        reasons.push(lit);
                                    }
                                }
                                for (reason, val) in
                                    upper.reasons.iter().zip(upper.reason_values.iter())
                                {
                                    let lit = TheoryLit::new(*reason, *val);
                                    if reason_seen.insert(lit) {
                                        reasons.push(lit);
                                    }
                                }
                            }
                        }
                    }
                }

                // Substitute known variable equalities (#3581):
                // If we know var_a = var_b, replace var_a with var_b in the equation.
                let mut var_eq_entries: Vec<_> = var_equalities.iter().collect();
                var_eq_entries.sort_unstable_by_key(|(tid, _)| tid.0);
                for (&from_var, &to_var) in &var_eq_entries {
                    if let Some(coeff) = coeffs.remove(&from_var) {
                        *coeffs.entry(to_var).or_insert_with(|| BigInt::from(0)) += &coeff;
                        if coeffs.get(&to_var) == Some(&BigInt::from(0)) {
                            coeffs.remove(&to_var);
                        }
                        // Add reasons for this variable equality
                        let canon_pair = if from_var.0 < to_var.0 {
                            (from_var, to_var)
                        } else {
                            (to_var, from_var)
                        };
                        if let Some(eq_reasons) = var_eq_reasons.get(&canon_pair) {
                            for r in eq_reasons {
                                if reason_seen.insert(*r) {
                                    reasons.push(*r);
                                }
                            }
                        }
                    }
                }

                // Remove zero coefficients
                coeffs.retain(|_, c| !c.is_zero());

                // Convert adjusted constant to BigInt
                let final_constant = if adj_constant.denom().is_one() {
                    adj_constant.numer().clone()
                } else {
                    continue;
                };

                if debug {
                    safe_eprintln!(
                        "[LIA N-O Algebraic] Eq {}: {} vars, constant={} (round {})",
                        eq_idx,
                        coeffs.len(),
                        final_constant,
                        round,
                    );
                }

                // Case 1: Single variable with a fixed value → tight bound (#3581)
                // coeff * var = constant → var = constant / coeff
                if coeffs.len() == 1 {
                    let (&var, coeff) = coeffs.iter().next().unwrap();
                    if !coeff.is_zero() {
                        let value = BigRational::from(final_constant.clone())
                            / BigRational::from(coeff.clone());
                        if value.is_integer() && !tight_bound_values.contains_key(&var) {
                            if debug {
                                safe_eprintln!(
                                    "[LIA N-O Algebraic]   Derived tight bound: {} = {}",
                                    var.0,
                                    value,
                                );
                            }
                            tight_bound_values.insert(var, value.clone());
                            // Only track as "derived" if not already known from LRA
                            if !initial_tight.contains(&var) {
                                derived_tight_bounds.push((var, value, reasons.clone()));
                            }
                            changed = true;
                        }
                    }
                }

                // Case 2: Two variables with opposite unit coefficients → equality
                if coeffs.len() == 2 && final_constant.is_zero() {
                    let mut entries: Vec<_> = coeffs.iter().collect();
                    entries.sort_by_key(|(&var, _)| var);
                    let (var_a, coeff_a) = entries[0];
                    let (var_b, coeff_b) = entries[1];

                    if coeff_a == &-coeff_b.clone() && (coeff_a.abs() == BigInt::one()) {
                        let (lhs_var, rhs_var) = if coeff_a.is_positive() {
                            (*var_a, *var_b)
                        } else {
                            (*var_b, *var_a)
                        };

                        let pair = if lhs_var.0 < rhs_var.0 {
                            (lhs_var, rhs_var)
                        } else {
                            (rhs_var, lhs_var)
                        };

                        if !self.propagated_equality_pairs.contains(&pair) && new_pairs.insert(pair)
                        {
                            if debug {
                                safe_eprintln!(
                                    "[LIA N-O Algebraic] Propagating: {} = {} (reasons: {})",
                                    lhs_var.0,
                                    rhs_var.0,
                                    reasons.len()
                                );
                            }

                            new_equalities.push(DiscoveredEquality::new(
                                lhs_var,
                                rhs_var,
                                reasons.clone(),
                            ));
                        }

                        // Record variable equality for substitution in other equations
                        if !var_equalities.contains_key(&lhs_var) {
                            var_equalities.insert(lhs_var, rhs_var);
                            var_eq_reasons.insert(pair, reasons.clone());
                            changed = true;
                        }
                    }
                }
            }
        }

        for equality in new_equalities {
            let pair = if equality.lhs.0 < equality.rhs.0 {
                (equality.lhs, equality.rhs)
            } else {
                (equality.rhs, equality.lhs)
            };
            self.propagated_equality_pairs.insert(pair);
            self.pending_equalities.push(equality);
        }

        derived_tight_bounds
    }
}
