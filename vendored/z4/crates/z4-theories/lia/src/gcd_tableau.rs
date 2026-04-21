// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tableau-level GCD infeasibility checks for LIA.
//!
//! Contains `gcd_test_tableau` (extended GCD on fractional integer rows),
//! `ext_gcd_test` (interval arithmetic feasibility), and
//! `collect_tableau_gcd_conflict_literals` (conflict reason collection).
//!
//! Extracted from gcd.rs as part of #5970 code-health splits.

use super::*;
use tracing::{debug, info};

impl LiaSolver<'_> {
    /// Extended GCD test on tableau rows with fractional integer basic variables.
    ///
    /// For each row where the basic variable is an integer with a non-integer
    /// value in the LP relaxation, we check:
    ///
    /// 1. Basic test: GCD of non-fixed coefficients must divide the constant
    /// 2. Extended test: If the variable with smallest coefficient is bounded,
    ///    use interval arithmetic to check if any integer solution exists
    ///
    /// This is ported from Z3's `theory_arith_int.h::gcd_test()` and `ext_gcd_test()`.
    ///
    /// Reference: Z3 src/smt/theory_arith_int.h:693-858
    pub(super) fn gcd_test_tableau(&self) -> Option<TheoryConflict> {
        let debug = self.debug_gcd_tab;

        let rows = self.lra.get_fractional_int_rows(&self.integer_vars);
        let row_count = rows.len();
        let mut basic_checks = 0usize;
        let mut extended_checks = 0usize;

        if debug && !rows.is_empty() {
            safe_eprintln!(
                "[GCD_TAB] Testing {} rows with fractional integer basic vars",
                rows.len()
            );
        }

        for row in rows {
            basic_checks += 1;
            // Compute LCM of denominators to work with integer coefficients
            let mut lcm_den = BigInt::one();
            for (_, coeff) in &row.coeffs {
                lcm_den = lcm_den.lcm(&coeff.denom().clone());
            }
            lcm_den = lcm_den.lcm(&row.constant.denom().clone());
            debug_assert!(
                lcm_den.is_positive(),
                "BUG: tableau denominator LCM is non-positive {lcm_den}"
            );

            // Accumulate constant from fixed variables and GCD of non-fixed coefficients
            let mut consts = BigInt::zero();
            let mut gcds = BigInt::zero();
            let mut least_coeff = BigInt::zero();
            let mut least_coeff_is_bounded = false;

            // The tableau row is: basic_var = Σ(coeff_i * nonbasic_i) + constant.
            // After scaling by lcm_den, the basic variable has implicit coefficient
            // lcm_den. If the basic variable is a non-fixed integer, its coefficient
            // must participate in the GCD computation. Without this, the GCD test
            // over-approximates infeasibility (e.g., 3x + 5y = 7 with GCD(5)=5
            // instead of GCD(3,5)=1). Fix for #5648.
            if !row.is_fixed {
                let basic_is_int = row
                    .basic_term
                    .is_some_and(|t| self.integer_vars.contains(&t));
                if basic_is_int {
                    Self::update_gcd_and_least_coeff(
                        &lcm_den,
                        row.is_bounded,
                        &mut gcds,
                        &mut least_coeff,
                        &mut least_coeff_is_bounded,
                    );
                }
            }

            for (var, coeff) in &row.coeffs {
                // Scale coefficient by LCM
                let scaled = (coeff * &lcm_den).to_integer();
                let abs_scaled = scaled.abs();

                // Check if this variable is fixed
                if let Some((lb, ub)) = self.lra.get_var_bounds(*var) {
                    let is_fixed = lb.is_some() && ub.is_some() && lb == ub;
                    let is_bounded = lb.is_some() && ub.is_some();
                    let is_int = self.lra.is_int_var(*var, &self.integer_vars);

                    if is_fixed {
                        // Fixed variable: accumulate its contribution to constant
                        if let Some(ref bound_val) = lb {
                            let contrib = &scaled * bound_val.numer() / bound_val.denom();
                            consts += contrib;
                        }
                    } else if !is_int {
                        // Real (non-integer) variable in the row - skip this row
                        // (GCD test only applies to pure integer rows)
                        gcds = BigInt::zero();
                        break;
                    } else {
                        // Non-fixed integer variable: contribute to GCD
                        Self::update_gcd_and_least_coeff(
                            &abs_scaled,
                            is_bounded,
                            &mut gcds,
                            &mut least_coeff,
                            &mut least_coeff_is_bounded,
                        );
                    }
                }
            }

            if gcds.is_zero() {
                // All variables are fixed or row has reals - skip
                continue;
            }

            // Scale the constant term and add fixed variable contributions
            // The row equation is: basic = Σ(coeff * var) + constant
            // Fixed vars contribute: Σ(scaled_coeff * value) = consts
            // So the "effective constant" is: scaled_constant + consts
            let scaled_const = (&row.constant * &lcm_den).to_integer() + &consts;

            // Basic GCD test: check if GCD divides constant
            let remainder = &scaled_const % &gcds;
            if !remainder.is_zero() {
                if debug {
                    safe_eprintln!(
                        "[GCD_TAB] UNSAT: Row basic_var={} GCD={} does not divide const={} (remainder={})",
                        row.basic_var, gcds, scaled_const, remainder
                    );
                }
                info!(
                    target: "z4::lia",
                    row_count,
                    basic_checks,
                    extended_checks,
                    basic_var = row.basic_var,
                    gcd = %gcds,
                    scaled_const = %scaled_const,
                    remainder = %remainder,
                    "LIA tableau GCD basic conflict"
                );
                let literals = self.collect_tableau_gcd_conflict_literals(&row);
                return Some(TheoryConflict::new(literals));
            }

            // Extended GCD test: if variable with smallest coefficient is bounded,
            // check if any integer solution exists using interval arithmetic
            if least_coeff_is_bounded && !least_coeff.is_one() {
                extended_checks += 1;
                if let Some(conflict) = self.ext_gcd_test(&row, &least_coeff, &lcm_den, &consts) {
                    if debug {
                        safe_eprintln!(
                            "[GCD_TAB] Extended GCD test detected UNSAT for row basic_var={}",
                            row.basic_var
                        );
                    }
                    info!(
                        target: "z4::lia",
                        row_count,
                        basic_checks,
                        extended_checks,
                        basic_var = row.basic_var,
                        least_coeff = %least_coeff,
                        "LIA tableau GCD extended conflict"
                    );
                    return Some(conflict);
                }
            }
        }

        debug!(
            target: "z4::lia",
            row_count,
            basic_checks,
            extended_checks,
            "LIA tableau GCD checks completed without conflict"
        );

        None
    }

    /// Extended GCD test auxiliary method.
    ///
    /// When the variable with the smallest coefficient in a row is bounded,
    /// we can use interval arithmetic to check if any integer solution exists.
    ///
    /// For variables with |coeff| == least_coeff, accumulate their bounds into [l, u].
    /// For other variables, compute their GCD.
    /// Check if ceil(l/gcds) <= floor(u/gcds).
    fn ext_gcd_test(
        &self,
        row: &GcdRowInfo,
        least_coeff: &BigInt,
        lcm_den: &BigInt,
        fixed_consts: &BigInt,
    ) -> Option<TheoryConflict> {
        let mut gcds = BigInt::zero();
        // Use rationals for precise interval computation (Z3 does the same)
        let mut l_rat = BigRational::from_integer(fixed_consts.clone());
        let mut u_rat = BigRational::from_integer(fixed_consts.clone());

        // Include basic variable's implicit coefficient (lcm_den) if non-fixed.
        // Same reasoning as in gcd_test_tableau: the basic variable participates
        // in the equation and its coefficient must be in the GCD. Fix for #5648.
        if !row.is_fixed {
            let basic_is_int = row
                .basic_term
                .is_some_and(|t| self.integer_vars.contains(&t));
            if basic_is_int {
                if lcm_den == least_coeff {
                    // Basic variable has the least coefficient — use its bounds
                    if let (Some(ref lb_val), Some(ref ub_val)) =
                        (&row.lower_bound, &row.upper_bound)
                    {
                        let scaled_rat = BigRational::from_integer(lcm_den.clone());
                        l_rat += &scaled_rat * lb_val;
                        u_rat += &scaled_rat * ub_val;
                    }
                } else {
                    // Basic variable contributes to GCD
                    if gcds.is_zero() {
                        gcds = lcm_den.clone();
                    } else {
                        gcds = gcds.gcd(lcm_den);
                    }
                }
            }
        }

        for (var, coeff) in &row.coeffs {
            if let Some((lb, ub)) = self.lra.get_var_bounds(*var) {
                let is_fixed = lb.is_some() && ub.is_some() && lb == ub;
                if is_fixed {
                    continue; // Already handled in fixed_consts
                }

                let scaled_rat = coeff * BigRational::from_integer(lcm_den.clone());
                let scaled = scaled_rat.to_integer();
                let abs_scaled = scaled.abs();

                if &abs_scaled == least_coeff {
                    // Variable with smallest coefficient - use its EXACT bounds
                    // Don't truncate to integer - keep full precision until the end
                    let (Some(lb_val), Some(ub_val)) = (lb, ub) else {
                        continue; // Need both bounds for extended test
                    };

                    if scaled.is_positive() {
                        l_rat += &scaled_rat * &lb_val;
                        u_rat += &scaled_rat * &ub_val;
                    } else {
                        l_rat += &scaled_rat * &ub_val;
                        u_rat += &scaled_rat * &lb_val;
                    }
                } else {
                    // Other non-fixed variables contribute to GCD
                    if gcds.is_zero() {
                        gcds = abs_scaled;
                    } else {
                        gcds = gcds.gcd(&abs_scaled);
                    }
                }
            }
        }

        if gcds.is_zero() {
            return None;
        }
        debug_assert!(
            gcds.is_positive(),
            "BUG: ext_gcd_test produced non-positive gcd {gcds}"
        );

        // Check if ceil(l/gcds) > floor(u/gcds) => UNSAT
        // Now apply ceil/floor AFTER the full interval computation
        let gcds_rat = BigRational::from_integer(gcds);
        let l1 = Self::ceil_rational(&(&l_rat / &gcds_rat));
        let u1 = Self::floor_rational(&(&u_rat / &gcds_rat));

        if u1 < l1 {
            // No integer solution exists in the interval
            let literals = self.collect_tableau_gcd_conflict_literals(row);
            return Some(TheoryConflict::new(literals));
        }

        None
    }

    /// Collect conflict literals for tableau-based GCD conflicts.
    ///
    /// We prefer bound reasons from terms that participate in the offending row.
    /// If those reasons are unavailable, fall back to all asserted literals to
    /// preserve soundness.
    pub(super) fn collect_tableau_gcd_conflict_literals(&self, row: &GcdRowInfo) -> Vec<TheoryLit> {
        let mut participant_terms = Vec::new();
        let mut seen_terms = HashSet::new();
        if let Some(term) = row.basic_term {
            seen_terms.insert(term);
            participant_terms.push(term);
        }
        for (var, _) in &row.coeffs {
            if let Some(term) = self.lra.var_term_id(*var) {
                if seen_terms.insert(term) {
                    participant_terms.push(term);
                }
            }
        }

        let mut seen = HashSet::new();
        let mut literals = Vec::new();

        for term in participant_terms {
            let Some((lower, upper)) = self.lra.get_bounds(term) else {
                continue;
            };
            if let Some(lower) = lower.as_ref() {
                Self::append_bound_reason_literals(lower, &mut seen, &mut literals);
            }
            if let Some(upper) = upper.as_ref() {
                Self::append_bound_reason_literals(upper, &mut seen, &mut literals);
            }
        }

        if !literals.is_empty() {
            return literals;
        }

        for &(term, value) in &self.asserted {
            let lit = TheoryLit::new(term, value);
            if seen.insert(lit) {
                literals.push(lit);
            }
        }

        literals
    }

    fn append_bound_reason_literals(
        bound: &Bound,
        seen: &mut HashSet<TheoryLit>,
        literals: &mut Vec<TheoryLit>,
    ) {
        debug_assert_eq!(
            bound.reasons.len(),
            bound.reason_values.len(),
            "BUG: bound reason vectors out of sync (reasons={0}, values={1})",
            bound.reasons.len(),
            bound.reason_values.len(),
        );
        for (reason, value) in bound.reasons.iter().zip(bound.reason_values.iter()) {
            if reason.is_sentinel() {
                continue;
            }
            let lit = TheoryLit::new(*reason, *value);
            if seen.insert(lit) {
                literals.push(lit);
            }
        }
    }
}
