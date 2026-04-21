// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA integer patching and direct bound injection.
//!
//! The `try_patch_integer_var` method implements Z3's patching technique that
//! avoids branching by adjusting non-basic integer variables. Direct bound
//! methods allow the LIA solver to inject Diophantine-derived bounds into
//! the simplex. Extracted from `lia_support.rs` to keep each file under
//! 500 lines.

use crate::rational::Rational;
use std::sync::OnceLock;

#[cfg(not(kani))]
use hashbrown::HashSet;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Zero};
use z4_core::extended_gcd_bigint;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::term::TermId;

use crate::types::InfRational;
use crate::{fractional_part, BoundType, LraSolver, VarStatus};

/// Cached `Z4_DEBUG_PATCH` env var (checked once per process).
fn debug_patch() -> bool {
    static CACHED: OnceLock<bool> = OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("Z4_DEBUG_PATCH").is_ok())
}

impl LraSolver {
    /// Try to patch a fractional basic variable to an integer value.
    ///
    /// This is Z3's "patching" technique that avoids branching by adjusting
    /// non-basic integer variables. For a fractional basic variable x, we look
    /// for a non-basic integer variable y in the same row such that adjusting y
    /// by a small integer delta makes x integral while keeping all bounds satisfied.
    ///
    /// Returns true if patching succeeded, false otherwise.
    pub fn try_patch_integer_var(&mut self, term: TermId, integer_vars: &HashSet<TermId>) -> bool {
        let debug = debug_patch();

        // Get the internal variable ID
        let Some(&var) = self.term_to_var.get(&term) else {
            return false;
        };

        // Check if this variable is basic (has a row)
        let Some(VarStatus::Basic(row_idx)) = self.vars.get(var as usize).and_then(|v| v.status)
        else {
            if debug {
                safe_eprintln!("[PATCH] Term {:?} var {} is not basic", term, var);
            }
            return false;
        };

        let row = &self.rows[row_idx];
        let basic_value = self.vars[var as usize].value.rational();

        // Already integer?
        if basic_value.denom().is_one() {
            return false;
        }

        // For patching, we need: x + coeff * delta to be integral
        // where x is the basic variable and delta is the adjustment to a non-basic var
        let x_frac = fractional_part(&basic_value);
        if x_frac.is_zero() {
            return false;
        }

        if debug {
            safe_eprintln!(
                "[PATCH] Trying to patch var {} (term {:?}) with fractional value {}",
                var,
                term,
                basic_value
            );
        }

        // Try each non-basic integer variable in this row
        for &(nb_var, ref coeff_rat) in &row.coeffs {
            // Must be an integer variable
            let Some(&nb_term) = self.var_to_term.get(&nb_var) else {
                continue;
            };
            if !integer_vars.contains(&nb_term) {
                continue;
            }

            // Must be non-basic
            if !matches!(self.vars[nb_var as usize].status, Some(VarStatus::NonBasic)) {
                continue;
            }

            // Convert Rational coefficient to BigRational for patching arithmetic.
            let coeff = coeff_rat.to_big();

            // Coefficient must have a compatible fractional structure
            // For x + coeff * delta to be integral when x has fractional part f,
            // we need coeff * delta to have fractional part -f (mod 1)
            let coeff_frac = fractional_part(&coeff);
            if coeff_frac.is_zero() {
                // Integer coefficient can't help fix fractional basic var
                // (would need fractional delta, but we need integer delta)
                continue;
            }

            // Find deltas that make x integral
            // x_new = x + coeff * delta must be integral
            // So we need (x + coeff * delta).is_int()
            // Let a1/a2 = coeff, x1/x2 = x (in lowest terms)
            // We need x1/x2 + (a1/a2)*delta to be integral
            // Rearranging: delta = (k*x2 - x1) * a2 / (a1 * x2) for some integer k
            // For delta to be integral, we need a2 divisible by x2
            let a1 = coeff.numer();
            let a2 = coeff.denom();
            let x1 = basic_value.numer();
            let x2 = basic_value.denom();

            if a2 % x2 != BigInt::zero() {
                if debug {
                    safe_eprintln!(
                        "[PATCH] Coeff denom {} not divisible by basic denom {}",
                        a2,
                        x2
                    );
                }
                continue;
            }

            // t = a2 / x2
            let t = a2 / x2;

            // Use extended GCD to find u, v such that u*a1 + v*x2 = gcd(a1, x2)
            // For this to work, we need gcd(a1, x2) = 1 (coprime)
            // If not coprime, patching with this variable won't work
            let g = a1.gcd(x2);
            if !g.is_one() && g != BigInt::from(-1) {
                if debug {
                    safe_eprintln!("[PATCH] gcd({}, {}) = {} != 1", a1, x2, g);
                }
                continue;
            }

            // Find u such that u*a1 ≡ 1 (mod x2)
            let (_, u, _) = extended_gcd_bigint(a1, x2);

            // delta_base = u * t * x1 makes x + coeff * delta_base integral
            // Any delta = delta_base + k * a2 for integer k also works
            let delta_base = &u * &t * x1;

            // Find the smallest magnitude delta that keeps bounds satisfied
            // Try delta_base, delta_base + a2, delta_base - a2, etc.
            let nb_info = &self.vars[nb_var as usize];
            let nb_value = nb_info.value.rational();

            for sign in [BigInt::one(), BigInt::from(-1)] {
                for k in 0..10 {
                    let delta = &delta_base + &sign * BigInt::from(k) * a2;
                    let delta_rat = BigRational::from(delta.clone());
                    let new_nb_value = &nb_value + &delta_rat;

                    // Check bounds on the non-basic variable
                    if let Some(ref lb) = nb_info.lower {
                        if Rational::from(&new_nb_value) < lb.value || (lb.strict && Rational::from(&new_nb_value) == lb.value) {
                            continue;
                        }
                    }
                    if let Some(ref ub) = nb_info.upper {
                        if Rational::from(&new_nb_value) > ub.value || (ub.strict && Rational::from(&new_nb_value) == ub.value) {
                            continue;
                        }
                    }

                    // Check that the new basic value is actually integral
                    let new_basic_value = &basic_value + &(&coeff * &delta_rat);
                    if !new_basic_value.denom().is_one() {
                        continue;
                    }

                    // Check bounds on all affected basic variables
                    let mut all_bounds_ok = true;
                    for other_row in &self.rows {
                        let other_coeff = other_row.coeff_big(nb_var);
                        if other_coeff.is_zero() {
                            continue;
                        }
                        let other_basic = other_row.basic_var as usize;
                        let other_info = &self.vars[other_basic];
                        let old_val = other_info.value.rational();
                        let new_val = &old_val + &(&other_coeff * &delta_rat);

                        if let Some(ref lb) = other_info.lower {
                            if Rational::from(&new_val) < lb.value || (lb.strict && Rational::from(&new_val) == lb.value) {
                                all_bounds_ok = false;
                                break;
                            }
                        }
                        if let Some(ref ub) = other_info.upper {
                            if Rational::from(&new_val) > ub.value || (ub.strict && Rational::from(&new_val) == ub.value) {
                                all_bounds_ok = false;
                                break;
                            }
                        }

                        // If patching would make an integer basic variable fractional, skip
                        if let Some(&other_term) = self.var_to_term.get(&(other_basic as u32)) {
                            if integer_vars.contains(&other_term)
                                && old_val.denom().is_one()
                                && !new_val.denom().is_one()
                            {
                                all_bounds_ok = false;
                                break;
                            }
                        }
                    }

                    if all_bounds_ok {
                        if debug {
                            safe_eprintln!(
                                "[PATCH] SUCCESS: adjusting var {} by delta {} -> new value {}",
                                nb_var,
                                delta_rat,
                                new_nb_value
                            );
                        }
                        // Apply the patch
                        self.update_nonbasic(nb_var, InfRational::from_rational(new_nb_value));
                        return true;
                    }
                }
            }
        }

        if debug {
            safe_eprintln!(
                "[PATCH] No valid patch found for var {} (term {:?})",
                var,
                term
            );
        }
        false
    }

    /// Add a direct bound on an internal variable.
    ///
    /// Used by LIA solver to add bounds discovered through Diophantine solving.
    /// The bound is: var >= value (if is_lower) or var <= value.
    ///
    /// Bounds added without reasons are skipped — they create sentinel-only
    /// bounds that degrade to Unknown or produce unsound partial conflicts (#4919).
    pub fn add_direct_bound(&mut self, var: u32, value: BigRational, is_lower: bool) {
        // Delegate to the version with reasons, using empty reasons.
        // add_direct_bound_with_reasons will skip this since reasons is empty.
        self.add_direct_bound_with_reasons(var, value, is_lower, &[]);
    }

    /// Add a direct bound on an internal variable with reason tracking.
    ///
    /// Used by LIA solver to add bounds discovered through Diophantine solving.
    /// The reasons parameter contains (term_id, value) pairs for the constraints
    /// that led to this bound - used for conflict clause generation.
    ///
    /// Bounds with empty reasons are skipped — they have no justification and
    /// would create sentinel-only bounds that degrade to Unknown (#4919).
    pub fn add_direct_bound_with_reasons(
        &mut self,
        var: u32,
        value: BigRational,
        is_lower: bool,
        reasons: &[(TermId, bool)],
    ) {
        // Skip bounds with no reasons — they have no justification and would
        // create sentinel-only bounds that degrade to Unknown (#4919).
        if reasons.is_empty() {
            return;
        }

        let bound_type = if is_lower {
            BoundType::Lower
        } else {
            BoundType::Upper
        };

        let scales: Vec<BigRational> = reasons.iter().map(|_| BigRational::one()).collect();
        self.assert_var_bound_with_reasons(var, value, bound_type, false, reasons, &scales);
        self.dirty = true;
    }
}
