// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GCD-based infeasibility checks and rational-bound helpers for LIA.

use super::*;
use tracing::{debug, info};

impl LiaSolver<'_> {
    pub(super) fn gcd_test(&self) -> Option<TheoryConflict> {
        use num_rational::Rational64;

        let debug = self.debug_gcd;
        let mut tested_equalities = 0usize;

        if debug {
            safe_eprintln!(
                "[GCD] Running GCD test on {} asserted literals",
                self.asserted.len()
            );
        }

        for &literal in &self.assertion_view().positive_equalities {
            // Check if this is an equality
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            // Parse both sides of the equality
            let (coeffs, constant) = self.parse_linear_expr_for_gcd(args[0], args[1]);

            if coeffs.is_empty() {
                continue;
            }
            tested_equalities += 1;

            if debug {
                safe_eprintln!("[GCD] Equality: coeffs={:?}, constant={}", coeffs, constant);
            }

            // All coefficients must be integer (which they should be for LIA)
            // Compute GCD of all coefficients.
            let gcd = gcd_of_abs(coeffs.iter().cloned());

            if gcd.is_zero() {
                continue;
            }
            debug_assert!(
                gcd.is_positive(),
                "BUG: gcd_of_abs returned non-positive gcd {gcd}"
            );

            // Check if GCD divides the constant
            // The constant is on the RHS, so we're checking GCD | constant
            let remainder = &constant % &gcd;
            if !remainder.is_zero() {
                if debug {
                    safe_eprintln!(
                        "[GCD] UNSAT: GCD={} does not divide constant={} (remainder={})",
                        gcd,
                        constant,
                        remainder
                    );
                }
                // Return conflict with the equality as the reason.
                // Farkas coefficient 1 - the equality is the sole contributor.
                let literals = vec![TheoryLit::new(literal, true)];
                // INVARIANT: GCD must be positive (zero was filtered above)
                debug_assert!(
                    gcd > BigInt::zero(),
                    "BUG: GCD test returning UNSAT with non-positive GCD {gcd}",
                );
                let farkas = FarkasAnnotation::new(vec![Rational64::from(1)]);
                info!(
                    target: "z4::lia",
                    tested_equalities,
                    conflicting_literal = literal.0,
                    gcd = %gcd,
                    constant = %constant,
                    "LIA GCD test found divisibility conflict"
                );
                return Some(TheoryConflict::with_farkas(literals, farkas));
            }
        }

        debug!(
            target: "z4::lia",
            tested_equalities,
            "LIA GCD test completed without conflict"
        );

        None
    }

    // gcd_test_tableau, ext_gcd_test, collect_tableau_gcd_conflict_literals,
    // append_bound_reason_literals extracted to gcd_tableau.rs

    pub(crate) fn update_gcd_and_least_coeff(
        abs_scaled: &BigInt,
        is_bounded: bool,
        gcds: &mut BigInt,
        least_coeff: &mut BigInt,
        least_coeff_is_bounded: &mut bool,
    ) {
        if gcds.is_zero() {
            gcds.clone_from(abs_scaled);
            least_coeff.clone_from(abs_scaled);
            *least_coeff_is_bounded = is_bounded;
            return;
        }

        *gcds = gcds.gcd(abs_scaled);

        if abs_scaled < &*least_coeff {
            least_coeff.clone_from(abs_scaled);
            *least_coeff_is_bounded = is_bounded;
        } else if abs_scaled == &*least_coeff {
            // Keep "bounded" true if any tied least-coefficient variable is bounded.
            *least_coeff_is_bounded |= is_bounded;
        }
    }

    /// Ceiling of a rational number: ceil(r)
    pub(crate) fn ceil_rational(r: &BigRational) -> BigInt {
        if r.is_integer() {
            r.to_integer()
        } else if r.is_positive() {
            r.to_integer() + BigInt::one()
        } else {
            r.to_integer()
        }
    }

    /// Floor of a rational number: floor(r)
    pub(crate) fn floor_rational(r: &BigRational) -> BigInt {
        if r.is_integer() {
            r.to_integer()
        } else if r.is_negative() {
            r.to_integer() - BigInt::one()
        } else {
            r.to_integer()
        }
    }

    /// Effective integer lower bound from a rational bound.
    ///
    /// For integer variables, a strict bound `x > n` (where n is integer) becomes
    /// `x >= n+1`. A non-strict bound `x >= r` becomes `x >= ceil(r)`.
    pub(crate) fn effective_int_lower(b: &Bound) -> BigInt {
        let bv = b.value.to_big();
        let result = if b.strict && Self::is_integer(&bv) {
            Self::floor_rational(&bv) + BigInt::one()
        } else {
            Self::ceil_rational(&bv)
        };
        // INVARIANT: effective lower bound must be >= the rational bound value
        debug_assert!(
            BigRational::from(result.clone()) >= bv,
            "BUG: effective_int_lower({}{}) = {} is below bound",
            if b.strict { ">" } else { ">=" },
            bv,
            result
        );
        result
    }

    /// Effective integer upper bound from a rational bound.
    ///
    /// For integer variables, a strict bound `x < n` (where n is integer) becomes
    /// `x <= n-1`. A non-strict bound `x <= r` becomes `x <= floor(r)`.
    pub(crate) fn effective_int_upper(b: &Bound) -> BigInt {
        let bv = b.value.to_big();
        let result = if b.strict && Self::is_integer(&bv) {
            Self::floor_rational(&bv) - BigInt::one()
        } else {
            Self::floor_rational(&bv)
        };
        // INVARIANT: effective upper bound must be <= the rational bound value
        debug_assert!(
            BigRational::from(result.clone()) <= bv,
            "BUG: effective_int_upper({}{}) = {} is above bound",
            if b.strict { "<" } else { "<=" },
            b.value,
            result
        );
        result
    }
}

#[cfg(test)]
#[path = "gcd_tests.rs"]
mod tests;
