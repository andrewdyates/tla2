// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas conflict construction for infeasible simplex states.
//!
//! Row-level infeasibility detection and Farkas proof construction.
//! Batch conflict collection, per-row conflict building, and deduplication
//! are in `farkas_collect`.

use super::*;
use z4_core::{FarkasAnnotation, TheoryConflict, TheoryLit, TheoryResult};

impl LraSolver {
    /// Check for row-level infeasibility caused by strict bounds (#2021).
    ///
    /// For each row `basic_var = Σ(coeff_i * nb_var_i) + constant`, compute:
    /// - Implied lower bound = sum of coeff*lb (positive coeff) or coeff*ub (negative coeff)
    /// - Implied upper bound = sum of coeff*ub (positive coeff) or coeff*lb (negative coeff)
    ///
    /// If implied_lower > basic_upper, or implied_lower == basic_upper with strictness,
    /// the row is infeasible. Similarly for implied_upper < basic_lower.
    ///
    /// This catches cases like x > 0, y > 0, x + y <= 0 which would cause simplex cycling.
    pub(crate) fn check_row_strict_infeasibility(&self) -> Option<TheoryResult> {
        // Two-pass approach (#6364): pass 1 uses only Rational arithmetic to
        // detect infeasibility (no Farkas vectors, no BigRational allocation).
        // Pass 2 runs only on the infeasible row to build the Farkas certificate.
        // Most rows are feasible, so pass 2 almost never executes.

        for row in &self.rows {
            let basic_info = &self.vars[row.basic_var as usize];

            // --- Pass 1: detect lower-bound infeasibility (cheap) ---
            let mut implied_lower = row.constant.clone();
            let mut lower_strict = false;
            let mut lower_valid = true;

            for &(nb_var, ref coeff) in &row.coeffs {
                if coeff.is_zero() {
                    continue;
                }
                let nb_info = &self.vars[nb_var as usize];
                if coeff.is_positive() {
                    if let Some(ref lb) = nb_info.lower {
                        implied_lower += coeff * &lb.value;
                        if lb.strict {
                            lower_strict = true;
                        }
                    } else {
                        lower_valid = false;
                        break;
                    }
                } else if let Some(ref ub) = nb_info.upper {
                    implied_lower += coeff * &ub.value;
                    if ub.strict {
                        lower_strict = true;
                    }
                } else {
                    lower_valid = false;
                    break;
                }
            }

            if lower_valid {
                if let Some(ref upper) = basic_info.upper {
                    let contradicts = implied_lower > upper.value
                        || (implied_lower == upper.value && (lower_strict || upper.strict));
                    if contradicts {
                        if self.debug_lra {
                            self.debug_log_row_lower_precheck(
                                row,
                                &implied_lower,
                                lower_strict,
                                upper,
                            );
                        }
                        // --- Pass 2: build Farkas certificate (rare) ---
                        if let Some(result) = self.build_lower_farkas_conflict(row, upper) {
                            return Some(result);
                        }
                    }
                }
            }

            // --- Pass 1: detect upper-bound infeasibility (cheap) ---
            let mut implied_upper = row.constant.clone();
            let mut upper_strict = false;
            let mut upper_valid = true;

            for &(nb_var, ref coeff) in &row.coeffs {
                if coeff.is_zero() {
                    continue;
                }
                let nb_info = &self.vars[nb_var as usize];
                if coeff.is_positive() {
                    if let Some(ref ub) = nb_info.upper {
                        implied_upper += coeff * &ub.value;
                        if ub.strict {
                            upper_strict = true;
                        }
                    } else {
                        upper_valid = false;
                        break;
                    }
                } else if let Some(ref lb) = nb_info.lower {
                    implied_upper += coeff * &lb.value;
                    if lb.strict {
                        upper_strict = true;
                    }
                } else {
                    upper_valid = false;
                    break;
                }
            }

            if upper_valid {
                if let Some(ref lower) = basic_info.lower {
                    let contradicts = implied_upper < lower.value
                        || (implied_upper == lower.value && (upper_strict || lower.strict));
                    if contradicts {
                        if self.debug_lra {
                            self.debug_log_row_upper_precheck(
                                row,
                                &implied_upper,
                                upper_strict,
                                lower,
                            );
                        }
                        // --- Pass 2: build Farkas certificate (rare) ---
                        if let Some(result) = self.build_upper_farkas_conflict(row, lower) {
                            return Some(result);
                        }
                    }
                }
            }
        }

        None
    }

    /// Build a Farkas conflict certificate for a row whose implied lower bound
    /// exceeds the basic variable's upper bound. Only called when infeasibility
    /// has already been detected by the cheap pass 1 check.
    fn build_lower_farkas_conflict(&self, row: &TableauRow, upper: &Bound) -> Option<TheoryResult> {
        use num_rational::Rational64;

        let mut literals = Vec::new();
        let mut coefficients = Vec::new();
        let mut all_fit = true;
        let mut has_sentinel_only_bound = false;
        let mut has_reasonless_bound = false;

        for &(nb_var, ref coeff) in &row.coeffs {
            if coeff.is_zero() {
                continue;
            }
            let nb_info = &self.vars[nb_var as usize];
            let bound = if coeff.is_positive() {
                nb_info.lower.as_ref()?
            } else {
                nb_info.upper.as_ref()?
            };
            let abs_coeff_big = coeff.abs_bigrational();
            let mut bound_has_real = false;
            for ((reason, &val), scale) in bound.reasons.iter().zip(&bound.reason_values).zip(
                bound
                    .reason_scales
                    .iter()
                    .chain(std::iter::repeat(types::big_rational_one())),
            ) {
                if !reason.is_sentinel() {
                    bound_has_real = true;
                    literals.push(TheoryLit::new(*reason, val));
                    let farkas_c = &abs_coeff_big * scale;
                    match Self::bigrational_to_rational64(&farkas_c) {
                        Some(c) => coefficients.push(c),
                        None => {
                            all_fit = false;
                            coefficients.push(Rational64::from(1));
                        }
                    }
                }
            }
            // Track sentinel-only vs reasonless bounds (#4919).
            if !bound_has_real {
                if bound.reasons.is_empty() {
                    has_reasonless_bound = true;
                } else {
                    has_sentinel_only_bound = true;
                }
            }
        }

        // Add the basic variable's upper bound reasons
        let mut upper_has_real = false;
        for ((reason, &val), scale) in upper.reasons.iter().zip(&upper.reason_values).zip(
            upper
                .reason_scales
                .iter()
                .chain(std::iter::repeat(types::big_rational_one())),
        ) {
            if !reason.is_sentinel() {
                upper_has_real = true;
                literals.push(TheoryLit::new(*reason, val));
                match Self::bigrational_to_rational64(scale) {
                    Some(c) => coefficients.push(c),
                    None => {
                        all_fit = false;
                        coefficients.push(Rational64::from(1));
                    }
                }
            }
        }
        if !upper_has_real {
            if upper.reasons.is_empty() {
                has_reasonless_bound = true;
            } else {
                has_sentinel_only_bound = true;
            }
        }

        // Reasonless bounds: unsound to omit (#4919). Return None to fall
        // through to the main simplex loop which degrades to Unknown.
        if has_reasonless_bound {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] row-strict lower conflict degraded: basic_var={}, reasonless=true, sentinel_only={}, literals={}",
                    row.basic_var,
                    has_sentinel_only_bound,
                    literals.len()
                );
            }
            return None;
        }

        // Sentinel-only bounds from axiom/definition sources: safe to omit.
        // Return partial conflict without Farkas metadata if we have real literals.
        if has_sentinel_only_bound {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] row-strict lower conflict partial: basic_var={}, reasonless=false, sentinel_only=true, literals={}",
                    row.basic_var,
                    literals.len()
                );
            }
            if literals.is_empty() {
                return None;
            }
            let (dedup_lits, _) = Self::deduplicate_conflict(literals, None);
            return Some(TheoryResult::UnsatWithFarkas(TheoryConflict::new(
                dedup_lits,
            )));
        }

        Self::finalize_farkas_conflict(literals, coefficients, all_fit)
    }

    /// Build a Farkas conflict certificate for a row whose implied upper bound
    /// is below the basic variable's lower bound. Only called when infeasibility
    /// has already been detected by the cheap pass 1 check.
    fn build_upper_farkas_conflict(&self, row: &TableauRow, lower: &Bound) -> Option<TheoryResult> {
        use num_rational::Rational64;

        let mut literals = Vec::new();
        let mut coefficients = Vec::new();
        let mut all_fit = true;
        let mut has_sentinel_only_bound = false;
        let mut has_reasonless_bound = false;

        for &(nb_var, ref coeff) in &row.coeffs {
            if coeff.is_zero() {
                continue;
            }
            let nb_info = &self.vars[nb_var as usize];
            let bound = if coeff.is_positive() {
                nb_info.upper.as_ref()?
            } else {
                nb_info.lower.as_ref()?
            };
            let abs_coeff_big = coeff.abs_bigrational();
            let mut bound_has_real = false;
            for ((reason, &val), scale) in bound.reasons.iter().zip(&bound.reason_values).zip(
                bound
                    .reason_scales
                    .iter()
                    .chain(std::iter::repeat(types::big_rational_one())),
            ) {
                if !reason.is_sentinel() {
                    bound_has_real = true;
                    literals.push(TheoryLit::new(*reason, val));
                    let farkas_c = &abs_coeff_big * scale;
                    match Self::bigrational_to_rational64(&farkas_c) {
                        Some(c) => coefficients.push(c),
                        None => {
                            all_fit = false;
                            coefficients.push(Rational64::from(1));
                        }
                    }
                }
            }
            // Track sentinel-only vs reasonless bounds (#4919).
            if !bound_has_real {
                if bound.reasons.is_empty() {
                    has_reasonless_bound = true;
                } else {
                    has_sentinel_only_bound = true;
                }
            }
        }

        // Add the basic variable's lower bound reasons
        let mut lower_has_real = false;
        for ((reason, &val), scale) in lower.reasons.iter().zip(&lower.reason_values).zip(
            lower
                .reason_scales
                .iter()
                .chain(std::iter::repeat(types::big_rational_one())),
        ) {
            if !reason.is_sentinel() {
                lower_has_real = true;
                literals.push(TheoryLit::new(*reason, val));
                match Self::bigrational_to_rational64(scale) {
                    Some(c) => coefficients.push(c),
                    None => {
                        all_fit = false;
                        coefficients.push(Rational64::from(1));
                    }
                }
            }
        }
        if !lower_has_real {
            if lower.reasons.is_empty() {
                has_reasonless_bound = true;
            } else {
                has_sentinel_only_bound = true;
            }
        }

        // Reasonless bounds: unsound to omit (#4919). Return None to fall
        // through to the main simplex loop which degrades to Unknown.
        if has_reasonless_bound {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] row-strict upper conflict degraded: basic_var={}, reasonless=true, sentinel_only={}, literals={}",
                    row.basic_var,
                    has_sentinel_only_bound,
                    literals.len()
                );
            }
            return None;
        }

        // Sentinel-only bounds from axiom/definition sources: safe to omit.
        // Return partial conflict without Farkas metadata if we have real literals.
        if has_sentinel_only_bound {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] row-strict upper conflict partial: basic_var={}, reasonless=false, sentinel_only=true, literals={}",
                    row.basic_var,
                    literals.len()
                );
            }
            if literals.is_empty() {
                return None;
            }
            let (dedup_lits, _) = Self::deduplicate_conflict(literals, None);
            return Some(TheoryResult::UnsatWithFarkas(TheoryConflict::new(
                dedup_lits,
            )));
        }

        Self::finalize_farkas_conflict(literals, coefficients, all_fit)
    }

    /// Shared Farkas conflict finalization: deduplicate and wrap.
    fn finalize_farkas_conflict(
        literals: Vec<TheoryLit>,
        coefficients: Vec<num_rational::Rational64>,
        all_fit: bool,
    ) -> Option<TheoryResult> {
        use num_rational::Rational64;

        let farkas_opt = if all_fit {
            Some(FarkasAnnotation::new(coefficients))
        } else {
            None
        };
        let (dedup_lits, dedup_coeffs) = Self::deduplicate_conflict(literals, farkas_opt.as_ref());
        if dedup_lits.is_empty() {
            return None;
        }
        let farkas = if !dedup_coeffs.is_empty() {
            Some(FarkasAnnotation::new(dedup_coeffs))
        } else if all_fit {
            Some(FarkasAnnotation::new(
                (0..dedup_lits.len()).map(|_| Rational64::from(1)).collect(),
            ))
        } else {
            None
        };
        Some(TheoryResult::UnsatWithFarkas(match farkas {
            Some(f) => TheoryConflict::with_farkas(dedup_lits, f),
            None => TheoryConflict::new(dedup_lits),
        }))
    }
}
