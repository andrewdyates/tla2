// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas conflict collection, per-row conflict building, and deduplication.
//!
//! Complements `farkas` (row-level infeasibility detection) with:
//! - Batch conflict collection across all contradictory variable bounds
//! - Per-row conflict construction with Farkas certificates
//! - Literal deduplication with coefficient combining

use super::*;
use z4_core::term::TermId;
use z4_core::{FarkasAnnotation, TheoryConflict, TheoryLit};

impl LraSolver {
    /// Collect ALL contradictory variable bound conflicts, not just the first.
    ///
    /// The `dual_simplex_with_max_iters` precheck returns on the first bound
    /// contradiction. For problems with many independent bound conflicts in a
    /// single model (e.g., QF_LIA benchmarks with hundreds of equalities and
    /// inequalities), this causes O(N) DPLL(T) round trips where one suffices.
    ///
    /// This method returns ALL bound conflicts (excluding the one already
    /// returned by `dual_simplex`), so the caller can add all blocking clauses
    /// before re-running the SAT solver.
    pub fn collect_all_bound_conflicts(&self, skip_first: bool) -> Vec<TheoryConflict> {
        use num_rational::Rational64;
        let mut conflicts = Vec::new();
        let mut found_first = false;

        for var in 0..self.vars.len() {
            let info = &self.vars[var];
            let (Some(lower), Some(upper)) = (&info.lower, &info.upper) else {
                continue;
            };

            let contradicts = lower.value > upper.value
                || (lower.value == upper.value && (lower.strict || upper.strict));
            if !contradicts {
                continue;
            }

            if skip_first && !found_first {
                found_first = true;
                continue;
            }

            let mut literals = Vec::new();
            let mut coefficients = Vec::new();
            let mut all_fit = true;
            let mut lower_has_real = false;
            let mut upper_has_real = false;
            for ((reason, reason_value), scale) in
                lower.reasons.iter().zip(&lower.reason_values).zip(
                    lower
                        .reason_scales
                        .iter()
                        .chain(std::iter::repeat(types::big_rational_one())),
                )
            {
                if !reason.is_sentinel() {
                    lower_has_real = true;
                    literals.push(TheoryLit::new(*reason, *reason_value));
                    match Self::bigrational_to_rational64(scale) {
                        Some(c) => coefficients.push(c),
                        None => {
                            all_fit = false;
                            coefficients.push(Rational64::from(1));
                        }
                    }
                }
            }
            for ((reason, reason_value), scale) in
                upper.reasons.iter().zip(&upper.reason_values).zip(
                    upper
                        .reason_scales
                        .iter()
                        .chain(std::iter::repeat(types::big_rational_one())),
                )
            {
                if !reason.is_sentinel() {
                    upper_has_real = true;
                    literals.push(TheoryLit::new(*reason, *reason_value));
                    match Self::bigrational_to_rational64(scale) {
                        Some(c) => coefficients.push(c),
                        None => {
                            all_fit = false;
                            coefficients.push(Rational64::from(1));
                        }
                    }
                }
            }
            // Both sides of the contradiction need real reasons (#4919).
            if !lower_has_real || !upper_has_real {
                continue;
            }
            let farkas_opt = if all_fit {
                Some(FarkasAnnotation::new(coefficients))
            } else {
                None
            };
            let (dedup_lits, dedup_coeffs) =
                Self::deduplicate_conflict(literals, farkas_opt.as_ref());
            if dedup_lits.is_empty() {
                continue;
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
            conflicts.push(match farkas {
                Some(f) => TheoryConflict::with_farkas(dedup_lits, f),
                None => TheoryConflict::new(dedup_lits),
            });
        }
        conflicts
    }

    /// Build conflict explanation with Farkas coefficients for interpolation
    ///
    /// For infeasible row: basic_var = Σ(coeff * nb_var) + constant
    /// When basic_var violates its bound, the Farkas certificate is:
    /// - Coefficient 1 for the basic variable's violated bound
    /// - Coefficient |coeff| for each non-basic variable's active bound
    pub(crate) fn build_conflict_with_farkas(&self, row_idx: usize) -> TheoryConflict {
        use num_rational::Rational64;

        let debug_farkas = std::env::var("Z4_DEBUG_FARKAS_ROW").is_ok();

        let mut literals = Vec::new();
        let mut coefficients: Option<Vec<Rational64>> = Some(Vec::new());
        let row = &self.rows[row_idx];
        let violated_bound = self.violates_bounds(row.basic_var);

        if debug_farkas {
            let basic_term_dbg = self.var_term_id(row.basic_var);
            safe_eprintln!(
                "[FARKAS-ROW] row_idx={}, basic_var={}, basic_term={:?}, violated={:?}, {} coeffs",
                row_idx, row.basic_var, basic_term_dbg, violated_bound, row.coeffs.len()
            );
            let basic_info_dbg = &self.vars[row.basic_var as usize];
            safe_eprintln!(
                "[FARKAS-ROW]   basic lower={} upper={} status={:?}",
                basic_info_dbg.lower.as_ref().map(|b| format!("val={} reasons={}", b.value, b.reasons.len())).unwrap_or_else(|| "None".into()),
                basic_info_dbg.upper.as_ref().map(|b| format!("val={} reasons={}", b.value, b.reasons.len())).unwrap_or_else(|| "None".into()),
                basic_info_dbg.status,
            );
            for (nb_var, coeff) in &row.coeffs {
                let nb_info_dbg = &self.vars[*nb_var as usize];
                let nb_term_dbg = self.var_term_id(*nb_var);
                safe_eprintln!(
                    "[FARKAS-ROW]   nb_var={}, term={:?}, coeff={}, status={:?}, lower={}, upper={}",
                    nb_var, nb_term_dbg, coeff, nb_info_dbg.status,
                    nb_info_dbg.lower.as_ref().map(|b| format!("val={} reasons={} reason_terms={:?}", b.value, b.reasons.len(), b.reasons.iter().zip(b.reason_values.iter()).map(|(r,v)| format!("({:?},{})", r, v)).collect::<Vec<_>>())).unwrap_or_else(|| "None".into()),
                    nb_info_dbg.upper.as_ref().map(|b| format!("val={} reasons={} reason_terms={:?}", b.value, b.reasons.len(), b.reasons.iter().zip(b.reason_values.iter()).map(|(r,v)| format!("({:?},{})", r, v)).collect::<Vec<_>>())).unwrap_or_else(|| "None".into()),
                );
            }
        }

        // Track two distinct forms of incomplete explanations:
        // - sentinel-only reasons from derived cuts, which can drop Farkas
        //   metadata but may still yield a valid blocking clause
        // - reasonless bounds, which are not safe to omit from the returned
        //   conflict because doing so can make the clause semantically SAT (#4919)
        let mut has_sentinel_only_bound = false;
        let mut has_reasonless_bound = false;

        // Basic variable's violated bound gets coefficient scaled by reason_scale.
        // For direct variable bounds, reason_scale=1. For bounds derived from
        // multi-coefficient atoms (fast path), reason_scale=1/|coeff|.
        let basic_info = &self.vars[row.basic_var as usize];
        match violated_bound {
            Some(BoundType::Lower) => {
                if let Some(ref lower) = basic_info.lower {
                    let mut pushed_basic = false;
                    // Add ALL reasons from the violated bound to the conflict clause.
                    for ((reason, reason_value), scale) in
                        lower.reasons.iter().zip(&lower.reason_values).zip(
                            lower
                                .reason_scales
                                .iter()
                                .chain(std::iter::repeat(types::big_rational_one())),
                        )
                    {
                        if !reason.is_sentinel() {
                            pushed_basic = true;
                            literals.push(TheoryLit::new(*reason, *reason_value));
                            if let Some(coeffs) = coefficients.as_mut() {
                                match Self::bigrational_to_rational64(scale) {
                                    Some(c) => coeffs.push(c),
                                    None => {
                                        coefficients = None;
                                    }
                                }
                            }
                        }
                    }
                    if !pushed_basic {
                        if lower.reasons.is_empty() {
                            has_reasonless_bound = true;
                        } else {
                            has_sentinel_only_bound = true;
                        }
                    }
                }
            }
            Some(BoundType::Upper) => {
                if let Some(ref upper) = basic_info.upper {
                    let mut pushed_basic = false;
                    for ((reason, reason_value), scale) in
                        upper.reasons.iter().zip(&upper.reason_values).zip(
                            upper
                                .reason_scales
                                .iter()
                                .chain(std::iter::repeat(types::big_rational_one())),
                        )
                    {
                        if !reason.is_sentinel() {
                            pushed_basic = true;
                            literals.push(TheoryLit::new(*reason, *reason_value));
                            if let Some(coeffs) = coefficients.as_mut() {
                                match Self::bigrational_to_rational64(scale) {
                                    Some(c) => coeffs.push(c),
                                    None => {
                                        coefficients = None;
                                    }
                                }
                            }
                        }
                    }
                    if !pushed_basic {
                        if upper.reasons.is_empty() {
                            has_reasonless_bound = true;
                        } else {
                            has_sentinel_only_bound = true;
                        }
                    }
                }
            }
            None => {
                // Defensive: shouldn't happen when called from infeasible row handling.
            }
        }

        // Non-basic variables' bounds get their tableau coefficients (absolute value)
        // scaled by the bound's per-reason Farkas scale factor.
        // The sign of the coefficient determines which bound is "active"
        for (nb_var, coeff) in &row.coeffs {
            let nb_info = &self.vars[*nb_var as usize];
            if coeff.is_zero() {
                continue;
            }
            // Skip basic variables (#4919): after pivots, row.coeffs may reference
            // variables that are now basic for other rows. These are not "stuck at
            // bounds" in the Dutertre & de Moura sense — their values are determined
            // by their row equations, not by bounds. Including them produces false
            // missing_active_bound_reasons aborts and spurious Unknown results.
            // This matches the guard in find_beneficial_entering (line 372).
            // #8012: basic vars with tight bounds (lower==upper, non-strict)
            // ARE fixed by their bounds, not row equations. Include their reasons.
            if !matches!(nb_info.status, Some(VarStatus::NonBasic)) {
                let has_tight = match (&nb_info.lower, &nb_info.upper) {
                    (Some(lb), Some(ub)) => lb.value == ub.value && !lb.strict && !ub.strict,
                    _ => false,
                };
                if !has_tight { continue; }
            }
            let abs_coeff_big = coeff.abs_bigrational();

            // Choose the *active* bound, per Dutertre & de Moura (CAV'06): when no pivot exists,
            // each non-basic var is stuck at the bound that blocks restoring feasibility.
            let active_bound = match violated_bound {
                Some(BoundType::Lower) => {
                    // Basic var is too small; we needed to move nb_var in the direction that increases it:
                    //   coeff > 0 => increase nb_var => blocked by upper bound
                    //   coeff < 0 => decrease nb_var => blocked by lower bound
                    if coeff.is_positive() {
                        nb_info.upper.as_ref()
                    } else {
                        nb_info.lower.as_ref()
                    }
                }
                Some(BoundType::Upper) => {
                    // Basic var is too large:
                    //   coeff > 0 => decrease nb_var => blocked by lower bound
                    //   coeff < 0 => increase nb_var => blocked by upper bound
                    if coeff.is_positive() {
                        nb_info.lower.as_ref()
                    } else {
                        nb_info.upper.as_ref()
                    }
                }
                None => None,
            };

            let mut pushed_any = false;
            match active_bound {
                Some(bound) => {
                    for ((reason, reason_value), scale) in
                        bound.reasons.iter().zip(&bound.reason_values).zip(
                            bound
                                .reason_scales
                                .iter()
                                .chain(std::iter::repeat(types::big_rational_one())),
                        )
                    {
                        if !reason.is_sentinel() {
                            pushed_any = true;
                            literals.push(TheoryLit::new(*reason, *reason_value));
                            if let Some(coeffs) = coefficients.as_mut() {
                                let scaled = &abs_coeff_big * scale;
                                match Self::bigrational_to_rational64(&scaled) {
                                    Some(c) => coeffs.push(c),
                                    None => {
                                        coefficients = None;
                                    }
                                }
                            }
                        }
                    }

                    if !pushed_any {
                        if bound.reasons.is_empty() {
                            has_reasonless_bound = true;
                        } else {
                            has_sentinel_only_bound = true;
                        }
                        coefficients = None;
                    }
                }
                None => {
                    let has_any_bound = nb_info.lower.is_some() || nb_info.upper.is_some();
                    if has_any_bound {
                        has_reasonless_bound = true;
                        coefficients = None;
                    }
                }
            }
        }

        // Reasonless bounds make the conflict semantically unsound (#4919):
        // the omitted bound is not justified, so the remaining literals alone
        // can be SAT. Return empty conflict to degrade gracefully to Unknown.
        if has_reasonless_bound {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] simplex conflict degraded: row={}, basic_var={}, reasonless=true, sentinel_only={}, literals={}",
                    row_idx,
                    row.basic_var,
                    has_sentinel_only_bound,
                    literals.len()
                );
            }
            return TheoryConflict::new(vec![]);
        }

        // Sentinel-only bounds from axiom/definition sources are safe to omit
        // after fixing #4919: Gomory cuts and Diophantine bounds with empty
        // reasons are now skipped (gomory.rs, lia_support.rs), so remaining
        // sentinel-only bounds come only from initial variable domain setup
        // or theory definitions which hold unconditionally.
        //
        // If we collected no real literals at all, return empty conflict
        // (the entire infeasibility depends on axiom bounds).
        if has_sentinel_only_bound && literals.is_empty() {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] simplex conflict degraded: row={}, basic_var={}, reasonless=false, sentinel_only=true, literals=0",
                    row_idx,
                    row.basic_var
                );
            }
            return TheoryConflict::new(vec![]);
        }

        // If we have some real literals + sentinel-only bounds, the clause
        // is valid but weaker (blocks a superset of assignments). Return
        // it without Farkas metadata since the certificate is incomplete.
        if has_sentinel_only_bound {
            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] simplex conflict partial: row={}, basic_var={}, reasonless=false, sentinel_only=true, literals={}",
                    row_idx,
                    row.basic_var,
                    literals.len()
                );
            }
            let (dedup_literals, _) = Self::deduplicate_conflict(literals, None);
            return TheoryConflict::new(dedup_literals);
        }

        // At this point, all bounds have complete non-sentinel reasons.
        // Attach Farkas coefficients if all fit in Rational64.
        let farkas = coefficients
            .filter(|coeffs| !coeffs.is_empty())
            .map(FarkasAnnotation::new);

        // Deduplicate literals while combining Farkas coefficients (#938).
        // Same literal can appear multiple times if the same constraint is a reason
        // for multiple bounds (e.g., equality x=4 implies both x>=4 and x<=4).
        let (dedup_literals, dedup_coeffs) = Self::deduplicate_conflict(literals, farkas.as_ref());
        let dedup_farkas = if !dedup_coeffs.is_empty() {
            Some(FarkasAnnotation::new(dedup_coeffs))
        } else {
            farkas
        };

        match dedup_farkas {
            Some(f) => TheoryConflict::with_farkas(dedup_literals, f),
            None => TheoryConflict::new(dedup_literals),
        }
    }

    /// Checked Rational64 addition using i128 intermediates to avoid overflow.
    /// Returns `None` when the result cannot fit in i64 numerator/denominator.
    fn checked_r64_add(
        a: num_rational::Rational64,
        b: num_rational::Rational64,
    ) -> Option<num_rational::Rational64> {
        let an = i128::from(*a.numer());
        let ad = i128::from(*a.denom());
        let bn = i128::from(*b.numer());
        let bd = i128::from(*b.denom());
        let num = an.checked_mul(bd)?.checked_add(bn.checked_mul(ad)?)?;
        let den = ad.checked_mul(bd)?;
        let num_i64 = i64::try_from(num).ok()?;
        let den_i64 = i64::try_from(den).ok()?;
        if den_i64 == 0 {
            return None;
        }
        Some(num_rational::Rational64::new(num_i64, den_i64))
    }

    /// Deduplicate conflict literals, combining Farkas coefficients for duplicates.
    pub(crate) fn deduplicate_conflict(
        literals: Vec<TheoryLit>,
        farkas: Option<&FarkasAnnotation>,
    ) -> (Vec<TheoryLit>, Vec<num_rational::Rational64>) {
        use num_rational::Rational64;
        use std::collections::{HashMap, HashSet};

        if literals.is_empty() {
            return (literals, vec![]);
        }

        if farkas.is_none() {
            let mut seen: HashSet<(TermId, bool)> = HashSet::new();
            let mut dedup_literals = Vec::new();
            for lit in literals {
                if seen.insert((lit.term, lit.value)) {
                    dedup_literals.push(lit);
                }
            }
            return (dedup_literals, vec![]);
        }

        // Build map: (term, value) -> accumulated coefficient
        let mut seen: HashMap<(TermId, bool), Rational64> = HashMap::new();
        let mut order: Vec<(TermId, bool)> = Vec::new();
        let mut overflow = false;

        // Borrow coefficients directly — no clone needed (#6221 Finding 2).
        // farkas.is_none() case returns early above.
        let coeffs = match farkas {
            Some(f) => &f.coefficients,
            None => return (literals, vec![]),
        };

        for (lit, coeff) in literals.iter().zip(coeffs.iter()) {
            let key = (lit.term, lit.value);
            if let Some(existing) = seen.get_mut(&key) {
                match Self::checked_r64_add(*existing, *coeff) {
                    Some(sum) => *existing = sum,
                    None => {
                        overflow = true;
                        break;
                    }
                }
            } else {
                seen.insert(key, *coeff);
                order.push(key);
            }
        }

        // On overflow, fall back to simple deduplication without Farkas coefficients.
        // The conflict clause is still valid; we just lose the proof annotation.
        if overflow {
            let mut seen_keys: HashSet<(TermId, bool)> = HashSet::new();
            let dedup_literals: Vec<_> = literals
                .into_iter()
                .filter(|lit| seen_keys.insert((lit.term, lit.value)))
                .collect();
            return (dedup_literals, vec![]);
        }

        let dedup_literals: Vec<_> = order
            .iter()
            .map(|(term, value)| TheoryLit::new(*term, *value))
            .collect();
        let dedup_coeffs: Vec<_> = order.iter().map(|key| seen[key]).collect();

        (dedup_literals, dedup_coeffs)
    }
}
