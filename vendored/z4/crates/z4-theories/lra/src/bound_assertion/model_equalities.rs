// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Offset equality discovery for nf==2 rows (Z3's `cheap_eq_on_nbase`).
    ///
    /// For each touched row with exactly 2 non-fixed columns (base `x` and non-base `y`
    /// with coefficient +1 or -1), compute the "offset" — the value `x` would have
    /// if `y` were zero (i.e., `row.constant - sum_of_fixed_contributions`).
    ///
    /// When two rows share the same `(y, y_sign)` and have the same offset, we can
    /// deduce `x1 = x2` since both equal `-y_sign * y + offset`.
    ///
    /// Reference: `reference/z3/src/math/lp/lp_bound_propagator.h:357-418`
    pub(crate) fn discover_offset_equalities(&mut self, rows_to_scan: &HashSet<usize>) {
        // Temporary table: (y_var, y_sign) → HashMap<offset → (row_idx, base_var)>
        // We use a HashMap keyed by (y_var, i8_sign) → Vec<(offset, row_idx, base_var)>
        // and do pairwise matching within each bucket.
        struct RowInfo {
            offset: Rational,
            base_var: u32,
            row_idx: usize,
        }

        // Map: (y_var, y_sign: i8) → list of (offset, base_var, row_idx)
        let mut buckets: HashMap<(u32, i8), Vec<RowInfo>> = HashMap::new();
        let num_vars = self.vars.len();

        for &row_idx in rows_to_scan {
            if row_idx >= self.rows.len() {
                continue;
            }
            let row = &self.rows[row_idx];
            let base_var = row.basic_var;
            let bv = base_var as usize;
            if bv >= num_vars {
                continue;
            }

            // Check if base var is fixed — if so, skip (nf would be 0 or handled by nf==1 path)
            if self.is_var_fixed_for_offset_eq(base_var) {
                continue;
            }

            // Skip rows with Big coefficients (same guard as compute_implied_bounds)
            if row
                .coeffs
                .iter()
                .any(|(_, c)| matches!(c, Rational::Big(_)))
            {
                continue;
            }

            // Count non-fixed non-basic columns, identify the single non-fixed one
            let mut nf = 1u32; // base var is non-fixed (checked above), counts as 1
            let mut y_var: Option<u32> = None;
            let mut y_sign: i8 = 0;
            let mut offset = row.constant.clone();
            let mut too_many = false;

            for &(var, ref coeff) in &row.coeffs {
                let vi = var as usize;
                if vi >= num_vars {
                    too_many = true;
                    break;
                }
                if self.is_var_fixed_for_offset_eq(var) {
                    // Fixed column: subtract its contribution from the offset.
                    // Row equation: base_var = Σ(coeff_j * x_j) + constant
                    // For a fixed variable with value `v`, contribution = coeff * v
                    if let Some(fixed_val) = self.get_fixed_value(var) {
                        offset = &offset - &(&fixed_val * coeff);
                    } else {
                        // Shouldn't happen if is_var_fixed returned true, but be safe
                        too_many = true;
                        break;
                    }
                } else {
                    nf += 1;
                    if nf > 2 {
                        too_many = true;
                        break;
                    }
                    y_var = Some(var);
                    // Check if coefficient is +1 or -1
                    if coeff.is_one() {
                        y_sign = 1;
                    } else if *coeff == Rational::Small(-1, 1) {
                        y_sign = -1;
                    } else {
                        // Coefficient not +/-1, can't do offset equality
                        too_many = true;
                        break;
                    }
                }
            }

            if too_many || nf != 2 || y_var.is_none() || y_sign == 0 {
                continue;
            }

            let y = y_var.unwrap();
            let bucket_key = (y, y_sign);
            buckets.entry(bucket_key).or_default().push(RowInfo {
                offset,
                base_var,
                row_idx,
            });
        }

        // Match within each bucket: rows with the same offset → equality
        for (_key, entries) in &buckets {
            if entries.len() < 2 {
                continue;
            }
            // Build an index from offset → first entry
            let mut offset_map: HashMap<Rational, usize> = HashMap::new(); // offset → index in entries
            for (idx, entry) in entries.iter().enumerate() {
                match offset_map.get(&entry.offset) {
                    None => {
                        offset_map.insert(entry.offset.clone(), idx);
                    }
                    Some(&prev_idx) => {
                        let prev = &entries[prev_idx];
                        // Check sort compatibility (both int or both real)
                        let sort_a = self.fixed_term_sort_key(entry.base_var);
                        let sort_b = self.fixed_term_sort_key(prev.base_var);
                        if sort_a != sort_b || sort_a.is_none() {
                            continue;
                        }
                        // Enqueue offset equality with row indices for reason construction.
                        // Unlike fixed-term equalities, the base vars are NOT fixed — the
                        // equality comes from row structure (shared non-fixed column y).
                        if entry.base_var != prev.base_var {
                            self.pending_offset_equalities.push((
                                entry.base_var,
                                prev.base_var,
                                entry.row_idx,
                                prev.row_idx,
                            ));
                        }
                    }
                }
            }
        }
    }

    /// Check if a variable is "fixed" for offset equality purposes.
    /// A variable is fixed if it has non-strict lower == upper bounds
    /// (from either direct bounds or implied bounds).
    #[inline]
    pub(crate) fn is_var_fixed_for_offset_eq(&self, var: u32) -> bool {
        let vi = var as usize;
        // Check implied bounds first (they may be tighter)
        if let Some((Some(lb), Some(ub))) = self.implied_bounds.get(vi) {
            if !lb.strict && !ub.strict && lb.value == ub.value {
                return true;
            }
        }
        // Check direct bounds
        if let Some(info) = self.vars.get(vi) {
            if let (Some(lower), Some(upper)) = (&info.lower, &info.upper) {
                if !lower.strict && !upper.strict && lower.value == upper.value {
                    return true;
                }
            }
        }
        false
    }

    /// Get the fixed value of a variable (for offset computation).
    /// Returns the non-strict bound value when lower == upper.
    #[inline]
    pub(crate) fn get_fixed_value(&self, var: u32) -> Option<Rational> {
        let vi = var as usize;
        // Check implied bounds first
        if let Some((Some(lb), Some(ub))) = self.implied_bounds.get(vi) {
            if !lb.strict && !ub.strict && lb.value == ub.value {
                return Some(lb.value.clone());
            }
        }
        // Check direct bounds
        if let Some(info) = self.vars.get(vi) {
            if let (Some(lower), Some(upper)) = (&info.lower, &info.upper) {
                if !lower.strict && !upper.strict && lower.value == upper.value {
                    return Some(lower.value.clone());
                }
            }
        }
        None
    }

    pub(crate) fn collect_fixed_term_var_reasons(&self, var_id: u32) -> Vec<TheoryLit> {
        let mut reasons = Vec::new();
        let mut seen_direct = HashSet::new();
        let vi = var_id as usize;

        if let Some(info) = self.vars.get(vi) {
            if let (Some(lower), Some(upper)) = (&info.lower, &info.upper) {
                if !lower.strict && !upper.strict && lower.value == upper.value {
                    for (term, value) in lower.reason_pairs().chain(upper.reason_pairs()) {
                        if term.is_sentinel() {
                            continue;
                        }
                        let lit = TheoryLit::new(term, value);
                        if seen_direct.insert(lit) {
                            reasons.push(lit);
                        }
                    }
                }
            }
        }

        if !reasons.is_empty() {
            return reasons;
        }

        if let Some((Some(lower), Some(upper))) = self.implied_bounds.get(vi) {
            if !lower.strict && !upper.strict && lower.value == upper.value {
                let mut seen_row = HashSet::new();
                let _ = self.collect_row_reasons_dedup(var_id, false, &mut reasons, &mut seen_row);
                let _ = self.collect_row_reasons_dedup(var_id, true, &mut reasons, &mut seen_row);
            }
        }

        reasons
    }

    pub(crate) fn take_pending_fixed_term_model_equalities(&mut self) -> Vec<ModelEqualityRequest> {
        let pending = std::mem::take(&mut self.pending_fixed_term_equalities);
        let mut requests = Vec::new();

        for (lhs_var, rhs_var) in pending {
            let (Some(&lhs_term), Some(&rhs_term)) = (
                self.var_to_term.get(&lhs_var),
                self.var_to_term.get(&rhs_var),
            ) else {
                continue;
            };
            if lhs_term == rhs_term || self.terms().sort(lhs_term) != self.terms().sort(rhs_term) {
                continue;
            }

            let pair = if lhs_term.0 < rhs_term.0 {
                (lhs_term, rhs_term)
            } else {
                (rhs_term, lhs_term)
            };
            if !self.propagated_equality_pairs.insert(pair) {
                continue;
            }

            let mut reasons = self.collect_fixed_term_var_reasons(lhs_var);
            let mut seen = reasons.iter().copied().collect::<HashSet<_>>();
            for lit in self.collect_fixed_term_var_reasons(rhs_var) {
                if seen.insert(lit) {
                    reasons.push(lit);
                }
            }

            if reasons.is_empty() {
                self.propagated_equality_pairs.remove(&pair);
                continue;
            }

            requests.push(ModelEqualityRequest {
                lhs: pair.0,
                rhs: pair.1,
                reason: reasons,
            });
        }

        requests.sort_by_key(|req| (req.lhs.0, req.rhs.0));
        requests
    }

    /// Materialize pending offset equalities into `ModelEqualityRequest`s.
    ///
    /// Offset equalities are derived from nf==2 rows sharing a non-fixed column.
    /// The reason is the union of all fixed-column bounds in both derivation rows.
    pub(crate) fn take_pending_offset_equalities(&mut self) -> Vec<ModelEqualityRequest> {
        let pending = std::mem::take(&mut self.pending_offset_equalities);
        let mut requests = Vec::new();
        let num_vars = self.vars.len();

        for (var1, var2, row_idx1, row_idx2) in pending {
            let (Some(&term1), Some(&term2)) =
                (self.var_to_term.get(&var1), self.var_to_term.get(&var2))
            else {
                continue;
            };
            if term1 == term2 || self.terms().sort(term1) != self.terms().sort(term2) {
                continue;
            }

            let pair = if term1.0 < term2.0 {
                (term1, term2)
            } else {
                (term2, term1)
            };
            if !self.propagated_equality_pairs.insert(pair) {
                continue;
            }

            // Construct reason: all fixed-column bounds in both rows.
            // Use collect_fixed_term_var_reasons per fixed column — it handles
            // both direct bounds AND implied-bounds-only variables correctly
            // (falls back to collect_row_reasons_dedup for implied bounds).
            let mut reasons = Vec::new();
            let mut seen = HashSet::new();
            for &ri in &[row_idx1, row_idx2] {
                if ri >= self.rows.len() {
                    continue;
                }
                let row = &self.rows[ri];
                for &(var, _) in &row.coeffs {
                    let vi = var as usize;
                    if vi >= num_vars {
                        continue;
                    }
                    if !self.is_var_fixed_for_offset_eq(var) {
                        continue;
                    }
                    let var_reasons = self.collect_fixed_term_var_reasons(var);
                    for lit in var_reasons {
                        if seen.insert(lit) {
                            reasons.push(lit);
                        }
                    }
                }
            }

            if reasons.is_empty() {
                self.propagated_equality_pairs.remove(&pair);
                continue;
            }

            requests.push(ModelEqualityRequest {
                lhs: pair.0,
                rhs: pair.1,
                reason: reasons,
            });
        }

        requests.sort_by_key(|req| (req.lhs.0, req.rhs.0));
        requests
    }

    /// Model-value-based equality detection (Z3's `assume_eqs`).
    ///
    /// After simplex finds a feasible model, group all shared (non-slack)
    /// variables by their current model value. For pairs with the same value,
    /// generate `ModelEqualityRequest`s so the SAT solver can try setting the
    /// corresponding equality atoms to true. This is a model-based *guess*,
    /// not a deduction — reasons are empty.
    ///
    /// This is critical for benchmarks with many real-variable equality
    /// comparisons (simple_startup, sc, uart families) where the SAT solver
    /// would otherwise blindly explore equality branches.
    ///
    /// Reference: Z3 `theory_lra.cpp` assume_eqs / random_update.
    pub(crate) fn discover_model_value_equalities(&mut self) -> Vec<ModelEqualityRequest> {
        // Collect (value, var_id, term_id) for shared variables.
        let mut entries: Vec<(&InfRational, u32, TermId)> = Vec::new();
        for (&var_id, &term_id) in &self.var_to_term {
            if self.slack_var_set.contains(&var_id) {
                continue;
            }
            let vi = var_id as usize;
            if vi >= self.vars.len() {
                continue;
            }
            entries.push((&self.vars[vi].value, var_id, term_id));
        }

        if entries.len() < 2 {
            return Vec::new();
        }

        // Sort by value, then by term_id for determinism.
        entries.sort_by(|a, b| a.0.cmp(b.0).then(a.2 .0.cmp(&b.2 .0)));

        let mut requests = Vec::new();
        let mut i = 0;
        while i < entries.len() {
            // Find the run of entries with the same value.
            let mut j = i + 1;
            while j < entries.len() && entries[j].0 == entries[i].0 {
                j += 1;
            }
            // entries[i..j] all have the same model value.
            if j - i >= 2 {
                // Anchor pattern: pair the first entry with each subsequent one.
                let anchor_term = entries[i].2;
                let anchor_sort = self.terms().sort(anchor_term);
                for k in (i + 1)..j {
                    let other_term = entries[k].2;
                    if anchor_term == other_term {
                        continue;
                    }
                    // Only pair same-sort variables.
                    if self.terms().sort(other_term) != anchor_sort {
                        continue;
                    }
                    let pair = if anchor_term.0 < other_term.0 {
                        (anchor_term, other_term)
                    } else {
                        (other_term, anchor_term)
                    };
                    if !self.propagated_equality_pairs.insert(pair) {
                        continue;
                    }
                    requests.push(ModelEqualityRequest {
                        lhs: pair.0,
                        rhs: pair.1,
                        reason: Vec::new(),
                    });
                }
            }
            i = j;
        }

        requests
    }
}
