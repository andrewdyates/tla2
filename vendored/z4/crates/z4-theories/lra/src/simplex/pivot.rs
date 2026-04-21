// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Find a suitable non-basic variable to pivot with (using Bland's rule)
    /// Returns (non_basic_var, direction) where direction is +1 or -1
    ///
    /// Bland's rule: to prevent cycling, always choose the eligible variable with
    /// the smallest index when there are ties. This guarantees termination.
    fn find_pivot_candidate(
        &self,
        row_idx: usize,
        violated_bound: BoundType,
    ) -> Option<(u32, i32)> {
        let row = &self.rows[row_idx];

        // Collect all eligible candidates, then pick smallest index (Bland's rule)
        let mut best: Option<(u32, i32)> = None;

        for &(nb_var, ref coeff) in &row.coeffs {
            if coeff.is_zero() {
                continue;
            }

            let info = &self.vars[nb_var as usize];

            // Skip basic variables that appear in coefficient lists (#4842).
            // After pivots rearrange the basis, incrementally-asserted rows
            // can reference variables that are now basic. Selecting a basic
            // variable as the entering pivot would violate the simplex invariant.
            if !matches!(info.status, Some(VarStatus::NonBasic)) {
                continue;
            }

            // Determine if we can increase or decrease this non-basic variable
            // based on its bounds. We can move if there's room (not at the bound).
            // Note: For strict bounds, being at the bound value is already a violation,
            // so we check if there's any room to move.
            let can_increase = match &info.upper {
                None => true,
                Some(b) => info.value.lt_bound(&b.value, b.strict, BoundType::Upper),
            };

            let can_decrease = match &info.lower {
                None => true,
                Some(b) => info.value.gt_bound(&b.value, b.strict, BoundType::Lower),
            };

            let direction = match violated_bound {
                BoundType::Lower => {
                    // Basic var is too small, need to increase it
                    // If coeff > 0: increase nb_var
                    // If coeff < 0: decrease nb_var
                    if coeff.is_positive() && can_increase {
                        Some(1)
                    } else if coeff.is_negative() && can_decrease {
                        Some(-1)
                    } else {
                        None
                    }
                }
                BoundType::Upper => {
                    // Basic var is too large, need to decrease it
                    // If coeff > 0: decrease nb_var
                    // If coeff < 0: increase nb_var
                    if coeff.is_positive() && can_decrease {
                        Some(-1)
                    } else if coeff.is_negative() && can_increase {
                        Some(1)
                    } else {
                        None
                    }
                }
            };

            if let Some(dir) = direction {
                // Bland's rule: keep the candidate with smallest variable index
                match &best {
                    None => best = Some((nb_var, dir)),
                    Some((best_var, _)) if nb_var < *best_var => best = Some((nb_var, dir)),
                    _ => {}
                }
            }
        }

        best
    }

    /// Find a beneficial entering variable using Z3's perturbation-minimizing
    /// heuristic for DPLL(T) feasibility search.
    ///
    /// Primary criterion: minimize `not_free_basic_dependent_vars` — the number
    /// of non-free basic variables in other rows that reference this column.
    /// This reduces cascading infeasibility from the pivot.
    /// Secondary: smallest column size (cheaper pivot update).
    /// Tiebreak: smallest variable index for determinism.
    ///
    /// Falls back to Bland when `bland_mode` is active (after repeated bases).
    ///
    /// Reference: Z3 `find_beneficial_entering_tableau_rows` in
    /// `lp_primal_core_solver.h:187-232`, `get_num_of_not_free_basic_dependent_vars`.
    pub(super) fn find_beneficial_entering(
        &mut self,
        row_idx: usize,
        violated_bound: BoundType,
    ) -> Option<(u32, i32)> {
        if self.bland_mode {
            return self.find_pivot_candidate(row_idx, violated_bound);
        }

        let row = &self.rows[row_idx];
        let basic_var = row.basic_var;

        // Score: (not_free_deps, col_size) — all minimized.
        // `tie_count` tracks how many candidates share the current best score,
        // for reservoir sampling tiebreak (Z3 simplex_def.h:575-580).
        let mut best: Option<(u32, i32, usize, usize)> = None;
        let mut tie_count: u32 = 0;

        for &(nb_var, ref coeff) in &row.coeffs {
            if coeff.is_zero() {
                continue;
            }

            let info = &self.vars[nb_var as usize];

            // Skip basic variables (#4842) — same guard as find_pivot_candidate.
            if !matches!(info.status, Some(VarStatus::NonBasic)) {
                continue;
            }

            let can_increase = match &info.upper {
                None => true,
                Some(b) => info.value.lt_bound(&b.value, b.strict, BoundType::Upper),
            };
            let can_decrease = match &info.lower {
                None => true,
                Some(b) => info.value.gt_bound(&b.value, b.strict, BoundType::Lower),
            };

            let direction = match violated_bound {
                BoundType::Lower => {
                    if coeff.is_positive() && can_increase {
                        Some(1)
                    } else if coeff.is_negative() && can_decrease {
                        Some(-1)
                    } else {
                        None
                    }
                }
                BoundType::Upper => {
                    if coeff.is_positive() && can_decrease {
                        Some(-1)
                    } else if coeff.is_negative() && can_increase {
                        Some(1)
                    } else {
                        None
                    }
                }
            };

            if let Some(dir) = direction {
                // Count non-free basic variables that depend on this column.
                // Z3: get_num_of_not_free_basic_dependent_vars (lp_primal_core_solver.h:147-160).
                // Use column index for O(col_size); fall back to 0 if unavailable.
                let best_nf = best.as_ref().map_or(usize::MAX, |b| b.2);
                let not_free_deps =
                    self.count_not_free_basic_deps(nb_var, basic_var, best_nf);
                let col_sz = self.col_size(nb_var);

                let is_strictly_better = match &best {
                    None => true,
                    Some((_, _, best_nfd, best_csz)) => {
                        not_free_deps < *best_nfd
                            || (not_free_deps == *best_nfd && col_sz < *best_csz)
                    }
                };
                if is_strictly_better {
                    best = Some((nb_var, dir, not_free_deps, col_sz));
                    tie_count = 1;
                } else if let Some((_, _, best_nfd, best_csz)) = &best {
                    // Tie: same (not_free_deps, col_size). Use reservoir sampling
                    // to pick uniformly at random among tied candidates.
                    // Reference: Z3 simplex_def.h:575-580.
                    if not_free_deps == *best_nfd && col_sz == *best_csz {
                        tie_count += 1;
                        let r = Self::pivot_xorshift32(&mut self.pivot_rng) % tie_count;
                        if r == 0 {
                            best = Some((nb_var, dir, not_free_deps, col_sz));
                        }
                    }
                }
            }
        }

        best.map(|(var, dir, _, _)| (var, dir))
    }

    /// Xorshift32 PRNG for pivot tiebreaking. Fast, minimal state.
    #[inline]
    fn pivot_xorshift32(state: &mut u32) -> u32 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        *state = x;
        x
    }

    /// Count non-free basic variables in other rows that depend on column `nb_var`,
    /// excluding the row containing `excluded_basic`. Stops early when count
    /// exceeds `bound` (the current best), avoiding full column scan.
    ///
    /// Reference: Z3 `get_num_of_not_free_basic_dependent_vars`
    /// (lp_primal_core_solver.h:147-160).
    fn count_not_free_basic_deps(&self, nb_var: u32, excluded_basic: u32, bound: usize) -> usize {
        let vi = nb_var as usize;
        if vi >= self.col_index.len() || self.col_index[vi].is_empty() {
            // No column index: conservative estimate — treat as expensive.
            return bound;
        }
        let mut count = 0usize;
        for &row_idx in &self.col_index[vi] {
            let basic = self.rows[row_idx].basic_var;
            if basic == excluded_basic {
                continue;
            }
            let bi = basic as usize;
            if bi < self.vars.len() {
                let basic_info = &self.vars[bi];
                let is_free = basic_info.lower.is_none() && basic_info.upper.is_none();
                if !is_free {
                    count += 1;
                    if count > bound {
                        return count; // early exit
                    }
                }
            }
        }
        count
    }

    /// Ensure column index is large enough for variable `var`.
    fn ensure_col_index(&mut self, var: u32) {
        let vi = var as usize;
        if vi >= self.col_index.len() {
            self.col_index.resize(vi + 1, Vec::new());
        }
    }

    /// Remove `row_idx` from `col_index[var]`.
    fn col_index_remove(&mut self, var: u32, row_idx: usize) {
        let vi = var as usize;
        if vi < self.col_index.len() {
            if let Some(pos) = self.col_index[vi].iter().position(|&r| r == row_idx) {
                self.col_index[vi].swap_remove(pos);
            }
        }
    }

    /// Add `row_idx` to `col_index[var]`.
    pub(crate) fn col_index_add(&mut self, var: u32, row_idx: usize) {
        self.ensure_col_index(var);
        let vi = var as usize;
        debug_assert!(
            !self.col_index[vi].contains(&row_idx),
            "BUG: col_index[{var}] already contains row {row_idx}"
        );
        self.col_index[vi].push(row_idx);
    }

    /// Get the column size (number of rows containing this variable).
    /// Returns 0 if the variable has no column index entry.
    fn col_size(&self, var: u32) -> usize {
        let vi = var as usize;
        if vi < self.col_index.len() {
            self.col_index[vi].len()
        } else {
            0
        }
    }

    /// Pop the last row and clean up column index entries.
    /// Used by optimization.rs for temporary objective rows.
    pub(crate) fn pop_row_with_col_cleanup(&mut self) {
        if let Some(row) = self.rows.pop() {
            let popped_idx = self.rows.len(); // index of the removed row
            for &(v, _) in &row.coeffs {
                self.col_index_remove(v, popped_idx);
            }
        }
    }

    /// Perform a pivot operation
    pub(crate) fn pivot(&mut self, row_idx: usize, entering_var: u32) {
        debug_assert!(
            row_idx < self.rows.len(),
            "BUG: pivot row {} out of bounds (rows={})",
            row_idx,
            self.rows.len()
        );
        debug_assert!(
            (entering_var as usize) < self.vars.len(),
            "BUG: pivot entering var {} out of bounds (vars={})",
            entering_var,
            self.vars.len()
        );
        debug_assert!(
            matches!(
                self.vars[entering_var as usize].status,
                Some(VarStatus::NonBasic)
            ),
            "BUG: pivot entering var {} must be non-basic, got {:?}",
            entering_var,
            self.vars[entering_var as usize].status
        );
        let leaving_var = self.rows[row_idx].basic_var;
        trace!(
            target: "z4::lra",
            row_idx,
            entering_var,
            leaving_var,
            "LRA pivot start"
        );

        // Get coefficient of entering variable in the row via coeff_ref + clone
        // to avoid redundant binary search in coeff().
        let entering_coeff = self.rows[row_idx]
            .coeff_ref(entering_var)
            .cloned()
            .unwrap_or_else(Rational::zero);

        // Invariant: caller should only select entering variables with non-zero coefficient.
        // Keep this as a hard assertion so release builds do not silently continue
        // with invalid tableau state.
        assert!(
            !entering_coeff.is_zero(),
            "BUG: pivot called with zero coefficient for entering variable {entering_var} in row {row_idx}"
        );

        // Capture old row variables for column index update (only if col_index is populated)
        let old_pivot_row_vars: Vec<u32> = if !self.col_index.is_empty() {
            self.rows[row_idx].coeffs.iter().map(|(v, _)| *v).collect()
        } else {
            Vec::new()
        };

        // Rearrange: leaving_var = ... + entering_coeff * entering_var + ...
        // => entering_var = (leaving_var - ... - ...) / entering_coeff

        // Build new row for entering_var: use recip() to avoid Rational::one()
        // allocation + division overhead.
        let inv_coeff = entering_coeff.recip();
        let neg_inv_coeff = -inv_coeff.clone();

        let mut new_coeffs: Vec<(u32, Rational)> = Vec::new();

        // Add leaving_var with coefficient 1/entering_coeff
        new_coeffs.push((leaving_var, inv_coeff));

        // Add other variables with negated scaled coefficients
        for &(v, ref c) in &self.rows[row_idx].coeffs {
            if v != entering_var {
                let new_c = c * &neg_inv_coeff;
                if !new_c.is_zero() {
                    new_coeffs.push((v, new_c));
                }
            }
        }

        let new_constant = &self.rows[row_idx].constant * &neg_inv_coeff;

        // Update the row
        self.rows[row_idx] = TableauRow::new_rat(entering_var, new_coeffs, new_constant);

        // Update column index for the pivot row itself:
        // Remove old variable entries, add new ones
        let use_col_index = !self.col_index.is_empty();
        if use_col_index {
            for &v in &old_pivot_row_vars {
                self.col_index_remove(v, row_idx);
            }
            let new_row_vars: Vec<u32> =
                self.rows[row_idx].coeffs.iter().map(|&(v, _)| v).collect();
            for v in new_row_vars {
                self.col_index_add(v, row_idx);
            }
        }

        // Update variable statuses
        self.vars[leaving_var as usize].status = Some(VarStatus::NonBasic);
        self.vars[entering_var as usize].status = Some(VarStatus::Basic(row_idx));

        // Update basic_var_to_row: leaving_var is no longer basic, entering_var takes the row
        self.basic_var_to_row.remove(&leaving_var);
        self.basic_var_to_row.insert(entering_var, row_idx);

        // Clone the new row data for substitution to avoid borrow conflicts
        let new_row_coeffs = self.rows[row_idx].coeffs.clone();
        let new_row_constant = self.rows[row_idx].constant.clone();

        // Substitute in all other rows that contain entering_var.
        // Use column index for O(nnz) instead of O(rows) scan (#4919 Phase 1).
        // Fall back to full scan if column index is not populated.
        let evi = entering_var as usize;
        let use_col_index = !self.col_index.is_empty();
        let affected_rows: Vec<usize> = if use_col_index && evi < self.col_index.len() {
            self.col_index[evi]
                .iter()
                .copied()
                .filter(|&i| i != row_idx)
                .collect()
        } else if use_col_index {
            // Column index exists but entering_var has no entry — no rows affected
            Vec::new()
        } else {
            // No column index — fall back to scanning all rows
            (0..self.rows.len()).filter(|&i| i != row_idx).collect()
        };

        // Approach D (#4919): track pivot-affected rows for bound propagation.
        // Z3's pivot_column_tableau inserts every modified row into m_touched_rows
        // (lp_core_solver_base_def.h:285). This feeds compute_implied_bounds with
        // rows where the bound analyzer may now succeed after pivoting.
        self.touched_rows.insert(row_idx);

        // Reusable scratch buffers for column-index deltas (#8003).
        // substitute_var_with_col_deltas tracks additions/removals during the
        // sorted merge itself, eliminating O(new_row_width * log(row_width))
        // post-hoc binary searches per affected row.
        let mut col_added: Vec<u32> = Vec::new();
        let mut col_removed: Vec<u32> = Vec::new();

        for i in affected_rows {
            // Use coeff_ref + clone to avoid the zero-returning clone path in coeff().
            let old_coeff = match self.rows[i].coeff_ref(entering_var) {
                Some(c) if !c.is_zero() => c.clone(),
                _ => continue,
            };
            // Track this row as pivot-modified (#4919 Approach D).
            self.touched_rows.insert(i);

            if use_col_index {
                // Substitute entering_var with scaled new_row, tracking column-index
                // deltas during the merge pass itself (#8003). Eliminates all post-hoc
                // binary searches from the previous implementation (#6194 Finding 2).
                self.rows[i].substitute_var_with_col_deltas(
                    entering_var,
                    &new_row_coeffs,
                    &old_coeff,
                    &mut col_added,
                    &mut col_removed,
                );
            } else {
                // No column index — use plain substitute_var
                self.rows[i].substitute_var(entering_var, &new_row_coeffs, &old_coeff);
            }

            // Update constant: fast-path for ±1 old_coeff (common in sparse LRA).
            if old_coeff.is_one() {
                self.rows[i].constant += &new_row_constant;
            } else if old_coeff.is_neg_one() {
                self.rows[i].constant -= &new_row_constant;
            } else {
                self.rows[i].constant += &new_row_constant * &old_coeff;
            }

            // Apply column-index deltas computed during the merge (#8003).
            if use_col_index {
                for &v in &col_removed {
                    self.col_index_remove(v, i);
                }
                for &v in &col_added {
                    self.col_index_add(v, i);
                }
            }
        }

        // entering_var is now basic (in its own row) — remove it from col_index
        // entries of other rows (should already be handled above), and remove
        // row_idx from entering_var's column (it's the basic var, not a coefficient)
        if use_col_index {
            self.col_index_remove(entering_var, row_idx);
        }

        debug_assert_eq!(
            self.rows[row_idx].basic_var, entering_var,
            "BUG: pivot did not install entering var {entering_var} as row {row_idx} basic var"
        );
        debug_assert!(
            self.rows[row_idx].coeff(entering_var).is_zero(),
            "BUG: pivot row {row_idx} still has entering var {entering_var} coefficient"
        );
        #[cfg(debug_assertions)]
        self.debug_assert_tableau_consistency("pivot");
        #[cfg(debug_assertions)]
        if use_col_index {
            self.debug_assert_col_index_consistency("pivot");
        }
        debug!(
            target: "z4::lra",
            row_idx,
            entering_var,
            leaving_var,
            row_non_basic_terms = self.rows[row_idx].coeffs.len(),
            "LRA pivot complete"
        );
    }
}
