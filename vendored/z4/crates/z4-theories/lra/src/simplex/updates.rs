// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Compute how much to change a non-basic variable to fix a basic variable's bound violation.
    /// Returns the new value for the non-basic variable.
    pub(super) fn compute_update_amount(
        &self,
        row_idx: usize,
        nb_var: u32,
        violated_bound: BoundType,
    ) -> InfRational {
        let row = &self.rows[row_idx];
        let basic_var = row.basic_var;
        let basic_info = &self.vars[basic_var as usize];
        let nb_info = &self.vars[nb_var as usize];
        // Use coeff_ref to avoid cloning; clone only if non-zero.
        let coeff_ref = match row.coeff_ref(nb_var) {
            Some(c) if !c.is_zero() => c,
            _ => return InfRational::default(),
        };

        let target_basic = match violated_bound {
            BoundType::Lower => match &basic_info.lower {
                Some(b) => b.as_inf(BoundType::Lower),
                None => InfRational::default(),
            },
            BoundType::Upper => match &basic_info.upper {
                Some(b) => b.as_inf(BoundType::Upper),
                None => InfRational::default(),
            },
        };

        let basic_delta = &target_basic - &basic_info.value;
        // Use recip() instead of Rational::one() / coeff to avoid one() allocation
        // and intermediate temporary.
        let inv_coeff = coeff_ref.recip();
        let nb_target = &nb_info.value + &basic_delta.mul_rat(&inv_coeff);

        // Clamp to nb_var's bounds
        let clamped = if let Some(ref lb) = nb_info.lower {
            let lb_inf = lb.as_inf(BoundType::Lower);
            if nb_target < lb_inf {
                lb_inf
            } else {
                nb_target
            }
        } else {
            nb_target
        };
        if let Some(ref ub) = nb_info.upper {
            let ub_inf = ub.as_inf(BoundType::Upper);
            if clamped > ub_inf {
                ub_inf
            } else {
                clamped
            }
        } else {
            clamped
        }
    }
    /// Update a non-basic variable's value and propagate to basic variables.
    /// Uses column index when available for O(nnz) instead of O(rows) (#4919 Phase 1).
    /// After value propagation, updates the infeasible heap for affected basic vars
    /// (#4919 Phase B).
    pub(crate) fn update_nonbasic(&mut self, var: u32, new_val: InfRational) {
        let delta = &new_val - &self.vars[var as usize].value;
        if delta.is_zero() {
            return;
        }
        self.vars[var as usize].value = new_val;
        let vi = var as usize;
        if vi < self.col_index.len() && !self.col_index[vi].is_empty() {
            // Use column index: only visit rows containing `var`.
            // Iterate by index to avoid cloning the column index vector.
            let n = self.col_index[vi].len();
            for idx in 0..n {
                let row_idx = self.col_index[vi][idx];
                if let Some(coeff) = self.rows[row_idx].coeff_ref(var) {
                    let basic_var = self.rows[row_idx].basic_var;
                    let adj = delta.mul_rat(coeff);
                    self.vars[basic_var as usize].value += &adj;
                    // Update infeasible heap for this basic variable (#4919 Phase B)
                    self.track_var_feasibility(basic_var);
                }
            }
        } else {
            // Fallback: scan all rows (column index not yet populated).
            // Collect (basic_var, adjustment) pairs, apply, then track feasibility.
            let updates: Vec<(u32, InfRational)> = self
                .rows
                .iter()
                .filter_map(|row| {
                    row.coeff_ref(var)
                        .map(|coeff| (row.basic_var, delta.mul_rat(coeff)))
                })
                .collect();
            for &(basic_var, ref adj) in &updates {
                self.vars[basic_var as usize].value += adj;
            }
            for &(basic_var, _) in &updates {
                self.track_var_feasibility(basic_var);
            }
        }
    }

    pub(super) fn choose_nonbasic_fix_value(
        info: &VarInfo,
        violated_type: BoundType,
    ) -> Option<InfRational> {
        match violated_type {
            BoundType::Lower => Some(info.lower.as_ref()?.as_inf(BoundType::Lower)),
            BoundType::Upper => Some(info.upper.as_ref()?.as_inf(BoundType::Upper)),
        }
    }

    /// Convert a `BigRational` to `Rational64` if it fits, otherwise return `None`.
    pub(crate) fn bigrational_to_rational64(r: &BigRational) -> Option<num_rational::Rational64> {
        use num_traits::ToPrimitive;

        let numer = r.numer().to_i64()?;
        let denom = r.denom().to_i64()?;
        if denom == 0 {
            return None;
        }
        Some(num_rational::Rational64::new(numer, denom))
    }
}
