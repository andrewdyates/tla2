// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Maximum row width for touched-row bound analysis (#6617).
    /// Used by `compute_implied_bounds`. The Z3 reference (`bound_analyzer_on_row`)
    /// has no width cap; 300 is the current widened limit from #6615.
    pub(crate) const MAX_TOUCHED_ROW_BOUND_SCAN_WIDTH: usize = 300;

    pub(crate) fn fixed_term_sort_key(&self, var_id: u32) -> Option<bool> {
        let term = *self.var_to_term.get(&var_id)?;
        Some(matches!(self.terms().sort(term), Sort::Int))
    }

    pub(crate) fn fixed_term_key(&self, var_id: u32) -> Option<(BigRational, bool)> {
        let is_int = self.fixed_term_sort_key(var_id)?;
        let vi = var_id as usize;

        if let Some((Some(lb), Some(ub))) = self.implied_bounds.get(vi) {
            if !lb.strict && !ub.strict && lb.value == ub.value {
                return Some((lb.value.to_big(), is_int));
            }
        }

        let info = self.vars.get(vi)?;
        let (Some(lower), Some(upper)) = (&info.lower, &info.upper) else {
            return None;
        };
        if lower.strict || upper.strict || lower.value != upper.value {
            return None;
        }
        Some((lower.value_big(), is_int))
    }

    pub(crate) fn enqueue_pending_fixed_term_equality(&mut self, var_id: u32, representative: u32) {
        if var_id == representative {
            return;
        }
        if self
            .pending_fixed_term_equalities
            .iter()
            .any(|&(lhs, rhs)| lhs == var_id && rhs == representative)
        {
            return;
        }
        self.pending_fixed_term_equalities
            .push((var_id, representative));
    }

    pub(crate) fn reassign_fixed_term_representative(
        &mut self,
        key: &(BigRational, bool),
        removed_var: u32,
    ) {
        if self.fixed_term_value_table.get(key) != Some(&removed_var) {
            return;
        }

        self.fixed_term_value_table.remove(key);

        let replacement = self
            .fixed_term_value_members
            .iter()
            .find_map(|(&candidate, candidate_key)| (candidate_key == key).then_some(candidate));
        let Some(representative) = replacement else {
            return;
        };

        self.fixed_term_value_table
            .insert(key.clone(), representative);

        let followers = self
            .fixed_term_value_members
            .iter()
            .filter_map(|(&candidate, candidate_key)| {
                (candidate != representative && candidate_key == key).then_some(candidate)
            })
            .collect::<Vec<_>>();
        for candidate in followers {
            self.enqueue_pending_fixed_term_equality(candidate, representative);
        }
    }

    pub(crate) fn register_fixed_term_var(&mut self, var_id: u32) {
        let current_key = self.fixed_term_key(var_id);
        let previous_key = self.fixed_term_value_members.get(&var_id).cloned();

        if current_key == previous_key {
            if let Some(key) = current_key {
                self.fixed_term_value_table.entry(key).or_insert(var_id);
            }
            return;
        }

        if previous_key.is_some() {
            self.pending_fixed_term_equalities
                .retain(|(lhs, rhs)| *lhs != var_id && *rhs != var_id);
        }

        if let Some(old_key) = previous_key {
            self.fixed_term_value_members.remove(&var_id);
            self.reassign_fixed_term_representative(&old_key, var_id);
        }

        let Some(key) = current_key else {
            return;
        };

        let representative = self.fixed_term_value_table.get(&key).copied();
        self.fixed_term_value_members.insert(var_id, key.clone());

        match representative {
            Some(existing) if existing != var_id => {
                self.enqueue_pending_fixed_term_equality(var_id, existing);
            }
            _ => {
                self.fixed_term_value_table.insert(key, var_id);
            }
        }
    }
}
