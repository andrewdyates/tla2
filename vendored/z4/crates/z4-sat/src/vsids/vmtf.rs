// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! VMTF queue operations (maintained in both focused and stable modes).

use super::{INVALID_VAR, VSIDS};
use crate::literal::Variable;

impl VSIDS {
    /// Remap variable indices during variable compaction.
    pub(crate) fn compact(&mut self, map: &crate::solver::compact::VariableMap) {
        let new_n = map.new_num_vars;
        let mut new_activities = vec![0.0f64; new_n];
        let mut new_bump_order = vec![0u64; new_n];
        let mut new_buried = vec![false; new_n];
        // Only allocate new CHB arrays if they were already allocated (#8121).
        let mut new_chb_scores = self.chb_scores.as_ref().map(|_| vec![0.0f64; new_n]);
        let mut new_chb_last_conflict = self.chb_last_conflict.as_ref().map(|_| vec![0u64; new_n]);
        for (old, &new_idx) in map.old_to_new.iter().enumerate() {
            if new_idx != crate::solver::compact::UNMAPPED {
                let new = new_idx as usize;
                new_activities[new] = self.activities[old];
                new_bump_order[new] = self.bump_order[old];
                new_buried[new] = self.buried[old];
                if let Some(ref scores) = self.chb_scores {
                    if old < scores.len() {
                        new_chb_scores.as_mut().expect("mirrors source")[new] = scores[old];
                    }
                }
                if let Some(ref last) = self.chb_last_conflict {
                    if old < last.len() {
                        new_chb_last_conflict.as_mut().expect("mirrors source")[new] = last[old];
                    }
                }
            }
        }
        self.activities = new_activities;
        self.bump_order = new_bump_order;
        self.buried = new_buried;
        self.chb_scores = new_chb_scores;
        self.chb_last_conflict = new_chb_last_conflict;
        self.heap.clear();
        self.heap_pos = vec![super::INVALID_POS; new_n];
        for var in 0..new_n {
            self.push_heap(var as u32);
        }
        self.rebuild_heap();
        self.vmtf_prev = vec![INVALID_VAR; new_n];
        self.vmtf_next = vec![INVALID_VAR; new_n];
        self.vmtf_first = INVALID_VAR;
        self.vmtf_last = INVALID_VAR;
        self.vmtf_unassigned = INVALID_VAR;
        self.vmtf_unassigned_bumped = 0;
        if new_n > 0 {
            let mut vars_by_order: Vec<u32> = (0..new_n as u32).collect();
            vars_by_order.sort_by_key(|&v| self.bump_order[v as usize]);
            for (i, &var) in vars_by_order.iter().enumerate() {
                if i == 0 {
                    self.vmtf_first = var;
                    self.vmtf_prev[var as usize] = INVALID_VAR;
                } else {
                    let prev = vars_by_order[i - 1];
                    self.vmtf_prev[var as usize] = prev;
                    self.vmtf_next[prev as usize] = var;
                }
                self.vmtf_next[var as usize] = INVALID_VAR;
            }
            self.vmtf_last = *vars_by_order
                .last()
                .expect("invariant: vars_by_order non-empty when new_n > 0");
            self.vmtf_unassigned = self.vmtf_last;
            self.vmtf_unassigned_bumped = self.bump_order[self.vmtf_last as usize];
        }
    }

    /// VMTF queue bump (focused mode): update bump order and move to front.
    /// CaDiCaL `analyze.cpp:52-103`.
    #[inline]
    pub(super) fn bump_queue(&mut self, var: Variable, vals: &[i8]) {
        let idx = var.index();
        debug_assert!(
            idx < self.bump_order.len(),
            "BUG: bump_queue variable {idx} out of range (num_vars={})",
            self.bump_order.len()
        );

        self.bump_order[idx] = self.bump_counter;
        self.bump_counter += 1;

        self.vmtf_bump_to_front(var);

        if vals[idx * 2] == 0 {
            self.vmtf_unassigned = idx as u32;
            self.vmtf_unassigned_bumped = self.bump_order[idx];
        }
    }

    /// Select next variable to branch on using VMTF (most recently bumped).
    #[inline]
    #[cfg(test)]
    pub(crate) fn pick_branching_variable_vmtf(&mut self, vals: &[i8]) -> Option<Variable> {
        self.pick_branching_variable_vmtf_with_lifecycle(vals, &[])
    }

    /// VMTF branching with eliminated-variable skipping.
    pub(crate) fn pick_branching_variable_vmtf_with_lifecycle(
        &mut self,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
    ) -> Option<Variable> {
        if self.vmtf_unassigned == INVALID_VAR {
            if self.vmtf_last != INVALID_VAR {
                self.vmtf_unassigned = self.vmtf_last;
                self.vmtf_unassigned_bumped = self.bump_order[self.vmtf_last as usize];
            } else {
                return None;
            }
        }

        let mut idx = self.vmtf_unassigned;
        let mut searched = 0u64;

        while idx != INVALID_VAR
            && (vals[idx as usize * 2] != 0
                || (idx as usize) < var_states.len() && var_states[idx as usize].is_removed())
        {
            idx = self.vmtf_prev[idx as usize];
            searched += 1;
        }

        if idx == INVALID_VAR && self.vmtf_unassigned != self.vmtf_last {
            idx = self.vmtf_last;
            while idx != INVALID_VAR
                && (vals[idx as usize * 2] != 0
                    || (idx as usize) < var_states.len() && var_states[idx as usize].is_removed())
            {
                idx = self.vmtf_prev[idx as usize];
                searched += 1;
            }
        }

        if idx == INVALID_VAR {
            return None;
        }

        if searched > 0 {
            self.vmtf_unassigned = idx;
            self.vmtf_unassigned_bumped = self.bump_order[idx as usize];
        }

        Some(Variable(idx))
    }

    /// Fisher-Yates shuffle of VMTF queue for focused-mode rephasing.
    pub(crate) fn shuffle_queue(&mut self, rephase_count: u64) {
        let mut vars: Vec<u32> = Vec::new();
        let mut cur = self.vmtf_first;
        while cur != INVALID_VAR {
            vars.push(cur);
            cur = self.vmtf_next[cur as usize];
        }

        if vars.len() <= 1 {
            return;
        }

        let mut rng = rephase_count
            .wrapping_mul(6364136223846793005)
            .wrapping_add(7046029254386353131);
        for i in (1..vars.len()).rev() {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
            let j = (rng >> 33) as usize % (i + 1);
            vars.swap(i, j);
        }

        self.vmtf_first = INVALID_VAR;
        self.vmtf_last = INVALID_VAR;
        for (i, &var) in vars.iter().enumerate() {
            if i == 0 {
                self.vmtf_first = var;
                self.vmtf_prev[var as usize] = INVALID_VAR;
            } else {
                let prev = vars[i - 1];
                self.vmtf_prev[var as usize] = prev;
                self.vmtf_next[prev as usize] = var;
            }
            self.vmtf_next[var as usize] = INVALID_VAR;
        }
        if let Some(&last) = vars.last() {
            self.vmtf_last = last;
            self.vmtf_unassigned = last;
            self.vmtf_unassigned_bumped = self.bump_order[last as usize];
        }

        #[cfg(debug_assertions)]
        self.debug_assert_vmtf_consistent();
    }

    #[inline]
    fn vmtf_bump_to_front(&mut self, var: Variable) {
        let idx = var.0;
        if idx == INVALID_VAR {
            return;
        }
        self.buried[idx as usize] = false;
        if idx == self.vmtf_last {
            return;
        }
        self.vmtf_dequeue(idx);
        self.vmtf_enqueue(idx);
    }

    #[inline]
    pub(super) fn vmtf_bury_to_oldest(&mut self, var: Variable) {
        let idx = var.0;
        if idx == INVALID_VAR || idx == self.vmtf_first {
            return;
        }
        self.vmtf_dequeue(idx);
        self.vmtf_prepend(idx);
    }

    #[inline]
    fn vmtf_dequeue(&mut self, idx: u32) {
        debug_assert!(
            (idx as usize) < self.vmtf_prev.len(),
            "BUG: vmtf_dequeue({idx}) out of range"
        );
        let prev = self.vmtf_prev[idx as usize];
        let next = self.vmtf_next[idx as usize];
        if prev != INVALID_VAR {
            self.vmtf_next[prev as usize] = next;
        } else {
            debug_assert_eq!(
                self.vmtf_first, idx,
                "BUG: dequeue node {idx} has no prev but vmtf_first={}",
                self.vmtf_first
            );
            self.vmtf_first = next;
        }
        if next != INVALID_VAR {
            self.vmtf_prev[next as usize] = prev;
        } else {
            debug_assert_eq!(
                self.vmtf_last, idx,
                "BUG: dequeue node {idx} has no next but vmtf_last={}",
                self.vmtf_last
            );
            self.vmtf_last = prev;
        }
        self.vmtf_prev[idx as usize] = INVALID_VAR;
        self.vmtf_next[idx as usize] = INVALID_VAR;
    }

    #[inline]
    pub(super) fn vmtf_enqueue(&mut self, idx: u32) {
        debug_assert!(
            (idx as usize) < self.vmtf_prev.len(),
            "BUG: vmtf_enqueue({idx}) out of range"
        );
        if self.vmtf_last == INVALID_VAR {
            self.vmtf_first = idx;
            self.vmtf_last = idx;
            self.vmtf_prev[idx as usize] = INVALID_VAR;
            self.vmtf_next[idx as usize] = INVALID_VAR;
            return;
        }
        let last = self.vmtf_last;
        debug_assert_eq!(
            self.vmtf_next[last as usize], INVALID_VAR,
            "BUG: vmtf_last ({last}) has non-INVALID next = {}",
            self.vmtf_next[last as usize]
        );
        self.vmtf_prev[idx as usize] = last;
        self.vmtf_next[idx as usize] = INVALID_VAR;
        self.vmtf_next[last as usize] = idx;
        self.vmtf_last = idx;
    }

    #[inline]
    fn vmtf_prepend(&mut self, idx: u32) {
        debug_assert!(
            (idx as usize) < self.vmtf_prev.len(),
            "BUG: vmtf_prepend({idx}) out of range"
        );
        if self.vmtf_first == INVALID_VAR {
            self.vmtf_first = idx;
            self.vmtf_last = idx;
            self.vmtf_prev[idx as usize] = INVALID_VAR;
            self.vmtf_next[idx as usize] = INVALID_VAR;
            return;
        }
        let first = self.vmtf_first;
        debug_assert_eq!(
            self.vmtf_prev[first as usize], INVALID_VAR,
            "BUG: vmtf_first ({first}) has non-INVALID prev = {}",
            self.vmtf_prev[first as usize]
        );
        self.vmtf_prev[idx as usize] = INVALID_VAR;
        self.vmtf_next[idx as usize] = first;
        self.vmtf_prev[first as usize] = idx;
        self.vmtf_first = idx;
    }
}
