// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Heap-backed EVSIDS operations.

use super::{INVALID_POS, VSIDS};
use crate::literal::Variable;

impl VSIDS {
    /// Set the random seed for tie-breaking.
    pub(crate) fn set_random_seed(&mut self, seed: u64) {
        self.random_seed = seed;
        if seed != 0 {
            let mut state = seed;
            for i in 0..self.activities.len() {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                self.activities[i] += (state as f64) * 1e-15;
            }
            self.rebuild_heap();
        }
    }

    /// Get the random seed.
    pub(crate) fn random_seed(&self) -> u64 {
        self.random_seed
    }

    /// VSIDS score bump (stable mode): increment activity and sift up in heap.
    /// CaDiCaL `analyze.cpp:105-125`.
    #[inline]
    pub(crate) fn bump_score(&mut self, var: Variable) {
        let idx = var.index();
        debug_assert!(
            idx < self.activities.len(),
            "BUG: bump_score variable {idx} out of range (num_vars={})",
            self.activities.len()
        );

        self.activities[idx] += self.increment;
        if self.activities[idx] > 1e100 {
            self.rescale();
        }

        debug_assert!(
            !self.activities[idx].is_nan(),
            "BUG: NaN activity for var {idx} after bump_score"
        );
        debug_assert!(
            self.activities[idx].is_finite(),
            "BUG: infinite activity for var {idx} after bump_score (rescale failed?)"
        );

        if self.heap_pos[idx] != INVALID_POS {
            self.sift_up(self.heap_pos[idx] as usize);
        }
    }

    /// Remove a variable from the heap (when assigned).
    #[inline]
    pub(crate) fn remove_from_heap(&mut self, var: Variable) {
        let idx = var.index();
        let pos = self.heap_pos[idx];
        if pos == INVALID_POS {
            return;
        }
        if pos == 0 {
            let _ = self.pop_heap_root();
            debug_assert_eq!(
                self.heap_pos[idx], INVALID_POS,
                "BUG: var {idx} still in heap_pos after pop_heap_root"
            );
            return;
        }

        let last_idx = self.heap.len() - 1;
        if pos as usize == last_idx {
            self.heap.pop();
            self.heap_pos[idx] = INVALID_POS;
        } else {
            let last_var = self.heap[last_idx] as usize;
            self.heap[pos as usize] = last_var as u32;
            self.heap_pos[last_var] = pos;
            self.heap.pop();
            self.heap_pos[idx] = INVALID_POS;

            self.sift_up(pos as usize);
            self.sift_down(self.heap_pos[last_var] as usize);
        }

        debug_assert_eq!(
            self.heap_pos[idx], INVALID_POS,
            "BUG: var {idx} still in heap_pos after remove_from_heap"
        );
    }

    /// Insert a variable into the heap (when unassigned during backtrack).
    #[inline]
    pub(crate) fn insert_into_heap(&mut self, var: Variable) {
        let idx = var.index();
        if self.heap_pos[idx] != INVALID_POS {
            return;
        }
        self.push_heap(idx as u32);
        debug_assert_ne!(
            self.heap_pos[idx], INVALID_POS,
            "BUG: var {idx} not in heap after insert_into_heap"
        );
    }

    /// Select next variable to branch on using VSIDS (highest activity).
    ///
    /// Performs lazy head pruning for assigned variables.
    #[inline]
    pub(crate) fn pick_branching_variable(&mut self, vals: &[i8]) -> Option<Variable> {
        while let Some(&top) = self.heap.first() {
            if vals[top as usize * 2] == 0 {
                return Some(Variable(top));
            }
            let _ = self.pop_heap_root();
        }
        None
    }

    /// Reset the heap to contain all variables (called on solver reset).
    pub(crate) fn reset_heap(&mut self) {
        let num_vars = self.activities.len();
        self.heap.clear();
        self.heap_pos.fill(INVALID_POS);

        for i in 0..num_vars {
            self.heap.push(i as u32);
            self.heap_pos[i] = i as u32;
        }

        self.rebuild_heap();
    }

    /// Fisher-Yates shuffle of EVSIDS heap scores for stable-mode rephasing.
    pub(crate) fn shuffle_scores(&mut self, rephase_count: u64) {
        let n = self.heap.len();
        if n <= 1 {
            return;
        }

        let mut rng = rephase_count
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        for i in (1..n).rev() {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
            let j = (rng >> 33) as usize % (i + 1);
            self.heap.swap(i, j);
        }

        self.increment = 1.0;
        for (rank, &var_idx) in self.heap.iter().enumerate() {
            self.activities[var_idx as usize] = rank as f64;
        }

        for (pos, &var_idx) in self.heap.iter().enumerate() {
            self.heap_pos[var_idx as usize] = pos as u32;
        }
        self.rebuild_heap();
    }

    /// Rebuild the heap from scratch (used after bulk activity changes).
    pub(super) fn rebuild_heap(&mut self) {
        if self.heap.len() <= 1 {
            return;
        }
        for i in (0..self.heap.len() / 2).rev() {
            self.sift_down(i);
        }

        #[cfg(debug_assertions)]
        {
            self.debug_assert_heap_property();
            self.debug_assert_heap_pos_consistent();
        }
    }

    /// Remove and return the heap root.
    #[inline]
    fn pop_heap_root(&mut self) -> Option<Variable> {
        let root = self.heap.first().copied()? as usize;
        self.heap_pos[root] = INVALID_POS;
        let tail = self.heap.pop().expect("non-empty heap");
        if !self.heap.is_empty() {
            self.heap[0] = tail;
            self.heap_pos[tail as usize] = 0;
            self.sift_down(0);
            debug_assert_eq!(
                self.heap_pos[self.heap[0] as usize], 0,
                "BUG: heap root position map inconsistent after pop"
            );
        }
        Some(Variable(root as u32))
    }

    /// Push a variable onto the heap and restore heap property.
    #[inline]
    pub(super) fn push_heap(&mut self, var_idx: u32) {
        debug_assert_eq!(
            self.heap_pos[var_idx as usize], INVALID_POS,
            "BUG: push_heap called for var {var_idx} already in heap at pos {}",
            self.heap_pos[var_idx as usize]
        );
        let pos = self.heap.len();
        self.heap.push(var_idx);
        self.heap_pos[var_idx as usize] = pos as u32;
        self.sift_up(pos);
    }

    /// Compare two variables for heap ordering.
    #[inline]
    #[allow(clippy::float_cmp)]
    pub(super) fn var_less(&self, var_a: usize, var_b: usize) -> bool {
        let act_a = self.activities[var_a];
        let act_b = self.activities[var_b];
        act_a > act_b || (act_a == act_b && var_a < var_b)
    }

    /// Sift up an element to restore heap property (after activity increase).
    #[inline]
    pub(super) fn sift_up(&mut self, mut pos: usize) {
        while pos > 0 {
            let parent = (pos - 1) / 2;
            let var = self.heap[pos] as usize;
            let parent_var = self.heap[parent] as usize;

            if !self.var_less(var, parent_var) {
                break;
            }

            self.heap[pos] = parent_var as u32;
            self.heap[parent] = var as u32;
            self.heap_pos[var] = parent as u32;
            self.heap_pos[parent_var] = pos as u32;
            pos = parent;
        }
    }

    /// Sift down an element to restore heap property.
    #[inline]
    pub(super) fn sift_down(&mut self, mut pos: usize) {
        loop {
            let left = 2 * pos + 1;
            let right = 2 * pos + 2;
            let mut largest = pos;

            let var = self.heap[pos] as usize;

            if left < self.heap.len() {
                let left_var = self.heap[left] as usize;
                if self.var_less(left_var, var) {
                    largest = left;
                }
            }

            if right < self.heap.len() {
                let right_var = self.heap[right] as usize;
                let largest_var = self.heap[largest] as usize;
                if self.var_less(right_var, largest_var) {
                    largest = right;
                }
            }

            if largest == pos {
                break;
            }

            let largest_var = self.heap[largest] as usize;
            self.heap[pos] = largest_var as u32;
            self.heap[largest] = var as u32;
            self.heap_pos[var] = largest as u32;
            self.heap_pos[largest_var] = pos as u32;
            pos = largest;
        }
    }
}
