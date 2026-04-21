// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! VSIDS variable selection heuristic with heap-based O(log n) selection
//!
//! This module provides VSIDS (Variable State Independent Decaying Sum) with
//! a binary max-heap for efficient variable selection.
//!
//! Design based on CaDiCaL's heap.hpp - maintains position mapping for
//! efficient update operations (decrease-key/increase-key).

#![allow(clippy::upper_case_acronyms)]

use crate::literal::Variable;

mod heap;
mod vmtf;

/// Invalid heap position marker (variable not in heap)
const INVALID_POS: u32 = u32::MAX;
/// Invalid variable marker (used for VMTF linked-list pointers)
pub(crate) const INVALID_VAR: u32 = u32::MAX;

// CHB constants (Liang et al., SAT 2016, Section 3.2).
const CHB_ALPHA_INIT: f64 = 0.4;
const CHB_ALPHA_MIN: f64 = 0.06;
const CHB_ALPHA_DECAY: f64 = 0.999_995;

/// VSIDS activity-based variable selection with heap
#[derive(Debug)]
pub(crate) struct VSIDS {
    /// Activity scores for each variable
    activities: Vec<f64>,
    /// Activity increment (grows on each decay)
    increment: f64,
    /// Decay factor
    decay: f64,
    /// Random seed for tie-breaking (affects initial perturbation)
    random_seed: u64,
    /// Bump order for each variable - higher means more recently bumped (VMTF)
    bump_order: Vec<u64>,
    /// Variables explicitly buried at the oldest end of the VMTF queue.
    ///
    /// Factorization uses zero activity to hide fresh extension variables from
    /// decisions. Focused mode needs an explicit guard as well because
    /// backtracking calls `vmtf_on_unassign`, which would otherwise move a
    /// buried variable back to the cursor.
    buried: Vec<bool>,
    /// Counter for bump ordering
    bump_counter: u64,

    // Heap data structures
    /// Binary max-heap of variable indices (ordered by activity)
    heap: Vec<u32>,
    /// Position of each variable in heap (INVALID_POS if not in heap)
    heap_pos: Vec<u32>,

    // CHB scoring (Liang et al., SAT 2016)
    /// Per-variable Q-scores for CHB heuristic.
    /// `None` until the first CHB bump — avoids 8 bytes/var allocation in
    /// LegacyCoupled mode where CHB is never used (#8121).
    chb_scores: Option<Vec<f64>>,
    /// Conflict number at which each variable was last bumped by CHB.
    /// `None` until the first CHB bump (lazy, same as `chb_scores`).
    chb_last_conflict: Option<Vec<u64>>,
    /// Current CHB learning rate.
    pub(crate) chb_alpha: f64,
    /// Global conflict counter for CHB reward computation.
    pub(crate) chb_conflicts: u64,
    /// Whether activities currently holds CHB scores (swapped for heap use).
    chb_loaded: bool,

    // VMTF decision queue (focused mode)
    /// Previous variable in bump-order list (towards older variables)
    vmtf_prev: Vec<u32>,
    /// Next variable in bump-order list (towards more recent variables)
    vmtf_next: Vec<u32>,
    /// Oldest variable in the queue
    vmtf_first: u32,
    /// Most recently bumped variable in the queue (front)
    vmtf_last: u32,
    /// Most recently bumped *unassigned* variable (used as starting point)
    vmtf_unassigned: u32,
    /// Bump timestamp of `vmtf_unassigned` at last update
    vmtf_unassigned_bumped: u64,
}

impl VSIDS {
    // ── Debug assertion helpers ──────────────────────────────────────

    /// O(n) check: every heap entry has a consistent position map entry and vice versa.
    #[cfg(debug_assertions)]
    fn debug_assert_heap_pos_consistent(&self) {
        for (pos, &var) in self.heap.iter().enumerate() {
            assert_eq!(
                self.heap_pos[var as usize], pos as u32,
                "BUG: heap_pos[{var}] = {} but heap[{pos}] = {var}",
                self.heap_pos[var as usize]
            );
        }
        for (var, &pos) in self.heap_pos.iter().enumerate() {
            if pos != INVALID_POS {
                assert!(
                    (pos as usize) < self.heap.len(),
                    "BUG: heap_pos[{var}] = {pos} but heap.len() = {}",
                    self.heap.len()
                );
                assert_eq!(
                    self.heap[pos as usize], var as u32,
                    "BUG: heap_pos[{var}] = {pos} but heap[{pos}] = {}",
                    self.heap[pos as usize]
                );
            }
        }
    }

    /// O(n) check: max-heap property holds for every parent-child pair.
    #[cfg(debug_assertions)]
    fn debug_assert_heap_property(&self) {
        for pos in 1..self.heap.len() {
            let parent = (pos - 1) / 2;
            let var = self.heap[pos] as usize;
            let parent_var = self.heap[parent] as usize;
            assert!(
                !self.var_less(var, parent_var),
                "BUG: heap property violated at pos {pos}: var {var} (act={}) > \
                 parent var {parent_var} (act={}) at pos {parent}",
                self.activities[var],
                self.activities[parent_var]
            );
        }
    }

    /// O(n) check: VMTF doubly-linked list is consistent (no cycles, correct
    /// forward/backward pointers, first/last sentinel values).
    #[cfg(debug_assertions)]
    fn debug_assert_vmtf_consistent(&self) {
        if self.vmtf_first == INVALID_VAR {
            assert_eq!(
                self.vmtf_last, INVALID_VAR,
                "BUG: vmtf_first is INVALID but vmtf_last = {}",
                self.vmtf_last
            );
            return;
        }
        assert_eq!(
            self.vmtf_prev[self.vmtf_first as usize], INVALID_VAR,
            "BUG: vmtf_first ({}) has non-INVALID prev = {}",
            self.vmtf_first, self.vmtf_prev[self.vmtf_first as usize]
        );
        assert_eq!(
            self.vmtf_next[self.vmtf_last as usize], INVALID_VAR,
            "BUG: vmtf_last ({}) has non-INVALID next = {}",
            self.vmtf_last, self.vmtf_next[self.vmtf_last as usize]
        );
        let mut count = 0usize;
        let mut cur = self.vmtf_first;
        while cur != INVALID_VAR {
            count += 1;
            assert!(
                count <= self.activities.len(),
                "BUG: VMTF cycle detected after {count} nodes (num_vars={})",
                self.activities.len()
            );
            let next = self.vmtf_next[cur as usize];
            if next != INVALID_VAR {
                assert_eq!(
                    self.vmtf_prev[next as usize], cur,
                    "BUG: vmtf_next[{cur}]={next} but vmtf_prev[{next}]={}",
                    self.vmtf_prev[next as usize]
                );
            } else {
                assert_eq!(
                    cur, self.vmtf_last,
                    "BUG: VMTF list ends at {cur} but vmtf_last = {}",
                    self.vmtf_last
                );
            }
            cur = next;
        }
    }

    /// Create a new VSIDS with n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        // Initialize bump_order so variables with lower indices are tried first initially
        // (same as CaDiCaL's init_queue)
        let mut bump_order = Vec::with_capacity(num_vars);
        for i in 0..num_vars {
            // Lower index = higher initial bump order (will be picked first)
            bump_order.push((num_vars - i) as u64);
        }

        // Initialize heap with all variables (all unassigned initially)
        // Variables are ordered by index initially (lower index = higher priority)
        let mut heap = Vec::with_capacity(num_vars);
        let mut heap_pos = vec![INVALID_POS; num_vars];
        for (i, pos) in heap_pos.iter_mut().enumerate().take(num_vars) {
            heap.push(i as u32);
            *pos = i as u32;
        }

        // Note: With zero initial activities, heap order doesn't matter much
        // The heap will reorganize as variables get bumped during solving

        // Initialize VMTF queue in index order, preferring smaller indices first.
        // The queue is a doubly linked list ordered by bump-recency where
        // `vmtf_last` is the most recently bumped (front).
        //
        // To pick smaller indices first initially, we build the initial order as:
        // (num_vars - 1) (oldest) -> ... -> 1 -> 0 (newest).
        let (vmtf_prev, vmtf_next, vmtf_first, vmtf_last, vmtf_unassigned, vmtf_unassigned_bumped) =
            if num_vars == 0 {
                (
                    Vec::new(),
                    Vec::new(),
                    INVALID_VAR,
                    INVALID_VAR,
                    INVALID_VAR,
                    0u64,
                )
            } else {
                let mut vmtf_prev = vec![INVALID_VAR; num_vars];
                let mut vmtf_next = vec![INVALID_VAR; num_vars];
                for i in 0..num_vars {
                    vmtf_prev[i] = if i + 1 < num_vars {
                        (i + 1) as u32
                    } else {
                        INVALID_VAR
                    };
                    vmtf_next[i] = if i > 0 { (i - 1) as u32 } else { INVALID_VAR };
                }
                let vmtf_first = (num_vars as u32) - 1;
                let vmtf_last = 0;
                let vmtf_unassigned = vmtf_last;
                let vmtf_unassigned_bumped = bump_order[vmtf_unassigned as usize];
                (
                    vmtf_prev,
                    vmtf_next,
                    vmtf_first,
                    vmtf_last,
                    vmtf_unassigned,
                    vmtf_unassigned_bumped,
                )
            };

        Self {
            activities: vec![0.0; num_vars],
            increment: 1.0,
            decay: 0.95,
            random_seed: 0,
            bump_order,
            buried: vec![false; num_vars],
            bump_counter: num_vars as u64 + 1,
            heap,
            heap_pos,
            chb_scores: None,
            chb_last_conflict: None,
            chb_alpha: CHB_ALPHA_INIT,
            chb_conflicts: 0,
            chb_loaded: false,
            vmtf_prev,
            vmtf_next,
            vmtf_first,
            vmtf_last,
            vmtf_unassigned,
            vmtf_unassigned_bumped,
        }
    }

    /// Ensure VSIDS has storage for `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let old_len = self.activities.len();
        if old_len < num_vars {
            self.activities.resize(num_vars, 0.0);
            self.heap_pos.resize(num_vars, INVALID_POS);
            self.vmtf_prev.resize(num_vars, INVALID_VAR);
            self.vmtf_next.resize(num_vars, INVALID_VAR);
            self.buried.resize(num_vars, false);
            if let Some(ref mut scores) = self.chb_scores {
                scores.resize(num_vars, 0.0);
            }
            if let Some(ref mut last) = self.chb_last_conflict {
                last.resize(num_vars, 0);
            }

            // New variables get increasing bump order
            for _ in old_len..num_vars {
                self.bump_order.push(self.bump_counter);
                self.bump_counter += 1;
            }

            // Add new variables to heap (they are unassigned)
            for i in old_len..num_vars {
                self.push_heap(i as u32);
            }

            // Add new variables to the VMTF queue (most recent/front).
            for i in old_len..num_vars {
                self.vmtf_enqueue(i as u32);
                // New variables are unassigned initially, so treat them as best candidate.
                self.vmtf_unassigned = i as u32;
                self.vmtf_unassigned_bumped = self.bump_order[i];
            }

            #[cfg(debug_assertions)]
            {
                self.debug_assert_heap_pos_consistent();
                self.debug_assert_vmtf_consistent();
            }
        }
    }

    /// Bump the activity of a variable.
    ///
    /// Updates both the VSIDS activity (for stable mode) and the
    /// VMTF bump order (for focused mode). The `vals` slice is needed
    /// to update the VMTF unassigned cursor when bumping an unassigned
    /// variable to the front of the queue.
    ///
    /// Reference: CaDiCaL `analyze.cpp:54-64` — after bumping, if the
    /// variable is unassigned, update `queue.unassigned` to point to it.
    /// Without this, the VMTF search cursor can get stuck behind the
    /// bumped variable, causing `pick_branching_variable_vmtf` to miss
    /// unassigned variables and falsely declare SAT.
    /// Bump a variable's priority in the active heuristic, always maintaining
    /// the VMTF queue for arena compaction.
    ///
    /// CaDiCaL `bump.cpp`: `bump_variable_score` (EVSIDS heap) runs only in
    /// stable mode, but `bump_variable_queue` (VMTF linked list) runs
    /// unconditionally in both modes. This keeps the VMTF queue current so
    /// arena locality compaction can use it as a clause visit order regardless
    /// of the active decision heuristic.
    #[inline]
    pub(crate) fn bump(&mut self, var: Variable, vals: &[i8], stable: bool) {
        if stable {
            self.bump_score(var);
        }
        self.bump_queue(var, vals); // Always maintain VMTF for arena compaction (#8036)
    }

    /// Decay all activities
    #[inline]
    pub(crate) fn decay(&mut self) {
        self.increment /= self.decay;
        // Proactive rescale: if increment exceeds the activity threshold,
        // rescale everything to prevent overflow to infinity (#5580).
        // Without this, decay() can push increment past f64::MAX before
        // bump() triggers the activity-based rescale check.
        if self.increment > 1e100 {
            self.rescale();
        }
        debug_assert!(
            self.increment.is_finite() && self.increment > 0.0,
            "BUG: increment became non-finite or non-positive after decay: {}",
            self.increment
        );
    }

    /// Get activity of a variable
    #[inline]
    pub(crate) fn activity(&self, var: Variable) -> f64 {
        self.activities[var.index()]
    }

    /// Get the current VSIDS activity increment.
    ///
    /// Used by `reset_search_state` to assign competitive activity scores
    /// to variables reactivated after BVE elimination (#7981).
    #[inline]
    pub(crate) fn current_increment(&self) -> f64 {
        self.increment
    }

    /// Set activity of a variable and update heap position.
    ///
    /// Zero activity has an extra meaning for factorization: the variable is
    /// also buried at the oldest end of the VMTF queue so focused-mode search
    /// does not immediately branch on fresh extension variables. This matches
    /// the intent of CaDiCaL's `queue.bury()` for factoring fresh vars
    /// (factor.cpp:769-839).
    #[inline]
    pub(crate) fn set_activity(&mut self, var: Variable, activity: f64) {
        let idx = var.index();
        debug_assert!(idx < self.activities.len());
        let old = self.activities[idx];
        self.activities[idx] = activity;
        if self.heap_pos[idx] != INVALID_POS {
            let pos = self.heap_pos[idx] as usize;
            if activity > old {
                self.sift_up(pos);
            } else if activity < old {
                self.sift_down(pos);
            }
        }

        if activity == 0.0 {
            self.buried[idx] = true;
            self.vmtf_bury_to_oldest(var);
            if self.vmtf_unassigned == idx as u32 {
                self.reset_vmtf_unassigned();
            }
        } else {
            self.buried[idx] = false;
        }
    }

    /// Rescale all activities to prevent overflow
    fn rescale(&mut self) {
        for act in &mut self.activities {
            *act *= 1e-100;
        }
        self.increment *= 1e-100;
        // Note: No need to restructure heap - relative ordering unchanged

        debug_assert!(
            self.increment.is_finite() && self.increment > 0.0,
            "BUG: increment is {}, expected positive finite after rescale",
            self.increment
        );
        debug_assert!(
            self.activities.iter().all(|a| a.is_finite()),
            "BUG: non-finite activity found after rescale"
        );
    }

    /// Get the bump order for a variable (for trail reuse comparison)
    #[inline]
    pub(crate) fn bump_order(&self, var: Variable) -> u64 {
        self.bump_order[var.index()]
    }

    /// Notify the VMTF queue that `var` became unassigned (during backtracking).
    ///
    /// This updates the "unassigned cursor" if this variable is more recently bumped
    /// than the current cursor (CaDiCaL's `update_queue_unassigned` logic).
    #[inline]
    pub(crate) fn vmtf_on_unassign(&mut self, var: Variable) {
        let idx = var.index();
        if self.buried[idx] {
            return;
        }
        let order = self.bump_order[idx];
        if self.vmtf_unassigned == INVALID_VAR || order > self.vmtf_unassigned_bumped {
            self.vmtf_unassigned = idx as u32;
            self.vmtf_unassigned_bumped = order;
        }
    }

    /// Reset VMTF cursor assuming all variables are unassigned.
    #[inline]
    pub(crate) fn reset_vmtf_unassigned(&mut self) {
        if self.vmtf_last == INVALID_VAR {
            self.vmtf_unassigned = INVALID_VAR;
            self.vmtf_unassigned_bumped = 0;
        } else {
            self.vmtf_unassigned = self.vmtf_last;
            self.vmtf_unassigned_bumped = self.bump_order[self.vmtf_unassigned as usize];
        }
    }

    // -- VMTF queue accessors for arena compaction --

    /// Most recently bumped variable (front of VMTF queue).
    /// Returns `INVALID_VAR` if the queue is empty.
    #[inline]
    pub(crate) fn vmtf_last(&self) -> u32 {
        self.vmtf_last
    }

    /// Previous variable in VMTF bump order (towards less recently bumped).
    /// Returns `INVALID_VAR` for end-of-list.
    #[inline]
    pub(crate) fn vmtf_prev_of(&self, var: u32) -> u32 {
        self.vmtf_prev[var as usize]
    }

    // -- Reorder support --

    /// Rebuild the VMTF queue in the order given by `vars_ascending`.
    ///
    /// Variables are moved to the front of the queue in the order they appear in
    /// the slice: the last variable in the slice ends up as `vmtf_last` (the most
    /// recently bumped, searched first). Callers should pass variables sorted by
    /// ascending score so the highest-score variables end up at the front.
    ///
    /// Reference: Kissat `reorder.c:162-173` — iterates sorted variables
    /// calling `move_to_front` so the last-moved (highest weight) is at front.
    ///
    /// `vals` is needed to update the VMTF unassigned cursor when bumping
    /// unassigned variables.
    pub(crate) fn reorder_vmtf_queue(&mut self, vars_ascending: &[u32], vals: &[i8]) {
        for &v in vars_ascending {
            let var = Variable(v);
            self.bump_queue(var, vals);
        }

        #[cfg(debug_assertions)]
        self.debug_assert_vmtf_consistent();
    }

    /// Add a weight to an EVSIDS activity score without going through the
    /// normal bump path. Used by stable-mode reorder (Kissat `reorder.c:176-196`)
    /// to fold clause weights into heap scores.
    pub(crate) fn add_to_activity(&mut self, var: Variable, weight: f64) {
        let idx = var.index();
        debug_assert!(idx < self.activities.len());
        let old = self.activities[idx];
        let new = old + weight;
        self.activities[idx] = new;
        if self.heap_pos[idx] != INVALID_POS {
            let pos = self.heap_pos[idx] as usize;
            if new > old {
                self.sift_up(pos);
            }
        }
    }

    // -- CHB methods --

    /// Lazily allocate CHB score arrays on first use.
    ///
    /// In LegacyCoupled mode (the default), CHB is never used and these
    /// arrays stay `None`, saving 16 bytes per variable (#8121).
    fn ensure_chb_arrays(&mut self) {
        let n = self.activities.len();
        if self.chb_scores.is_none() {
            self.chb_scores = Some(vec![0.0; n]);
            self.chb_last_conflict = Some(vec![0; n]);
        }
    }

    /// Read a variable CHB Q-score (respects swap state).
    #[cfg(test)]
    pub(crate) fn chb_score(&self, var: Variable) -> f64 {
        if self.chb_loaded {
            self.activities[var.index()]
        } else {
            self.chb_scores
                .as_ref()
                .map_or(0.0, |s| s[var.index()])
        }
    }

    /// Bump a variable CHB score using the exponential recency reward.
    #[inline]
    pub(crate) fn chb_bump(&mut self, var: Variable) {
        self.ensure_chb_arrays();
        let idx = var.index();
        let last_conflict = self.chb_last_conflict.as_ref().expect("ensured")[idx];
        let reward = 1.0 / (self.chb_conflicts.saturating_sub(last_conflict) + 1) as f64;
        let alpha = self.chb_alpha;
        if self.chb_loaded {
            self.activities[idx] = (1.0 - alpha).mul_add(self.activities[idx], alpha * reward);
            if self.heap_pos[idx] != INVALID_POS {
                self.sift_up(self.heap_pos[idx] as usize);
            }
        } else {
            let scores = self.chb_scores.as_mut().expect("ensured");
            scores[idx] = (1.0 - alpha).mul_add(scores[idx], alpha * reward);
        }
        self.chb_last_conflict.as_mut().expect("ensured")[idx] = self.chb_conflicts;
    }

    /// Advance the CHB conflict counter and decay the learning rate.
    #[inline]
    pub(crate) fn chb_on_conflict(&mut self) {
        self.chb_conflicts += 1;
        self.chb_alpha = (self.chb_alpha * CHB_ALPHA_DECAY).max(CHB_ALPHA_MIN);
    }

    /// Swap EVSIDS activities and CHB scores so the heap orders by CHB.
    pub(crate) fn swap_chb_scores(&mut self) {
        self.ensure_chb_arrays();
        let scores = self.chb_scores.as_mut().expect("ensured");
        std::mem::swap(&mut self.activities, scores);
        self.chb_loaded = !self.chb_loaded;
        self.rebuild_heap();
    }

    /// Reset CHB state (used on search reset / incremental solve).
    pub(crate) fn chb_reset(&mut self) {
        if self.chb_loaded {
            let scores = self.chb_scores.as_mut().expect("chb_loaded implies allocated");
            std::mem::swap(&mut self.activities, scores);
            self.chb_loaded = false;
        }
        if let Some(ref mut scores) = self.chb_scores {
            scores.fill(0.0);
        }
        if let Some(ref mut last) = self.chb_last_conflict {
            last.fill(0);
        }
        self.chb_alpha = CHB_ALPHA_INIT;
        self.chb_conflicts = 0;
    }

    /// Bump EVSIDS score for a variable while CHB is the active heuristic.
    #[inline]
    pub(crate) fn bump_evsids_score_dormant(&mut self, var: Variable) {
        let idx = var.index();
        debug_assert!(
            self.chb_loaded,
            "bump_evsids_score_dormant requires CHB loaded"
        );
        // chb_scores holds EVSIDS data when chb_loaded is true (swapped).
        let scores = self.chb_scores.as_mut().expect("chb_loaded implies allocated");
        scores[idx] += self.increment;
        if scores[idx] > 1e100 {
            self.rescale_dormant_evsids();
        }
    }

    /// Decay EVSIDS increment while CHB is active.
    #[inline]
    pub(crate) fn decay_evsids_dormant(&mut self) {
        debug_assert!(self.chb_loaded, "decay_evsids_dormant requires CHB loaded");
        self.increment /= self.decay;
        if self.increment > 1e100 {
            self.rescale_dormant_evsids();
        }
    }

    /// Rescale dormant EVSIDS scores (in chb_scores) to prevent overflow.
    fn rescale_dormant_evsids(&mut self) {
        if let Some(ref mut scores) = self.chb_scores {
            for score in scores.iter_mut() {
                *score *= 1e-100;
            }
        }
        self.increment *= 1e-100;
    }

    /// Heap-backed buffer bytes used by VSIDS state.
    ///
    /// Excludes the inline `VSIDS` struct itself so callers can count the
    /// parent solver shell exactly once.
    #[cfg(test)]
    pub(crate) fn buffer_bytes(&self) -> usize {
        use std::mem::size_of;

        fn packed_bool_vec_bytes(capacity: usize) -> usize {
            capacity.div_ceil(8)
        }

        self.activities.capacity() * size_of::<f64>()
            + self.bump_order.capacity() * size_of::<u64>()
            + packed_bool_vec_bytes(self.buried.capacity())
            + self.heap.capacity() * size_of::<u32>()
            + self.heap_pos.capacity() * size_of::<u32>()
            + self.chb_scores.as_ref().map_or(0, |v| v.capacity() * size_of::<f64>())
            + self.chb_last_conflict.as_ref().map_or(0, |v| v.capacity() * size_of::<u64>())
            + self.vmtf_prev.capacity() * size_of::<u32>()
            + self.vmtf_next.capacity() * size_of::<u32>()
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
