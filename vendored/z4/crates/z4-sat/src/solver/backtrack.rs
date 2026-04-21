// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backtracking with chronological reimplication and phase saving.

use super::*;

impl Solver {
    /// Backtrack to the given level with phase saving and target/best updates.
    ///
    /// Implements lazy reimplication for chronological backtracking:
    /// - Literals at levels <= target_level are kept on the trail (out of order)
    /// - Only literals at levels > target_level are unassigned
    /// - Phase saving: when a variable is unassigned, we save its polarity
    /// - Target/best phase saving: if we reached a longer trail, save the phases
    ///
    /// REQUIRES: target_level <= decision_level (or no-op)
    /// ENSURES: decision_level == target_level, trail_lim.len() == target_level,
    ///          no variable assigned at level > target_level,
    ///          qhead <= trail.len(), no_conflict_until <= trail.len()
    pub(super) fn backtrack(&mut self, target_level: u32) {
        self.backtrack_core(target_level, true);
    }

    /// Backtrack to the given level without updating phase saving.
    ///
    /// Used during vivification where decisions are artificial and should not
    /// corrupt the phase heuristic. Same as `backtrack()` but skips:
    /// - Phase saving (no `self.phase[...] = ...`)
    /// - Target/best phase updates
    pub(super) fn backtrack_without_phase_saving(&mut self, target_level: u32) {
        self.backtrack_core(target_level, false);
    }

    /// Core backtracking: compact the trail, unassign variables above target_level.
    ///
    /// When `save_phases` is true (normal CDCL), captures target/best phases and
    /// saves each unassigned variable's polarity. When false (vivification),
    /// skips both to avoid corrupting heuristics with artificial decisions.
    ///
    /// Uses chronological backtracking with lazy reimplication: out-of-order
    /// literals at levels <= target are kept on the trail.
    fn backtrack_core(&mut self, target_level: u32, save_phases: bool) {
        // REQUIRES: target_level <= decision_level (callers must not request
        // backtrack to a level above the current one).
        debug_assert!(
            target_level <= self.decision_level,
            "BUG: backtrack to level {target_level} > decision_level {}",
            self.decision_level
        );

        if save_phases {
            self.update_target_and_best_phases();
        }

        if self.decision_level <= target_level {
            return;
        }

        let assigned_limit = if target_level == 0 {
            0
        } else {
            self.trail_lim[target_level as usize - 1]
        };
        // CaDiCaL backtrack.cpp:52: assigned_limit within trail bounds
        debug_assert!(
            assigned_limit <= self.trail.len(),
            "BUG: assigned_limit ({assigned_limit}) > trail.len() ({})",
            self.trail.len(),
        );

        // CaDiCaL clips propagated to control[new_level+1].trail = start of
        // the level ABOVE target. In-order target_level literals don't need
        // re-propagation; only out-of-order compacted literals from higher
        // levels do. Save this before trail_lim truncation (#6931).
        let next_level_start = self.trail_lim[target_level as usize];

        let mut write_pos = assigned_limit;
        let mut read_pos = assigned_limit;

        while read_pos < self.trail.len() {
            let lit = self.trail[read_pos];
            let var = lit.variable();
            let var_level = self.var_data[var.index()].level;

            if var_level > target_level {
                // CaDiCaL backtrack.cpp:11: trail literal must be true before unassign.
                debug_assert!(
                    z4_prefetch::val_at(&self.vals, lit.index()) > 0,
                    "BUG: unassigning non-true {lit:?}"
                );
                if save_phases {
                    // CaDiCaL backtrack.cpp:14: phases.saved[idx] = sign(lit)
                    // Use trail literal polarity directly — the literal on the
                    // trail IS the assigned polarity, so a vals[] read is
                    // redundant (#3758).
                    self.phase[var.index()] = lit.sign_i8();
                }
                // Clear both vals entries. Use var index arithmetic directly
                // to avoid Literal construction overhead (#3758).
                let base = var.index() * 2;
                z4_prefetch::val_set(&mut self.vals, base, 0);
                z4_prefetch::val_set(&mut self.vals, base + 1, 0);
                // CaDiCaL backtrack.cpp:10-30: unassign() only clears vals,
                // pushes to VSIDS heap, and updates VMTF queue. It does NOT
                // clear reason, trail_pos, or unit_proof_id. Stale values for
                // unassigned variables are never read — all reads go through
                // enqueue() which unconditionally sets fresh values.
                // probe_parent is probe-round metadata, not trail state.
                // probe() disables probing_mode before calling backtrack(0),
                // and the next probe round overwrites parents for every
                // implied literal it visits. Per-unassign clearing here is
                // dead release-mode work in the hot loop.
                debug_assert!(
                    !self.var_lifecycle.is_removed(var.index()),
                    "BUG: backtrack encountered removed variable {} on the trail",
                    var.index()
                );
                self.vsids.insert_into_heap(var);
                self.vsids.vmtf_on_unassign(var);
            } else {
                if write_pos != read_pos {
                    self.trail[write_pos] = lit;
                }
                self.var_data[var.index()].trail_pos = write_pos as u32;
                write_pos += 1;
            }
            read_pos += 1;
        }

        self.trail.truncate(write_pos);
        self.trail_lim.truncate(target_level as usize);
        self.decision_level = target_level;

        // Re-propagate out-of-order literals from chrono BT compaction.
        // CaDiCaL backtrack.cpp:152-155 clips propagated/propagated2 to
        // control[new_level+1].trail (= next_level_start), which is the
        // start of the compacted out-of-order region in the trail.
        // Previously clipped to write_pos, skipping re-propagation (#6931).
        self.qhead = self.qhead.min(next_level_start);
        #[cfg(feature = "jit")]
        {
            self.jit_qhead = self.jit_qhead.min(next_level_start);
        }
        self.no_conflict_until = self.no_conflict_until.min(next_level_start);
        self.bump_reason_graph_epoch(); // Reason edges cleared (#3518)
        self.debug_assert_backtrack_postconditions(target_level);
    }

    /// ENSURES: backtrack postconditions (TLA+ TypeInvariant mirror).
    #[inline]
    fn debug_assert_backtrack_postconditions(&self, target_level: u32) {
        debug_assert_eq!(
            self.decision_level, target_level,
            "backtrack: decision_level must equal target_level"
        );
        debug_assert_eq!(
            self.trail_lim.len(),
            target_level as usize,
            "backtrack: trail_lim.len() must equal target_level"
        );
        let trail_len = self.trail.len();
        debug_assert!(
            self.qhead <= trail_len,
            "backtrack: qhead ({}) > trail.len() ({trail_len})",
            self.qhead
        );
        debug_assert!(
            self.no_conflict_until <= trail_len,
            "backtrack: no_conflict_until ({}) > trail.len() ({trail_len})",
            self.no_conflict_until
        );
        // CaDiCaL backtrack.cpp:174: post-backtrack assigned count == trail length.
        // Sampled every 1024 conflicts: the O(num_vars) scan is too expensive to
        // run on every backtrack (caused 50x debug slowdown on schup-l2s, #4967).
        // After #3758 Phase 3, count assigned from vals[] (positive literal slots).
        #[cfg(debug_assertions)]
        if self.num_conflicts & 0x3ff == 0 {
            let assigned_count = (0..self.num_vars)
                .filter(|&v| self.vals[v * 2] != 0)
                .count();
            debug_assert_eq!(
                assigned_count, trail_len,
                "backtrack: post assigned count != trail.len()",
            );
        }
        // trail_lim monotonicity: entries must be strictly non-decreasing.
        // Violation indicates a bug in chronological backtracking or decision logic
        // that left trail_lim in an inconsistent state (#4172).
        #[cfg(debug_assertions)]
        for w in self.trail_lim.windows(2) {
            debug_assert!(
                w[0] <= w[1],
                "BUG: trail_lim not monotonic: trail_lim[..] contains {} > {}",
                w[0],
                w[1]
            );
        }
        // CaDiCaL backtrack.cpp:176: trail level bounds + active reason refs.
        #[cfg(debug_assertions)]
        {
            let check_reasons = trail_len <= 256 || self.num_conflicts & 0x3ff == 0;
            for &lit in &self.trail {
                let vi = lit.variable().index();
                let vd = self.var_data[vi];
                debug_assert!(
                    vd.level <= target_level,
                    "backtrack: trail lit {lit:?} at level {} > target {target_level}",
                    vd.level
                );
                if check_reasons && is_clause_reason(vd.reason) {
                    let r = ClauseRef(vd.reason);
                    debug_assert!(
                        self.arena.is_active(r.0 as usize),
                        "backtrack: trail lit {lit:?} has stale reason ClauseRef({})",
                        r.0
                    );
                }
            }
        }
    }
}
