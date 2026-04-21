// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arena locality compaction (CaDiCaL arenatype=3, #8030).
//!
//! After `reduce_db()` deletes learned clauses, reorder remaining clauses
//! in the arena by VMTF decision-queue order so clauses watched by the
//! same literal are contiguous in memory. This improves L1/L2 cache hit
//! rates during BCP.
//!
//! Algorithm: iterate VMTF queue (vmtf_last -> vmtf_prev), for each
//! variable visit both-polarity watch lists (likely_phase first), copy
//! referenced clauses to fresh arena. Sweep remaining live clauses.
//! Remap clause refs in-place in existing watch lists (preserving BCP
//! traversal order). Remap trail reasons and LRAT clause_ids.
//!
//! Reference: CaDiCaL collect.cpp:385-399, Kissat collect.c:213-275.

use super::*;
use crate::vsids::INVALID_VAR;

impl Solver {
    /// Returns true if arena garbage exceeds the compaction threshold.
    ///
    /// The VMTF queue is now maintained in both focused and stable modes
    /// (#8036), matching CaDiCaL's `bump_variable_queue` which runs
    /// unconditionally. Arena compaction can run in either mode.
    pub(super) fn should_compact_arena(&self) -> bool {
        self.arena.dead_words() > self.arena.len() / 4
    }

    /// Compact the clause arena in VMTF decision-queue order for cache locality.
    /// Reference: CaDiCaL collect.cpp:385-399 (arenatype=3).
    pub(super) fn compact_arena_locality(&mut self) {
        // Structural invariants: compaction requires a quiescent solver state.
        // Skip compaction (rather than panic) when BCP has pending work — this
        // can happen legitimately during reduce_db since learned clause deletion
        // doesn't drain the propagation queue.
        if self.qhead < self.trail.len() || self.pending_theory_conflict.is_some() {
            return;
        }

        // 1. Build clause visit order from VMTF queue + watch lists.
        let arena_len = self.arena.len();
        let mut ordered: Vec<u32> = Vec::new();
        let mut seen = vec![false; arena_len];

        // Walk VMTF queue: most-recently-bumped first, likely_phase first per variable.
        let mut var = self.vsids.vmtf_last();
        while var != INVALID_VAR {
            let var_idx = var as usize;
            // Two phases: likely first, then unlikely.
            let positive = self
                .phase
                .get(var_idx)
                .copied()
                .map_or(false, |p| p > 0);
            for &use_positive in &[true, false] {
                let phase = if use_positive { positive } else { !positive };
                let lit = if phase {
                    Literal::positive(Variable(var))
                } else {
                    Literal::negative(Variable(var))
                };
                let wl = self.watches.get_watches(lit);
                for i in 0..wl.len() {
                    if !wl.is_binary(i) {
                        let offset = wl.clause_ref(i).index();
                        if offset < arena_len && !seen[offset] && self.arena.is_active(offset) {
                            seen[offset] = true;
                            ordered.push(offset as u32);
                        }
                    }
                }
            }
            var = self.vsids.vmtf_prev_of(var);
        }

        // 2. Sweep remaining live clauses not reached via any watch list.
        for offset in self.arena.active_indices() {
            if !seen[offset] {
                ordered.push(offset as u32);
            }
        }

        if ordered.is_empty() {
            return;
        }

        // 3. Compact arena in computed order.
        let remap = self.arena.compact_reorder(&ordered);

        // 4. Remap clause refs in-place in existing watch lists.
        // Critical: this preserves watch list ordering, which determines BCP
        // traversal order and search trajectory. The previous clear-and-rebuild
        // approach destroyed this ordering, causing >6x regressions on some
        // benchmarks (Battleship-14-26: 3s → 20s+ timeout).
        // Reference: CaDiCaL collect.cpp:216-262 flush_watches().
        self.watches.remap_clause_refs(&remap);

        // Binary-first invariant is maintained incrementally by remap_clause_refs.
        self.watches.debug_assert_binary_first();

        // 4b. Refresh blocker literals to current watched literal.
        // After arena compaction, clause literals may have been reordered by
        // replace() or other inprocessing, making cached blockers stale. Stale
        // blockers cause unnecessary slow-path clause reads in BCP (the blocker
        // check fails, forcing the solver to load clause data from the arena).
        // CaDiCaL flush_watches() (collect.cpp:238-242) refreshes blockers here.
        self.refresh_blocker_literals();

        // 5. Remap trail reasons.
        // Assigned variables with reason clauses must have valid remapped offsets
        // (reason clauses are protected from deletion by reason_clause_marks).
        // Unassigned variables may have stale reason fields from backtrack-store
        // elimination (#6991) — clear these to NO_REASON to prevent stale offsets
        // from aliasing new clauses in the compacted arena.
        for (var_idx, vd) in self.var_data.iter_mut().enumerate() {
            if is_clause_reason(vd.reason) {
                let old = vd.reason as usize;
                if old < remap.len() && remap[old] != u32::MAX {
                    vd.reason = remap[old];
                } else if z4_prefetch::val_at(&self.vals, var_idx * 2) != 0 {
                    // Assigned variable with a deleted reason — this is a bug.
                    debug_assert!(
                        false,
                        "BUG: assigned variable {var_idx} has reason at deleted clause offset {old}"
                    );
                } else {
                    // Unassigned variable with stale reason — clear it.
                    vd.reason = NO_REASON;
                }
            }
        }

        // 6. Remap LRAT clause_ids side vector.
        if !self.cold.clause_ids.is_empty() {
            let old_ids = std::mem::take(&mut self.cold.clause_ids);
            let new_arena_len = self.arena.len();
            let mut new_ids = vec![0u64; new_arena_len];
            for &old_off in &ordered {
                let old_idx = old_off as usize;
                let new_off = remap[old_idx];
                if new_off != u32::MAX && old_idx < old_ids.len() {
                    let new_off_usize = new_off as usize;
                    if new_off_usize < new_ids.len() {
                        new_ids[new_off_usize] = old_ids[old_idx];
                    }
                }
            }
            self.cold.clause_ids = new_ids;
        }

        // 7. Invalidate reason_clause_marks epoch.
        // After remapping var_data[].reason (step 5), all arena offsets changed
        // but the epoch system still thinks marks are "clean" (synced == graph).
        // Without this bump, ensure_reason_clause_marks_current() would skip
        // the rebuild, leaving marks indexed by stale pre-compaction offsets.
        // This could cause a reason clause to be incorrectly deleted → trail
        // corruption → unsound results.
        self.bump_reason_graph_epoch();

        // 8. Remap learned_clause_trail (arena offsets for eager subsumption).
        self.cold.learned_clause_trail.retain_mut(|off| {
            let old = *off;
            if old < remap.len() && remap[old] != u32::MAX {
                *off = remap[old] as usize;
                true
            } else {
                false
            }
        });

        // 9. Remap original_clause_boundary.
        // After locality-aware reordering, original and learned clauses are
        // interleaved by VMTF order, so the single-offset boundary between
        // "all original below, all learned above" no longer holds. Set to
        // new arena length so the `idx >= boundary` guard in transred passes
        // all clauses through to the is_learned() check (always correct).
        self.cold.original_clause_boundary = self.arena.len();

        // 10. Invalidate JIT compiled formula — embedded arena offsets are stale.
        #[cfg(feature = "jit")]
        if self.has_compiled_formula() {
            self.invalidate_compiled_formula();
        }

        // 11. Shrink watch list capacities.
        self.watches.shrink_capacity();
    }

    /// Refresh blocker literals in all watch lists to match current watched
    /// literals in the arena.
    ///
    /// For each non-binary watcher in the watch list for literal `lit`, the
    /// blocker should be the OTHER watched literal of the clause (i.e., the
    /// one that is not `lit`). After inprocessing (vivification, subsumption,
    /// etc.) may have reordered clause literals, the cached blocker can become
    /// stale, causing unnecessary slow-path clause reads in BCP.
    ///
    /// Reference: CaDiCaL collect.cpp:238-242 (flush_watches blocker refresh).
    fn refresh_blocker_literals(&mut self) {
        for lit_idx in 0..self.watches.num_lists() {
            let lit = Literal::from_index(lit_idx);
            let mut wl = self.watches.get_watches_mut(lit);
            for i in 0..wl.len() {
                if wl.is_binary(i) {
                    continue;
                }
                let offset = wl.clause_ref(i).index();
                let clause_raw = wl.clause_raw(i);
                let (w0, w1) = self.arena.watched_literals(offset);
                // The blocker is the watched literal that is NOT this list's literal.
                let new_blocker = if w0 == lit { w1 } else { w0 };
                wl.set_entry(i, new_blocker.raw(), clause_raw);
            }
        }
    }
}
