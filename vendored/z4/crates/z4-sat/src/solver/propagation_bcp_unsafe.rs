// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CaDiCaL-exact unsafe BCP (Boolean Constraint Propagation) using raw pointers.
//!
//! This module implements the same BCP algorithm as `propagation_bcp.rs` but
//! uses raw pointer arithmetic for watch list iteration and literal/val access,
//! matching CaDiCaL's `propagate.cpp:226-498` pattern exactly.
//!
//! Key differences from the safe version:
//! - In-place pointer iteration on the watch list (no deferred swap buffer)
//! - Raw `*const i8` for vals lookups (no bounds checks)
//! - Raw `*const u32` for arena literal access (no bounds checks)
//! - Prefetch after each enqueue
//!
//! # Safety
//!
//! All unsafe operations rely on the same invariants as the safe BCP:
//! - `Literal::index() < vals.len()` (2 * num_vars)
//! - Watch list entries reference valid clause offsets in the arena
//! - Clause offsets + HEADER_WORDS + literal_index < arena.words.len()
//! - The compaction invariant `j <= i <= end` holds throughout iteration
//!
//! Reference: CaDiCaL `src/propagate.cpp:226-498` (Armin Biere, MIT license).

// Allow unsafe in this module — the entire point is raw pointer BCP.
#![allow(unsafe_code)]
// Same as safe BCP: range loops needed for swap_literals calls.
#![allow(clippy::needless_range_loop)]

use super::*;
use crate::clause_arena::HEADER_WORDS;
use crate::solver::propagation::bcp_mode;
use crate::solver_log::solver_log;
use crate::watched::BINARY_FLAG;

impl Solver {
    /// CaDiCaL-exact BCP using raw pointer iteration.
    ///
    /// Semantically identical to `propagate_bcp::<MODE>()` but uses unsafe
    /// raw pointer arithmetic for the inner watch scan, val lookups, and
    /// arena literal access. This eliminates bounds checks and enables
    /// the compiler to keep hot pointers in registers throughout the loop.
    ///
    /// REQUIRES: qhead <= trail.len(), watches initialized for all clauses
    /// ENSURES: if None returned, qhead == trail.len() (all propagated);
    ///          if Some(cref), conflicting clause identified, qhead frozen
    #[inline]
    pub(super) fn propagate_bcp_unsafe<const MODE: u8>(&mut self) -> Option<ClauseRef> {
        debug_assert!(
            !self.has_empty_clause,
            "BUG: propagate_bcp_unsafe called with has_empty_clause=true"
        );
        if MODE != bcp_mode::PROBE {
            debug_assert!(
                !self.probing_mode,
                "BUG: propagate_bcp_unsafe (non-probe) called in probing mode"
            );
        }
        self.last_conflict_clause_ref = None;
        self.last_conflict_clause_id = 0;
        let qhead_start = self.qhead;
        let collect_bcp_telemetry = cfg!(debug_assertions);
        let mut ticks: u64 = 0;

        debug_assert!(
            self.qhead <= self.trail.len(),
            "BUG: propagate_bcp_unsafe entry qhead ({}) > trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );

        // Cache raw pointers for vals and arena words outside the outer loop.
        // These are stable for the duration of BCP (no reallocation occurs
        // during propagation — new clauses/vars are not added mid-BCP).
        let vals_ptr: *const i8 = self.vals.as_ptr();
        let words_ptr: *const u32 = self.arena.words().as_ptr();

        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            if MODE == bcp_mode::PROBE {
                solver_log!(self, "propagate {}", p.to_dimacs());
            }

            let false_lit = p.negated();

            // CaDiCaL pattern: get raw pointers into the watch list for
            // in-place iteration. `i` is the read pointer, `j` is the write
            // pointer (compaction). Both start at the beginning.
            let (ws_ptr, watch_len) = self.watches.get_watches_mut(false_lit).entries_raw_mut();
            // SAFETY: ws_ptr points to `watch_len` contiguous u64 entries.
            // We iterate with i in [0, watch_len) and write with j in [0, i].
            let end = watch_len;
            let mut i: usize = 0;
            let mut j: usize = 0;

            // CaDiCaL propagate.cpp:249: tick accounting
            ticks += 1 + (watch_len as u64).div_ceil(16);

            // CaDiCaL propagate.cpp:289-302: binary conflicts do NOT
            // immediately break — continue scanning binary watchers (#8043).
            let mut binary_conflict: Option<ClauseRef> = None;
            'watch: while i < end {
                // SAFETY: i < end = watch_len, so ws_ptr.add(i) is in bounds.
                // j <= i, so ws_ptr.add(j) is in bounds.
                let packed = unsafe { *ws_ptr.add(i) };
                let blocker_raw = packed as u32;
                i += 1;

                // Speculatively copy to write position (CaDiCaL: *j++ = *i++).
                // SAFETY: j < i <= end, so ws_ptr.add(j) is in bounds.
                unsafe { *ws_ptr.add(j) = packed };

                // Val lookup via raw pointer — no bounds check.
                // SAFETY: blocker_raw is a Literal::index() value, which is
                // < 2 * num_vars = vals.len() by the literal encoding invariant.
                let blocker_val: i8 = unsafe { *vals_ptr.add(blocker_raw as usize) };

                if blocker_val > 0 {
                    // Blocker satisfied — keep watcher, continue.
                    j += 1;
                    if collect_bcp_telemetry {
                        self.stats.bcp_blocker_fastpath_hits += 1;
                    }
                    continue 'watch;
                }

                let clause_raw = (packed >> 32) as u32;

                // Binary clause fast path.
                let is_binary = clause_raw & BINARY_FLAG != 0;
                if is_binary {
                    if collect_bcp_telemetry {
                        self.stats.bcp_binary_path_hits += 1;
                    }
                    let clause_ref = ClauseRef(clause_raw & !BINARY_FLAG);
                    if blocker_val < 0 {
                        // CaDiCaL propagate.cpp:289-290: record binary conflict
                        // but continue scanning binary watchers (#8043).
                        binary_conflict = Some(clause_ref);
                        j += 1;
                        continue 'watch;
                    }
                    // Unassigned — propagate, keep watcher.
                    ticks += 1;
                    j += 1;
                    if MODE == bcp_mode::PROBE
                        && self.probing_mode
                        && self.decision_level == 1
                    {
                        let propagated_var = Literal(blocker_raw).variable().index();
                        self.probe_parent[propagated_var] = Some(p);
                    }
                    // Jump reasons (#8034): in SEARCH mode at decision_level > 0
                    // with LRAT disabled. LRAT requires clause reasons for forward
                    // resolution chain collection — jump reasons lose the clause ID.
                    if MODE == bcp_mode::SEARCH
                        && self.decision_level > 0
                        && !self.cold.lrat_enabled
                    {
                        self.enqueue_binary_reason(Literal(blocker_raw), false_lit);
                    } else if MODE == bcp_mode::SEARCH {
                        self.enqueue_bcp(Literal(blocker_raw), clause_ref);
                        // Mark binary reason flag for non-jump path (#8034).
                        let prop_var = Literal(blocker_raw).variable().index();
                        self.var_data[prop_var].set_binary_reason(true);
                    } else {
                        self.enqueue(Literal(blocker_raw), Some(clause_ref));
                    }
                    continue 'watch;
                }

                // CaDiCaL propagate.cpp:301-302: stop at long clauses if
                // a binary conflict was already found (#8043).
                if binary_conflict.is_some() {
                    j += 1; // keep speculatively-copied watcher
                    break 'watch;
                }

                // Long clause path.
                let clause_idx = clause_raw as usize;
                let off = clause_idx;

                // Lookahead prefetch (#8000): prefetch the NEXT watcher's clause
                // arena data while we process the current long clause. Hides
                // ~60-80 cycles of main-memory latency per long clause access.
                if i < end {
                    // SAFETY: i < end = watch_len, so ws_ptr.add(i) is in bounds.
                    let next_packed = unsafe { *ws_ptr.add(i) };
                    let next_clause_raw = (next_packed >> 32) as u32;
                    if next_clause_raw & BINARY_FLAG == 0 {
                        // Prefetch arena data for next long clause using raw
                        // pointer arithmetic — no bounds check needed since
                        // prefetch on invalid addresses is silently ignored.
                        z4_prefetch::prefetch_read_l2(
                            unsafe { words_ptr.add(next_clause_raw as usize) },
                        );
                    }
                }

                // Read BCP header (garbage + vivify-skip + clause_len + saved_pos).
                let bcp_header = self.arena.bcp_header(off);
                if bcp_header.is_garbage_any() {
                    // Garbage — drop watcher (don't increment j).
                    continue 'watch;
                }
                if MODE != bcp_mode::SEARCH && bcp_header.is_vivify_skipped() {
                    j += 1;
                    continue 'watch;
                }
                ticks += 1;

                let clause_ref = ClauseRef(clause_raw);
                let clause_len = bcp_header.clause_len();
                let cached_saved_pos = bcp_header.saved_pos();

                // XOR trick for the other watched literal.
                // SAFETY: off + HEADER_WORDS + 0 and off + HEADER_WORDS + 1
                // are within arena bounds (clause has >= 2 literals).
                let lit0_raw = unsafe { *words_ptr.add(off + HEADER_WORDS) };
                let lit1_raw = unsafe { *words_ptr.add(off + HEADER_WORDS + 1) };
                let lit0 = Literal(lit0_raw);
                let lit1 = Literal(lit1_raw);

                debug_assert!(
                    lit0 == false_lit || lit1 == false_lit,
                    "BUG: watch list for {false_lit:?} contains clause {clause_idx} \
                     with watched lits {lit0:?}, {lit1:?} — neither matches"
                );
                let first = Literal(lit0_raw ^ lit1_raw ^ false_lit.0);
                // SAFETY: first.index() < vals.len() by literal invariant.
                let first_val: i8 = unsafe { *vals_ptr.add(first.index()) };

                let false_pos = usize::from(lit0 != false_lit);

                if first_val > 0 {
                    // Other watched literal satisfied — update blocker, keep watcher.
                    // SAFETY: j < i <= end, ws_ptr.add(j) in bounds.
                    unsafe {
                        *ws_ptr.add(j) =
                            (first.0 as u64) | ((clause_raw as u64) << 32);
                    }
                    j += 1;
                    continue 'watch;
                }

                // Replacement search (Gent saved position).
                debug_assert!(clause_len > 2);
                let mut pos = cached_saved_pos;
                if pos < 2 || pos >= clause_len {
                    pos = 2;
                }

                let mut replacement_k: usize = clause_len; // sentinel
                let mut replacement_val: i8 = -1;
                let mut replacement_lit = false_lit;

                // First scan: from saved_pos to end.
                for k in pos..clause_len {
                    if collect_bcp_telemetry {
                        self.stats.bcp_replacement_scan_steps += 1;
                    }
                    // SAFETY: off + HEADER_WORDS + k is within arena bounds
                    // (k < clause_len, clause was allocated with clause_len literals).
                    let lit_k_raw = unsafe { *words_ptr.add(off + HEADER_WORDS + k) };
                    // SAFETY: lit_k_raw is a valid Literal index < vals.len().
                    let v: i8 = unsafe { *vals_ptr.add(lit_k_raw as usize) };
                    if v >= 0 {
                        replacement_k = k;
                        replacement_val = v;
                        replacement_lit = Literal(lit_k_raw);
                        break;
                    }
                }
                // Second scan: from 2 to saved_pos (wrap-around).
                if replacement_val < 0 && pos > 2 {
                    for k in 2..pos {
                        if collect_bcp_telemetry {
                            self.stats.bcp_replacement_scan_steps += 1;
                        }
                        let lit_k_raw = unsafe { *words_ptr.add(off + HEADER_WORDS + k) };
                        let v: i8 = unsafe { *vals_ptr.add(lit_k_raw as usize) };
                        if v >= 0 {
                            replacement_k = k;
                            replacement_val = v;
                            replacement_lit = Literal(lit_k_raw);
                            break;
                        }
                    }
                }

                // Update saved position.
                if replacement_k != cached_saved_pos {
                    self.arena.set_saved_pos(off, replacement_k);
                }

                if replacement_val > 0 {
                    // Replacement satisfied — update blocker in watch entry.
                    // SAFETY: j < i <= end, ws_ptr.add(j) in bounds.
                    unsafe {
                        *ws_ptr.add(j) =
                            (replacement_lit.0 as u64) | ((clause_raw as u64) << 32);
                    }
                    j += 1;
                    continue 'watch;
                } else if replacement_val == 0 {
                    // Found unassigned replacement — move watch.
                    debug_assert!(
                        replacement_k >= 2 && replacement_k < clause_len,
                        "BUG: replacement index {replacement_k} outside [2, {clause_len})"
                    );
                    ticks += 1;
                    self.arena.swap_literals(off, false_pos, replacement_k);
                    // Defer watch addition to avoid cache pollution (#8041).
                    self.deferred_replacement_watches.push(
                        (replacement_lit, Watcher::new(clause_ref, first)),
                    );
                    // Drop this watcher (don't increment j).
                    continue 'watch;
                }

                // No replacement found — all tail literals false.
                debug_assert!(
                    (2..clause_len).all(|k| {
                        let lk = self.arena.literal(off, k);
                        self.lit_val(lk) < 0
                    }),
                    "BUG: no-replacement path but a tail literal is not false"
                );

                if first_val < 0 {
                    // Conflict — both watched literals false.
                    j += 1; // keep current watcher
                    self.unsafe_copy_remaining(ws_ptr, &mut j, i, end);
                    // SAFETY: j <= end. All entries in [0, j) are valid.
                    unsafe {
                        self.watches
                            .get_watches_mut(false_lit)
                            .set_len(j);
                    }
                    self.flush_bcp_ticks::<MODE>(ticks);
                    return Some(self.unsafe_conflict_finalize(
                        clause_ref,
                        qhead_start,
                    ));
                }

                // Unit propagation.
                let mut unit_reason = Some(clause_ref);

                // Probe HBR handling (same as safe version — delegates to helper).
                if MODE == bcp_mode::PROBE
                    && self.probing_mode
                    && self.decision_level == 1
                    && clause_len > 2
                {
                    self.handle_probe_hbr(
                        false_lit,
                        first,
                        clause_idx,
                        clause_len,
                        &mut unit_reason,
                    );
                }

                if MODE == bcp_mode::PROBE {
                    debug_assert!(
                        !self.probing_mode
                            || self.decision_level != 1
                            || clause_len <= 2
                            || self.probe_parent[first.variable().index()].is_some(),
                        "BUG: probe_parent missing for level-1 implied literal"
                    );
                }

                ticks += 1;
                j += 1;
                // Lightweight enqueue for SEARCH mode (#8042).
                if MODE == bcp_mode::SEARCH {
                    self.enqueue_bcp(first, unit_reason.expect("unit propagation always has reason"));
                } else {
                    self.enqueue(first, unit_reason);
                }
            }

            // Compaction complete: truncate the watch list to j entries.
            // When a binary conflict triggered a break at a long clause boundary,
            // copy remaining unvisited watchers first.
            if binary_conflict.is_some() && i < end {
                // SAFETY: both source [i..end) and dest [j..j+(end-i)) are
                // within the watch list buffer, and j <= i.
                unsafe {
                    let src = ws_ptr.add(i);
                    let dst = ws_ptr.add(j);
                    std::ptr::copy(src, dst, end - i);
                }
                j += end - i;
            }
            debug_assert!(
                j <= watch_len,
                "BCP unsafe: final j ({j}) > watch_len ({watch_len})"
            );
            // SAFETY: j <= watch_len = original length. All entries in [0, j)
            // were written by the loop above (either copied from the original
            // position or updated with new blocker values).
            unsafe {
                self.watches.get_watches_mut(false_lit).set_len(j);
            }

            // CaDiCaL propagate.cpp:289-302: if a binary conflict was found
            // during the binary watcher scan, finalize it now (#8043).
            if let Some(conflict_ref) = binary_conflict {
                self.flush_bcp_ticks::<MODE>(ticks);
                // Batch-invalidate reason graph epoch for enqueue_bcp (#8042).
                if MODE == bcp_mode::SEARCH {
                    self.bump_reason_graph_epoch();
                }
                return Some(self.unsafe_conflict_finalize(
                    conflict_ref,
                    qhead_start,
                ));
            }

            // Handle HBR overflow watchers that were added to watches[false_lit]
            // during probe mode. In the safe version this is done by
            // finalize_watch_list; here we check if any overflow entries exist
            // and append them.
            // NOTE: In the unsafe path, watches[false_lit] was NOT swapped out,
            // so HBR watchers added via self.watches.add_watch(false_lit, ...)
            // during handle_probe_hbr would have been appended AFTER the entries
            // we were iterating (since we captured the length as `end` before
            // any HBR additions). The set_len(j) above truncated those away.
            // We need to re-add any overflow entries.
            //
            // However, this is a subtlety: in the unsafe path, ws_ptr was
            // obtained from watches[false_lit] directly. Any push_watcher()
            // calls during HBR would reallocate the Vec, invalidating ws_ptr.
            // The safe version avoids this by swapping the list out first.
            //
            // For correctness, the unsafe BCP must NOT use in-place iteration
            // when HBR can add watchers to false_lit. We handle this by
            // falling back to the safe BCP for PROBE mode, or by swapping
            // out the watch list like the safe version does when in PROBE mode.
            //
            // DESIGN DECISION: For PROBE mode (which is rare and not perf-critical),
            // we use the same deferred swap pattern as the safe BCP. The raw
            // pointer path is only used for SEARCH and VIVIFY modes.
            // This is enforced by the dispatch in propagation.rs.

            // Flush deferred replacement watches (#8041). Collected during the
            // scan above to avoid cache pollution from writing to other literals'
            // watch lists during the hot BCP inner loop.
            for &(lit, watcher) in &self.deferred_replacement_watches {
                self.watches.add_watch(lit, watcher);
            }
            self.deferred_replacement_watches.clear();
        }

        self.num_propagations += (self.qhead - qhead_start) as u64;
        self.flush_bcp_ticks::<MODE>(ticks);
        // Batch-invalidate reason graph epoch for enqueue_bcp (#8042).
        if MODE == bcp_mode::SEARCH {
            self.bump_reason_graph_epoch();
        }
        self.no_conflict_until = self.trail.len();
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: propagate_bcp_unsafe completed but qhead ({}) != trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        None
    }

    /// Copy remaining unvisited watchers during conflict finalization.
    ///
    /// # Safety
    /// `ws_ptr` must point to a valid watch entry buffer of at least `end` entries.
    /// `j` must be <= `end`, `i` must be <= `end`.
    #[inline(always)]
    fn unsafe_copy_remaining(
        &self,
        ws_ptr: *mut u64,
        j: &mut usize,
        i: usize,
        end: usize,
    ) {
        if i < end {
            // SAFETY: i < end and *j < end (since j <= i before copy).
            // Both source [i..end) and dest [*j..*j+(end-i)) are within
            // the watch list buffer. They may overlap, so we use copy.
            unsafe {
                let src = ws_ptr.add(i);
                let dst = ws_ptr.add(*j);
                let count = end - i;
                std::ptr::copy(src, dst, count);
                *j += count;
            }
        }
    }

    /// Conflict finalization for the unsafe BCP path.
    ///
    /// Unlike the safe version, the watch list has already been truncated
    /// by the caller (via set_len). This function only updates stats and
    /// records the conflict.
    #[inline(always)]
    fn unsafe_conflict_finalize(
        &mut self,
        clause_ref: ClauseRef,
        qhead_start: usize,
    ) -> ClauseRef {
        // Flush deferred replacement watches on conflict path (#8041).
        for &(lit, watcher) in &self.deferred_replacement_watches {
            self.watches.add_watch(lit, watcher);
        }
        self.deferred_replacement_watches.clear();
        self.num_propagations += (self.qhead - qhead_start) as u64;
        self.no_conflict_until = if self.decision_level == 0 {
            0
        } else {
            self.trail_lim[self.decision_level as usize - 1]
        };
        debug_assert!(
            {
                let ci = clause_ref.0 as usize;
                let l0 = self.arena.literal(ci, 0);
                let l1 = self.arena.literal(ci, 1);
                self.lit_val(l0) < 0 && self.lit_val(l1) < 0
            },
            "BUG: conflict clause {} does not have both watched lits false",
            clause_ref.0
        );
        let clause_id = self.clause_id(clause_ref);
        self.last_conflict_clause_ref = Some(clause_ref);
        self.last_conflict_clause_id = clause_id;
        let trace_clause_id = if clause_id == 0 {
            u64::from(clause_ref.0) + 1
        } else {
            clause_id
        };
        self.trace_conflict(trace_clause_id);
        solver_log!(
            self,
            "conflict clause {} at level {}",
            clause_ref.0,
            self.decision_level
        );
        clause_ref
    }
}
