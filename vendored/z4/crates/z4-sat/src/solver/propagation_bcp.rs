// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core BCP (Boolean Constraint Propagation) loop and helpers.
//!
//! Split from `propagation.rs` for file-size compliance (#5142).
//! Contains the unified const-generic `propagate_bcp::<MODE>()` function,
//! the hyper-binary resolution (HBR) helper, and conflict finalization.

// BCP replacement scan loops use `for k in pos..len` where k is needed both
// to index `clause_lits[k]` and to call `swap_literals(clause_idx, _, k)`.
// The clippy suggestion `.iter().enumerate().take().skip()` adds iterator
// overhead in the hottest loop of the solver.
#![allow(clippy::needless_range_loop)]

use super::*;
use crate::solver::propagation::bcp_mode;
use crate::solver_log::solver_log;
use z4_prefetch::val_at;

/// Scan watch entries for blocker fast-path hits.
///
/// Iterates from position `i` through `entries.len()`, speculatively
/// copying each entry to the compaction write position `j`. If the blocker
/// literal is satisfied (val > 0), the entry is kept (j incremented)
/// and the scan continues. Otherwise, returns the slow-path entry details.
///
/// Taking `entries` and `vals` as separate slice parameters (instead of
/// through `&mut self`) lets LLVM cache both data pointers in registers
/// across consecutive fast-path iterations, eliminating pointer reloads
/// per watcher that `&mut self` aliasing would otherwise force (#3758).
///
/// All slice accesses use `z4_prefetch::entry_at`/`entry_set`/`val_at`
/// which bypass bounds checks in release builds. This eliminates 3
/// `cmp + b.hs` branch pairs per iteration that were preventing LLVM from
/// hoisting the slice data pointers into registers. The invariants:
/// - `i < entries.len()` from the loop condition
/// - `j <= i` from the compaction invariant (j only increments on fast path)
/// - `blocker_raw < vals.len()` from the literal encoding invariant
#[inline(always)]
fn bcp_scan_blocker_fast_path(
    entries: &mut [u64],
    vals: &[i8],
    mut i: usize,
    mut j: usize,
) -> (usize, usize, Option<(u32, u32, i8)>) {
    let watch_len = entries.len();
    while i < watch_len {
        debug_assert!(j <= i, "BCP fast path: j ({j}) > i ({i})");
        let packed = z4_prefetch::entry_at(entries, i);
        let blocker_raw = packed as u32;
        i += 1;
        // Speculatively copy to write position (CaDiCaL pattern).
        z4_prefetch::entry_set(entries, j, packed);
        let blocker_val = val_at(vals, blocker_raw as usize);
        if blocker_val > 0 {
            j += 1;
            continue;
        }
        let clause_raw = (packed >> 32) as u32;
        return (i, j, Some((blocker_raw, clause_raw, blocker_val)));
    }
    (i, j, None)
}

impl Solver {
    /// Unified BCP propagation, const-generic over MODE (#5037).
    ///
    /// Three modes are compiled as separate monomorphized functions:
    /// - `SEARCH` (0): Main CDCL search. Tracks `ticks` for stabilization
    ///   phase accounting. No vivify-skip check, no probe parent, no HBR.
    /// - `PROBE` (1): Failed-literal probing. Vivify-skip check, probe_parent
    ///   tracking at level 1, hyper-binary resolution (HBR) at level 1.
    /// - `VIVIFY` (2): Vivification. Vivify-skip check, no probe parent,
    ///   no HBR.
    ///
    /// All modes use the deferred swap pattern: watch list is swapped into
    /// `self.deferred_watch_list` (a direct Solver field) for iteration,
    /// eliminating Vec<WatchList> double-indirection per access (#3758).
    ///
    /// REQUIRES: qhead <= trail.len(), watches initialized for all clauses
    /// ENSURES: if None returned, qhead == trail.len() (all propagated),
    ///          every binary unit clause propagated, watch lists consistent;
    ///          if Some(cref), conflicting clause identified, qhead frozen
    #[inline]
    pub(super) fn propagate_bcp<const MODE: u8>(&mut self) -> Option<ClauseRef> {
        debug_assert!(
            !self.has_empty_clause,
            "BUG: propagate_bcp called with has_empty_clause=true"
        );
        if MODE != bcp_mode::PROBE {
            debug_assert!(
                !self.probing_mode,
                "BUG: propagate_bcp (non-probe) called in probing mode"
            );
        }
        self.last_conflict_clause_ref = None;
        self.last_conflict_clause_id = 0;
        let qhead_start = self.qhead;
        let collect_bcp_telemetry = cfg!(debug_assertions);
        // BCP ticks: counts cache-line work for effort budgeting.
        // CaDiCaL propagate.cpp:238,473. Used in all modes: SEARCH for
        // stabilization, PROBE/VIVIFY for effort limits (#3758).
        let mut ticks: u64 = 0;
        debug_assert!(
            self.qhead <= self.trail.len(),
            "BUG: propagate_bcp entry qhead ({}) > trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            if MODE == bcp_mode::PROBE {
                solver_log!(self, "propagate {}", p.to_dimacs());
            }

            let false_lit = p.negated();

            // Swap watch list into deferred buffer for iteration.
            // All modes use this pattern: the deferred buffer is a direct
            // field on Solver, eliminating the Vec<WatchList> indirection
            // that `self.watches.entry_at(lit, i)` requires per access.
            // For SEARCH mode (no HBR), the overflow merge in
            // finalize_watch_list is a no-op since watches[false_lit] is
            // empty after the swap.
            self.watches
                .swap_to_deferred(false_lit, &mut self.deferred_watch_list);
            let watch_len = self.deferred_watch_list.len();
            let mut i: usize = 0;
            let mut j: usize = 0;
            // CaDiCaL propagate.cpp:249: 1 + cache_lines(ws.size(), sizeof Watch).
            // Each Z4 watch entry is 8 bytes; 128-byte cache line ≈ 16 entries.
            ticks += 1 + (watch_len as u64).div_ceil(16);

            // CaDiCaL propagate.cpp:289-302: binary conflicts do NOT
            // immediately break — propagation continues scanning remaining
            // binary watchers (cheap, no arena access). Only long clause
            // processing checks for a prior binary conflict and breaks.
            // This improves conflict analysis by exposing additional
            // conflicting binary clauses (#8043).
            let mut binary_conflict: Option<ClauseRef> = None;
            // Inner watch-scan loop: the blocker fast path is extracted
            // into bcp_scan_blocker_fast_path() which takes &mut [u64]
            // and &[i8] as separate parameters. This lets LLVM cache
            // both pointers in registers across consecutive fast-path
            // iterations, eliminating the pointer reloads that &mut self
            // aliasing would otherwise force (#3758).
            'watch: loop {
                let j_before = j;
                let (new_i, new_j, slow_entry) = bcp_scan_blocker_fast_path(
                    self.deferred_watch_list.entries_mut(),
                    &self.vals,
                    i,
                    j,
                );
                i = new_i;
                j = new_j;
                if collect_bcp_telemetry {
                    self.stats.bcp_blocker_fastpath_hits += (j - j_before) as u64;
                }
                let Some((blocker_raw, clause_raw, blocker_val)) = slow_entry else {
                    break 'watch;
                };

                // Binary clause handling.
                // Binary watcher lifecycle (#4924): deletion eagerly unlinks
                // binary watches, so hot-path propagation can avoid header
                // liveness checks (CaDiCaL parity).
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
                        continue;
                    }
                    // Unassigned - propagate, keep watcher
                    ticks += 1; // CaDiCaL propagate.cpp:295
                    j += 1;
                    // Set probe_parent for binary propagation at level 1 (#3419).
                    // CaDiCaL probe.cpp:405: parent = negation of watching literal.
                    if MODE == bcp_mode::PROBE && self.probing_mode && self.decision_level == 1 {
                        let propagated_var = Literal(blocker_raw).variable().index();
                        self.probe_parent[propagated_var] = Some(p);
                    }
                    // Jump reasons (#8034): in SEARCH mode at decision_level > 0
                    // with LRAT disabled, store a tagged literal reason instead of
                    // a ClauseRef. This avoids arena access during conflict analysis.
                    // LRAT requires clause reasons for forward resolution chain
                    // collection — jump reasons lose the clause ID needed for hints.
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
                    continue;
                }

                // CaDiCaL propagate.cpp:301-302: stop at long clauses if
                // a binary conflict was already found (#8043).
                if binary_conflict.is_some() {
                    j += 1; // keep speculatively-copied watcher
                    break 'watch;
                }

                // Lookahead prefetch (#8000): while we process this long clause,
                // peek at the next watcher entry and prefetch its clause arena
                // data. By the time we finish the current clause's replacement
                // scan, the next clause's header + first literals will be in cache.
                // This hides ~60-80 cycles of main-memory latency per long clause.
                //
                // We prefetch even if the next entry turns out to be binary or
                // blocker-satisfied — prefetch is a no-op hint with zero penalty.
                if i < watch_len {
                    let next_packed = z4_prefetch::entry_at(
                        self.deferred_watch_list.entries_mut(),
                        i,
                    );
                    let next_clause_raw = (next_packed >> 32) as u32;
                    // Only prefetch non-binary clause data (binary clauses don't
                    // access the arena in the hot path).
                    if next_clause_raw & BINARY_FLAG == 0 {
                        self.arena.prefetch_clause(next_clause_raw as usize);
                    }
                }

                // Long clause: garbage check (after blocker shortcut
                // to avoid a cache miss on every watcher — CaDiCaL propagate.cpp:264-280).
                // Watched clauses always have >= 2 literals, so is_empty_clause
                // is unreachable here. Single combined bitmask test covers both
                // garbage and pending_garbage in one cached header read.
                let clause_idx = clause_raw as usize;
                let off = clause_idx;
                let bcp_header = self.arena.bcp_header(off);
                if bcp_header.is_garbage_any() {
                    continue;
                }
                // Vivify-skip: clause is being vivified — keep watcher but
                // skip propagation (CaDiCaL vivify.cpp:268-282). The bit is
                // in the same cached header word we just read.
                // SEARCH mode never vivifies, so this check is compiled out.
                if MODE != bcp_mode::SEARCH && bcp_header.is_vivify_skipped() {
                    j += 1;
                    continue;
                }
                ticks += 1; // CaDiCaL propagate.cpp:309 — long clause cache-line access

                // Non-binary clause
                let clause_ref = ClauseRef(clause_raw);

                // Clause length cached from bcp_header (word[0]), avoiding the
                // `arena.literals()` call which goes through bytemuck::cast_slice
                // + bounds-checked slice creation. All subsequent literal access
                // uses `arena.bcp_literal()` (unchecked in release) matching
                // CaDiCaL's raw `lits[k]` pattern.
                let clause_len = bcp_header.clause_len();
                let cached_saved_pos = bcp_header.saved_pos();

                // XOR trick for the other watched literal.
                // Uses bcp_literal (unchecked release access) instead of
                // creating a &[Literal] slice. CaDiCaL propagate.cpp:328.
                let lit0 = self.arena.bcp_literal(off, 0);
                let lit1 = self.arena.bcp_literal(off, 1);
                // CaDiCaL propagate.cpp:317: watched literal identity
                debug_assert!(
                    lit0 == false_lit || lit1 == false_lit,
                    "BUG: watch list for {false_lit:?} contains clause {clause_idx} \
                     with watched lits {lit0:?}, {lit1:?} — neither matches"
                );
                let first = Literal(lit0.0 ^ lit1.0 ^ false_lit.0);
                let first_val = val_at(&self.vals, first.index());

                let false_pos = usize::from(lit0 != false_lit);

                if first_val > 0 {
                    // Satisfied - update blocker to `first`, keep watcher
                    self.deferred_watch_list.set_entry(j, first.0, clause_raw);
                    j += 1;
                    continue;
                }

                // Search for replacement literal.
                debug_assert!(clause_len > 2);

                // Gent's (JAIR'13) saved position optimization (cached from header above).
                let mut pos = cached_saved_pos;
                // CaDiCaL propagate.cpp:360: saved position within clause bounds
                debug_assert!(
                    cached_saved_pos <= clause_len,
                    "BUG: saved_pos {cached_saved_pos} > clause_len {clause_len} for clause {clause_idx}",
                );
                if pos < 2 || pos >= clause_len {
                    pos = 2;
                }

                // Replacement scan: CaDiCaL propagate.cpp:348-398 pattern.
                // Uses sentinel (replacement_k = clause_len) instead of
                // Option<usize> to avoid branch overhead on the discriminant.
                // Caches the replacement literal's value (replacement_val) to
                // avoid a duplicate vals[] read after the scan (#3758).
                //
                // All literal access uses arena.bcp_literal() which bypasses
                // bounds checks in release builds via word_at(). This eliminates
                // one cmp+jae branch pair per literal compared to slice indexing.
                let mut replacement_k: usize = clause_len; // sentinel = not found
                let mut replacement_val: i8 = -1;
                let mut replacement_lit = false_lit;
                for k in pos..clause_len {
                    if collect_bcp_telemetry {
                        self.stats.bcp_replacement_scan_steps += 1;
                    }
                    let lit_k = self.arena.bcp_literal(off, k);
                    let v = val_at(&self.vals, lit_k.index());
                    if v >= 0 {
                        replacement_k = k;
                        replacement_val = v;
                        replacement_lit = lit_k;
                        break;
                    }
                }
                if replacement_val < 0 && pos > 2 {
                    for k in 2..pos {
                        if collect_bcp_telemetry {
                            self.stats.bcp_replacement_scan_steps += 1;
                        }
                        let lit_k = self.arena.bcp_literal(off, k);
                        let v = val_at(&self.vals, lit_k.index());
                        if v >= 0 {
                            replacement_k = k;
                            replacement_val = v;
                            replacement_lit = lit_k;
                            break;
                        }
                    }
                }

                let off = clause_idx;
                if replacement_k != cached_saved_pos {
                    self.arena.set_saved_pos(off, replacement_k);
                }

                if replacement_val > 0 {
                    // CaDiCaL propagate.cpp:369-373: replacement satisfied,
                    // just replace blit (blocker). No watch movement needed.
                    self.deferred_watch_list
                        .set_entry(j, replacement_lit.0, clause_raw);
                    j += 1;
                    continue;
                } else if replacement_val == 0 {
                    // CaDiCaL propagate.cpp:375-389: found new unassigned
                    // replacement literal. Move watch from false_lit to lit_k.
                    debug_assert!(
                        replacement_k >= 2 && replacement_k < clause_len,
                        "BUG: replacement index {replacement_k} outside [2, {clause_len}) for clause {clause_idx}"
                    );
                    ticks += 1; // CaDiCaL propagate.cpp:389 — watch replacement
                    self.arena.swap_literals(off, false_pos, replacement_k);
                    // Defer the watch addition to avoid cache pollution from
                    // writing to a different literal's watch list during the
                    // hot BCP scan. Flushed after the current literal's watch
                    // list processing completes. Kissat proplit.h pattern (#8041).
                    self.deferred_replacement_watches.push(
                        (replacement_lit, Watcher::new(clause_ref, first)),
                    );
                    continue;
                }

                // replacement_val < 0: no replacement found. All non-watched
                // literals are false.
                // CaDiCaL propagate.cpp:393: every tail literal must be false
                // when we reach the unit/conflict branch.
                debug_assert!(
                    (2..clause_len).all(|k| self.lit_val(self.arena.literal(off, k)) < 0),
                    "BUG: no-replacement path reached but a tail literal in clause {clause_idx} is not false"
                );
                if first_val < 0 {
                    // CaDiCaL propagate.cpp:439-448: conflict — both watched
                    // literals false, all tail literals false.
                    self.flush_bcp_ticks::<MODE>(ticks);
                    return Some(self.conflict_finalize(
                        false_lit,
                        clause_ref,
                        j + 1,
                        i,
                        watch_len,
                        qhead_start,
                    ));
                }

                // Unit propagation
                let mut unit_reason = Some(clause_ref);

                // Probe parent tracking + hyper-binary resolution at level 1.
                //
                // Parent tracking (probe_parent) runs whenever probing_mode is
                // active — CaDiCaL ALWAYS sets parent = dominator for level-1
                // long-clause propagation (probe.cpp:477-478), regardless of
                // whether HBR is enabled or LRAT is on.
                //
                // HBR clause creation additionally requires hbr_enabled and
                // !lrat_enabled (HBR clauses lack LRAT proof steps — #4647).
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

                // Debug contract: probe assignment coherence (#4753 Step 2).
                if MODE == bcp_mode::PROBE {
                    debug_assert!(
                        !self.probing_mode
                            || self.decision_level != 1
                            || clause_len <= 2
                            || self.probe_parent[first.variable().index()].is_some(),
                        "BUG: probe_parent missing for level-1 implied literal"
                    );
                }

                ticks += 1; // CaDiCaL propagate.cpp:401 — long clause unit
                j += 1;
                // Lightweight enqueue for SEARCH mode (#8042).
                if MODE == bcp_mode::SEARCH {
                    self.enqueue_bcp(first, unit_reason.expect("unit propagation always has reason"));
                } else {
                    self.enqueue(first, unit_reason);
                }
            }

            // Copy remaining unscanned watchers when breaking early due to binary conflict (#8043).
            // When a binary conflict is found, BCP continues through binary watchers but
            // breaks at the first long-clause watcher (CaDiCaL propagate.cpp:301-302).
            // The break skips entries from i..watch_len that must be preserved.
            if binary_conflict.is_some() && i < watch_len {
                self.deferred_watch_list.copy_within(i, watch_len, j);
                j += watch_len - i;
            }

            // ENSURES: compaction preserved all kept watchers
            debug_assert!(
                j <= watch_len,
                "BCP: final j ({j}) > watch_len ({watch_len}) after compaction"
            );

            // Compaction complete: truncate + swap back. For SEARCH mode (no HBR)
            // the overflow merge in finalize_watch_list is a no-op since
            // watches[false_lit] is empty after the initial swap.
            self.finalize_watch_list(false_lit, j);

            // Flush deferred replacement watches (#8041). These were collected
            // during the scan above to avoid cache pollution from writing to
            // other literals' watch lists during the hot BCP inner loop.
            for &(lit, watcher) in &self.deferred_replacement_watches {
                self.watches.add_watch(lit, watcher);
            }
            self.deferred_replacement_watches.clear();

            // CaDiCaL propagate.cpp:289-302: if a binary conflict was found
            // during the binary watcher scan, finalize it now (#8043).
            if let Some(conflict_ref) = binary_conflict {
                self.flush_bcp_ticks::<MODE>(ticks);
                self.num_propagations += (self.qhead - qhead_start) as u64;
                // Batch-invalidate reason graph epoch for enqueue_bcp (#8042).
                if MODE == bcp_mode::SEARCH {
                    self.bump_reason_graph_epoch();
                }
                self.no_conflict_until = if self.decision_level == 0 {
                    0
                } else {
                    self.trail_lim[self.decision_level as usize - 1]
                };
                let clause_id = self.clause_id(conflict_ref);
                self.last_conflict_clause_ref = Some(conflict_ref);
                self.last_conflict_clause_id = clause_id;
                let trace_clause_id = if clause_id == 0 {
                    u64::from(conflict_ref.0) + 1
                } else {
                    clause_id
                };
                self.trace_conflict(trace_clause_id);
                return Some(conflict_ref);
            }
        }

        self.num_propagations += (self.qhead - qhead_start) as u64;
        self.flush_bcp_ticks::<MODE>(ticks);
        // Batch-invalidate reason graph epoch for enqueue_bcp (#8042).
        // enqueue_bcp skips per-assignment epoch bumps; one bump at BCP exit
        // is sufficient since reduction only runs between propagation rounds.
        if MODE == bcp_mode::SEARCH {
            self.bump_reason_graph_epoch();
        }
        self.no_conflict_until = self.trail.len();
        // CaDiCaL propagate.cpp:505: post-BCP propagation completeness
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: propagate_bcp completed but qhead ({}) != trail.len() ({})",
            self.qhead,
            self.trail.len(),
        );
        None
    }

    /// Flush accumulated BCP ticks to the per-technique counter.
    ///
    /// Zero-cost: the const-generic MODE is known at monomorphization, so the
    /// match compiles to a single branch. CaDiCaL stats.hpp:36.
    #[inline(always)]
    pub(super) fn flush_bcp_ticks<const MODE: u8>(&mut self, ticks: u64) {
        match MODE {
            bcp_mode::SEARCH => {
                self.search_ticks[usize::from(self.stable_mode)] += ticks;
            }
            bcp_mode::PROBE => {
                self.cold.probe_ticks += ticks;
            }
            bcp_mode::VIVIFY => {
                self.cold.vivify_ticks += ticks;
            }
            _ => {}
        }
    }

    /// Hyper-binary resolution (HBR) helper for PROBE mode.
    ///
    /// Handles probe_parent tracking and optional HBR clause creation
    /// at decision level 1 during probing. Extracted from the BCP loop
    /// to keep the unified function readable (#5037).
    pub(super) fn handle_probe_hbr(
        &mut self,
        false_lit: Literal,
        first: Literal,
        clause_idx: usize,
        clause_len: usize,
        unit_reason: &mut Option<ClauseRef>,
    ) {
        let off = clause_idx;
        self.hbr_lits.clear();
        self.hbr_lits.push(first);
        for k in 0..clause_len {
            let lit_k = self.arena.literal(off, k);
            if lit_k != first {
                self.hbr_lits.push(lit_k);
            }
        }

        let is_learned = self.arena.is_learned(off);
        let hbr_result = hyper_binary_resolve(
            &self.hbr_lits,
            &self.trail,
            &self.var_data,
            &self.probe_parent,
            &self.arena,
            is_learned,
        );

        // Set probe_parent for the propagated literal (#3419/#4719).
        // CaDiCaL probe.cpp:477-478: parent = dominator ALWAYS,
        // even when no HBR binary clause is created. The dominator
        // is the parent in the binary implication tree at level 1.
        let var_idx = first.variable().index();
        self.probe_parent[var_idx] = hbr_result.dominator;

        if self.hbr_enabled && !self.cold.lrat_enabled {
            if let Some((dom_neg, unit)) = hbr_result.binary_clause {
                // Emit HBR clause to proof stream (#4966). HBR clauses
                // are derived via resolution from the original clause and
                // binary implication chains — they ARE RUP-derivable.
                let _ =
                    self.proof_emit_add_prechecked(&[dom_neg, unit], &[], ProofAddKind::Derived);
                let hbr_idx = self.add_clause_db_checked(
                    &[dom_neg, unit],
                    hbr_result.is_redundant,
                    true,
                    &[],
                );
                // CaDiCaL propagate.cpp:434-438: mark HBR clause for
                // one-round lifetime in reduce_db (reduce.cpp:116-120).
                self.arena.set_hyper(hbr_idx, true);
                self.inproc.prober.record_hbr(
                    clause_len,
                    hbr_result.is_redundant,
                    hbr_result.subsumes_original,
                );

                let hbr_ref = ClauseRef(hbr_idx as u32);
                let dom_watch = Watcher::binary(hbr_ref, unit);
                let unit_watch = Watcher::binary(hbr_ref, dom_neg);
                let mut hbr_dom_targets_false_lit = false;
                let mut hbr_unit_targets_false_lit = false;

                // CaDiCaL probe.cpp:262: probe_reason = c
                // When HBR emits a binary clause, the propagated
                // literal's reason is ALWAYS the new binary clause.
                *unit_reason = Some(hbr_ref);

                if dom_neg == false_lit {
                    hbr_dom_targets_false_lit = true;
                } else {
                    self.watches.add_watch(dom_neg, dom_watch);
                }
                if unit == false_lit {
                    hbr_unit_targets_false_lit = true;
                } else {
                    self.watches.add_watch(unit, unit_watch);
                }

                // CaDiCaL probe.cpp:267-271: subsumed original is marked
                // garbage immediately.
                if hbr_result.subsumes_original {
                    let off = clause_idx;
                    if !self.arena.is_pending_garbage(off) {
                        self.arena.set_pending_garbage(off, true);
                        self.pending_garbage_count += 1;
                    }
                }

                // HBR watchers targeting false_lit go into watches[false_lit]
                // which is currently empty (swapped out). They will be
                // merged back after the inner loop via finalize_watch_list.
                if hbr_dom_targets_false_lit {
                    self.watches
                        .get_watches_mut(false_lit)
                        .push_watcher(dom_watch);
                }
                if hbr_unit_targets_false_lit {
                    self.watches
                        .get_watches_mut(false_lit)
                        .push_watcher(unit_watch);
                }
            }
        }
    }

    /// Finalize the watch list after processing all watchers for a literal:
    /// truncate to the compacted length, merge any HBR overflow, and swap back.
    #[inline(always)]
    fn finalize_watch_list(&mut self, false_lit: Literal, j: usize) {
        self.deferred_watch_list.truncate(j);
        self.watches
            .swap_from_deferred(false_lit, &mut self.deferred_watch_list);
    }

    /// Finalize a conflict in the BCP loop: copy remaining watchers, finalize
    /// the watch list, and update propagation statistics.
    ///
    /// `j_start` is the write position after keeping the current watcher (j+1).
    /// `i` / `watch_len` delimit the unvisited watcher range to copy.
    #[inline(always)]
    fn conflict_finalize(
        &mut self,
        false_lit: Literal,
        clause_ref: ClauseRef,
        j_start: usize,
        i: usize,
        watch_len: usize,
        qhead_start: usize,
    ) -> ClauseRef {
        let mut j = j_start;
        if i < watch_len {
            self.deferred_watch_list.copy_within(i, watch_len, j);
            j += watch_len - i;
        }
        self.finalize_watch_list(false_lit, j);
        // Flush deferred replacement watches on conflict path (#8041).
        for &(lit, watcher) in &self.deferred_replacement_watches {
            self.watches.add_watch(lit, watcher);
        }
        self.deferred_replacement_watches.clear();
        self.num_propagations += (self.qhead - qhead_start) as u64;
        // CaDiCaL propagate.cpp:487: trail before current decision level
        // was conflict-free.
        self.no_conflict_until = if self.decision_level == 0 {
            0
        } else {
            self.trail_lim[self.decision_level as usize - 1]
        };
        // CaDiCaL propagate.cpp:441-442: conflict clause has both watched lits false
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
