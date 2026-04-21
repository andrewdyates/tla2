// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable compaction: remove holes in variable-indexed arrays after
//! elimination/substitution.
//!
//! After BVE eliminates 20-50% of variables on industrial instances, every
//! variable-indexed array (`assignment`, `vals`, `phases`, `vsids.scores`,
//! `watch_lists`, `level`, `reason`, etc.) is 20-50% wasted memory with
//! holes. Compaction remaps all active variable indices to a contiguous
//! range `[0..active_count)`, shrinking every array and improving cache
//! utilization in BCP — the #1 performance bottleneck.
//!
//! Reference: CaDiCaL `compact.cpp` (550 lines).

use super::lifecycle;
use super::*;
use crate::literal::{Literal, Variable};
use crate::watched::Watcher;

/// Minimum number of inactive variables before compaction triggers.
/// CaDiCaL: `compactmin = 100` (options.hpp).
const COMPACT_MIN_INACTIVE: usize = 100;

/// Inactive fraction threshold (per-mille of max_var).
/// CaDiCaL: `compactlim = 100` → 100 * 0.001 = 10% of max_var.
const COMPACT_LIMIT_PER_MILLE: usize = 10;

/// Base conflict interval between compaction attempts.
/// CaDiCaL: `compactint = 2000` (options.hpp:55).
const COMPACT_INTERVAL_BASE: u64 = 2_000;

/// Sentinel value meaning "variable is not mapped" (inactive).
pub(crate) const UNMAPPED: u32 = u32::MAX;

/// Mapping table for variable compaction.
///
/// Maps old variable indices to new contiguous indices. Eliminated and
/// substituted variables are unmapped; all active variables (including
/// level-0 fixed) get contiguous new indices.
pub(crate) struct VariableMap {
    /// `old_to_new[old_var_idx]` = new variable index, or `UNMAPPED` if
    /// the variable is inactive (eliminated/substituted).
    pub(crate) old_to_new: Vec<u32>,
    /// New maximum variable count (contiguous range `[0..new_num_vars)`).
    pub(crate) new_num_vars: usize,
}

impl VariableMap {
    /// Build the mapping table from the current solver state.
    ///
    /// Active and non-eliminated variables get contiguous new indices.
    /// Eliminated/substituted variables are unmapped.
    fn build(num_vars: usize, lifecycle: &lifecycle::VarLifecycle) -> Self {
        let mut old_to_new = vec![UNMAPPED; num_vars];
        let mut next_idx: u32 = 0;

        for (var_idx, slot) in old_to_new.iter_mut().enumerate() {
            if lifecycle.is_removed(var_idx) {
                continue;
            }
            *slot = next_idx;
            next_idx += 1;
        }

        Self {
            old_to_new,
            new_num_vars: next_idx as usize,
        }
    }

    /// Map a variable index. Returns `None` if unmapped (inactive).
    #[inline]
    pub(crate) fn map_var(&self, old: usize) -> Option<usize> {
        if old >= self.old_to_new.len() {
            return None;
        }
        let new = self.old_to_new[old];
        if new == UNMAPPED {
            None
        } else {
            Some(new as usize)
        }
    }

    /// Map a literal. Returns `None` if its variable is unmapped.
    #[inline]
    pub(crate) fn map_lit(&self, lit: Literal) -> Option<Literal> {
        self.map_var(lit.variable().index()).map(|new_var| {
            if lit.is_positive() {
                Literal::positive(Variable(new_var as u32))
            } else {
                Literal::negative(Variable(new_var as u32))
            }
        })
    }

    /// Remap a variable-indexed vector in place: copy `vec[old] → vec[new]`,
    /// then truncate to `new_num_vars`.
    pub(crate) fn remap_var_vec<T: Default + Clone>(&self, vec: &mut Vec<T>) {
        if vec.len() < self.old_to_new.len() {
            vec.resize_with(self.old_to_new.len(), T::default);
        }

        // Process forward: since new <= old for all mapped variables,
        // this is safe without a temporary buffer.
        for old in 0..self.old_to_new.len() {
            if let Some(new) = self.map_var(old) {
                if new != old {
                    vec[new] = vec[old].clone();
                }
            }
        }
        vec.truncate(self.new_num_vars);
    }

    /// Remap a literal-indexed vector in place: move entries for both
    /// polarities of each variable, then truncate to `2 * new_num_vars`.
    pub(crate) fn remap_lit_vec<T: Default + Clone>(&self, vec: &mut Vec<T>) {
        let old_num_lits = self.old_to_new.len().saturating_mul(2);
        if vec.len() < old_num_lits {
            vec.resize_with(old_num_lits, T::default);
        }

        for old_var in 0..self.old_to_new.len() {
            if let Some(new_var) = self.map_var(old_var) {
                if new_var != old_var {
                    let old_pos = old_var * 2;
                    let old_neg = old_var * 2 + 1;
                    let new_pos = new_var * 2;
                    let new_neg = new_var * 2 + 1;
                    vec[new_pos] = vec[old_pos].clone();
                    vec[new_neg] = vec[old_neg].clone();
                }
            }
        }
        vec.truncate(self.new_num_vars * 2);
    }
}

impl Solver {
    /// Check if variable compaction should run.
    ///
    /// CaDiCaL `compacting()` guard (compact.cpp:13-27).
    pub(super) fn compacting(&self) -> bool {
        if self.decision_level != 0 {
            return false;
        }
        if self.cold.has_been_incremental {
            return false;
        }
        if self.proof_manager.is_some() {
            return false;
        }
        if self.cold.freeze_counts.iter().any(|&c| c > 0) {
            return false;
        }
        // NOTE: Z4 skips CaDiCaL's conflict-based interval guard. More
        // aggressive compaction keeps the clause arena tight for cache
        // performance on large formulas (bvsub 598K vars, stable-300).
        let inactive = self.var_lifecycle.count_removed();
        if inactive < COMPACT_MIN_INACTIVE {
            return false;
        }
        // inactive >= 0.001 * COMPACT_LIMIT_PER_MILLE * num_vars
        if inactive * 1000 < COMPACT_LIMIT_PER_MILLE * self.num_vars {
            return false;
        }
        true
    }

    /// Compact variable indices: remap all active variables to a contiguous
    /// range, shrinking every variable-indexed data structure.
    ///
    /// Preconditions: decision level 0, no pending propagation.
    ///
    /// Reference: CaDiCaL `Internal::compact()` (compact.cpp:162-548).
    pub(super) fn compact(&mut self) {
        debug_assert_eq!(self.decision_level, 0);
        debug_assert_eq!(self.qhead, self.trail.len());

        let map = VariableMap::build(self.num_vars, &self.var_lifecycle);

        if map.new_num_vars == self.num_vars {
            return;
        }

        let old_num_vars = self.num_vars;

        // ── Phase 1: Remap clause literals ────────────────────────────
        for idx in self.arena.active_indices().collect::<Vec<_>>() {
            // Debug: pre-check for unmapped literals with diagnostic info.
            #[cfg(debug_assertions)]
            {
                let lits = self.arena.literals(idx);
                for &lit in lits {
                    if map.map_lit(lit).is_none() {
                        let var = lit.variable().index();
                        let state = self.var_lifecycle.as_slice().get(var).copied();
                        let is_learned = self.arena.is_learned(idx);
                        let clause_lits: Vec<_> = lits.to_vec();
                        panic!(
                            "invariant: active clause {idx} (learned={is_learned}, len={}) \
                             contains eliminated-variable literal {lit:?} (var={var}, \
                             state={state:?}). Clause: {clause_lits:?}",
                            clause_lits.len(),
                        );
                    }
                }
            }
            let lits = self.arena.literals_mut(idx);
            for lit in lits.iter_mut() {
                *lit = map
                    .map_lit(*lit)
                    .expect("invariant: active clause contains eliminated-variable literal");
            }
            // Arena is the sole storage after #3904 cutover — no sync needed.
        }

        // ── Phase 2: Remap watch lists ────────────────────────────────
        // compact_watches() rebuilds watches with binary-first invariant.
        self.compact_watches(&map);

        // ── Phase 3: Remap trail ──────────────────────────────────────
        let mut new_trail = Vec::with_capacity(self.trail.len());
        for &lit in &self.trail {
            if let Some(new_lit) = map.map_lit(lit) {
                new_trail.push(new_lit);
            }
        }
        self.trail = new_trail;
        self.qhead = self.trail.len();
        #[cfg(feature = "jit")]
        {
            self.jit_qhead = self.trail.len();
            // Variable indices are remapped by compaction — compiled JIT
            // functions reference stale indices. Invalidate defensively.
            if self.compiled_formula.is_some() {
                self.invalidate_compiled_formula();
            }
        }

        // ── Phase 3b: Clear conflict analyzer seen flags BEFORE remap ──
        // `seen_to_clear` contains OLD variable indices from the last
        // conflict analysis. Phase 4 remaps `var_data` to NEW indices.
        // If we clear AFTER remap, the old indices in `seen_to_clear`
        // operate on wrong `var_data` entries, leaving stale seen flags
        // that corrupt `counter`/`resolvent_size` in the next conflict
        // analysis (#7331).
        self.conflict.compact(&mut self.var_data);

        // ── Phase 4: Remap variable-indexed solver arrays ─────────────
        map.remap_var_vec(&mut self.var_data);
        if !self.unit_proof_id.is_empty() {
            map.remap_var_vec(&mut self.unit_proof_id);
        }
        map.remap_var_vec(&mut self.phase);
        map.remap_var_vec(&mut self.target_phase);
        map.remap_var_vec(&mut self.best_phase);
        map.remap_var_vec(&mut self.cold.freeze_counts);
        if !self.cold.level0_proof_id.is_empty() {
            map.remap_var_vec(&mut self.cold.level0_proof_id);
        }
        map.remap_var_vec(&mut self.cold.scope_selector_set);
        map.remap_var_vec(&mut self.glue_stamp);
        map.remap_var_vec(&mut self.shrink_stamp);
        map.remap_var_vec(&mut self.min.minimize_flags);

        // probe_parent: variable-indexed, values are Literals.
        {
            let mut new_pp: Vec<Option<Literal>> = vec![None; map.new_num_vars];
            for old_var in 0..old_num_vars {
                if let Some(new_var) = map.map_var(old_var) {
                    new_pp[new_var] = self.probe_parent[old_var].and_then(|lit| map.map_lit(lit));
                }
            }
            self.probe_parent = new_pp;
        }

        // stale_reasons: contains old variable indices — remap to new indices,
        // dropping entries for eliminated variables.
        if !self.stale_reasons.is_empty() {
            self.stale_reasons.retain_mut(|vi| {
                if let Some(new_var) = map.map_var(*vi as usize) {
                    *vi = new_var as u32;
                    true
                } else {
                    false
                }
            });
        }

        // ── Phase 5: Remap literal-indexed arrays ─────────────────────
        map.remap_lit_vec(&mut self.vals);

        // ── Phase 6: Remap VSIDS ──────────────────────────────────────
        self.vsids.compact(&map);

        // ── Phase 7: Remap VarLifecycle ───────────────────────────────
        // All mapped variables are active by construction.
        self.var_lifecycle = lifecycle::VarLifecycle::new(map.new_num_vars);

        // ── Phase 8: Remap scope selectors ────────────────────────────
        self.cold.scope_selectors = self
            .cold
            .scope_selectors
            .iter()
            .filter_map(|v| map.map_var(v.index()).map(|nv| Variable(nv as u32)))
            .collect();

        // ── Phase 9: Conflict analyzer ────────────────────────────────
        // Seen flags already cleared in Phase 3b (before var_data remap).
        // No further remapping needed — ConflictAnalyzer doesn't store
        // variable indices persistently (seen_to_clear was cleared in 3b).

        // ── Phase 9b: Update external↔internal index tables (#5250) ──
        // CaDiCaL compact.cpp:210-233. Rebuild i2e for the compacted
        // variable space and update e2i so that external indices point
        // to the new internal indices. Eliminated variables get
        // UNMAPPED in e2i; the reconstruction stack (which stores
        // external indices) does NOT need remapping.
        {
            let mut new_i2e = vec![UNMAPPED; map.new_num_vars];
            for old_var in 0..old_num_vars {
                if let Some(new_var) = map.map_var(old_var) {
                    let ext_var = self.cold.i2e[old_var];
                    new_i2e[new_var] = ext_var;
                    self.cold.e2i[ext_var as usize] = new_var as u32;
                } else {
                    // Eliminated/substituted: mark as unmapped in e2i
                    let ext_var = self.cold.i2e[old_var];
                    if (ext_var as usize) < self.cold.e2i.len() {
                        self.cold.e2i[ext_var as usize] = UNMAPPED;
                    }
                }
            }
            self.cold.i2e = new_i2e;
        }

        // ── Phase 10: Reconstruction stack uses external indices (#5250) ──
        // No remapping needed — entries store stable external indices that
        // are never affected by internal variable compaction.
        // (Previously: self.reconstruction.compact(&map);)

        // ── Phase 11: Recreate inprocessing engines ───────────────────
        // Save accumulated stats before recreating engines with new variable count.
        let bve_stats = self.inproc.bve.stats().clone();
        let decompose_stats = self.inproc.decompose_engine.stats.clone();
        let subsume_stats = self.inproc.subsumer.stats().clone();
        let sweep_stats = self.inproc.sweeper.stats().clone();
        let transred_stats = self.inproc.transred_engine.stats().clone();
        let htr_stats = self.inproc.htr.stats().clone();
        let conditioning_stats = self.inproc.conditioning.stats().clone();
        let bce_stats = self.inproc.bce.stats().clone();
        let probe_stats = self.inproc.prober.stats().clone();
        let congruence_stats = self.inproc.congruence.stats().clone();

        self.inproc.bve = BVE::new(map.new_num_vars);
        self.inproc.bve.restore_stats(bve_stats);
        self.inproc.bce = BCE::new(map.new_num_vars);
        self.inproc.bce.restore_stats(bce_stats);
        self.inproc.subsumer = Subsumer::new(map.new_num_vars);
        self.inproc.subsumer.restore_stats(subsume_stats);
        self.subsume_dirty = vec![true; map.new_num_vars]; // all dirty after compaction
        self.inproc.sweeper = Sweeper::new(map.new_num_vars);
        self.inproc.sweeper.restore_stats(sweep_stats);
        self.inproc.prober = Prober::new(map.new_num_vars);
        self.inproc.prober.restore_stats(probe_stats);
        self.inproc.decompose_engine = Decompose::new(map.new_num_vars);
        self.inproc.decompose_engine.restore_stats(decompose_stats);
        self.inproc.factor_engine = Factor::new(map.new_num_vars);
        self.inproc.transred_engine = TransRed::new(map.new_num_vars);
        self.inproc.transred_engine.restore_stats(transred_stats);
        self.inproc.htr = HTR::new(map.new_num_vars);
        self.inproc.htr.restore_stats(htr_stats);
        self.inproc.conditioning = Conditioning::new(map.new_num_vars);
        self.inproc.conditioning.restore_stats(conditioning_stats);
        self.lit_marks = LitMarks::new(map.new_num_vars);
        self.inproc.congruence = CongruenceClosure::new(map.new_num_vars);
        self.inproc.congruence.restore_stats(congruence_stats);

        // Factor candidate marks are indexed by variable — must be reset
        // after compaction renumbers variables (#5172).
        self.cold.factor_candidate_marks = vec![0; map.new_num_vars];
        self.cold.factor_marked_epoch = 1;
        self.cold.factor_last_completed_epoch = 0;

        // ── Phase 12: Clear transient buffers ─────────────────────────
        self.hbr_lits.clear();
        self.min.minimize_to_clear.clear();
        self.min.lrat_to_clear.clear();
        // Level-seen tracking is indexed by decision level, not variable —
        // clearing is sufficient (no remapping needed).
        self.clear_level_seen();

        // ── Phase 13: Forward checker ─────────────────────────────────
        // Recreate with new size, preserving sampling mode (#5625).
        if let Some(ref checker) = self.cold.forward_checker {
            let sample_period = checker.sample_period();
            self.cold.forward_checker = if sample_period > 0 {
                Some(crate::forward_checker::ForwardChecker::new_sampled(
                    map.new_num_vars,
                    sample_period,
                ))
            } else {
                Some(crate::forward_checker::ForwardChecker::new(
                    map.new_num_vars,
                ))
            };
        }

        // ── Phase 14: Solution witness ────────────────────────────────
        if let Some(ref mut witness) = self.cold.solution_witness {
            map.remap_var_vec(witness);
        }

        // ── Phase 15: Original clauses use external indices (#5250) ──
        // Original clauses were added in the initial internal space which
        // equals external space (identity mapping). With external indices,
        // they stay in external space permanently — no remapping needed.
        // (Previously: map_lit_for_reconstruction remapped to compacted space.)

        // ── Phase 16: Root-satisfied clauses use external indices (#5250) ──
        // Root-satisfied clauses are externalized at save time (condition.rs).
        // No remapping needed during compaction.
        // (Previously: map_lit_for_reconstruction remapped to compacted space.)

        // ── Finalize ──────────────────────────────────────────────────
        self.num_vars = map.new_num_vars;
        // user_num_vars is intentionally NOT updated during compaction.
        // It represents the external variable count (what the user/DPLL(T)
        // layer created), which is the full e2i.len(). Compaction only
        // changes internal variable indices; external indices are stable.
        // Reducing user_num_vars would truncate the returned model,
        // losing variables with high external indices (#5522).
        debug_assert!(
            !self.cold.has_been_incremental,
            "BUG: compact must not run in incremental mode"
        );
        self.target_trail_len = self.trail.len();
        self.best_trail_len = self.trail.len();

        // Schedule next compaction (CaDiCaL compact.cpp:540-541).
        self.cold.compact_count += 1;
        let delta = COMPACT_INTERVAL_BASE.saturating_mul(self.cold.compact_count + 1);
        self.cold.compact_next_conflict = self.num_conflicts.saturating_add(delta);
    }

    /// Remap watch lists during compaction.
    fn compact_watches(&mut self, map: &VariableMap) {
        let old_num_lits = self.num_vars * 2;
        let mut new_watches = WatchedLists::new(map.new_num_vars);

        for old_lit_idx in 0..old_num_lits {
            let old_lit = Literal::from_index(old_lit_idx);
            let new_lit = match map.map_lit(old_lit) {
                Some(nl) => nl,
                None => continue,
            };

            let wl = self.watches.get_watches(old_lit);
            let mut dst = new_watches.get_watches_mut(new_lit);
            for wi in 0..wl.len() {
                let old_blocker = wl.blocker(wi);
                let clause_raw = wl.clause_raw(wi);
                let is_bin = wl.is_binary(wi);
                let new_watcher = if is_bin {
                    // Binary watcher: blocker IS the other literal in the clause —
                    // used structurally for propagation and conflict detection.
                    // If the other literal's variable was eliminated, this binary
                    // clause is stale (BVE should have deleted it, but watches
                    // may not have been flushed). Skip the entry.
                    let Some(new_blocker) = map.map_lit(old_blocker) else {
                        continue;
                    };
                    Watcher::binary(ClauseRef(clause_raw), new_blocker)
                } else {
                    // Long watcher: blocker is a propagation hint, not structural.
                    // May reference an eliminated variable if watch lists weren't
                    // flushed before compaction. Fall back to the watched literal.
                    let new_blocker = map.map_lit(old_blocker).unwrap_or(new_lit);
                    Watcher::new(ClauseRef(clause_raw), new_blocker)
                };
                dst.push_watcher(new_watcher);
            }
        }

        self.watches = new_watches;
        // Binary-first invariant is maintained incrementally via push_watcher.
        self.watches.debug_assert_binary_first();
    }
}

#[cfg(test)]
#[path = "compact_tests.rs"]
mod tests;
