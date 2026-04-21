// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing techniques: vivification, subsumption, probing, BVE, BCE, transitive reduction, HTR, gate extraction, SAT sweeping.
//!
//! # DRAT Proof Compatibility
//!
//! When proof logging is enabled (`proof_manager.is_some()`), each technique
//! either emits valid DRAT add/delete records or is disabled:
//!
//! | Technique        | DRAT Status | Notes |
//! |------------------|-------------|-------|
//! | BVE              | Emits       | Add resolvents, delete originals |
//! | BCE              | Emits       | Delete blocked clauses |
//! | Subsumption      | Emits       | Delete subsumed clauses |
//! | Vivification     | Emits       | Add strengthened, delete original |
//! | Transred         | Emits       | Delete redundant binary clauses |
//! | HTR              | Emits       | Delete hyper-binary resolvable clauses |
//! | Probing          | Emits       | Add failed-literal units |
//! | Conditioning     | Emits       | Delete globally blocked clauses via `delete_clause_checked` |
//! | Congruence       | Emits       | Add equivalence binaries, delete/replace rewritten |
//! | Factorization    | Emits (DRAT) | Divider+blocked+quotient per application; LRAT skipped |
//! | SAT Sweeping     | Emits       | Add sweep-derived units |
//! | SCC Decompose    | Emits       | Delete/replace rewritten, add units |

use super::mutate::{ReasonPolicy, ReplaceResult};
use super::*;

/// Minimum irredundant clause count before enabling random-k-SAT skip heuristics.
///
/// Small formulas can accidentally look "uniform" while still being highly
/// structured (for example, hand-crafted XOR encodings). Use a conservative
/// floor so we only skip gate/BVE passes on large, likely-random instances.
pub(crate) const RANDOM_KSAT_MIN_CLAUSES: usize = 128;
const FACTOR_TICK_THRESHOLD: u64 = 7;
const HTR_TICK_THRESHOLD: u64 = 6;
/// CaDiCaL options.hpp: `backbonethresh = 5`.
const BACKBONE_TICK_THRESHOLD: u64 = 5;
/// CaDiCaL options.hpp: `sweepthresh = 5`.
const SWEEP_TICK_THRESHOLD: u64 = 5;
/// Tick-proportional scheduling threshold for vivification.
///
/// CaDiCaL uses `vivifythresh = 20`, but Z4 counts fewer ticks per conflict
/// (~10x less). Threshold=1 corrects for this so vivification fires. (#8134)
const VIVIFY_TICK_THRESHOLD: u64 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FactorSkipReason {
    DisabledFlag,
    IntervalNotDue,
    DelayGuard,
    ThresholdDelay,
    NoNewMarks,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum HtrSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BackboneSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SweepSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum VivifySkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Default, Clone, Copy)]
struct VivifyTierRun {
    processed: u64,
    strengthened: u64,
    enqueued_units: bool,
    conflict: bool,
}

impl VivifyTierRun {
    #[inline]
    fn is_low_yield(self) -> bool {
        self.processed == 0 || self.strengthened.saturating_mul(100) < self.processed
    }
}

mod accessors;
mod backbone;
mod bce;
mod bve;
mod cce;
mod condition;
mod congruence;
mod decompose;
mod deduplicate;
mod factorize;
mod htr;
mod instantiate;
#[cfg(test)]
pub(super) use instantiate::InstCandidate;
mod probe;
mod reorder;
mod subsume;
mod sweep;
mod transred;
mod vivify;

impl Solver {
    /// Level-0 garbage collection: remove satisfied clauses and root-false literals.
    ///
    /// CaDiCaL equivalent: `mark_satisfied_clauses_as_garbage()` +
    /// `remove_falsified_literals()` in `collect.cpp`. This ensures all
    /// inprocessing techniques (especially HTR) operate on clauses without
    /// stale level-0 false literals (#3971).
    ///
    /// Fixpoint guard: skips if no new level-0 assignments since last collection.
    /// Returns true if UNSAT detected (empty clause derived).
    ///
    /// REQUIRES: called at decision level 0 (level-0 assignments are permanent)
    /// ENSURES: no active clause is satisfied at level 0,
    ///          no active clause contains a level-0 false literal
    /// Lightweight level-0 garbage collection for large bit-blasted formulas.
    ///
    /// Skips clause modification entirely. The two-watch invariant handles
    /// stale false literals correctly during search, and satisfied clauses
    /// are inert (both watched literals are true, so BCP never visits them).
    ///
    /// Full GC on 1M+ clause formulas costs 12s+ due to per-clause watch
    /// removal/re-addition for satisfied clause deletion. This skip saves
    /// that overhead when expensive preprocessing (congruence, decompose)
    /// is already bypassed.
    ///
    /// Returns true if UNSAT detected (all-false clause found).
    pub(super) fn collect_level0_garbage_lightweight(&mut self) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: collect_level0_garbage_lightweight at decision level {}",
            self.decision_level,
        );
        if self.fixed_count == self.cold.last_collect_fixed {
            return false;
        }

        // Quick scan: only check for all-false clauses (UNSAT detection).
        // Do NOT delete satisfied clauses or remove false literals.
        let active: Vec<usize> = self.arena.active_indices().collect();
        for clause_idx in active {
            let clause_len = self.arena.len_of(clause_idx);
            if clause_len < 2 {
                continue;
            }
            let lits = self.arena.literals(clause_idx);
            let mut has_non_false = false;
            for &lit in lits {
                let val = self.lit_val(lit);
                if val >= 0 || self.var_data[lit.variable().index()].level != 0 {
                    has_non_false = true;
                    break;
                }
            }
            if !has_non_false {
                return true; // All literals false at level 0 — UNSAT
            }
        }

        self.cold.last_collect_fixed = self.fixed_count;
        false
    }

    pub(super) fn collect_level0_garbage(&mut self) -> bool {
        // Level-0 detection relies on decision_level == 0
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: collect_level0_garbage at decision level {}",
            self.decision_level,
        );
        // Fixpoint guard: skip if no new level-0 assignments.
        if self.fixed_count == self.cold.last_collect_fixed {
            return false;
        }

        // Prime unit proof IDs before the loop so that the first clause scan
        // can look up direct unit IDs. In LRAT mode we also refresh inside the
        // per-clause sweep below: earlier clause rewrites in the same pass can
        // materialize new level-0 unit proofs that later explicit-only hint
        // collection needs to see immediately.
        if self.cold.lrat_enabled {
            self.materialize_level0_unit_proofs();
        }

        loop {
            self.ensure_reason_clause_marks_current();

            // Collect active clause indices to avoid borrow conflicts during mutation.
            let active: Vec<usize> = self.arena.active_indices().collect();
            let mut new_lits: Vec<Literal> = Vec::new();
            let mut falsified_unit_ids: Vec<u64> = Vec::new();
            let mut pass_mutated = false;
            let trail_len_before = self.trail.len();

            for clause_idx in active {
                let clause_len = self.arena.len_of(clause_idx);
                if clause_len < 2 {
                    continue;
                }

                if self.cold.lrat_enabled {
                    self.materialize_level0_unit_proofs();
                }

                // Scan literals for level-0 assignments. Literals are copied into
                // new_lits; the immutable borrow on clause_db ends before mutation.
                let lits = self.arena.literals(clause_idx);
                let mut satisfied = false;
                new_lits.clear();
                falsified_unit_ids.clear();

                for &lit in lits {
                    let val = self.lit_val(lit);
                    if val > 0 && self.var_data[lit.variable().index()].level == 0 {
                        // Literal true at level 0 — clause is satisfied.
                        satisfied = true;
                        break;
                    }
                    if val < 0 && self.var_data[lit.variable().index()].level == 0 {
                        // Literal false at level 0 — drop from clause.
                        // CaDiCaL Proof::flush_clause: collect unit_id(-lit) for
                        // each falsified literal directly (#7108).
                        if self.cold.lrat_enabled {
                            let vi = lit.variable().index();
                            if let Some(pid) = self.level0_var_proof_id(vi) {
                                if !falsified_unit_ids.contains(&pid) {
                                    falsified_unit_ids.push(pid);
                                }
                            }
                        }
                        continue;
                    }
                    new_lits.push(lit);
                }

                if satisfied {
                    // CaDiCaL: mark_garbage() for satisfied clauses.
                    // Use ClearLevel0 so level-0 reason references don't block deletion.
                    //
                    // LRAT guard (#5028): When LRAT is enabled, reason clauses must
                    // stay alive. ClearLevel0 saves the LRAT clause ID into
                    // level0_proof_id before deletion, but also emits an LRAT 'd'
                    // (delete) step. Later, append_lrat_unit_chain references
                    // level0_proof_id as a hint — pointing at a clause the checker
                    // considers deleted. Skipping deletion keeps the proof valid.
                    // The clause remains inert (satisfied, won't propagate) but its
                    // LRAT ID stays live for future proof chains.
                    if self.cold.lrat_enabled && self.is_reason_clause_marked(clause_idx) {
                        continue;
                    }
                    self.delete_clause_checked(clause_idx, ReasonPolicy::ClearLevel0);
                    pass_mutated = true;
                    continue;
                }

                if new_lits.len() < clause_len {
                    // All literals false at level 0 → clause unsatisfied → UNSAT.
                    if new_lits.is_empty() {
                        return true;
                    }
                    // CaDiCaL Proof::flush_clause starts from the direct
                    // unit IDs of falsified literals, but Z4 still needs the
                    // ordinary transitive level-0 LRAT chain here when one of
                    // those units depends on earlier root implications in the
                    // same sweep. Keep the direct unit IDs as explicit seeds
                    // and let replace_clause_checked_with_lrat_hints extend
                    // them as needed.
                    let result = if self.cold.lrat_enabled && !falsified_unit_ids.is_empty() {
                        self.replace_clause_checked_with_lrat_hints(
                            clause_idx,
                            &new_lits,
                            &falsified_unit_ids,
                        )
                    } else {
                        self.replace_clause_checked(clause_idx, &new_lits)
                    };
                    match result {
                        ReplaceResult::Empty => return true,
                        ReplaceResult::Unit | ReplaceResult::Replaced => {
                            pass_mutated = true;
                        }
                        ReplaceResult::Skipped => {}
                    }
                }
            }

            if self.propagate_check_unsat() {
                return true;
            }

            let trail_grew = self.trail.len() > trail_len_before;
            if !pass_mutated && !trail_grew {
                break;
            }
        }

        self.cold.last_collect_fixed = self.fixed_count;

        // Post-condition: no active clause should be satisfied at level 0
        // or contain a level-0 false literal. This validates the GC was thorough.
        // Exception: LRAT-protected reason clauses may remain satisfied (#5028).
        #[cfg(debug_assertions)]
        {
            self.ensure_reason_clause_marks_current();
            for idx in self.arena.active_indices() {
                let off_header = idx;
                if self.arena.is_empty_clause(off_header) || self.arena.len_of(off_header) < 2 {
                    continue;
                }
                // LRAT-protected reason clauses are exempt from the satisfied check.
                if self.cold.lrat_enabled && self.is_reason_clause_marked(idx) {
                    continue;
                }
                for &lit in self.arena.literals(idx) {
                    let val = self.lit_val(lit);
                    let lvl = self.var_data[lit.variable().index()].level;
                    debug_assert!(
                        !(val > 0 && lvl == 0),
                        "BUG: collect_level0_garbage left satisfied clause {idx} \
                         (lit {lit:?} true at level 0)"
                    );
                    debug_assert!(
                        !(val < 0 && lvl == 0),
                        "BUG: collect_level0_garbage left false literal {lit:?} \
                         at level 0 in clause {idx}"
                    );
                }
            }
        }

        false
    }

    /// Remove a watch for a clause from a literal's watch list
    pub(super) fn remove_watch(&mut self, lit: Literal, clause_ref: ClauseRef) {
        let mut list = self.watches.get_watches_mut(lit);
        // Defensive: a buggy inprocessing pass can leave duplicate watchers behind.
        // Remove all occurrences to avoid stale watches corrupting propagation/transred.
        let target = clause_ref.0;
        let mut i = 0;
        while i < list.len() {
            if list.clause_ref(i).0 == target {
                list.swap_remove(i);
            } else {
                i += 1;
            }
        }
    }

    /// Push equivalence reconstruction entries for substituted variables.
    ///
    /// For each variable where `reprs[pos] != pos`, records two equivalence
    /// clauses so `extend_model` can reconstruct the original assignment:
    ///   (repr ∨ ¬pos) with witness ¬pos
    ///   (¬repr ∨ pos) with witness pos
    ///
    /// Used by `decompose()` (reprs).
    fn push_equivalence_reconstruction(&mut self, reprs: &[Literal]) {
        // Keep the original-clause ledger immutable. Decompose may rewrite the
        // working clause DB, but `verify_against_original` must continue to
        // check the user-provided clauses as-added, not a representative-space
        // projection of them (#7432).
        for var_idx in 0..self.num_vars {
            let pos = Literal::positive(Variable(var_idx as u32));
            let repr = reprs[pos.index()];
            if repr == pos {
                continue;
            }
            let ext_pos = self.externalize(pos);
            let ext_repr = self.externalize(repr);
            self.inproc
                .reconstruction
                .push_bce(ext_pos.negated(), vec![ext_repr, ext_pos.negated()]);
            self.inproc
                .reconstruction
                .push_bce(ext_pos, vec![ext_repr.negated(), ext_pos]);
        }
    }

    /// Clear stale reason references pointing to dead clauses.
    ///
    /// Clear stale reason references after a deferred-cleanup batch.
    ///
    /// When the dirty list (`stale_reasons`) is non-empty, iterates only the
    /// collected variable indices — O(stale_count) instead of O(num_vars).
    /// Falls back to a full scan when the dirty list is empty (e.g. after
    /// watch-free BVE where per-deletion tracking was skipped entirely).
    ///
    /// Must be called after inprocessing/BVE completes but before
    /// rebuild_watches/BCP, since conflict analysis follows reason chains.
    pub(super) fn clear_stale_reasons(&mut self) {
        let mut cleared = false;

        if self.stale_reasons.is_empty() {
            // Fallback: full scan for watch-free BVE or other paths that
            // don't populate the dirty list.
            for vi in 0..self.num_vars {
                let reason = self.var_data[vi].reason;
                if is_clause_reason(reason) && !self.arena.is_active(reason as usize) {
                    self.var_data[vi].reason = NO_REASON;
                    cleared = true;
                }
            }
        } else {
            // Fast path: process only dirty variables.
            for i in 0..self.stale_reasons.len() {
                let vi = self.stale_reasons[i] as usize;
                if vi < self.num_vars {
                    let reason = self.var_data[vi].reason;
                    if is_clause_reason(reason) && !self.arena.is_active(reason as usize) {
                        self.var_data[vi].reason = NO_REASON;
                        cleared = true;
                    }
                }
            }
            self.stale_reasons.clear();
        }

        // Debug verification: check that no ASSIGNED variable has a stale
        // reason reference. Unassigned variables (backtracked to level > 0)
        // may retain stale reason fields — these are dead data that will be
        // overwritten on re-propagation and are never dereferenced.
        #[cfg(debug_assertions)]
        {
            for vi in 0..self.num_vars {
                if !self.var_is_assigned(vi) {
                    continue;
                }
                let reason = self.var_data[vi].reason;
                debug_assert!(
                    !is_clause_reason(reason) || self.arena.is_active(reason as usize),
                    "BUG: clear_stale_reasons missed stale reason for assigned var {vi} \
                     (reason={reason}, active=false, level={})",
                    self.var_data[vi].level,
                );
            }
        }

        if cleared {
            self.bump_reason_graph_epoch();
        }
    }

    /// Rebuild watched literals for all non-empty clauses.
    ///
    /// Reorders each clause's literals for optimal watch placement before
    /// re-attaching. After inprocessing, clause mutations (strengthening, BVE)
    /// may leave suboptimal literals in positions [0]/[1]. (#3812)
    pub(super) fn rebuild_watches(&mut self) {
        // Clear all watch lists
        self.watches = WatchedLists::new(self.num_vars);

        // Collect indices to avoid borrow conflict (active_indices borrows clause_db)
        let indices: Vec<usize> = self.arena.active_indices().collect();

        for i in indices {
            let clause_len = self.arena.len_of(i);
            if clause_len < 2 {
                continue;
            }
            let watched = {
                let lits = self.arena.literals_mut(i);
                Self::prepare_watched_literals_with_state(
                    &self.vals,
                    &self.var_data,
                    lits,
                    WatchOrderPolicy::AssignmentScore,
                )
                .expect("rebuild_watches only handles clauses with len >= 2")
            };
            let clause_ref = ClauseRef(i as u32);
            self.attach_clause_watches(clause_ref, watched, clause_len == 2);
        }

        // Binary-first invariant is maintained incrementally via push_watcher.
        self.watches.debug_assert_binary_first();

        // Re-propagate assignments against the rebuilt watch graph.
        // Without rewinding qhead, propagate() may skip all currently assigned
        // literals and miss immediate unit/conflict consequences.
        //
        // Minimal trail rewind (#8095): at level 0, use earliest_affected_trail_pos
        // to avoid re-propagating the entire trail when only a few positions changed.
        // At higher levels (rare during inprocessing), rewind to level start.
        self.qhead = if self.decision_level == 0 {
            self.earliest_affected_trail_pos.unwrap_or(self.trail.len())
        } else {
            self.trail_lim[self.decision_level as usize - 1]
        };
        #[cfg(feature = "jit")]
        {
            self.jit_qhead = self.qhead;
        }

        // Shadow mode (#8095): verify that no active clause is a unit whose
        // propagation literal would be missed by the minimal qhead. A clause
        // is a "missed unit" if: (a) exactly one literal is unassigned, (b) all
        // others are false at level 0, and (c) neither watched literal is on
        // the trail at a position >= qhead (meaning BCP from qhead would not
        // visit it). Any such clause is a soundness bug in the trail tracking.
        #[cfg(debug_assertions)]
        if self.decision_level == 0 && self.earliest_affected_trail_pos.is_some() {
            let minimal_qhead = self.qhead;
            for idx in self.arena.active_indices() {
                if self.arena.is_empty_clause(idx) || self.arena.len_of(idx) < 2 {
                    continue;
                }
                let lits = self.arena.literals(idx);
                let mut unassigned_lit = None;
                let mut has_true = false;
                let mut all_others_false_l0 = true;
                for &cl in lits {
                    let v = self.lit_val(cl);
                    if v > 0 {
                        has_true = true;
                        break;
                    }
                    if v == 0 {
                        if unassigned_lit.is_some() {
                            all_others_false_l0 = false; // 2+ unassigned = not unit
                            break;
                        }
                        unassigned_lit = Some(cl);
                    } else {
                        // v < 0 (false): check level
                        let lvl = self.var_data[cl.variable().index()].level;
                        if lvl != 0 {
                            all_others_false_l0 = false;
                            break;
                        }
                    }
                }
                // A unit clause: exactly one unassigned literal, rest false at level 0.
                if !has_true && all_others_false_l0 {
                    if let Some(unit_lit) = unassigned_lit {
                        // This literal must be reachable from qhead via BCP.
                        // BCP scans watches on trail[qhead..]. The unit is
                        // reachable if either watched literal's negation is
                        // on the trail at position >= minimal_qhead.
                        let w0 = self.arena.literal(idx, 0);
                        let w1 = self.arena.literal(idx, 1);
                        let w0_neg_pos = if self.lit_val(w0.negated()) > 0 {
                            None // w0 is false, check if ~w0 = true => w0's negation value
                        } else {
                            // w0 is false means w0's var is assigned with w0 being false
                            let vi = w0.variable().index();
                            if self.var_is_assigned(vi) {
                                Some(self.var_data[vi].trail_pos as usize)
                            } else {
                                None
                            }
                        };
                        let w1_neg_pos = {
                            let vi = w1.variable().index();
                            if self.var_is_assigned(vi) {
                                Some(self.var_data[vi].trail_pos as usize)
                            } else {
                                None
                            }
                        };
                        // At least one watched false literal must have trail
                        // pos >= minimal_qhead for BCP to discover this unit.
                        let reachable = w0_neg_pos.is_some_and(|p| p >= minimal_qhead)
                            || w1_neg_pos.is_some_and(|p| p >= minimal_qhead)
                            || unit_lit == w0  // unit lit is watched; BCP propagates it
                            || unit_lit == w1; // unit lit is watched; BCP propagates it
                        debug_assert!(
                            reachable,
                            "BUG: minimal trail rewind (#8095) would miss unit clause {idx} \
                             (unit_lit={unit_lit:?}, qhead={minimal_qhead}, \
                             w0={w0:?} pos={w0_neg_pos:?}, w1={w1:?} pos={w1_neg_pos:?})"
                        );
                    }
                }
            }
        }

        // Post-condition: every active clause with len >= 2 should have watches.
        // Missing watches cause missed propagations — a soundness bug that is
        // extremely hard to diagnose because it manifests as non-deterministic
        // incorrect SAT/UNSAT results.
        #[cfg(debug_assertions)]
        {
            for idx in self.arena.active_indices() {
                let off_header = idx;
                if self.arena.is_empty_clause(off_header) || self.arena.len_of(off_header) < 2 {
                    continue;
                }
                let cref = ClauseRef(idx as u32);
                let lit0 = self.arena.literal(idx, 0);
                let lit1 = self.arena.literal(idx, 1);
                // attach_clause_watches(cref, (lit0, lit1), ..) stores watches under
                // lit0/lit1 (not negations). During BCP, propagating p scans watches[¬p].
                debug_assert!(
                    {
                        let w0 = self.watches.get_watches(lit0);
                        let w1 = self.watches.get_watches(lit1);
                        (0..w0.len()).any(|i| w0.clause_ref(i) == cref)
                            && (0..w1.len()).any(|i| w1.clause_ref(i) == cref)
                    },
                    "BUG: rebuild_watches: active clause {idx} (len={}) missing watch on \
                     lit0={lit0:?} or lit1={lit1:?}",
                    self.arena.len_of(off_header)
                );
            }
        }
    }
}
