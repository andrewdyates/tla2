// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core CDCL propagation and decision helpers.
//!
//! Contains literal value queries, assignment/enqueue, VSIDS/VMTF decision
//! selection with random injection, 2-watched literal initialization, and
//! the hot BCP loop with deferred watch buffer swap and in-place compaction.
//!
//! BCP is unified into a single const-generic `propagate_bcp::<MODE>()`
//! function (#5037). The compiler monomorphizes three variants at compile
//! time, and `if MODE == ...` branches on the const parameter are eliminated
//! as dead code, producing identical machine code to the hand-specialized
//! versions.

// BCP replacement scan loops use `for k in pos..len` where k is needed both
// to index `clause_lits[k]` and to call `swap_literals(clause_idx, _, k)`.
// The clippy suggestion `.iter().enumerate().take().skip()` adds iterator
// overhead in the hottest loop of the solver.
#![allow(clippy::needless_range_loop)]

use super::*;
use crate::solver_log::solver_log;

/// BCP mode constants for the unified `propagate_bcp::<MODE>()` function.
///
/// These are used as const-generic parameters. The compiler eliminates
/// dead branches at monomorphization time, so mode checks are zero-cost.
pub(super) mod bcp_mode {
    pub(crate) const SEARCH: u8 = 0;
    pub(crate) const PROBE: u8 = 1;
    pub(crate) const VIVIFY: u8 = 2;
}

impl Solver {
    #[inline]
    pub(super) fn lit_value(&self, lit: Literal) -> Option<bool> {
        match z4_prefetch::val_at(&self.vals, lit.index()) {
            0 => None,
            v => Some(v > 0),
        }
    }

    /// Branch-free literal value: 1 (true), -1 (false), 0 (unassigned).
    ///
    /// Uses unchecked access in release builds (via `val_at`) to match
    /// CaDiCaL's raw pointer `vals[lit]` pattern. The invariant that
    /// `lit.index() < vals.len()` is maintained by construction (vals is
    /// sized `2 * num_vars`, every literal satisfies `index() < 2 * num_vars`).
    #[inline]
    pub(super) fn lit_val(&self, lit: Literal) -> i8 {
        z4_prefetch::val_at(&self.vals, lit.index())
    }

    /// Check if a variable is assigned using the branch-free vals[] array.
    /// vals[] is the sole source of truth for assignment state (#3758 Phase 3).
    #[inline]
    pub(super) fn var_is_assigned(&self, var_idx: usize) -> bool {
        // vals[positive_literal(var)] is 0 iff unassigned, nonzero iff assigned.
        z4_prefetch::val_at(&self.vals, var_idx * 2) != 0
    }

    /// Get variable assignment from vals[] as Option<bool>.
    /// vals[] is the sole source of truth for assignment state (#3758 Phase 3).
    #[inline]
    pub(super) fn var_value_from_vals(&self, var_idx: usize) -> Option<bool> {
        match z4_prefetch::val_at(&self.vals, var_idx * 2) {
            0 => None,
            v => Some(v > 0),
        }
    }

    /// Compute the assignment level for a propagated literal (ChrBT).
    ///
    /// CaDiCaL propagate.cpp:25-56: the assignment level is the maximum level
    /// among the *other* literals in the reason clause. This can be lower than
    /// `decision_level` when chronological backtracking has left out-of-order
    /// literals on the trail.
    ///
    /// Unassigned literals must be ignored here. Chronological backtracking
    /// intentionally leaves stale `var_data.level` metadata on variables after
    /// unassigning them, and inprocessing can add fresh clauses at level 0
    /// before those stale levels are scrubbed. Reading raw levels for
    /// unassigned reason literals can therefore manufacture an assignment level
    /// above the current `decision_level`, tripping root-level enqueue during
    /// preprocessing.
    ///
    /// Returns `decision_level` for decisions (no reason clause) or when ChrBT
    /// is disabled.
    #[inline]
    fn assignment_level(&self, lit: Literal, reason: ClauseRef) -> u32 {
        let clause_idx = reason.0 as usize;
        let lits = self.arena.literals(clause_idx);
        let len = lits.len();
        // Fast path: binary clauses (most common in BCP).
        // Position of propagated literal is not fixed; check both.
        if len == 2 {
            let other = if lits[0] == lit { lits[1] } else { lits[0] };
            // Use lit_val (i8 comparison) instead of lit_value (Option<bool>)
            // to avoid enum construction overhead in the hot BCP path.
            return if self.lit_val(other) < 0 {
                self.var_data[other.variable().index()]
                    .level
                    .min(self.decision_level)
            } else {
                0
            };
        }
        // General path: scan all non-self literals.
        // Uses lit_val (i8) instead of lit_value (Option<bool>) to avoid
        // enum construction + pattern matching per literal. The invariant
        // is: only falsified reason literals (val < 0) contribute to the
        // assignment level. Unassigned (val == 0) and satisfied (val > 0)
        // literals are skipped. CaDiCaL propagate.cpp:49 uses `val(other)`.
        let mut level = 0u32;
        let decision_level = self.decision_level;
        for &other in lits {
            if other == lit {
                continue;
            }
            if self.lit_val(other) >= 0 {
                continue;
            }
            let other_level = self.var_data[other.variable().index()].level;
            if other_level >= decision_level {
                // Early exit: can't exceed decision_level, and we found
                // a literal at or above it. CaDiCaL propagate.cpp:51-52.
                return decision_level;
            }
            if other_level > level {
                level = other_level;
            }
        }
        level
    }

    /// REQUIRES: variable is unassigned (assignment[var] == None)
    /// ENSURES: variable assigned at its actual assignment level (which may be
    ///          below `decision_level` under chronological backtracking),
    ///          literal appended to trail, vals[] updated for both polarities
    #[inline]
    pub(super) fn enqueue(&mut self, lit: Literal, reason: Option<ClauseRef>) {
        let var = lit.variable();
        let reason_clause = reason;
        // CaDiCaL propagate.cpp:140: assignment count overflow guard.
        // Ensures we never assign more variables than exist.
        debug_assert!(
            self.trail.len() < self.num_vars,
            "BUG: enqueue would exceed num_vars ({}) — trail already has {} entries",
            self.num_vars,
            self.trail.len(),
        );
        debug_assert!(
            !self.var_is_assigned(var.index()),
            "BUG: enqueue of already-assigned variable {} (lit {:?})",
            var.index(),
            lit
        );
        // CaDiCaL propagate.cpp:110: eliminated variables only via decision/external
        debug_assert!(
            !self.var_lifecycle.is_removed(var.index()) || reason.is_none(),
            "BUG: propagating eliminated variable {} with reason clause",
            var.index(),
        );
        // CaDiCaL propagate.cpp:151: save phase on every search assignment.
        // Keeps phases fresh between backtracks, especially during trail reuse.
        if !self.suppress_phase_saving {
            self.phase[var.index()] = lit.sign_i8();
        }
        // CaDiCaL propagate.cpp:130-140: with ChrBT enabled, compute the true
        // assignment level from the reason clause. This allows propagated
        // literals to have level < decision_level, enabling chronological
        // backtracking to keep more of the trail (#6998).
        // Computed before the var_data borrow to avoid &self / &mut conflict.
        let (assigned_level, assigned_reason) = if self.chrono_enabled {
            if let Some(reason) = reason_clause {
                let al = self.assignment_level(lit, reason);
                if al == 0 {
                    // CaDiCaL propagate.cpp:134-135: if assignment level is 0,
                    // the literal is a root-level unit. Mark as fixed so
                    // collect_level0_garbage fires correctly.
                    //
                    // Keep the reason clause (unlike CaDiCaL which clears it).
                    // Z4 uses lazy proof materialization: materialize_level0_unit_proofs()
                    // needs the reason clause to build LRAT proof chains for
                    // level-0 units discovered during ChrBT propagation (#6998).
                    if !self.var_lifecycle.is_fixed(var.index()) {
                        self.fixed_count += 1;
                        self.var_lifecycle.mark_fixed(var.index());
                    }
                    (0, reason.0)
                } else {
                    (al, reason.0)
                }
            } else {
                // Decision literal — always at decision_level.
                (self.decision_level, NO_REASON)
            }
        } else {
            // ChrBT disabled: always use decision_level (original behavior).
            (
                self.decision_level,
                reason_clause.map_or(NO_REASON, |r| r.0),
            )
        };
        // vals[] is the sole source of truth for assignment state (#3758 Phase 3).
        z4_prefetch::val_set(&mut self.vals, lit.index(), 1);
        z4_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        debug_assert!(
            assigned_level <= self.decision_level,
            "BUG: assignment_level {} exceeds decision_level {} for {:?}",
            assigned_level,
            self.decision_level,
            lit
        );
        let vd = &mut self.var_data[var.index()];
        vd.level = assigned_level;
        vd.reason = assigned_reason;
        vd.trail_pos = self.trail.len() as u32;
        // Clear binary reason flag; caller sets it for binary propagation (#8034).
        vd.set_binary_reason(false);
        if assigned_reason != NO_REASON {
            // Reason-edge mutations are tracked lazily via epoch refresh in
            // deletion/reduction paths; skip decision assignments (reason=None).
            self.bump_reason_graph_epoch();
        }
        self.trail.push(lit);
        solver_log!(
            self,
            "assign {} at level {} (dl={}) reason {:?}",
            lit.to_dimacs(),
            assigned_level,
            self.decision_level,
            reason_clause
        );
        // Propagation events are omitted from the decision trace because BCP is
        // deterministic: given the same decisions and clause database state,
        // propagations are identical. Omitting them keeps traces compact
        // (~50 bytes/conflict vs ~300 bytes with propagations), satisfying the
        // <200MB criterion for 1M-conflict runs.
        // CaDiCaL propagate.cpp:148-149: post-assignment polarity check
        debug_assert_eq!(
            self.vals[lit.index()],
            1,
            "BUG: val[lit] != 1 after enqueue of {lit:?}"
        );
        debug_assert_eq!(
            self.vals[lit.negated().index()],
            -1,
            "BUG: val[¬lit] != -1 after enqueue of {lit:?}"
        );
        // CaDiCaL propagate.cpp:141: trail length mirrors assignment count.
        // Sampled every 1024 enqueues: the O(num_vars) scan is too expensive to
        // run on every propagation (caused 50x debug slowdown on schup-l2s, #4967).
        // After #3758 Phase 3, vals[] is the sole source of truth. Count assigned
        // variables by scanning vals[] (positive literal positions only).
        #[cfg(debug_assertions)]
        if self.trail.len() & 0x3ff == 0 {
            let assigned_count = (0..self.num_vars)
                .filter(|&v| self.vals[v * 2] != 0)
                .count();
            debug_assert_eq!(
                assigned_count,
                self.trail.len(),
                "BUG: assigned variable count != trail.len() after enqueue of {lit:?}",
            );
        }
        // CaDiCaL propagate.cpp:160-166: prefetch watch list for -lit.
        // BCP will scan this list on the next propagation step. Issue a
        // non-blocking L2 prefetch to hide main-memory latency (~60-80 cycles)
        // behind the current propagation work.
        self.watches.prefetch_first(lit.negated());
    }

    /// Lightweight enqueue for BCP propagation assignments (Kissat fastassign.h).
    ///
    /// Skips work that is unnecessary during propagation:
    /// - `suppress_phase_saving` check (always false during search BCP)
    /// - `bump_reason_graph_epoch()` (caller batch-invalidates at BCP exit)
    /// - Periodic debug-mode trail/vals consistency scan
    /// - `solver_log!` macro (only useful in PROBE mode; PROBE still uses `enqueue`)
    ///
    /// REQUIRES: variable is unassigned, reason is always present (propagation)
    /// ENSURES: same post-conditions as `enqueue` for propagation assignments
    #[inline(always)]
    pub(super) fn enqueue_bcp(&mut self, lit: Literal, reason: ClauseRef) {
        let var = lit.variable();
        debug_assert!(
            self.trail.len() < self.num_vars,
            "BUG: enqueue_bcp would exceed num_vars ({}) — trail already has {} entries",
            self.num_vars,
            self.trail.len(),
        );
        debug_assert!(
            !self.var_is_assigned(var.index()),
            "BUG: enqueue_bcp of already-assigned variable {} (lit {:?})",
            var.index(),
            lit
        );
        // Phase saving: always active during search BCP (suppress_phase_saving=false).
        self.phase[var.index()] = lit.sign_i8();
        // ChrBT assignment level computation.
        let (assigned_level, assigned_reason) = if self.chrono_enabled {
            let al = self.assignment_level(lit, reason);
            if al == 0 {
                if !self.var_lifecycle.is_fixed(var.index()) {
                    self.fixed_count += 1;
                    self.var_lifecycle.mark_fixed(var.index());
                }
                (0, reason.0)
            } else {
                (al, reason.0)
            }
        } else {
            (self.decision_level, reason.0)
        };
        // vals[] update.
        z4_prefetch::val_set(&mut self.vals, lit.index(), 1);
        z4_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        debug_assert!(
            assigned_level <= self.decision_level,
            "BUG: assignment_level {} exceeds decision_level {} for {:?}",
            assigned_level,
            self.decision_level,
            lit
        );
        let vd = &mut self.var_data[var.index()];
        vd.level = assigned_level;
        vd.reason = assigned_reason;
        vd.trail_pos = self.trail.len() as u32;
        vd.set_binary_reason(false);
        // Skip bump_reason_graph_epoch — caller invalidates once at BCP exit.
        self.trail.push(lit);
        // Prefetch watch list for next propagation step.
        self.watches.prefetch_first(lit.negated());
    }

    /// Enqueue a single JIT-propagated literal, skipping vals[] writes (#8126).
    ///
    /// The JIT compiled function already set `vals[lit]=1` and `vals[~lit]=-1`
    /// inline during propagation. This method completes the enqueue by writing
    /// var_data, trail, and phase -- identical to `enqueue_bcp` minus the vals[]
    /// stores.
    ///
    /// Note: `batch_enqueue_from_jit()` is the primary entry point for JIT
    /// propagation replay. This single-literal variant is retained for testing
    /// and future use (e.g., single-clause JIT paths).
    #[allow(dead_code)]
    #[inline(always)]
    pub(super) fn enqueue_from_jit(&mut self, lit: Literal, reason: ClauseRef) {
        let var = lit.variable();
        debug_assert!(
            self.trail.len() < self.num_vars,
            "BUG: enqueue_from_jit would exceed num_vars ({}) — trail already has {} entries",
            self.num_vars,
            self.trail.len(),
        );
        // Phase saving.
        self.phase[var.index()] = lit.sign_i8();
        // ChrBT assignment level computation.
        let (assigned_level, assigned_reason) = if self.chrono_enabled {
            let al = self.assignment_level(lit, reason);
            if al == 0 {
                if !self.var_lifecycle.is_fixed(var.index()) {
                    self.fixed_count += 1;
                    self.var_lifecycle.mark_fixed(var.index());
                }
                (0, reason.0)
            } else {
                (al, reason.0)
            }
        } else {
            (self.decision_level, reason.0)
        };
        // vals[] already set by JIT — skip z4_prefetch::val_set.
        let vd = &mut self.var_data[var.index()];
        vd.level = assigned_level;
        vd.reason = assigned_reason;
        vd.trail_pos = self.trail.len() as u32;
        vd.set_binary_reason(false);
        self.trail.push(lit);
        self.watches.prefetch_first(lit.negated());
    }

    /// Batch-enqueue all JIT-propagated literals from the staging trail.
    ///
    /// Processes all entries in `jit_staging_trail[0..count]` in a tight loop,
    /// completing each enqueue by writing var_data, trail, and phase. The JIT
    /// has already set `vals[]` for each propagation (#8126).
    ///
    /// This replaces the per-propagation `enqueue_from_jit()` call in a Rust
    /// for-loop. Hoisting the `chrono_enabled` check and `decision_level` read
    /// outside the loop eliminates redundant field loads per iteration.
    ///
    /// Returns the number of propagations enqueued.
    #[inline(always)]
    pub(super) fn batch_enqueue_from_jit(&mut self, count: usize) -> u64 {
        let chrono = self.chrono_enabled;
        let dl = self.decision_level;
        let mut enqueued: u64 = 0;

        for i in 0..count {
            let encoded_lit = self.jit_staging_trail[i];
            let lit = Literal(encoded_lit);
            let var = lit.variable();
            let reason_id = self.jit_staging_reasons[var.index()];

            solver_log!(
                self,
                "JIT propagate: lit={} reason={}",
                lit.to_dimacs(),
                reason_id
            );

            // Phase saving.
            self.phase[var.index()] = lit.sign_i8();

            // Assignment level: chrono check hoisted outside loop.
            let (assigned_level, assigned_reason) = if chrono {
                let reason = ClauseRef(reason_id);
                let al = self.assignment_level(lit, reason);
                if al == 0 {
                    if !self.var_lifecycle.is_fixed(var.index()) {
                        self.fixed_count += 1;
                        self.var_lifecycle.mark_fixed(var.index());
                    }
                    (0, reason_id)
                } else {
                    (al, reason_id)
                }
            } else {
                (dl, reason_id)
            };

            // var_data update (vals[] already set by JIT).
            let vd = &mut self.var_data[var.index()];
            vd.level = assigned_level;
            vd.reason = assigned_reason;
            vd.trail_pos = self.trail.len() as u32;
            vd.set_binary_reason(false);
            self.trail.push(lit);
            self.watches.prefetch_first(lit.negated());
            enqueued += 1;
        }
        enqueued
    }

    /// Enqueue a binary propagation with a literal reason (#8034).
    ///
    /// Kissat fastassign.h:12-19: stores a tagged literal in `VarData.reason`
    /// instead of a `ClauseRef`. The reason literal is the OTHER (false)
    /// literal from the binary clause. Jump reasons: if the reason literal's
    /// own reason is also binary, store the transitive reason to shorten
    /// reason chains (reducing arena dereferences during conflict analysis).
    ///
    /// REQUIRES: variable is unassigned, SEARCH mode, decision_level > 0, LRAT disabled
    /// ENSURES: variable assigned with binary literal reason
    #[inline(always)]
    pub(super) fn enqueue_binary_reason(&mut self, lit: Literal, mut reason_lit: Literal) {
        let var = lit.variable();
        debug_assert!(
            self.trail.len() < self.num_vars,
            "BUG: enqueue_binary_reason would exceed num_vars ({}) -- trail already has {} entries",
            self.num_vars,
            self.trail.len(),
        );
        debug_assert!(
            !self.var_is_assigned(var.index()),
            "BUG: enqueue_binary_reason of already-assigned variable {} (lit {:?})",
            var.index(),
            lit
        );
        debug_assert!(
            self.decision_level > 0,
            "BUG: enqueue_binary_reason at level 0"
        );
        // Jump reason: if the reason literal's own reason is also binary,
        // follow the chain one step. This shortens reason chains, reducing
        // arena dereferences during conflict analysis. Kissat fastassign.h:12-19.
        let other_var = reason_lit.variable().index();
        let other_vd = self.var_data[other_var];
        if other_vd.is_binary_reason() {
            reason_lit = Literal(binary_reason_lit(other_vd.reason));
        }
        // Phase saving: always active during search BCP.
        self.phase[var.index()] = lit.sign_i8();
        // ChrBT assignment level: for binary reasons, the assignment level
        // is the reason literal's level (single other literal in the clause).
        let assigned_level = if self.chrono_enabled {
            let reason_level = self.var_data[reason_lit.variable().index()].level;
            if self.lit_val(reason_lit) < 0 {
                reason_level.min(self.decision_level)
            } else {
                0
            }
        } else {
            self.decision_level
        };
        if assigned_level == 0 {
            if !self.var_lifecycle.is_fixed(var.index()) {
                self.fixed_count += 1;
                self.var_lifecycle.mark_fixed(var.index());
            }
        }
        // vals[] update.
        z4_prefetch::val_set(&mut self.vals, lit.index(), 1);
        z4_prefetch::val_set(&mut self.vals, lit.negated().index(), -1);
        debug_assert!(
            assigned_level <= self.decision_level,
            "BUG: assignment_level {} exceeds decision_level {} for {:?}",
            assigned_level,
            self.decision_level,
            lit
        );
        let vd = &mut self.var_data[var.index()];
        vd.level = assigned_level;
        vd.reason = make_binary_reason(reason_lit.0);
        vd.trail_pos = self.trail.len() as u32;
        vd.set_binary_reason(true);
        // Skip bump_reason_graph_epoch -- caller invalidates once at BCP exit.
        self.trail.push(lit);
        // Prefetch watch list for next propagation step.
        self.watches.prefetch_first(lit.negated());
    }

    /// Make a decision (assign without reason, start new decision level)
    ///
    /// REQUIRES: variable not eliminated, variable unassigned
    /// ENSURES: decision_level incremented, trail_lim extended, literal enqueued with no reason
    #[inline]
    pub(super) fn decide(&mut self, lit: Literal) {
        // CaDiCaL propagate.cpp:188: all propagations complete before deciding
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: deciding {lit:?} with pending propagations (qhead={}, trail={})",
            self.qhead,
            self.trail.len(),
        );
        // O(1) check — must be assert!() because deciding on an eliminated
        // variable silently corrupts the search (stale watch lists, wrong model).
        assert!(
            !self.var_lifecycle.is_removed(lit.variable().index()),
            "BUG: decided removed variable {}",
            lit.variable().index()
        );
        self.decision_level += 1;
        // trail_lim monotonicity: each decision level's trail start must be >=
        // the previous level's start. Violation indicates a backtracking bug
        // that corrupted the trail/trail_lim correspondence (#4172).
        debug_assert!(
            self.trail_lim.is_empty()
                || *self.trail_lim.last().expect("invariant: non-empty") <= self.trail.len(),
            "BUG: trail_lim monotonicity violated: last={}, trail.len()={}",
            self.trail_lim.last().copied().unwrap_or(0),
            self.trail.len()
        );
        self.trail_lim.push(self.trail.len());
        self.num_decisions += 1;
        if self.stable_mode {
            self.stats.stable_decisions += 1;
        } else {
            self.stats.focused_decisions += 1;
        }
        self.trace_decide(lit);
        self.enqueue(lit, None);
        solver_log!(
            self,
            "decide {} level {}",
            self.fmt_lit(lit),
            self.decision_level
        );
    }

    /// Pick the next decision variable, selecting between VSIDS (stable mode)
    /// and VMTF (focused mode). Checks for random decision injection first.
    /// Eliminated variables (BVE) are never returned.
    #[inline]
    pub(super) fn pick_next_decision_variable(&mut self) -> Option<Variable> {
        // Z3-style per-decision random frequency: with probability random_var_freq,
        // pick a random unassigned variable. Z3 SMT default: 0.01 (1%).
        if self.cold.random_var_freq > 0.0 {
            let mut rng = Random::new(self.num_decisions.wrapping_add(self.num_conflicts));
            if rng.generate_double() < self.cold.random_var_freq {
                let num_vars = self.num_vars;
                if num_vars > 0 {
                    for _ in 0..num_vars {
                        let idx = rng.pick(num_vars);
                        if !self.var_is_assigned(idx) && !self.var_lifecycle.is_removed(idx) {
                            self.stats.random_decisions += 1;
                            return Some(Variable(idx as u32));
                        }
                    }
                }
            }
        }

        // Try random decision injection (CaDiCaL-style burst)
        if let Some(var) = self.next_random_decision() {
            return Some(var);
        }
        let result = self.pick_branch_variable_by_active_heuristic();
        // CaDiCaL decide.cpp:186 — postcondition: returned variable is unassigned
        // and not eliminated. Catches heap corruption or stale assignment state.
        if let Some(var) = result {
            debug_assert!(
                !self.var_is_assigned(var.index()),
                "BUG: pick_next_decision_variable returned assigned variable {}",
                var.index()
            );
            debug_assert!(
                !self.var_lifecycle.is_removed(var.index()),
                "BUG: pick_next_decision_variable returned removed variable {}",
                var.index()
            );
        }
        result
    }

    /// Start a new random decision burst. Sets burst length and schedules
    /// the next burst using CaDiCaL's phase * ln(phase) interval growth.
    pub(crate) fn start_random_sequence(&mut self) {
        let count = self.cold.random_decision_phases + 1;
        self.cold.random_decision_phases = count;

        // Burst length: RANDEC_LENGTH * ln(count + 10)
        let length = (RANDEC_LENGTH * ((count + 10) as f64).ln()) as u64;
        self.cold.randomized_deciding = length.max(1);

        // Schedule next burst: conflicts + phases * ln(phases) * RANDEC_INT
        let phases = self.cold.random_decision_phases as f64;
        let delta = phases * phases.ln();
        self.cold.next_random_decision = self
            .num_conflicts
            .saturating_add((delta * RANDEC_INT) as u64);
    }

    /// Check if a random decision should be made. Returns a random unassigned
    /// variable if we are in a random burst, or starts one if the conflict
    /// threshold is reached. CaDiCaL only enables this in focused mode.
    fn next_random_decision(&mut self) -> Option<Variable> {
        // Only inject random decisions in focused mode (CaDiCaL: randecfocused=1, randecstable=0)
        if self.stable_mode {
            return None;
        }

        // Not yet time for random decisions
        if self.num_conflicts < self.cold.next_random_decision {
            return None;
        }

        // Start a new random burst if not already in one
        if self.cold.randomized_deciding == 0 {
            // CaDiCaL decide.cpp:80: delay random burst start if too deep.
            // `level > assumptions.size()` — with no assumptions, only level 0.
            if self.decision_level > 0 {
                return None;
            }
            self.start_random_sequence();
        }

        // Pick a random unassigned, non-eliminated variable using LCG seeded from decisions
        let num_vars = self.num_vars;
        if num_vars == 0 {
            return None;
        }
        let mut rng = Random::new(self.num_decisions);
        for _ in 0..num_vars {
            let idx = rng.pick(num_vars);
            if !self.var_is_assigned(idx) && !self.var_lifecycle.is_removed(idx) {
                self.stats.random_decisions += 1;
                return Some(Variable(idx as u32));
            }
        }
        // All sampled vars are assigned or eliminated; fall through to normal decision
        None
    }

    /// Decrement the random decision burst counter on conflict.
    /// Called from conflict analysis paths to end the burst after enough conflicts.
    #[inline]
    pub(super) fn on_conflict_random_decision(&mut self) {
        self.poll_process_memory_limit();
        if self.cold.randomized_deciding > 0 {
            self.cold.randomized_deciding -= 1;
        }
    }

    /// Initialize 2-watched literals for all clauses.
    pub(super) fn initialize_watches(&mut self) {
        let all_indices: Vec<usize> = self.arena.indices().collect();
        for i in all_indices {
            let off = i;
            let clause_ref = ClauseRef(i as u32);
            let clause_len = self.arena.len_of(off);
            // Catch eliminated variables in active clauses during watch init.
            #[cfg(debug_assertions)]
            if clause_len >= 2 {
                for j in 0..clause_len {
                    let lit = self.arena.literal(off, j);
                    debug_assert!(
                        !self.var_lifecycle.is_removed(lit.variable().index()),
                        "BUG: initialize_watches: active clause {off} (len={clause_len}, \
                         learned={}) contains eliminated variable {} at position {j}",
                        self.arena.is_learned(off),
                        lit.variable().index(),
                    );
                }
            }
            if clause_len >= 2 {
                let lit0 = self.arena.literal(off, 0);
                let mut lit1 = self.arena.literal(off, 1);
                // Guard: if the first two literals are identical, scan for a
                // distinct literal to watch (#6506). Duplicate literals can
                // enter the arena via theory propagation or inprocessing paths
                // that skip clause normalization. The 2WL scheme requires
                // distinct watch pointers so we must find a non-duplicate pair.
                if lit0 == lit1 {
                    let mut found = false;
                    for j in 2..clause_len {
                        let candidate = self.arena.literal(off, j);
                        if candidate != lit0 {
                            // Swap candidate into position 1 in the arena
                            self.arena.swap_literals(off, 1, j);
                            lit1 = candidate;
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        // All literals are identical — clause is effectively
                        // unit. Skip watch attachment (unit handled elsewhere).
                        continue;
                    }
                }
                let mut watched = [lit0, lit1];
                let watched = self
                    .prepare_watched_literals(&mut watched, WatchOrderPolicy::Preserve)
                    .expect("initialize_watches requires clauses with len >= 2");
                self.attach_clause_watches(clause_ref, watched, clause_len == 2);
            }
        }
        // Binary-first invariant is maintained incrementally on insert.
        self.watches.debug_assert_binary_first();
    }

    /// Propagate unit clauses using 2-watched literals.
    /// Propagate and check for UNSAT: returns `true` if `has_empty_clause`
    /// is set or propagation discovers a conflict at decision level 0.
    ///
    /// When a level-0 propagation conflict is found, records the BCP resolution
    /// chain for LRAT proof generation (#4397).
    ///
    /// Used as the standard inprocessing guard after any technique that may
    /// produce unit clauses or derive empty clauses.
    #[inline]
    pub(super) fn propagate_check_unsat(&mut self) -> bool {
        if self.has_empty_clause {
            return true;
        }
        // Level-0 propagation after inprocessing: no probing_mode, no vivify
        // flags — use the lightweight search variant.
        if let Some(conflict_ref) = self.search_propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            true
        } else {
            false
        }
    }

    /// Probe-specialized propagation with probe-parent tracking and HBR support.
    ///
    /// Always uses safe BCP even with `unsafe-bcp` enabled: HBR during PROBE
    /// can call `add_watch(false_lit, ...)` which may reallocate the watch list
    /// Vec, invalidating raw pointers. The safe version avoids this by swapping
    /// the list out first. PROBE mode is rare and not performance-critical.
    #[inline]
    pub(super) fn probe_propagate(&mut self) -> Option<ClauseRef> {
        self.propagate_bcp::<{ bcp_mode::PROBE }>()
    }

    /// Legacy propagation entry point kept for compatibility with tests and
    /// verification harnesses.
    #[cfg(any(test, kani))]
    #[inline]
    pub(super) fn propagate(&mut self) -> Option<ClauseRef> {
        self.propagate_bcp::<{ bcp_mode::PROBE }>()
    }

    /// Search-specialized BCP propagation — no probing or vivification overhead.
    ///
    /// When the `unsafe-bcp` feature is enabled, dispatches to the
    /// CaDiCaL-exact raw-pointer implementation for maximum throughput.
    #[inline]
    pub(super) fn search_propagate(&mut self) -> Option<ClauseRef> {
            if self.compiled_formula.is_some() {
            return self.propagate_hybrid();
        }
        self.search_propagate_standard()
    }

    /// Standard 2WL BCP without JIT. Called directly by propagate_hybrid after
    /// the JIT pre-scan, and as the fallback when JIT is not compiled.
    #[inline]
    pub(super) fn search_propagate_standard(&mut self) -> Option<ClauseRef> {
        #[cfg(feature = "unsafe-bcp")]
        {
            self.propagate_bcp_unsafe::<{ bcp_mode::SEARCH }>()
        }
        #[cfg(not(feature = "unsafe-bcp"))]
        {
            self.propagate_bcp::<{ bcp_mode::SEARCH }>()
        }
    }

    /// Vivification-specialized BCP propagation — vivify-skip check, no probing.
    ///
    /// When the `unsafe-bcp` feature is enabled, dispatches to the
    /// CaDiCaL-exact raw-pointer implementation for maximum throughput.
    #[inline]
    pub(super) fn vivify_propagate(&mut self) -> Option<ClauseRef> {
        #[cfg(feature = "unsafe-bcp")]
        {
            self.propagate_bcp_unsafe::<{ bcp_mode::VIVIFY }>()
        }
        #[cfg(not(feature = "unsafe-bcp"))]
        {
            self.propagate_bcp::<{ bcp_mode::VIVIFY }>()
        }
    }
}
