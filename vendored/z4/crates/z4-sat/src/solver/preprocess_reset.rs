// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Chronological backtracking and search state reset.
//!
//! Split from `preprocess.rs` for file-size compliance (#5142).
//! Contains chrono backtracking level computation and incremental
//! solve reset logic.

use super::*;

impl Solver {
    /// Handle initial unit clauses (before solve loop).
    ///
    /// Returns `None` on success, or `Some(conflict_ref)` if a contradictory
    /// unit clause is found (all its literals falsified). The caller should
    /// use the conflict ref for LRAT hint collection via
    /// `record_level0_conflict_chain`.
    pub(super) fn process_initial_clauses(&mut self) -> Option<ClauseRef> {
        // Must be at decision level 0 when processing initial units
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: process_initial_clauses at level {} (expected 0)",
            self.decision_level,
        );
        let all_indices: Vec<usize> = self.arena.indices().collect();
        for i in all_indices {
            if !self.arena.is_active(i) {
                continue;
            }
            let off = i;
            if self.arena.len_of(off) == 1 {
                let lit = self.arena.literal(off, 0);
                if let Some(val) = self.lit_value(lit) {
                    if !val {
                        // Unit clause is already falsified — return conflict ref
                        // so caller can collect LRAT resolution hints.
                        return Some(ClauseRef(off as u32));
                    }
                    // Already satisfied, skip
                } else {
                    // Propagate unit clause (CaDiCaL: clause.cpp:361-363).
                    // Use reason=None: unit clauses have no antecedent literals,
                    // so they cannot be used as reason clauses in conflict
                    // analysis (which requires len >= 2). (#6257)
                    // Store proof ID for LRAT and clause-trace (#6368).
                    let cid = self.cold.clause_ids.get(off).copied().unwrap_or(0);
                    if cid != 0 {
                        self.unit_proof_id[lit.variable().index()] = cid;
                    }
                    self.enqueue(lit, None);
                    self.fixed_count += 1;
                    self.var_lifecycle.mark_fixed(lit.variable().index());
                }
            }
        }
        None
    }

    /// Pick the polarity for a decision variable using phase saving with target phases
    ///
    /// Phase selection priority:
    /// 1. Target phase (if available): Uses the assignment from the longest conflict-free
    ///    trail seen. This guides the search toward promising regions.
    /// 2. Saved phase: The last polarity this variable was assigned.
    /// 3. Default: Positive polarity if no phase information exists.
    ///
    /// Target phases help the solver explore variations of assignments that were
    /// close to satisfying the formula.
    pub(super) fn pick_phase(&self, var: Variable) -> Literal {
        let idx = var.index();
        // Variable must be within bounds
        debug_assert!(
            idx < self.num_vars,
            "BUG: pick_phase for var {} >= num_vars {}",
            idx,
            self.num_vars,
        );
        // Variable must be unassigned (we're picking a phase for a decision)
        debug_assert!(
            !self.var_is_assigned(idx),
            "BUG: pick_phase for already-assigned var {idx}",
        );

        // Target phases only in stable mode (CaDiCaL opts.target=1).
        if self.stable_mode {
            let tp = self.target_phase[idx];
            if tp != 0 {
                return if tp > 0 {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                };
            }
        }

        // Kissat-style focused-mode phase cycling (decide.c:178-187).
        // Uses `(switched >> 1) & 7` to produce an 8-step cycle where
        // slots 1 and 3 force INITIAL_PHASE (+1) and inverted (-1),
        // overriding saved phases 25% of the time. This diversifies
        // focused-mode search on hard combinatorial instances like
        // battleship-14-26 and stable-300 (#8085).
        if !self.stable_mode {
            let slot = (self.cold.mode_switch_count >> 1) & 7;
            match slot {
                1 => return Literal::positive(var),
                3 => return Literal::negative(var),
                _ => {}
            }
        }

        // Fall back to saved phase (0 = unset defaults to positive)
        if self.phase[idx] < 0 {
            Literal::negative(var)
        } else {
            Literal::positive(var)
        }
    }

    /// Compute the actual backtrack level, deciding between chronological and
    /// non-chronological backtracking based on the jump distance.
    ///
    /// Based on the SAT'18 paper "Chronological Backtracking" and CaDiCaL's
    /// `chronoreusetrail` optimization:
    ///
    /// - If the jump would skip many levels (> CHRONO_LEVEL_LIMIT), use
    ///   chronological backtracking (just go back one level)
    /// - Otherwise, try to reuse trail by finding the best variable above the
    ///   jump level and backtracking only to that level
    pub(super) fn compute_chrono_backtrack_level(&mut self, jump_level: u32) -> u32 {
        // CaDiCaL analyze.cpp:653: backtrack level must be strictly below current level
        debug_assert!(
            jump_level < self.decision_level,
            "BUG: jump_level ({jump_level}) >= decision_level ({})",
            self.decision_level,
        );

        if !self.chrono_enabled {
            return jump_level;
        }

        // Unit clauses (jump_level == 0) MUST backtrack to level 0.
        // Chronological backtracking cannot be used here because the unit literal
        // would be enqueued at a non-zero level, and subsequent backtracking could
        // undo the assignment. The unit clause would then be unsatisfied in the model.
        // This was the root cause of #1696.
        if jump_level == 0 {
            return 0;
        }

        // If jump level is at or above current level - 1, no point in chrono BT
        if jump_level >= self.decision_level.saturating_sub(1) {
            return jump_level;
        }

        // Compute how many levels we'd skip with NCB
        let skip_levels = self.decision_level - jump_level;

        let actual_level = if skip_levels > CHRONO_LEVEL_LIMIT {
            // Too many levels to skip - use chronological backtracking
            self.stats.chrono_backtracks += 1;
            self.decision_level - 1
        } else if self.chrono_reuse_trail {
            // CaDiCaL-style trail reuse: find the best variable above the jump level
            // and only backtrack to that level to keep more of the useful trail.
            // CaDiCaL analyze.cpp:675 applies this unconditionally in both stable
            // and focused modes — use_scores() selects the metric (VSIDS activity
            // for stable, bump order for focused), not whether to apply trail reuse.
            self.compute_chrono_reuse_level(jump_level)
        } else {
            // Use non-chronological backtracking
            jump_level
        };

        // Emit diagnostic event when chrono BT was chosen (#4172, #4674).
        if actual_level != jump_level {
            self.emit_diagnostic_chrono_backtrack(self.decision_level, jump_level, actual_level);
        }

        actual_level
    }

    /// Find the best variable above the jump level and return its level.
    ///
    /// This implements CaDiCaL's `chronoreusetrail` optimization. Instead of
    /// always backtracking to the asserting level, we look for valuable variables
    /// above that level. In stable mode, we look for the variable with highest
    /// VSIDS activity. In focused mode, we look for the most recently bumped
    /// variable. We then backtrack only to the level containing that trail
    /// position, preserving more of the useful search state.
    ///
    /// Key: we use trail POSITION to determine level, not the variable's stored
    /// level. This is important for correctness with chronological backtracking
    /// where variables can have out-of-order level assignments.
    pub(super) fn compute_chrono_reuse_level(&mut self, jump_level: u32) -> u32 {
        // Precondition: jump_level must be below decision level
        debug_assert!(
            jump_level < self.decision_level,
            "BUG: compute_chrono_reuse_level: jump_level {} >= decision_level {}",
            jump_level,
            self.decision_level,
        );
        // Get the trail position where jump_level+1 starts
        let start_pos = if (jump_level as usize) < self.trail_lim.len() {
            self.trail_lim[jump_level as usize]
        } else {
            return jump_level;
        };

        // If no assignments above jump level, just use jump level
        if start_pos >= self.trail.len() {
            return jump_level;
        }

        // Find the best variable's trail position (not just index)
        let mut best_pos: Option<usize> = None;

        for i in start_pos..self.trail.len() {
            let var = self.trail[i].variable();
            let is_better = match best_pos {
                Some(current_best) => self.branch_priority_is_lower(
                    self.trail[current_best].variable(),
                    var,
                    self.active_branch_heuristic,
                ),
                None => true,
            };
            if is_better {
                best_pos = Some(i);
            }
        }

        // Find the level containing the best variable's trail position
        // CaDiCaL: while (res < level - 1 && control[res + 1].trail <= best_pos) res++;
        let Some(best_pos) = best_pos else {
            return jump_level;
        };

        // CaDiCaL: while (res < level - 1 && control[res + 1].trail <= best_pos) res++;
        // In Z4: trail_lim[i] = start of level i+1's assignments
        // So to match control[res+1].trail (start of level res+1), use trail_lim[res]
        let mut res = jump_level;
        while res < self.decision_level - 1
            && (res as usize) < self.trail_lim.len()
            && self.trail_lim[res as usize] <= best_pos
        {
            res += 1;
        }

        if res > jump_level {
            self.stats.chrono_backtracks += 1;
        }

        // Post-condition: result must be between jump_level and decision_level - 1
        debug_assert!(
            res >= jump_level && res < self.decision_level,
            "BUG: chrono_reuse_level result {} out of range [{}, {})",
            res,
            jump_level,
            self.decision_level,
        );
        res
    }

    /// Reset transient search state so the solver can be reused across multiple `solve()` calls.
    ///
    /// This keeps the clause database intact (including learned clauses), but clears assignments,
    /// watches, and scheduling state that assume a fresh search.
    pub(super) fn reset_search_state(&mut self) {
        #[cfg(debug_assertions)]
        {
            // Proof mode must not toggle during a solve call. Snapshot it at
            // solve/reset entry so proof-sensitive passes can assert stability.
            self.solve_proof_mode = Some(self.proof_manager.is_some());
        }

        // #5031: Restore formula to pristine state after inprocessing.
        //
        // The previous solve's inprocessing may have permanently modified
        // clause_db in ways not tracked by the reconstruction stack:
        // - Decompose: substitutes equivalent variables and deletes subsumed
        //   clauses WITHOUT reconstruction entries
        // - Congruence: merges gates and deletes duplicate clauses
        // - BVE/BCE: deletes clauses WITH reconstruction entries
        // - Level-0 GC: deletes satisfied clauses permanently
        //
        // Drain reconstruction stack first (BVE/BCE witness clauses).
        if self.inproc.reconstruction.len() > 0 {
            let drain_result = self.inproc.reconstruction.drain_witness_entries();
            self.inproc.reconstruction = ReconstructionStack::new();

            // Targeted reactivation (#3644 Wave 3): reactivate variables
            // from drained witness entries. Give them competitive VSIDS
            // activity so they are actually decided (#7981).
            let reactivation_activity = self.vsids.current_increment();
            for &idx in &drain_result.reactivate_vars {
                if idx < self.var_lifecycle.len() && self.var_lifecycle.can_reactivate(idx) {
                    if let Some(ref writer) = self.cold.diagnostic_trace {
                        writer.emit_var_transition(
                            idx as u32,
                            crate::diagnostic_trace::VarState::Eliminated,
                            crate::diagnostic_trace::VarState::Active,
                            self.cold.diagnostic_pass,
                        );
                    }
                    self.var_lifecycle.reactivate(idx);
                    self.inproc.bve.clear_removed_external(idx);
                    // #7981: Reactivated variables had zero activity from
                    // BVE elimination. Without a competitive score they sit
                    // at the bottom of the decision heap and may never be
                    // branched on, causing incomplete search → false UNSAT.
                    let var = Variable(idx as u32);
                    if self.vsids.activity(var) == 0.0 {
                        self.vsids.set_activity(var, reactivation_activity);
                    }
                }
            }
        }

        // #5031/#5608: Restore original clauses for incremental solving.
        //
        // Two cases:
        // (a) Inprocessing deleted some original clauses (subsumption, BVE,
        //     decompose, level-0 GC): rebuild arena from original_clauses
        //     ledger. Count only non-learned clauses to detect this — learned
        //     clauses inflate active_count and mask missing originals.
        // (b) No deletions, but new originals were appended (bound-tightening
        //     from add_upper_bound/add_lower_bound): add only the new ones.
        if !self.cold.original_ledger.is_empty() {
            let active_original_count = self
                .arena
                .active_indices()
                .filter(|&idx| !self.arena.is_learned(idx))
                .count();
            if active_original_count < self.cold.original_ledger.num_clauses() {
                // Case (a): Some originals were deleted by inprocessing.
                // Rebuild arena from original_ledger.
                //
                // Do NOT preserve learned clauses across rebuilds. While
                // learned clauses are logically valid (CDCL consequences),
                // their presence after a rebuild causes spurious UNSAT on
                // incremental optimization (TSP regression). The root cause:
                // learned clauses derived under BVE-simplified clause sets
                // can force level-0 assignments that conflict with new bounds.
                //
                // Callers that need learned clause preservation should call
                // set_incremental_mode() before the first solve to prevent
                // destructive inprocessing from running (#5608).
                let rebuild_reactivation_activity = self.vsids.current_increment();
                for i in 0..self.var_lifecycle.len() {
                    if self.var_lifecycle.is_removed(i) && self.var_lifecycle.can_reactivate(i) {
                        self.var_lifecycle.reactivate(i);
                        self.inproc.bve.clear_removed_external(i);
                        // #7981: Give reactivated variables competitive VSIDS
                        // activity so they are branched on during search.
                        let var = Variable(i as u32);
                        if self.vsids.activity(var) == 0.0 {
                            self.vsids.set_activity(var, rebuild_reactivation_activity);
                        }
                    }
                }
                self.arena = ClauseArena::new();
                if self.cold.lrat_enabled {
                    self.cold.clause_ids.clear();
                }
                for (ordinal, clause) in self.cold.original_ledger.iter_clauses().enumerate() {
                    let idx = self.arena.add(clause, false);
                    if self.cold.lrat_enabled {
                        if idx >= self.cold.clause_ids.len() {
                            self.cold.clause_ids.resize(idx + 1, 0);
                        }
                        self.cold.clause_ids[idx] = (ordinal as u64) + 1;
                    }
                }
                self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
            } else if self.cold.incremental_original_boundary
                < self.cold.original_ledger.num_clauses()
            {
                // Case (b): No rebuild needed, just add new original clauses.
                let start = self.cold.incremental_original_boundary;
                for (ordinal, clause) in self
                    .cold
                    .original_ledger
                    .iter_clauses_from(start)
                    .enumerate()
                {
                    let idx = self.arena.add(clause, false);
                    if self.cold.lrat_enabled {
                        if idx >= self.cold.clause_ids.len() {
                            self.cold.clause_ids.resize(idx + 1, 0);
                        }
                        self.cold.clause_ids[idx] = (start + ordinal + 1) as u64;
                    }
                }
                self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
            }
        }

        // Core assignment / trail state (#3758 Phase 3: vals[] is sole source)
        self.vals.fill(0);
        // Clear conflict analyzer seen marks before resetting var_data, because
        // seen marks now live in var_data.flags (#6994). Without this, the fill
        // below silently erases seen marks without updating seen_true_count.
        self.conflict.clear(&mut self.var_data);
        self.var_data.fill(VarData::UNASSIGNED);
        self.bump_reason_graph_epoch();
        self.trail.clear();
        self.trail_lim.clear();
        self.decision_level = 0;
        self.qhead = 0;
        #[cfg(feature = "jit")]
        {
            self.jit_qhead = 0;
        }

        // Clear LRAT proof provenance arrays (#5229). Without this, stale
        // proof IDs from the previous solve persist across incremental solves.
        // The 3-tier fallback (reason → unit_proof_id → level0_proof_id)
        // could consult stale entries if a variable ends up at level 0 with
        // reason=None for a reason other than BVE ClearLevel0.
        self.unit_proof_id.fill(0);
        self.cold.level0_proof_id.fill(0);

        // Reset CHB state before rebuilding the heap.
        // After chb_reset(), chb_loaded is false. Reset active_branch_heuristic
        // to Evsids so that sync_active_branch_heuristic() (called later) will
        // correctly re-swap into CHB mode if the selector mode requires it.
        self.vsids.chb_reset();
        self.active_branch_heuristic = BranchHeuristic::Evsids;

        // Reset VSIDS heap to include all variables (they are all unassigned now),
        // then remove non-active variables — they must never be decided.
        self.vsids.reset_heap();
        for (i, state) in self.var_lifecycle.iter_enumerated() {
            if state.is_removed() {
                self.vsids.remove_from_heap(Variable(i as u32));
            }
        }
        self.vsids.reset_vmtf_unassigned();

        // Watches are rebuilt each solve. Use clear() + ensure_num_vars() to avoid
        // reallocating the outer Vec on incremental solves.
        self.watches.clear();
        self.watches.ensure_num_vars(self.num_vars);

        // Restart / scheduling state
        self.conflicts_since_restart = 0;
        self.cold.luby_idx = 1;
        self.cold.restarts = 0;

        // Glucose-style EMA state (ADAM bias-corrected)
        self.cold.lbd_ema_fast = 0.0;
        self.cold.lbd_ema_slow = 0.0;
        self.cold.lbd_ema_fast_biased = 0.0;
        self.cold.lbd_ema_slow_biased = 0.0;
        self.cold.lbd_ema_fast_exp = 1.0;
        self.cold.lbd_ema_slow_exp = 1.0;
        self.cold.saved_lbd_ema_fast = 0.0;
        self.cold.saved_lbd_ema_slow = 0.0;
        self.cold.saved_lbd_ema_fast_biased = 0.0;
        self.cold.saved_lbd_ema_slow_biased = 0.0;
        self.cold.saved_lbd_ema_fast_exp = 1.0;
        self.cold.saved_lbd_ema_slow_exp = 1.0;
        self.cold.ema_swapped = false;

        // Trail-length EMA for restart blocking
        self.cold.trail_ema_slow = 0.0;
        self.cold.trail_ema_count = 0;
        self.cold.trail_blocked_restarts = 0;

        // Stabilization state
        self.stable_mode = matches!(self.cold.mode_lock, cold::ModeLock::Stable);
        self.cold.stable_mode_start_conflicts = 0;
        self.cold.stable_phase_length = STABLE_PHASE_INIT;
        self.cold.stable_phase_count = 0;
        self.search_ticks = [0; 2];
        self.cold.stabilize_tick_inc = 0;
        self.cold.stabilize_tick_limit = 0;
        self.cold.reluctant_u = 1;
        self.cold.reluctant_v = 1;
        self.cold.reluctant_countdown = RELUCTANT_INIT;
        self.cold.reluctant_ticked_at = 0;
        self.sync_active_branch_heuristic();

        self.no_conflict_until = 0;
        self.target_trail_len = 0;
        self.target_phase.fill(0);
        // Note: best_phase and best_trail_len are kept across solves for rephasing

        // Bumpreason rate-limiting state (must reset with num_decisions/num_conflicts).
        // Without this, bumpreason_saved_decisions retains the previous solve's value
        // while num_decisions resets to 0, causing u64 wrapping in the delta computation
        // and disabling reason bumping for the first many conflicts (#5119).
        self.cold.bumpreason_delay_interval = [0; 2];

        // Clause database management scheduling (counters restart each solve).
        self.num_conflicts = 0;
        self.num_decisions = 0;
        self.num_propagations = 0;
        self.num_original_clauses = 0;
        self.cold.next_reduce_db = FIRST_REDUCE_DB;
        self.cold.process_memory_interrupt = false;

        // Learned clause trail: arena offsets of recently learned clauses for
        // eager subsumption in conflict analysis. Must be cleared because the
        // arena may have been rebuilt above (offsets are stale), and even
        // without rebuild, learned clauses from the previous solve have
        // different reduction/GC eligibility in the new search.
        self.cold.learned_clause_trail.clear();

        // Walk/rephase state: walk_last_ticks is compared against
        // search_ticks (reset above to [0; 2]). Without resetting
        // walk_last_ticks, walk effort = ticks - stale_high_watermark
        // underflows via saturating_sub → walk never triggers until ticks
        // catch up to the stale value.
        self.phase_init.walk_last_ticks = 0;

        // Bumpreason rate limiting: compared against num_decisions (reset
        // above to 0). Stale saved_decisions produces wrong delta on the
        // first conflicts of the new solve.
        self.cold.bumpreason_saved_decisions = 0;
        self.cold.bumpreason_decision_rate = 0.0;
        self.cold.bumpreason_delay_remaining = [0; 2];
        self.cold.bumpreason_delay_interval = [0; 2];
        self.cold.next_flush = FLUSH_INIT;
        self.cold.flush_inc = FLUSH_INIT;
        self.cold.num_flushes = 0;
        self.cold.num_reductions = 0;
        self.cold.last_inprobe_reduction = 0;
        self.cold.inprobe_phases = 0;
        self.cold.eager_subsumed = 0;

        // Tick watermarks: search_ticks reset to [0,0] above, so last_*_ticks
        // must also be zeroed or saturating_sub blocks all tick-gated passes.
        self.cold.last_vivify_ticks = 0;
        self.cold.last_vivify_irred_ticks = 0;
        // Engine watermarks: same saturating_sub starvation pattern as vivify.
        // search_ticks and num_propagations reset above; engine watermarks must
        // follow or the affected technique is starved until ticks catch up (#8159).
        self.cold.last_factor_ticks = 0;
        self.cold.last_sweep_ticks = 0;
        self.cold.last_backbone_ticks = 0;
        self.inproc.reset_watermarks();

        // Inprocessing scheduling (relative to `num_conflicts`)
        self.inproc_ctrl.vivify.next_conflict = VIVIFY_INTERVAL;
        self.inproc_ctrl.vivify_irred.next_conflict = VIVIFY_IRRED_INTERVAL;
        self.cold.vivify_irred_delay_multiplier = 1;
        self.inproc_ctrl.subsume.reset_interval(SUBSUME_INTERVAL);
        self.inproc_ctrl.probe.next_conflict = PROBE_INTERVAL;
        self.inproc_ctrl.bve.next_conflict = BVE_INTERVAL_BASE;
        self.inproc_ctrl.bce.next_conflict = BCE_INTERVAL;
        self.inproc_ctrl.transred.next_conflict = TRANSRED_INTERVAL;
        self.inproc_ctrl.htr.next_conflict = HTR_INTERVAL;
        self.inproc_ctrl.sweep.next_conflict = SWEEP_INTERVAL;
        self.inproc_ctrl.condition.next_conflict = CONDITION_INTERVAL;
        self.inproc_ctrl.decompose.next_conflict = 0;
        self.inproc_ctrl.factor.next_conflict = FACTOR_INTERVAL;
        self.inproc_ctrl.congruence.next_conflict = 0;
        self.cold.next_rephase = REPHASE_INITIAL;
        self.tiers.next_recompute_tier = TIER_RECOMPUTE_INIT;
        self.fixed_count = 0;
        self.cold.last_collect_fixed = 0;
        self.pending_garbage_count = 0;
        // Revert Fixed -> Active since all assignments are cleared.
        self.var_lifecycle.reset_fixed();
        self.reset_branch_heuristic_selector();

        // Post-conditions: search state is clean
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: reset_search_state left decision_level non-zero"
        );
        debug_assert!(
            self.trail.is_empty(),
            "BUG: reset_search_state left trail non-empty"
        );
        debug_assert_eq!(self.qhead, 0, "BUG: reset_search_state left qhead non-zero");
        debug_assert_eq!(
            self.num_conflicts, 0,
            "BUG: reset_search_state left num_conflicts non-zero"
        );
    }
}
