// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver configuration and statistics accessors.

use super::*;
#[cfg(test)]
use std::mem::size_of;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

impl Solver {
    /// Store an interrupt handle for cooperative cancellation (#3638).
    ///
    /// The flag is polled by `is_interrupted()` during preprocessing and
    /// inprocessing phases where the `should_stop` closure is not available.
    /// The CDCL main loop still uses the closure-based check.
    pub fn set_interrupt(&mut self, handle: Arc<AtomicBool>) {
        self.cold.interrupt = Some(handle);
    }

    /// Check whether an external interrupt has been requested.
    ///
    /// Returns true if `set_interrupt()` was called and the flag was set.
    /// Used in preprocessing/inprocessing to honor timeout during long-running
    /// techniques where the `should_stop` closure is not threaded through.
    #[inline]
    pub(super) fn is_interrupted(&self) -> bool {
        if self.cold.process_memory_interrupt {
            return true;
        }
        self.cold
            .interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
    }

    /// Enable periodic progress line emission to stderr during solving.
    ///
    /// When enabled, the solver emits a compact one-line status summary to
    /// stderr approximately every 5 seconds. The format uses the DIMACS `c`
    /// comment prefix for compatibility with SAT competition tooling.
    ///
    /// Format: `c [5.0s] conflicts=N decisions=N props=N restarts=N learned=N mode=focused`
    pub fn set_progress_enabled(&mut self, enabled: bool) {
        self.cold.progress_enabled = enabled;
    }

    /// Enter incremental mode before the first solve (#5608).
    ///
    /// Disables destructive inprocessing (BVE, BCE, subsumption, etc.) so
    /// that the clause database is never rebuilt between incremental solves.
    /// This preserves learned clauses across optimization iterations.
    ///
    /// Call this after adding initial clauses but before the first `solve()`.
    /// Without this, the first solve may run BVE which eliminates variables,
    /// forcing a full arena rebuild on the second solve that drops all learned
    /// clauses — causing incremental optimization to re-derive everything.
    pub fn set_incremental_mode(&mut self) {
        self.disable_destructive_inprocessing();
    }

    /// Enable or disable initial preprocessing
    pub fn set_preprocess_enabled(&mut self, enabled: bool) {
        self.cold.preprocess_enabled = enabled;
    }

    /// Select between quick and full preprocessing passes.
    ///
    /// This does not toggle preprocessing itself; it only controls whether the
    /// heavier preprocessing passes guarded by `preprocessing_quick_mode` are
    /// allowed to run when preprocessing is enabled.
    pub fn set_full_preprocessing(&mut self, enabled: bool) {
        self.preprocessing_quick_mode = !enabled;
    }

    /// Returns whether initial preprocessing is enabled.
    pub fn is_preprocess_enabled(&self) -> bool {
        self.cold.preprocess_enabled
    }

    /// Returns whether full preprocessing is enabled.
    pub fn is_full_preprocessing_enabled(&self) -> bool {
        !self.preprocessing_quick_mode
    }

    /// Enable or disable root symmetry preprocessing.
    pub fn set_symmetry_enabled(&mut self, enabled: bool) {
        self.cold.symmetry_enabled = enabled;
    }

    /// Returns whether root symmetry preprocessing is enabled.
    pub fn is_symmetry_enabled(&self) -> bool {
        self.cold.symmetry_enabled
    }

    /// Returns whether walk-based phase initialization is enabled.
    pub fn is_walk_enabled(&self) -> bool {
        self.phase_init.walk_enabled
    }

    /// Enable or disable walk-based phase initialization (#1816)
    pub fn set_walk_enabled(&mut self, enabled: bool) {
        self.phase_init.walk_enabled = enabled;
    }

    /// Returns whether warmup-based phase initialization is enabled.
    pub fn is_warmup_enabled(&self) -> bool {
        self.phase_init.warmup_enabled
    }

    /// Enable or disable warmup-based phase initialization (#1816)
    pub fn set_warmup_enabled(&mut self, enabled: bool) {
        self.phase_init.warmup_enabled = enabled;
    }

    /// Snapshot the current inprocessing feature-enable profile.
    ///
    /// This is consumed by soundness-gate integration tests to assert that
    /// feature isolation toggles only the requested technique.
    pub fn inprocessing_feature_profile(&self) -> crate::InprocessingFeatureProfile {
        crate::InprocessingFeatureProfile {
            preprocess: self.cold.preprocess_enabled,
            walk: self.phase_init.walk_enabled,
            warmup: self.phase_init.warmup_enabled,
            shrink: self.shrink_enabled,
            hbr: self.hbr_enabled,
            vivify: self.inproc_ctrl.vivify.enabled,
            subsume: self.inproc_ctrl.subsume.enabled,
            probe: self.inproc_ctrl.probe.enabled,
            bve: self.inproc_ctrl.bve.enabled,
            bce: self.inproc_ctrl.bce.enabled,
            condition: self.inproc_ctrl.condition.enabled,
            decompose: self.inproc_ctrl.decompose.enabled,
            factor: self.inproc_ctrl.factor.enabled,
            transred: self.inproc_ctrl.transred.enabled,
            htr: self.inproc_ctrl.htr.enabled,
            gate: self.inproc_ctrl.gate.enabled,
            congruence: self.inproc_ctrl.congruence.enabled,
            sweep: self.inproc_ctrl.sweep.enabled,
            backbone: self.inproc_ctrl.backbone.enabled,
            symmetry: self.cold.symmetry_enabled,
        }
    }

    /// Set maximum number of learned clauses before aggressive reduction (#1609)
    ///
    /// When the number of learned clauses exceeds this limit, the solver
    /// triggers clause reduction more aggressively to prevent memory exhaustion.
    /// Set to `None` to disable the limit (default behavior).
    pub fn set_max_learned_clauses(&mut self, limit: Option<usize>) {
        self.cold.max_learned_clauses = limit;
    }

    /// Set maximum clause database memory in bytes before aggressive reduction (#1609)
    ///
    /// When the clause database memory exceeds this limit, the solver triggers
    /// aggressive clause reduction and arena compaction to reclaim memory.
    /// Set to `None` to disable the limit (default behavior).
    ///
    /// Example: `set_max_clause_db_bytes(Some(500 * 1024 * 1024))` for 500MB limit.
    pub fn set_max_clause_db_bytes(&mut self, limit: Option<usize>) {
        self.cold.max_clause_db_bytes = limit;
    }

    /// Remove stale watchers for deleted/garbage clauses from all watch lists.
    ///
    /// This is an O(total_watches) sweep and is intended for level-0
    /// maintenance points (for example before inprocessing), not the BCP hot
    /// path.
    pub(super) fn flush_watches(&mut self) {
        for lit_idx in 0..(self.num_vars * 2) {
            let lit = Literal::from_index(lit_idx);
            self.watches
                .swap_to_deferred(lit, &mut self.deferred_watch_list);

            let watch_len = self.deferred_watch_list.len();
            let mut j: usize = 0;
            for i in 0..watch_len {
                let packed = self.deferred_watch_list.entry(i);
                let clause_raw = (packed >> 32) as u32;
                let clause_idx = (clause_raw & !BINARY_FLAG) as usize;

                if clause_idx >= self.arena.len() {
                    continue;
                }
                if self.arena.is_empty_clause(clause_idx) || self.arena.is_garbage(clause_idx) {
                    continue;
                }

                self.deferred_watch_list.set_packed(j, packed);
                j += 1;
            }

            // Two-pointer compaction: j <= watch_len always.
            debug_assert!(
                j <= watch_len,
                "BUG: flush_watches compaction j ({j}) > watch_len ({watch_len}) for lit {lit_idx}"
            );
            self.deferred_watch_list.truncate(j);
            self.watches
                .swap_from_deferred(lit, &mut self.deferred_watch_list);
        }
    }

    /// Enable or disable Glucose-style EMA restarts.
    ///
    /// When enabled, restarts are triggered based on the exponential moving average
    /// of learned clause LBD values. When disabled, uses Luby sequence restarts.
    ///
    /// CP solvers typically benefit from Luby restarts (set to `false`) because
    /// propagation-derived clauses often have high LBD, causing Glucose restarts
    /// to fire too aggressively.
    pub fn set_glucose_restarts(&mut self, enabled: bool) {
        self.cold.glucose_restarts = enabled;
    }

    /// Set the base restart interval for Luby-sequence restarts (in conflicts).
    ///
    /// Only effective when Glucose restarts are disabled. The actual restart
    /// interval is `base * luby(n)` where `luby(n)` is the Luby sequence.
    /// Default is 100. CP solvers may benefit from larger values (e.g., 250)
    /// to allow more exploration between restarts.
    pub fn set_restart_base(&mut self, base: u64) {
        self.cold.restart_base = base;
    }

    /// Set the initial stabilization phase length (in conflicts).
    ///
    /// Controls how many conflicts the solver spends in its first focused
    /// phase before switching to stable mode. Default is 1000 (CaDiCaL
    /// `stabinit`). Larger values favor longer focused-mode exploration.
    pub fn set_stable_phase_init(&mut self, conflicts: u64) {
        self.cold.stable_phase_length = conflicts;
    }

    /// Set the vivification scheduling interval (in conflicts).
    ///
    /// Minimum spacing between vivification rounds for learned clauses.
    /// Default is 2000. Lower values vivify more frequently.
    pub fn set_vivify_interval(&mut self, conflicts: u64) {
        self.inproc_ctrl.vivify.reset_interval(conflicts);
    }

    /// Set the irredundant vivification scheduling interval (in conflicts).
    ///
    /// Minimum spacing between vivification rounds for original clauses.
    /// Default is 5000.
    pub fn set_vivify_irred_interval(&mut self, conflicts: u64) {
        self.inproc_ctrl.vivify_irred.reset_interval(conflicts);
    }

    /// Set the subsumption scheduling interval (in conflicts).
    ///
    /// Minimum spacing between forward subsumption rounds.
    /// Default is 20000.
    pub fn set_subsume_interval(&mut self, conflicts: u64) {
        self.inproc_ctrl.subsume.reset_interval(conflicts);
    }

    /// Set the probing scheduling interval (in conflicts).
    ///
    /// Minimum spacing between failed-literal probing rounds.
    /// Default is 1000.
    pub fn set_probe_interval(&mut self, conflicts: u64) {
        self.inproc_ctrl.probe.reset_interval(conflicts);
    }

    /// Enable true stable-only mode for DIMACS SAT workloads.
    ///
    /// When enabled, the solver starts and stays in stable mode
    /// (EVSIDS + reluctant doubling) across preprocessing resets.
    pub fn set_stable_only(&mut self, enabled: bool) {
        self.cold.mode_lock = if enabled {
            cold::ModeLock::Stable
        } else {
            cold::ModeLock::None
        };
        self.stable_mode = enabled;
        self.cold.stable_mode_start_conflicts = 0;
        self.sync_active_branch_heuristic();
    }

    /// Return whether stable-only search is currently locked on.
    #[cfg(test)]
    pub(crate) fn stable_only_enabled(&self) -> bool {
        self.cold.mode_lock == cold::ModeLock::Stable
    }

    /// Set BVE effort as per-mille of cumulative search propagations.
    pub fn set_bve_effort_permille(&mut self, permille: u64) {
        self.cold.bve_effort_permille = permille;
    }

    /// Set subsumption effort as per-mille of cumulative search propagations.
    pub fn set_subsume_effort_permille(&mut self, permille: u64) {
        self.cold.subsume_effort_permille = permille;
    }

    /// Return the configured BVE effort in per-mille.
    pub fn bve_effort_permille(&self) -> u64 {
        self.cold.bve_effort_permille
    }

    /// Return the configured subsumption effort in per-mille.
    pub fn subsume_effort_permille(&self) -> u64 {
        self.cold.subsume_effort_permille
    }

    /// Enable geometric restart schedule matching Z3's QF_LRA mode.
    ///
    /// Geometric restarts use `next_restart = initial * factor^n` where `n` is
    /// the restart count. Z3 defaults: initial=100, factor=1.1, giving the
    /// sequence 100, 110, 121, 133, 146, ...
    ///
    /// When enabled, this overrides both Glucose-style and Luby restarts.
    /// Also disables CaDiCaL-style stabilization mode switching since geometric
    /// restarts use a fixed schedule independent of clause quality signals.
    pub fn set_geometric_restarts(&mut self, initial: f64, factor: f64) {
        self.cold.geometric_restarts = true;
        self.cold.geometric_initial = initial;
        self.cold.geometric_factor = factor;
    }

    /// Force a specific branching heuristic, independent of restart mode.
    pub fn set_branch_heuristic(&mut self, heuristic: BranchHeuristic) {
        self.cold.branch_selector_mode = BranchSelectorMode::Fixed(heuristic);
        self.switch_branch_heuristic(heuristic);
        self.start_branch_heuristic_epoch();
    }

    /// Enable or disable UCB1 multi-armed-bandit branching selection.
    ///
    /// When enabled, the solver starts from EVSIDS and may switch to VMTF at
    /// restart boundaries after scoring completed heuristic epochs.
    pub fn set_branch_selector_ucb1(&mut self, enabled: bool) {
        self.cold.branch_selector_mode = if enabled {
            BranchSelectorMode::MabUcb1
        } else {
            BranchSelectorMode::LegacyCoupled
        };
        self.reset_branch_heuristic_selector();
    }

    /// Set the minimum number of conflicts required before scoring a branch-heuristic epoch.
    pub fn set_branch_selector_epoch_min_conflicts(&mut self, conflicts: u64) {
        self.cold.branch_mab.set_epoch_min_conflicts(conflicts);
        self.start_branch_heuristic_epoch();
    }

    /// Set random variable frequency for decisions (Z3-style).
    ///
    /// With probability `freq`, each decision will select a random unassigned
    /// variable instead of the VSIDS/VMTF-highest one. Z3 default for SMT: 0.01
    /// (1% of decisions). Set to 0.0 to disable (default for pure SAT).
    pub fn set_random_var_freq(&mut self, freq: f64) {
        self.cold.random_var_freq = freq.clamp(0.0, 1.0);
    }

    /// Enable or disable chronological backtracking
    ///
    /// When enabled, the solver may backtrack by only one level instead of jumping
    /// to the asserting level, which can help on certain problem classes.
    #[cfg(test)]
    pub(crate) fn set_chrono_enabled(&mut self, enabled: bool) {
        self.chrono_enabled = enabled;
    }

    /// Enable or disable CaDiCaL-style trail reuse for chronological backtracking
    ///
    /// When enabled, the solver uses trail reuse heuristic to find the best
    /// variable above the jump level and backtrack only to that level, preserving
    /// more of the useful trail state. Only active in stable mode.
    #[cfg(test)]
    pub(crate) fn set_chrono_reuse_trail(&mut self, enabled: bool) {
        self.chrono_reuse_trail = enabled;
    }

    /// Set the initial phase for all variables.
    ///
    /// If `phase` is `true`, variables will initially be assigned positive.
    /// If `phase` is `false`, variables will initially be assigned negative.
    #[cfg(test)]
    pub(crate) fn set_initial_phase(&mut self, phase: bool) {
        self.phase.fill(if phase { 1 } else { -1 });
    }

    /// Set the preferred phase for a specific variable
    ///
    /// This is useful for guiding the search - for example, in LIA solving,
    /// when splitting on an integer variable with fractional value, we can
    /// set the preferred phase to try the closer integer first.
    ///
    /// # Arguments
    /// * `var` - The variable to set phase for
    /// * `phase` - `true` for positive polarity, `false` for negative
    pub fn set_var_phase(&mut self, var: Variable, phase: bool) {
        let idx = var.index();
        if idx < self.num_vars {
            self.phase[idx] = if phase { 1 } else { -1 };
        }
    }

    /// Get the forced phase hint for a variable, if one has been set.
    ///
    /// Returns `None` if no phase hint was set for this variable.
    /// Used by tests to verify that `set_var_phase` was called correctly.
    pub fn var_phase(&self, var: Variable) -> Option<bool> {
        let idx = var.index();
        if idx < self.num_vars {
            match self.phase[idx] {
                1 => Some(true),
                -1 => Some(false),
                _ => None,
            }
        } else {
            None
        }
    }

    /// Bump the VSIDS activity of a variable.
    ///
    /// This increases the variable's priority in the decision heuristic,
    /// making it more likely to be selected as the next branching variable.
    /// Used by z4-cp to boost objective variable literals after finding
    /// a solution during optimization, biasing the search toward improving
    /// the objective.
    pub fn bump_variable_activity(&mut self, var: Variable) {
        if var.index() < self.num_vars {
            self.vsids.bump(var, &self.vals, true);
            self.vsids.bump(var, &self.vals, false);
        }
    }

    /// Set the random seed for variable selection tie-breaking
    ///
    /// This affects the order of variables with equal VSIDS scores.
    /// Different seeds can lead to different search paths.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.vsids.set_random_seed(seed);
    }

    /// Return the current random seed for variable selection tie-breaking.
    #[must_use]
    pub fn random_seed(&self) -> u64 {
        self.vsids.random_seed()
    }

    /// Estimate memory usage of the solver (in bytes)
    ///
    /// Returns a breakdown of live heap-backed buffers plus the inline solver
    /// shell. Tracks the current hot/cold split layout so `#5090` regressions
    /// show up in tests.
    #[cfg(test)]
    pub(crate) fn memory_stats(&self) -> MemoryStats {
        fn packed_bool_vec_bytes(capacity: usize) -> usize {
            capacity.div_ceil(8)
        }

        let solver_shell = size_of::<Self>();

        let var_data = self.vals.capacity() * size_of::<i8>()
            + self.var_data.capacity() * size_of::<VarData>()
            + self.phase.capacity() * size_of::<i8>()
            + self.target_phase.capacity() * size_of::<i8>()
            + self.best_phase.capacity() * size_of::<i8>();

        let vsids = self.vsids.buffer_bytes();

        let minimize_bytes = self.min.minimize_flags.capacity() * size_of::<u8>()
            + self.min.minimize_to_clear.capacity() * size_of::<usize>()
            + self.min.level_seen_count.capacity() * size_of::<u32>()
            + self.min.level_seen_trail.capacity() * size_of::<usize>()
            + self.min.level_seen_to_clear.capacity() * size_of::<u32>()
            + self.min.lrat_to_clear.capacity() * size_of::<usize>()
            + self.min.minimize_level_count.capacity() * size_of::<u32>()
            + self.min.minimize_level_trail.capacity() * size_of::<usize>()
            + self.min.minimize_levels_to_clear.capacity() * size_of::<u32>();
        let conflict = self.conflict.buffer_bytes()
            + self.reason_clause_marks.capacity() * size_of::<u32>()
            + self.bump_sort_buf.capacity() * size_of::<usize>()
            + self.glue_stamp.capacity() * size_of::<u32>()
            + self.shrink_stamp.capacity() * size_of::<u32>()
            + minimize_bytes;

        // Clause database with arena allocation:
        // - ClauseArena contains headers Vec and literals Vec (arena)
        // - No per-clause heap allocation
        let arena = self.arena.memory_bytes();
        let total_literals = self.arena.active_literals();

        let watches = self.watches.heap_bytes()
            + self.deferred_watch_list.capacity() * size_of::<u64>()
            + self.deferred_replacement_watches.capacity()
                * size_of::<(Literal, Watcher)>();

        let trail = self.trail.capacity() * size_of::<Literal>()
            + self.trail_lim.capacity() * size_of::<usize>()
            + self.cold.learned_clause_trail.capacity() * size_of::<usize>();

        let support = self.cold.e2i.capacity() * size_of::<u32>()
            + self.cold.i2e.capacity() * size_of::<u32>()
            + self.var_lifecycle.heap_bytes()
            + packed_bool_vec_bytes(self.phase_init.walk_prev_phase.capacity())
            + self
                .cold
                .solution_witness
                .as_ref()
                .map_or(0, |witness| witness.capacity() * size_of::<Option<bool>>());

        let clause_ids = self.cold.clause_ids.capacity() * size_of::<u64>()
            + self.unit_proof_id.capacity() * size_of::<u64>()
            + self.cold.level0_proof_id.capacity() * size_of::<u64>()
            + self.cold.scope_selectors.capacity() * size_of::<Variable>()
            + self.cold.root_satisfied_saved.capacity() * size_of::<Vec<Literal>>()
            + self
                .cold
                .root_satisfied_saved
                .iter()
                .map(|clause| clause.capacity() * size_of::<Literal>())
                .sum::<usize>();

        let original_ledger = self.cold.original_ledger.heap_bytes();

        let inprocessing = packed_bool_vec_bytes(self.subsume_dirty.capacity())
            + self.probe_parent.capacity() * size_of::<Option<Literal>>()
            + self.cold.freeze_counts.capacity() * size_of::<u32>()
            + self.cold.factor_candidate_marks.capacity() * size_of::<u8>()
            + packed_bool_vec_bytes(self.cold.scope_selector_set.capacity())
            + packed_bool_vec_bytes(self.cold.was_scope_selector.capacity())
            + self.hbr_lits.capacity() * size_of::<Literal>()
            + self.tiers.tier_usage[0].capacity() * size_of::<u64>()
            + self.tiers.tier_usage[1].capacity() * size_of::<u64>();

        MemoryStats {
            solver_shell,
            num_vars: self.num_vars,
            num_clauses: self.arena.num_clauses(),
            total_literals,
            var_data,
            vsids,
            conflict,
            arena,
            watches,
            trail,
            support,
            clause_ids,
            original_ledger,
            inprocessing,
        }
    }
}
