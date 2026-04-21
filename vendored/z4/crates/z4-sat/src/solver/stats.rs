// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver statistics, queries, debug diagnostics, and clause database access.

use super::solver_stats::INPROCESS_TIMING_LABELS;
use super::*;

impl Solver {
    /// Return the number of user-visible variables.
    pub fn user_num_vars(&self) -> usize {
        self.user_num_vars
    }

    /// Return the total number of variables, including internal scope selectors.
    pub fn total_num_vars(&self) -> usize {
        self.num_vars
    }

    /// Get the number of conflicts encountered during solving
    pub fn num_conflicts(&self) -> u64 {
        self.num_conflicts
    }

    /// Get the number of restarts performed during solving
    pub fn num_restarts(&self) -> u64 {
        self.cold.restarts
    }

    /// Get the number of decisions made during solving
    pub fn num_decisions(&self) -> u64 {
        self.num_decisions
    }

    /// Get the currently active branching heuristic.
    pub fn active_branch_heuristic(&self) -> BranchHeuristic {
        self.active_branch_heuristic
    }

    /// Get per-arm heuristic reward statistics in `[EVSIDS, VMTF]` order.
    pub fn branch_heuristic_epoch_stats(
        &self,
    ) -> [BranchHeuristicStats; crate::mab::NUM_BRANCH_HEURISTIC_ARMS] {
        self.cold.branch_mab.arm_stats()
    }

    /// Get the number of propagations performed during solving
    pub fn num_propagations(&self) -> u64 {
        self.num_propagations
    }

    /// Get the number of chronological backtracks performed during solving
    pub fn num_chrono_backtracks(&self) -> u64 {
        self.stats.chrono_backtracks
    }

    /// Get the number of block-UIP shrink attempts during conflict analysis.
    pub fn shrink_block_attempts(&self) -> u64 {
        self.stats.shrink_block_attempts
    }

    /// Get the number of successful block-UIP replacements.
    pub fn shrink_block_successes(&self) -> u64 {
        self.stats.shrink_block_successes
    }

    /// Get the number of random decisions made during solving
    pub fn num_random_decisions(&self) -> u64 {
        self.stats.random_decisions
    }

    /// Get the number of forced-literal early returns (skip 1UIP).
    pub fn num_forced_backtracks(&self) -> u64 {
        self.stats.forced_backtracks
    }

    /// Get focused-mode EMA restart check/fire counts (diagnostic).
    pub fn focused_ema_stats(&self) -> (u64, u64) {
        (self.stats.focused_ema_checks, self.stats.focused_ema_fires)
    }

    /// Get stable-mode reluctant fire count (diagnostic).
    pub fn stable_reluctant_fires(&self) -> u64 {
        self.stats.stable_reluctant_fires
    }

    /// Get current LBD EMA values (diagnostic).
    pub fn lbd_ema_values(&self) -> (f64, f64) {
        (self.cold.lbd_ema_fast, self.cold.lbd_ema_slow)
    }

    /// Get the number of MAB arm switches (branch heuristic changes via UCB1).
    pub fn mab_arm_switches(&self) -> u64 {
        self.stats.mab_arm_switches
    }

    /// Get the number of focused/stable mode switches (diagnostic).
    pub fn mode_switch_count(&self) -> u64 {
        self.cold.mode_switch_count
    }

    /// Get the number of focused-mode EMA restart blocked by conflict gate.
    pub fn focused_ema_blocked_by_conflict_gate(&self) -> u64 {
        self.stats.focused_ema_blocked_by_conflict_gate
    }

    /// Get the per-decision random variable frequency.
    pub fn random_var_freq(&self) -> f64 {
        self.cold.random_var_freq
    }

    /// Get the active geometric restart schedule, if enabled.
    pub fn geometric_restart_config(&self) -> Option<(f64, f64)> {
        self.cold
            .geometric_restarts
            .then_some((self.cold.geometric_initial, self.cold.geometric_factor))
    }

    /// Get the number of clauses removed by per-conflict eager subsumption.
    pub fn num_eager_subsumptions(&self) -> u64 {
        self.cold.num_eager_subsumptions
    }

    /// Get the number of OTFS trigger events during conflict analysis.
    pub fn otfs_subsumed(&self) -> u64 {
        self.stats.otfs_subsumed
    }

    /// Get the number of reason clauses strengthened by OTFS.
    pub fn otfs_strengthened(&self) -> u64 {
        self.stats.otfs_strengthened
    }

    /// OTFS diagnostic: number of OTFS candidates (resolvent < antecedent).
    pub fn otfs_candidates(&self) -> u64 {
        self.stats.otfs_candidates
    }

    /// OTFS diagnostic: blocked by open==0.
    pub fn otfs_blocked_open0(&self) -> u64 {
        self.stats.otfs_blocked_open0
    }

    /// OTFS diagnostic: blocked by watch invariant.
    pub fn otfs_blocked_watch(&self) -> u64 {
        self.stats.otfs_blocked_watch
    }

    /// OTFS diagnostic: blocked by otfs_strengthen returning false.
    pub fn otfs_blocked_strengthen(&self) -> u64 {
        self.stats.otfs_blocked_strengthen
    }

    /// Get the number of aggressive clause flushes performed (CaDiCaL flush).
    pub fn num_flushes(&self) -> u64 {
        self.cold.num_flushes
    }

    /// Get the number of reduce_db calls performed.
    pub fn num_reductions(&self) -> u64 {
        self.cold.num_reductions
    }

    /// Get the number of learned clauses eagerly subsumed per-conflict.
    pub fn eager_subsumed(&self) -> u64 {
        self.cold.eager_subsumed
    }

    /// Get the number of completed inprocessing (inprobe) phases.
    pub fn inprobe_phases(&self) -> u64 {
        self.cold.inprobe_phases
    }

    /// Get cumulative per-pass inprocessing timings in nanoseconds.
    pub fn inprocessing_pass_times_ns(&self) -> Vec<(&'static str, u64)> {
        INPROCESS_TIMING_LABELS
            .iter()
            .copied()
            .zip(self.stats.inprocessing_time_ns)
            .collect()
    }

    /// Get cumulative per-pass inprocessing timings in milliseconds.
    pub fn inprocessing_pass_times_ms(&self) -> Vec<(&'static str, u64)> {
        self.inprocessing_pass_times_ns()
            .into_iter()
            .map(|(label, nanos)| (label, nanos / 1_000_000))
            .collect()
    }

    /// Get the number of propagations discovered by JIT-compiled BCP.
    pub fn jit_propagations(&self) -> u64 {
        self.stats.jit_propagations
    }

    /// Get the number of conflicts found by JIT-compiled BCP.
    pub fn jit_conflicts(&self) -> u64 {
        self.stats.jit_conflicts
    }

    /// Get the JIT compile time in microseconds.
    pub fn jit_compile_time_us(&self) -> u64 {
        self.stats.jit_compile_time_us
    }

    /// Get the number of clauses compiled into native JIT code.
    pub fn jit_clauses_compiled(&self) -> u64 {
        self.stats.jit_clauses_compiled
    }

    /// Get the number of 2WL watch entries detached for JIT-compiled clauses (#8005).
    pub fn jit_watches_detached(&self) -> u64 {
        self.stats.jit_watches_detached
    }

    /// Get the number of 2WL watch entries reattached after JIT invalidation (#8005).
    pub fn jit_watches_reattached(&self) -> u64 {
        self.stats.jit_watches_reattached
    }

    /// Get the number of inprocessing rounds where JIT recompilation was
    /// skipped because only deletion-only passes ran (#8128).
    pub fn jit_recompilations_skipped(&self) -> u64 {
        self.stats.jit_recompilations_skipped
    }

    /// Get phase timing: preprocess wall-clock nanoseconds.
    pub fn preprocess_time_ns(&self) -> u64 {
        self.stats.preprocess_time_ns
    }

    /// Get phase timing: CDCL search loop wall-clock nanoseconds.
    pub fn search_time_ns(&self) -> u64 {
        self.stats.search_time_ns
    }

    /// Get phase timing: lucky-phase probing wall-clock nanoseconds.
    pub fn lucky_time_ns(&self) -> u64 {
        self.stats.lucky_time_ns
    }

    /// Get phase timing: walk-based phase init wall-clock nanoseconds.
    pub fn walk_time_ns(&self) -> u64 {
        self.stats.walk_time_ns
    }

    /// Get cumulative LBD sum and count for average LBD computation.
    pub fn lbd_sum_count(&self) -> (u64, u64) {
        (self.stats.lbd_sum, self.stats.lbd_count)
    }

    /// Get the number of completed inprocessing rounds.
    pub fn inprocessing_rounds(&self) -> u64 {
        self.stats.inprocessing_rounds
    }

    /// Get total inprocessing simplifications across all rounds.
    pub fn inprocessing_simplifications(&self) -> u64 {
        self.stats.inprocessing_simplifications
    }

    /// Get the number of fixed (unit-propagated at level 0) variables
    pub fn num_fixed(&self) -> i64 {
        self.fixed_count
    }

    /// Get the number of active clauses currently stored in the clause database.
    pub fn num_clauses(&self) -> usize {
        self.arena.num_clauses()
    }

    /// Check if the solver has derived an empty clause (UNSAT indicator).
    pub fn has_empty_clause(&self) -> bool {
        self.has_empty_clause
    }

    /// Take and clear the pending theory conflict, if any (#6262).
    ///
    /// Returns `Some(clause_ref)` if `add_theory_lemma` detected a clause where
    /// both watched literals are false at level > 0. BCP cannot discover this
    /// conflict through normal watch propagation, so the main solve loop must
    /// handle it explicitly.
    pub fn take_pending_theory_conflict(&mut self) -> Option<ClauseRef> {
        self.pending_theory_conflict.take()
    }

    /// Debug: dump all unit clauses in the arena as DIMACS literals.
    pub fn debug_dump_unit_clauses(&self) -> Vec<(usize, i32)> {
        let mut result = Vec::new();
        for idx in self.arena.indices() {
            if self.arena.is_active(idx) && self.arena.len_of(idx) == 1 {
                let lit = self.arena.literal(idx, 0);
                result.push((idx, lit.to_dimacs()));
            }
        }
        result
    }

    /// Count learned vs original clauses in the arena (debug diagnostic).
    pub fn debug_clause_counts(&self) -> (usize, usize) {
        let mut original = 0;
        let mut learned = 0;
        for idx in self.arena.indices() {
            if self.arena.is_active(idx) {
                if self.arena.is_learned(idx) {
                    learned += 1;
                } else {
                    original += 1;
                }
            }
        }
        (original, learned)
    }

    /// Remove all learned clauses from the arena.
    ///
    /// This is a drastic measure for debugging incremental optimization.
    /// It discards all learned clauses and theory lemmas, keeping only originals.
    pub fn clear_learned_clauses(&mut self) {
        let indices: Vec<usize> = self
            .arena
            .indices()
            .filter(|&idx| self.arena.is_active(idx) && self.arena.is_learned(idx))
            .collect();
        for idx in indices {
            // #5910: Must eagerly unlink binary watches before arena deletion.
            // Binary watcher lifecycle (#4924) requires eager removal so BCP's
            // hot path can skip liveness checks. Without this, stale binary
            // watches from deleted theory lemmas would cause incorrect
            // propagation in subsequent incremental solves.
            self.delete_binary_clause_watches(idx);
            self.arena.delete(idx);
        }
    }

    /// Clear the `has_empty_clause` flag for incremental solving.
    ///
    /// In incremental optimization (e.g., CP-SAT), a previous solve may have
    /// derived the empty clause (UNSAT) due to bound-tightening constraints.
    /// After clearing learned clauses and adding new constraints, the empty
    /// clause derivation is no longer valid — the new constraint set may be
    /// satisfiable. Without clearing this flag, all subsequent solves would
    /// immediately return UNSAT (#5910).
    ///
    /// Must be called AFTER `clear_learned_clauses()` to ensure the clauses
    /// that led to the empty clause derivation have been removed.
    pub fn clear_empty_clause(&mut self) {
        self.has_empty_clause = false;
        self.cold.empty_clause_in_proof = false;
        self.cold.empty_clause_lrat_id = None;
        self.pending_theory_conflict = None;
    }

    /// Dump all active clauses in DIMACS format to a file (debug only).
    pub fn dump_dimacs(&self, path: &str) -> std::io::Result<()> {
        use std::io::Write;
        let mut f = std::fs::File::create(path)?;
        let nc = self.arena.active_indices().count();
        writeln!(f, "p cnf {} {}", self.num_vars, nc)?;
        for idx in self.arena.indices() {
            if !self.arena.is_active(idx) {
                continue;
            }
            let len = self.arena.len_of(idx);
            let mut line = String::new();
            for j in 0..len {
                let lit = self.arena.literal(idx, j);
                let v = lit.variable().index() as i32 + 1;
                if lit.is_positive() {
                    line.push_str(&format!("{v} "));
                } else {
                    line.push_str(&format!("-{v} "));
                }
            }
            line.push('0');
            writeln!(f, "{line}")?;
        }
        Ok(())
    }

    /// Get the number of original (non-learned) clauses
    pub fn num_original_clauses(&self) -> usize {
        self.num_original_clauses
    }

    /// Convert an internal literal to its stable external representation.
    ///
    /// External indices are assigned at variable creation time and never
    /// change, even across compaction rounds. This is O(1): a single array
    /// lookup into `i2e`.
    ///
    /// Called at reconstruction stack push sites during inprocessing.
    /// Reference: CaDiCaL `internal.hpp:1628-1637`.
    #[inline]
    pub(crate) fn externalize(&self, lit: Literal) -> Literal {
        let int_var = lit.variable().index();
        debug_assert!(
            int_var < self.cold.i2e.len(),
            "BUG: externalize: internal var {} >= i2e.len() ({})",
            int_var,
            self.cold.i2e.len(),
        );
        let ext_var = self.cold.i2e[int_var];
        if lit.is_positive() {
            Literal::positive(Variable(ext_var))
        } else {
            Literal::negative(Variable(ext_var))
        }
    }

    /// Convert a slice of internal literals to external representation.
    ///
    /// Convenience wrapper for `externalize()` on each literal in a clause
    /// or witness. Used at reconstruction stack push sites.
    #[inline]
    pub(crate) fn externalize_lits(&self, lits: &[Literal]) -> Vec<Literal> {
        lits.iter().map(|&lit| self.externalize(lit)).collect()
    }

    /// Get the number of learned (non-original) clauses currently retained.
    pub fn num_learned_clauses(&self) -> u64 {
        let mut count: u64 = 0;
        for idx in self.arena.active_indices() {
            if self.arena.is_learned(idx) {
                count += 1;
            }
        }
        count
    }

    /// Extract all learned (non-original) clauses from the clause database.
    ///
    /// This is useful for preserving learned clauses when recreating the solver,
    /// such as in branch-and-bound algorithms for LIA.
    pub fn get_learned_clauses(&self) -> Vec<Vec<Literal>> {
        let mut learned = Vec::new();
        for idx in self.arena.active_indices() {
            if self.arena.is_learned(idx) {
                let lits = self.arena.literals(idx);
                // Skip clauses referencing internal variables (scope selectors,
                // factoring extension vars) that won't exist in a fresh solver.
                // Only preserve clauses whose variables are all within the
                // user-visible range. (#4716 soundness fix)
                if lits
                    .iter()
                    .all(|l| l.variable().index() < self.user_num_vars)
                {
                    learned.push(lits.to_vec());
                }
            }
        }
        learned
    }

    /// Add a clause that was learned from a previous solve session.
    ///
    /// Unlike regular learned clauses, these are added without proof logging
    /// since they were already proven in the previous session.
    #[allow(clippy::needless_pass_by_value)]
    pub fn add_preserved_learned(&mut self, mut literals: Vec<Literal>) -> bool {
        self.add_preserved_learned_watched(&mut literals)
    }

    // ── Progress reporting ──────────────────────────────────────────────

    /// Minimum interval between progress line emissions.
    const PROGRESS_INTERVAL_SECS: f64 = 5.0;

    /// Format a compact one-line progress summary for SAT solving.
    ///
    /// Uses the DIMACS `c` comment prefix for compatibility with SAT
    /// competition tooling. Includes conflicts, decisions, propagations,
    /// restarts, learned clause count, and current search mode.
    pub(crate) fn format_progress_line(&self, elapsed_secs: f64) -> String {
        let mode = if self.stable_mode { "stable" } else { "focused" };
        let learned = self.num_learned_clauses();
        format!(
            "c [{:.1}s] conflicts={} decisions={} props={} restarts={} learned={} mode={}",
            elapsed_secs,
            self.num_conflicts,
            self.num_decisions,
            self.num_propagations,
            self.cold.restarts,
            learned,
            mode,
        )
    }

    /// Check elapsed time and emit a progress line to stderr if due.
    ///
    /// Called from the CDCL loop on conflicts (high frequency). The actual
    /// emission is gated by a wall-clock check so overhead when progress is
    /// disabled is a single bool branch. When enabled, the `Instant::now()`
    /// call runs at most once per conflict; the 5-second gate ensures actual
    /// formatting + I/O happens rarely.
    #[inline]
    pub(crate) fn maybe_emit_progress(&mut self) {
        if !self.cold.progress_enabled {
            return;
        }
        let now = std::time::Instant::now();
        let should_emit = match self.cold.last_progress_time {
            Some(last) => now.duration_since(last).as_secs_f64() >= Self::PROGRESS_INTERVAL_SECS,
            None => {
                // First check: emit if at least PROGRESS_INTERVAL_SECS from solve start.
                self.cold.solve_start_time.is_some_and(|start| {
                    now.duration_since(start).as_secs_f64() >= Self::PROGRESS_INTERVAL_SECS
                })
            }
        };
        if should_emit {
            let elapsed = self
                .cold
                .solve_start_time
                .map_or(0.0, |start| now.duration_since(start).as_secs_f64());
            let line = self.format_progress_line(elapsed);
            // Use write! to stderr to avoid panic on broken pipe.
            let _ = Write::write_all(&mut std::io::stderr(), line.as_bytes());
            let _ = Write::write_all(&mut std::io::stderr(), b"\n");
            self.cold.last_progress_time = Some(now);
        }
    }
}
