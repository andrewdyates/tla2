// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver constructors: `new`, `with_proof`, `with_proof_output`, `build`.

use super::*;

impl Solver {
    /// Create a new solver with n variables (no proof logging)
    pub fn new(num_vars: usize) -> Self {
        Self::build(num_vars, None)
    }

    /// Create a new solver with DRAT proof logging (text format)
    pub fn with_proof(num_vars: usize, writer: impl Write + Send + 'static) -> Self {
        Self::with_proof_output(num_vars, ProofOutput::drat_text(writer))
    }

    /// Create a new solver with proof logging (DRAT or LRAT)
    ///
    /// For LRAT proofs, use `ProofOutput::lrat_text()` or `ProofOutput::lrat_binary()`.
    /// Note: LRAT proof requires knowing the number of original clauses, which is
    /// determined after all clauses are added. Construct a `ProofOutput::lrat_text()`
    /// or `ProofOutput::lrat_binary()` with an estimate of the clause count.
    pub fn with_proof_output(num_vars: usize, proof_output: ProofOutput) -> Self {
        Self::build(num_vars, Some(proof_output))
    }

    /// Shared constructor: all Solver initialization in one place.
    fn build(num_vars: usize, proof_output: Option<ProofOutput>) -> Self {
        let has_proof = proof_output.is_some();
        let lrat_enabled = proof_output.as_ref().is_some_and(ProofOutput::is_lrat);
        // Removed 100k cap for BV performance (#757) - BV CNF has ~3-5 clauses/var
        let clauses_capacity = num_vars.saturating_mul(4);
        let literals_capacity = clauses_capacity.saturating_mul(3); // avg 3 lits/clause
        #[allow(unused_mut)]
        let mut solver = Self {
            num_vars,
            user_num_vars: num_vars,
            arena: ClauseArena::with_capacity(clauses_capacity, literals_capacity),

            watches: WatchedLists::new(num_vars),
            watches_disconnected: false,
            defer_stale_reason_cleanup: false,
            earliest_affected_trail_pos: None,
            stale_reasons: Vec::new(),
            vsids: VSIDS::new(num_vars),
            conflict: ConflictAnalyzer::new(num_vars),
            vals: vec![0i8; num_vars * 2],
            var_data: vec![VarData::UNASSIGNED; num_vars],
            // Always allocate unit_proof_id unconditionally (#8069: Phase 2a).
            // Clause IDs are always tracked for deferred backward proof
            // reconstruction, so unit proof IDs must also always be available.
            unit_proof_id: vec![0; num_vars],
            reason_clause_marks: Vec::new(),
            reason_clause_epoch: 1,
            reason_graph_epoch: 0,
            reason_marks_synced_epoch: 0,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
            qhead: 0,
            phase: vec![0i8; num_vars],
            target_phase: vec![0i8; num_vars],
            best_phase: vec![0i8; num_vars],
            target_trail_len: 0,
            best_trail_len: 0,
            no_conflict_until: 0,
            suppress_phase_saving: false,
            suppress_reduce_db: false,
            proof_manager: proof_output.map(|output| ProofManager::new(output, num_vars)),
            #[cfg(debug_assertions)]
            solve_proof_mode: None,
            conflicts_since_restart: 0,
            // Stabilization state (start in focused mode)
            stable_mode: false,
            active_branch_heuristic: BranchHeuristic::Vmtf,
            search_ticks: [0; 2],
            num_conflicts: 0,
            num_original_clauses: 0,
            chrono_enabled: true, // Enable chronological backtracking by default
            chrono_reuse_trail: true, // CaDiCaL-style trail reuse (re-enabled #112)
            stats: solver_stats::SolverStats::new(),
            num_decisions: 0,
            bump_sort_buf: Vec::new(),
            backbone_seen: vec![false; num_vars],
            num_propagations: 0,
            pending_garbage_count: 0,
            inproc_ctrl: if has_proof {
                inproc_control::InprocessingControls::new().with_proof_overrides(lrat_enabled)
            } else {
                inproc_control::InprocessingControls::new()
            },
            preprocessing_quick_mode: true,
            inproc: inproc_engines::InprocessingEngines::new(num_vars),
            subsume_dirty: vec![true; num_vars], // all dirty initially so first round processes everything
            probing_mode: false,
            hbr_enabled: true, // Re-enabled: probe_parent array fixes #3419
            hbr_lits: Vec::with_capacity(32),
            probe_parent: vec![None; num_vars],
            deferred_watch_list: WatchList::new(),
            deferred_replacement_watches: Vec::new(),
            fixed_count: 0,
            var_lifecycle: lifecycle::VarLifecycle::new(num_vars),
            lit_marks: LitMarks::new(num_vars),
            last_conflict_clause_ref: None,
            last_conflict_clause_id: 0,
            has_empty_clause: false,
            // Glue recomputation stamp table
            glue_stamp: vec![0u32; num_vars + 1], // indexed by decision level (0..=max_level)
            glue_stamp_counter: 0u32,
            // Block-level shrinking stamp table
            shrink_stamp: vec![0u32; num_vars],
            shrink_stamp_counter: 0,
            shrink_enabled: true,
            reap: reap::Reap::new(),
            ws_shrink_entries: Vec::new(),
            ws_shrink_result: Vec::new(),
            ws_shrink_block_lits: Vec::new(),
            ws_shrink_chain: Vec::new(),
            tiers: tier_state::TierState::new(),
            min: minimization_state::MinimizationState::new(num_vars),
            phase_init: phase_init_state::PhaseInitState::new(num_vars),
            cold: Box::new(cold::ColdState::new(
                num_vars,
                clauses_capacity,
                lrat_enabled,
            )),
            pending_theory_conflict: None,
            #[cfg(feature = "jit")]
            compiled_formula: None,
            #[cfg(feature = "jit")]
            jit_staging_trail: Vec::with_capacity(256),
            #[cfg(feature = "jit")]
            jit_staging_reasons: vec![0u32; num_vars],
            #[cfg(feature = "jit")]
            jit_guards: z4_jit::ClauseGuards::new(clauses_capacity),
            #[cfg(feature = "jit")]
            jit_qhead: 0,
        };

        // - Debug builds: full checking (every derived clause RUP-verified, #4564)
        // - Release builds: sampled checking (every 10th clause, #5625)
        if solver.proof_manager.is_some() {
            #[cfg(debug_assertions)]
            {
                solver.cold.forward_checker =
                    Some(crate::forward_checker::ForwardChecker::new(num_vars));
            }
            #[cfg(not(debug_assertions))]
            {
                solver.cold.forward_checker = Some(
                    crate::forward_checker::ForwardChecker::new_sampled(num_vars, 10),
                );
            }
        }

        solver
    }
}
