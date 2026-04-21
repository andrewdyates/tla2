// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified CDCL backend loop for theory callback and extension modes.

use super::super::*;
use super::theory_callback::{TheoryCallback, TheoryModelCheck};

impl Solver {
    pub(super) fn disable_extension_inprocessing(&mut self) {
        self.inproc_ctrl.condition.enabled = false;
        self.inproc_ctrl.bve.enabled = false;
        self.inproc_ctrl.bce.enabled = false;
        self.inproc_ctrl.sweep.enabled = false;
        self.inproc_ctrl.congruence.enabled = false;
        self.inproc_ctrl.factor.enabled = false;
        self.inproc_ctrl.decompose.enabled = false;
        // #7979: Vivification is SAFE for theory/extension mode. It strengthens
        // clauses by removing redundant literals via BCP — no variable elimination,
        // no binary implication generation, no reconstruction needed. Disabling
        // vivification degraded learned clause quality, breaking CDCL search
        // trajectories that E-matching depends on for AUFLIA convergence.
        // Subsumption and HTR were already enabled; vivify completes the set
        // of theory-safe inprocessing techniques.
        //
        // UNSAFE techniques remain disabled:
        //   BVE: eliminates variables, reconstruction interacts with theory lemmas
        //   BCE: removes clauses, may drop theory-relevant blocking clauses
        //   Sweep: variable equivalence substitution without theory consultation
        //   Congruence/Decompose: SCC-based rewriting without theory awareness
        //   Factor: introduces extension variables
        //   Condition: root-satisfied clause GC, may drop theory-visible clauses
        //   Probe: HBR-derived implications are unsound without theory (#7935)
        //   Backbone: uses probing internally, inherits probe unsoundness
        //
        // #7935: Probing with HBR generates binary implication clauses that
        // are sound for pure SAT but unsound in DPLL(T) — the SAT-level
        // probe does not consult the theory, so implications derived from
        // failed literals may not hold under theory semantics. Backbone
        // detection uses probing internally and inherits the same unsoundness.
        self.inproc_ctrl.probe.enabled = false;
        self.inproc_ctrl.backbone.enabled = false;
    }

    /// Unified CDCL loop for theory callback and extension modes (Wave 2).
    ///
    /// The optional `should_stop` closure is polled every 100 conflicts and
    /// every 1000 decisions, matching `solve_no_assumptions`. When it returns
    /// `true`, the solver returns `Unknown` with reason `Interrupted`.
    pub(super) fn solve_no_assumptions_with_theory_backend<C, F>(
        &mut self,
        callback: &mut C,
        should_stop: F,
    ) -> SatResult
    where
        C: TheoryCallback,
        F: Fn() -> bool,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;
        self.cold.finalize_sat_fail_count = 0;

        // Record wall-clock start time for progress reporting (matches init_solve).
        if self.cold.progress_enabled {
            self.cold.solve_start_time = Some(std::time::Instant::now());
            self.cold.last_progress_time = None;
        }

        if let Some(result) = callback.init_loop(self) {
            return result;
        }

        // Run initial preprocessing in theory/extension mode.
        // Only safe techniques run: subsumption, probing, HTR (add implications
        // only). Clause-deleting and variable-eliminating techniques are disabled
        // because theory callbacks may add lemmas referencing any variable/clause
        // during the CDCL loop that follows.
        if self.cold.preprocess_enabled && !self.cold.has_been_incremental {
            // #7935: Disable ALL preprocessing in theory/extension mode.
            // SAT-level preprocessing (probing, backbone, HTR, subsumption)
            // operates without theory solver consultation. It can derive
            // implications that are sound for pure SAT but unsound in DPLL(T),
            // forcing theory atoms TRUE at level 0 and creating spurious
            // theory conflicts. Previously only clause-deleting techniques
            // were disabled; now all techniques are blocked.
            self.cold.preprocess_enabled = false;
        }

        // Disable destructive inprocessing techniques for theory/extension mode.
        //
        // BVE, BCE, sweep, congruence, decompose, factor, condition, probe, and
        // backbone are unsound in DPLL(T): they modify or eliminate variables
        // and clauses without consulting the theory solver. BVE in particular
        // creates reconstruction entries that can cause finalize_sat_model to
        // fail original-formula verification, producing InvalidSatModel -> Unknown.
        //
        // Previously only the preprocessing_extension path (used by standalone
        // SAT with preprocessing) called disable_extension_inprocessing(). The
        // extension/theory paths that enter through solve_with_extension() or
        // solve_with_theory() did NOT, leaving BVE/probe/sweep/etc. enabled
        // during the CDCL loop. After enough conflicts, inprocessing_gates_pass()
        // would trigger run_restart_inprocessing() with these destructive
        // techniques active, causing QF_LRA (and other theory) benchmarks to
        // return Unknown instead of Sat/Unsat.
        //
        // Safe techniques (vivify, subsume, HTR, reorder) remain enabled --
        // see disable_extension_inprocessing() for the full rationale.
        self.disable_extension_inprocessing();

        // CaDiCaL init_search_limits (internal.cpp:487-489) for DPLL(T) path.
        // Same formula-size-proportional inprobe limit as the pure SAT path.
        {
            let irredundant = self.arena.active_clause_count() as f64;
            let delta = (irredundant + 10.0).log10();
            let delta = delta * delta;
            let limit = (INPROBE_INTERVAL as f64 * delta) as u64;
            self.cold.next_inprobe_conflict = self.num_conflicts.saturating_add(limit);
        }

        self.cdcl_loop(callback, should_stop)
    }

    #[inline]
    pub(in crate::solver) fn maybe_run_restart<C: TheoryCallback>(
        &mut self,
        callback: &mut C,
    ) -> bool {
        if self.num_conflicts < callback.restart_warmup_conflicts() {
            return false;
        }
        if !self.should_restart() {
            return false;
        }
        if callback.should_block_restart(self.trail.len() as u32, self.num_vars as u32) {
            return false;
        }

        let vars_to_bump = callback.on_restart();
        self.do_restart();
        // #7982: Re-boost theory atom VSIDS activity at restart time.
        // Theory atoms get one initial bump at registration but are quickly
        // overwhelmed by conflict-driven activity. Re-boosting at restart
        // keeps theory atoms competitive in the VSIDS heap, ensuring the
        // DPLL solver continues deciding theory atoms and feeding bounds
        // to the theory solver.
        //
        // Each theory atom gets 3 bumps (equivalent to 3 conflict
        // participations). This compensates for the fact that conflict
        // variables get bumped ~5-10 times per conflict through resolution,
        // while theory atoms get 0 bumps unless they appear in theory lemmas.
        let use_vsids = self.active_branch_heuristic != BranchHeuristic::Vmtf;
        for var in vars_to_bump {
            if var.index() < self.num_vars {
                for _ in 0..3 {
                    self.vsids.bump(var, &self.vals, use_vsids);
                }
            }
        }
        true
    }

    /// Unified CDCL inner loop shared by pure SAT, theory, and extension modes.
    ///
    /// All solve-mode specific preamble (init, preprocessing, walk, and search
    /// limit setup) is done by the caller before entering this loop.
    pub(in crate::solver) fn cdcl_loop<C, F>(
        &mut self,
        callback: &mut C,
        should_stop: F,
    ) -> SatResult
    where
        C: TheoryCallback,
        F: Fn() -> bool,
    {
        loop {
            if self.is_interrupted() {
                return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
            }

            // Check if an inprocessing/theory lemma detected global UNSAT.
            if self.has_empty_clause {
                return self.declare_unsat();
            }

            // Propagate — search-specialized BCP (no probe/vivify overhead).
            let trail_len_before_prop = self.trail.len();
            let propagate_result = self.search_propagate();
            if let Some(conflict_ref) = propagate_result {
                if self.cold.tla_trace.is_some() && self.trail.len() > trail_len_before_prop {
                    self.tla_trace_step("PROPAGATING", Some("Propagate"));
                }
                self.tla_trace_step("CONFLICTING", Some("DetectConflict"));

                if self.decision_level == 0 {
                    if self.cold.trace_ext_conflict {
                        let lits = self.arena.literals(conflict_ref.0 as usize);
                        eprintln!(
                            "[CDCL] BCP level-0 conflict! clause_ref={:?} lits={:?}",
                            conflict_ref,
                            lits.iter()
                                .map(|l| (l.variable().index(), l.is_positive()))
                                .collect::<Vec<_>>()
                        );
                    }
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat();
                }

                self.conflicts_since_restart += 1;
                self.num_conflicts += 1;
                self.on_conflict_random_decision();

                if self.cold.trace_ext_conflict {
                    let lits = self.arena.literals(conflict_ref.0 as usize);
                    eprintln!(
                        "[CDCL] BCP conflict at dl={} clause_ref={:?} lits={:?}",
                        self.decision_level,
                        conflict_ref,
                        lits.iter()
                            .map(|l| (l.variable().index(), l.is_positive()))
                            .collect::<Vec<_>>()
                    );
                    for lit in lits {
                        let var = lit.variable();
                        let val = self.var_value_from_vals(var.index());
                        let level = self.var_data[var.index()].level;
                        eprintln!(
                            "[CDCL]   var={} pos={} val={:?} level={}",
                            var.index(),
                            lit.is_positive(),
                            val,
                            level
                        );
                    }
                }

                // Interrupt check on conflict path (#6296): matches
                // solve_no_assumptions' every-100-conflicts check.
                if self.num_conflicts.is_multiple_of(100) {
                    if should_stop() {
                        return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                    }
                    // Periodic progress reporting (wall-clock gated, ~5s interval).
                    self.maybe_emit_progress();
                }

                let context = callback.conflict_context();
                self.analyze_and_backtrack(conflict_ref, context, |_, level| {
                    callback.backtrack(level);
                });
                self.maybe_run_restart(callback);
                continue;
            }

            if self.cold.tla_trace.is_some() && self.trail.len() > trail_len_before_prop {
                self.tla_trace_step("PROPAGATING", Some("Propagate"));
            }

            // Run backend-specific propagation checks before making a SAT decision.
            let theory_result = callback.propagate(self);
            if self.cold.trace_ext_conflict {
                let tag = match &theory_result {
                    TheoryPropResult::Continue => "",
                    TheoryPropResult::Propagate => "Propagate",
                    TheoryPropResult::Conflict(_) => "Conflict",
                    TheoryPropResult::Stop => "Stop",
                };
                if !tag.is_empty() {
                    eprintln!(
                        "[CDCL] theory returned {} at dl={} trail_len={}",
                        tag,
                        self.decision_level,
                        self.trail.len()
                    );
                }
            }
            match theory_result {
                TheoryPropResult::Continue => {}
                TheoryPropResult::Propagate => {
                    // #8003 Gap 3: BCP-Theory fixed-point loop.
                    // Z3 loops BCP + theory propagation to quiescence before
                    // making a decision. Previously Z4 did a single BCP pass,
                    // single theory propagation, then `continue`d to the top
                    // of the CDCL loop (hitting all scheduling checks). Now we
                    // run an inner loop: re-run BCP + theory propagation until
                    // both return no-change, then fall through to scheduling.
                    // Bounded to MAX_FIXPOINT_ITERS to prevent infinite loops.
                    const MAX_FIXPOINT_ITERS: u32 = 8;
                    let mut fixpoint_iter = 0u32;
                    loop {
                        // Check for pending theory conflict before BCP (#6262).
                        if let Some(conflict_ref) = self.take_pending_theory_conflict() {
                            self.conflicts_since_restart += 1;
                            self.num_conflicts += 1;
                            self.on_conflict_random_decision();
                            if self.decision_level == 0 {
                                self.record_level0_conflict_chain(conflict_ref);
                                return self.declare_unsat();
                            }
                            let context = callback.conflict_context();
                            self.analyze_and_backtrack(conflict_ref, context, |_, level| {
                                callback.backtrack(level);
                            });
                            self.maybe_run_restart(callback);
                            break;
                        }

                        fixpoint_iter += 1;
                        if fixpoint_iter > MAX_FIXPOINT_ITERS {
                            break;
                        }

                        // Theory lemma may have set has_empty_clause (e.g.,
                        // contradicting unit clauses). The outer loop checks
                        // this at the top, so break and let it handle UNSAT.
                        if self.has_empty_clause {
                            break;
                        }

                        // Re-run BCP on any new unit propagations from theory lemmas.
                        let trail_before = self.trail.len();
                        let bcp_result = self.search_propagate();
                        if let Some(conflict_ref) = bcp_result {
                            // BCP found a conflict — handle normally.
                            if self.decision_level == 0 {
                                self.record_level0_conflict_chain(conflict_ref);
                                return self.declare_unsat();
                            }
                            self.conflicts_since_restart += 1;
                            self.num_conflicts += 1;
                            self.on_conflict_random_decision();
                            if self.num_conflicts.is_multiple_of(100) {
                                if should_stop() {
                                    return self
                                        .declare_unknown_with_reason(SatUnknownReason::Interrupted);
                                }
                                self.maybe_emit_progress();
                            }
                            let context = callback.conflict_context();
                            self.analyze_and_backtrack(conflict_ref, context, |_, level| {
                                callback.backtrack(level);
                            });
                            self.maybe_run_restart(callback);
                            break;
                        }
                        let bcp_propagated = self.trail.len() > trail_before;

                        // Re-run theory propagation.
                        let inner_theory = callback.propagate(self);
                        match inner_theory {
                            TheoryPropResult::Continue => {
                                if !bcp_propagated {
                                    // Fixed point: neither BCP nor theory produced
                                    // anything new. Fall through to scheduling.
                                    break;
                                }
                                // BCP propagated but theory didn't — loop once more
                                // in case theory needs another look.
                            }
                            TheoryPropResult::Propagate => {
                                // Theory produced new propagations; loop to re-run BCP.
                            }
                            TheoryPropResult::Conflict(clause) => {
                                if let Some(result) =
                                    callback.handle_conflict_clause(self, clause)
                                {
                                    return result;
                                }
                                self.maybe_run_restart(callback);
                                break;
                            }
                            TheoryPropResult::Stop => {
                                return self
                                    .declare_unknown_with_reason(SatUnknownReason::TheoryStop);
                            }
                        }
                    }
                    continue;
                }
                TheoryPropResult::Conflict(clause) => {
                    if let Some(result) = callback.handle_conflict_clause(self, clause) {
                        return result;
                    }
                    self.maybe_run_restart(callback);
                    continue;
                }
                TheoryPropResult::Stop => {
                    return self.declare_unknown_with_reason(SatUnknownReason::TheoryStop);
                }
            }

            // Catch pending theory conflicts from non-propagation paths (#6262).
            // This handles the edge case where callback.propagate() returns
            // Continue but a previous iteration left a pending conflict.
            if let Some(conflict_ref) = self.take_pending_theory_conflict() {
                self.conflicts_since_restart += 1;
                self.num_conflicts += 1;
                self.on_conflict_random_decision();
                if self.decision_level == 0 {
                    self.record_level0_conflict_chain(conflict_ref);
                    return self.declare_unsat();
                }
                let context = callback.conflict_context();
                self.analyze_and_backtrack(conflict_ref, context, |_, level| {
                    callback.backtrack(level);
                });
                self.maybe_run_restart(callback);
                continue;
            }

            // CaDiCaL internal.cpp:290-332: else-if priority chain.
            // Exactly one scheduling action per CDCL iteration.
            // Restart has highest priority, then rephase, then inprocessing, then decide.
            if self.maybe_run_restart(callback) {
            } else if self.should_rephase() {
                if self.decision_level != 0 {
                    self.backtrack(0);
                    callback.backtrack(0);
                }
                self.rephase();
            } else if self.inprocessing_gates_pass() {
                if self.decision_level != 0 {
                    self.backtrack(0);
                    callback.backtrack(0);
                }
                let found_unsat = self.run_restart_inprocessing();
                if found_unsat {
                    return self.declare_unsat();
                }
                continue;
            } else if let Some(suggested) = callback
                .suggest_decision(self)
                .filter(|lit| self.value(lit.variable()).is_none())
            {
                // Extension suggested a decision (CP search heuristic)
                self.decide(suggested);
                if self.num_decisions.is_multiple_of(1000)
                    && (self.is_interrupted() || should_stop())
                {
                    return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                }
                self.tla_trace_step("PROPAGATING", Some("DecideExt"));
            } else if let Some(var) = self.pick_next_decision_variable() {
                // Ask the extension for a phase suggestion (Z3's get_phase).
                // Theory can suggest polarity consistent with its model.
                let lit = if let Some(phase) = callback.suggest_phase(var) {
                    if phase {
                        Literal::positive(var)
                    } else {
                        Literal::negative(var)
                    }
                } else {
                    self.pick_phase(var)
                };
                self.decide(lit);
                // Interrupt check on decision path (#3237, #6296): ensures
                // check_sat_with_timeout is respected even without conflicts.
                if self.num_decisions.is_multiple_of(1000)
                    && (self.is_interrupted() || should_stop())
                {
                    return self.declare_unknown_with_reason(SatUnknownReason::Interrupted);
                }
                self.tla_trace_step("PROPAGATING", Some("Decide"));
            } else {
                // Drain any pending theory conflict before model check (#6262).
                // A prior callback.propagate() may have set this via
                // add_theory_lemma's all-false detection without it being
                // consumed (e.g., propagate returned Continue).
                if let Some(conflict_ref) = self.take_pending_theory_conflict() {
                    self.conflicts_since_restart += 1;
                    self.num_conflicts += 1;
                    self.on_conflict_random_decision();
                    if self.decision_level == 0 {
                        self.record_level0_conflict_chain(conflict_ref);
                        return self.declare_unsat();
                    }
                    let context = callback.conflict_context();
                    self.analyze_and_backtrack(conflict_ref, context, |_, level| {
                        callback.backtrack(level);
                    });
                    self.maybe_run_restart(callback);
                    continue;
                }
                match callback.check_model(self) {
                    TheoryModelCheck::Sat => {
                        self.tla_trace_step("SAT", Some("DeclareSat"));
                        return self.declare_sat_from_current_assignment();
                    }
                    TheoryModelCheck::Conflict(clause) => {
                        if self.decision_level == 0 {
                            return self.declare_unsat();
                        }
                        if let Some(result) = callback.handle_conflict_clause(self, clause) {
                            return result;
                        }
                    }
                    TheoryModelCheck::Unknown(reason) => {
                        return self.declare_unknown_with_reason(reason);
                    }
                    TheoryModelCheck::AddClauses(clauses) => {
                        // #6546: theory returned lemma clauses — add them and
                        // continue SAT solving. This avoids restarting the
                        // SAT solve from scratch via the outer split loop.
                        for clause in clauses {
                            self.add_theory_lemma(clause);
                        }
                        // Continue the CDCL loop — BCP will process the new
                        // clauses and potentially find conflicts or propagate.
                    }
                }
            }
        }
    }
}
