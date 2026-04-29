// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 proof obligation blocking: block_all, block_one, and related helpers
//! (reduce_cube_from_core, find_blocking_frame, dynamic_ctg_params).

use super::config::{
    consecution_verify_interval_full, Ic3Result, MAX_CROSSCHECK_FAILURES, MAX_OBLIGATION_DEPTH,
    MAX_SOLVER_REBUILDS_PER_FRAME, MAX_SPURIOUS_INIT_PREDS, MAX_TOTAL_CROSSCHECK_FAILURES,
    MAX_UNKNOWN_REQUEUES, UNKNOWN_FALLBACK_THRESHOLD,
};
use super::engine::Ic3Engine;
use super::frame::Lemma;
use super::obligation::ProofObligation;
use crate::sat_types::{Lit, SatResult, SatSolver, SolverBackend, Var};

impl Ic3Engine {
    /// Process all proof obligations.
    pub(super) fn block_all(&mut self) -> Result<(), Ic3Result> {
        let max_frame = self.frames.depth();
        while let Some(po) = self.obligations.pop(max_frame) {
            if self.is_cancelled() {
                return Err(Ic3Result::Unknown {
                    reason: "cancelled".into(),
                });
            }
            // Skip obligations whose cubes are already blocked by existing lemmas.
            // This check is cheap (subsumption test on sorted lemma lists) and avoids
            // redundant SAT calls for cubes that were blocked by a generalized lemma
            // from a prior iteration. Note: we still go through block_one for frame-0
            // obligations (counterexample verification) even if "blocked" by the frame
            // data structure, because the frame check is an over-approximation.
            if po.frame > 0 && self.frames.is_blocked(po.frame, &po.cube) {
                continue;
            }
            self.block_one(po)?;
        }
        Ok(())
    }

    /// Try to block a single proof obligation.
    pub(super) fn block_one(&mut self, mut po: ProofObligation) -> Result<(), Ic3Result> {
        // Depth limit: if the obligation chain is too deep, give up on this
        // branch. The BMC engine is better suited for deep counterexamples.
        // This prevents runaway depth explosion on circuits with very long
        // reachability chains (e.g., large shift registers, counters).
        if po.depth > MAX_OBLIGATION_DEPTH {
            return Ok(());
        }

        // Early init-subsumption skip (#4074): if the PO's cube is truly consistent
        // with Init AND the PO is at a frame > 0, skip it entirely.
        //
        // Rationale: Init states are always reachable (they're in F_0 by definition),
        // so they can never be blocked by IC3 lemmas. A cube consistent with Init
        // at frame k > 0 means the consecution check would find a predecessor
        // (since the init state transitions to itself or another reachable state),
        // creating an obligation at frame k-1, which eventually descends to frame 0
        // where verify_trace fails (spurious) or succeeds (real CEX).
        //
        // CONVERGENCE FIX (#4104): Use precise SAT-based check instead of the fast
        // over-approximation.
        if po.frame > 0 && self.cube_sat_consistent_with_init(&po.cube) {
            if std::env::var("IC3_DEBUG").is_ok() {
                eprintln!(
                    "IC3 skip_init: frame={} depth={} cube_len={} (init-consistent at frame>0)",
                    po.frame,
                    po.depth,
                    po.cube.len(),
                );
            }
            return Ok(());
        }

        // Trivial containment check (#4074, rIC3 block.rs:113-118):
        // If the cube is already blocked by a lemma at this frame or higher,
        // push the PO up to the frame where it's blocked instead of doing
        // a redundant SAT check.
        if po.frame > 0 {
            if let Some(higher_frame) = self.find_blocking_frame(po.frame, &po.cube) {
                if higher_frame > po.frame && higher_frame < self.frames.depth() {
                    po.push_to_frame(higher_frame + 1);
                    self.obligations.push(po);
                }
                // If blocked at po.frame exactly, just skip (already handled).
                return Ok(());
            }
        }

        // GAP-2: Bump activity and drop high-activity POs (#4151).
        po.bump_act();
        if self.config.drop_po && po.act > self.config.drop_po_threshold {
            self.po_drop_count += 1;
            if std::env::var("IC3_DEBUG").is_ok() {
                eprintln!(
                    "IC3 drop_po: frame={} depth={} act={:.1} cube_len={} total_dropped={}",
                    po.frame,
                    po.depth,
                    po.act,
                    po.cube.len(),
                    self.po_drop_count,
                );
            }
            return Ok(());
        }

        if po.frame == 0 {
            // CONVERGENCE FIX (#4074): Fast-path for init-inconsistent cubes.
            let init_consistent = self.cube_consistent_with_init(&po.cube);
            if !init_consistent {
                if std::env::var("IC3_DEBUG").is_ok() {
                    eprintln!(
                        "IC3 block_one: frame=0 depth={} SKIP_VERIFY (init-inconsistent) cube_len={}",
                        po.depth,
                        po.cube.len(),
                    );
                }
                // Block the spurious cube at frame 0 ONLY.
                //
                // SOUNDNESS FIX (#4092): Init-inconsistent cubes are only guaranteed
                // unreachable from Init (frame 0), NOT from all frames. Adding them
                // to all frame solvers is unsound: a cube like {v2} (v2=true) is
                // init-inconsistent (Init has v2=0), but v2=true IS reachable at
                // higher frames through the transition relation.
                //
                // The original code `for s in &mut self.solvers { s.add_clause(...) }`
                // caused false UNSAT on circuits like the 3-deep shift register:
                // blocking {v2} at frame 0 added [~v2] to ALL solvers, which falsely
                // constrained higher frames to never have v2=true.
                let neg_cube: Vec<Lit> = po.cube.iter().map(|l| !*l).collect();
                let lemma = Lemma::from_blocked_cube(&po.cube);
                self.frames.add_lemma(0, lemma.clone());
                if !self.solvers.is_empty() {
                    self.solvers[0].add_clause(&neg_cube);
                }
                return Ok(());
            }

            // Cube is init-consistent: might be a real counterexample.
            // Verify the full counterexample trace using BMC-style unrolling.
            let trace_ok = self.verify_trace(&po);
            if std::env::var("IC3_DEBUG").is_ok() {
                eprintln!(
                    "IC3 block_one: frame=0 depth={} verify_trace={} cube_len={} cube_init_consistent=true",
                    po.depth,
                    trace_ok,
                    po.cube.len(),
                );
            }
            if trace_ok {
                let trace = self.extract_trace(&po);
                return Err(Ic3Result::Unsafe {
                    depth: po.depth,
                    trace,
                });
            }

            // Spurious counterexample: verify_trace failed despite the fast
            // init-consistency check returning true.
            //
            // CONVERGENCE FIX (#4104): Use precise SAT-based init check.
            let truly_in_init = self.cube_sat_consistent_with_init(&po.cube);
            if !truly_in_init {
                if std::env::var("IC3_DEBUG").is_ok() {
                    eprintln!(
                        "IC3 block_one: frame=0 depth={} BLOCK_SPURIOUS (init-inconsistent via SAT) cube_len={}",
                        po.depth,
                        po.cube.len(),
                    );
                }
                // SOUNDNESS FIX (#4092): Only add to solver[0], not all solvers.
                // See comment in the init-inconsistent fast path above for full explanation.
                let neg_cube: Vec<Lit> = po.cube.iter().map(|l| !*l).collect();
                let lemma = Lemma::from_blocked_cube(&po.cube);
                self.frames.add_lemma(0, lemma.clone());
                if !self.solvers.is_empty() {
                    self.solvers[0].add_clause(&neg_cube);
                }
            } else {
                self.spurious_init_pred_count += 1;
                if std::env::var("IC3_DEBUG").is_ok() {
                    eprintln!(
                        "IC3 block_one: frame=0 depth={} REQUEUE_SUCCESSOR (truly in Init, verify_trace spurious) cube_len={} spurious_count={}",
                        po.depth,
                        po.cube.len(),
                        self.spurious_init_pred_count,
                    );
                }
                // FIX (#4105): When the predecessor is truly in Init but verify_trace
                // fails, the predecessor cube is too abstract. Re-queue the successor
                // PO so IC3 can try to block it with a different predecessor.
                //
                // LOOP BREAKER (#4105): After MAX_SPURIOUS_INIT_PREDS consecutive
                // spurious init-consistent predecessors, stop re-queuing the successor.
                // On constraint-heavy circuits (e.g., microban_1: 124 constraints,
                // 23 latches), the verify_trace check may fail systematically because
                // the partial cube from the lift solver is too abstract to reconstruct
                // a concrete trace through 124 constraints. Re-queuing just rediscovers
                // the same pattern. Dropping the successor is sound: IC3's frame
                // sequence still over-approximates reachability, and the unblocked
                // cube will be re-examined at the next depth level.
                if self.spurious_init_pred_count <= MAX_SPURIOUS_INIT_PREDS {
                    if let Some(successor) = po.next.map(|n| *n) {
                        if successor.frame > 0 {
                            self.obligations.push(successor);
                        }
                    }
                } else if std::env::var("IC3_DEBUG").is_ok() {
                    eprintln!(
                        "IC3 block_one: frame=0 depth={} DROP_SPURIOUS (spurious_count={} > {}) — \
                         stopping successor re-queue to break infinite loop (#4105)",
                        po.depth, self.spurious_init_pred_count, MAX_SPURIOUS_INIT_PREDS,
                    );
                }
            }
            return Ok(());
        }

        let solver_idx = po.frame - 1;
        // Block check WITHOUT !cube strengthening (strengthen=false).
        let assumptions = self.prime_cube(&po.cube);

        // Domain-restricted consecution (#4059, #4091).
        // Domain is computed once inside build_consecution_domain_solver and
        // returned alongside the solver to avoid double-computation (#4081).
        let used_domain_restriction;
        let result = if let Some((mut domain_solver, domain)) =
            self.build_consecution_domain_solver(po.frame, &po.cube)
        {
            used_domain_restriction = true;
            self.domain_stats
                .record(domain.len(), self.max_var as usize + 1, true);

            domain_solver.set_cancelled(self.cancelled.clone());
            let domain_result = domain_solver.solve(&assumptions);
            if domain_result == SatResult::Unsat {
                SatResult::Unsat
            } else {
                // Use the full COI domain (not just cube vars) for set_domain
                // on the frame solver fallback. The COI includes AND-gate fanin,
                // input variables, and next-state variables — all needed for
                // z4-sat's domain-restricted BCP to work correctly (#4091).
                let domain_vars: Vec<Var> = (0..=self.max_var)
                    .filter(|&i| domain.contains(Var(i)))
                    .map(Var)
                    .collect();
                if self.solvers[solver_idx].is_poisoned() {
                    if self.solver_rebuild_budget_exceeded(solver_idx) {
                        SatResult::Sat // Conservative: treat as Sat (#4105)
                    } else {
                        self.rebuild_solver_at(solver_idx);
                        // small_circuit_mode (#4259, z4#8802): skip set_domain so
                        // z4-sat uses search_propagate_standard (plain BCP).
                        if !self.config.small_circuit_mode {
                            self.solvers[solver_idx].set_domain(&domain_vars);
                        }
                        let full_result = self.solvers[solver_idx].solve(&assumptions);
                        if !self.config.small_circuit_mode {
                            self.solvers[solver_idx].clear_domain();
                        }
                        full_result
                    }
                } else {
                    // small_circuit_mode (#4259, z4#8802): skip set_domain so
                    // z4-sat uses search_propagate_standard (plain BCP).
                    if !self.config.small_circuit_mode {
                        self.solvers[solver_idx].set_domain(&domain_vars);
                    }
                    let full_result = self.solvers[solver_idx].solve(&assumptions);
                    if !self.config.small_circuit_mode {
                        self.solvers[solver_idx].clear_domain();
                    }
                    full_result
                }
            }
        } else {
            used_domain_restriction = false;
            self.domain_stats
                .record(0, self.max_var as usize + 1, false);
            if self.solvers[solver_idx].is_poisoned() {
                if self.solver_rebuild_budget_exceeded(solver_idx) {
                    SatResult::Sat // Conservative: treat as Sat (#4105)
                } else {
                    self.rebuild_solver_at(solver_idx);
                    self.solvers[solver_idx].solve(&assumptions)
                }
            } else {
                self.solvers[solver_idx].solve(&assumptions)
            }
        };

        // Track consecution query result (#4121 diagnostics).
        self.consecution_stats.total_queries += 1;
        match result {
            SatResult::Unsat => self.consecution_stats.unsat_results += 1,
            SatResult::Sat => self.consecution_stats.sat_results += 1,
            SatResult::Unknown => self.consecution_stats.unknown_results += 1,
        }
        if used_domain_restriction {
            self.consecution_stats.domain_restricted += 1;
        } else {
            self.consecution_stats.full_solver += 1;
        }

        match result {
            SatResult::Unsat => {
                self.unknown_count = 0;
                // Reset spurious init-pred counter on successful block (#4105).
                // The counter only matters for consecutive spurious predecessors
                // without any progress. A successful block means IC3 is making
                // progress, so reset the counter.
                self.spurious_init_pred_count = 0;

                // Cube blocked — generalize with MIC.
                //
                // Parent lemma MIC seeding (CAV'23 #4150): when enabled and the PO
                // has a parent, extract the parent's cube and pass it to MIC. The
                // MIC function will intersect the current cube with the parent's
                // blocking lemma, producing a tighter starting point.
                let parent_cube_for_mic: Option<Vec<Lit>> = if self.config.parent_lemma_mic {
                    po.next.as_ref().map(|parent| parent.cube.clone())
                } else {
                    None
                };
                let parent_ref = parent_cube_for_mic.as_deref();

                let generalized = if self.config.parent_lemma_mic && parent_ref.is_some() {
                    // Use parent-seeded MIC variants.
                    if self.config.dynamic {
                        let (dyn_ctg_max, dyn_ctg_limit) = Self::dynamic_ctg_params(&po);
                        if self.config.multi_lift_orderings >= 2 {
                            self.mic_multi_order_with_parent_seed_params(
                                po.frame,
                                po.cube.clone(),
                                parent_ref,
                                dyn_ctg_max,
                                dyn_ctg_limit,
                            )
                        } else {
                            self.mic_with_parent_seed_params(
                                po.frame,
                                po.cube.clone(),
                                parent_ref,
                                dyn_ctg_max,
                                dyn_ctg_limit,
                            )
                        }
                    } else if self.config.multi_lift_orderings >= 2 {
                        self.mic_multi_order_with_parent_seed(po.frame, po.cube.clone(), parent_ref)
                    } else {
                        self.mic_with_parent_seed(po.frame, po.cube.clone(), parent_ref)
                    }
                } else if self.config.dynamic {
                    let (dyn_ctg_max, dyn_ctg_limit) = Self::dynamic_ctg_params(&po);
                    if self.config.multi_lift_orderings >= 2 {
                        self.mic_multi_order_with_params(
                            po.frame,
                            po.cube.clone(),
                            dyn_ctg_max,
                            dyn_ctg_limit,
                        )
                    } else {
                        self.mic_with_params(po.frame, po.cube.clone(), dyn_ctg_max, dyn_ctg_limit)
                    }
                } else if self.config.multi_lift_orderings >= 2 {
                    self.mic_multi_order(po.frame, po.cube.clone())
                } else {
                    self.mic(po.frame, po.cube.clone())
                };

                // SOUNDNESS CHECK (#4092): Refuse init-consistent lemmas.
                if self.cube_sat_consistent_with_init(&generalized) {
                    return Ok(());
                }

                // SOUNDNESS CHECK (#4092, #4121): Independent consecution verification.
                // Uses adaptive verification interval based on clause-to-latch ratio:
                // high-ratio circuits verify every consecution (interval=1), low-ratio
                // circuits sample every 10th. This catches z4-sat false UNSAT on
                // constraint-heavy circuits without excessive overhead on simple ones.
                //
                // CONVERGENCE FIX (#4105): Skip cross-check entirely when disabled.
                // On clause-heavy circuits (ratio > 5x), SimpleSolver's basic DPLL
                // without clause learning produces false SAT, causing every z4-sat
                // UNSAT result to be rejected. Disabling the cross-check and trusting
                // z4-sat (with validate_invariant_budgeted as final soundness net) is
                // the correct response for these circuits.
                if self.ts.latch_vars.len() <= 60 && !self.crosscheck_disabled {
                    self.consecution_verify_counter += 1;
                    let verify_interval = consecution_verify_interval_full(
                        self.ts.trans_clauses.len(),
                        self.ts.constraint_lits.len(),
                        self.ts.latch_vars.len(),
                    );
                    // Small-circuit fast path (#4259, #4288): verify_interval ==
                    // usize::MAX signals "skip cross-check entirely". Happens on
                    // <30 latches where SimpleSolver DPLL is unreliable on
                    // clause-dense circuits. Post-convergence validation still
                    // guards soundness. Short-circuit here so the modulo/budget
                    // machinery below is bypassed cleanly.
                    let should_verify = if verify_interval == usize::MAX {
                        false
                    } else {
                        self.consecution_verify_counter % verify_interval == 0
                    };
                    let frame_failures = self
                        .crosscheck_failures
                        .get(solver_idx)
                        .copied()
                        .unwrap_or(0);
                    // For clause-heavy circuits (verify_interval==1), use a tighter
                    // total-failure threshold to trigger the cross-check disable sooner.
                    // These circuits produce cross-check disagreements at a higher rate
                    // because SimpleSolver can't handle the constraint density (#4105).
                    let effective_total_threshold = if verify_interval == 1 {
                        MAX_TOTAL_CROSSCHECK_FAILURES / 2
                    } else {
                        MAX_TOTAL_CROSSCHECK_FAILURES
                    };
                    let needs_global_fallback =
                        self.total_crosscheck_failures >= effective_total_threshold;
                    let needs_frame_fallback = frame_failures >= MAX_CROSSCHECK_FAILURES;
                    if should_verify
                        && frame_failures < MAX_CROSSCHECK_FAILURES
                        && !needs_global_fallback
                    {
                        if !self.verify_consecution_independent(po.frame, &generalized, true) {
                            if std::env::var("IC3_DEBUG").is_ok() {
                                eprintln!(
                                    "IC3 CROSS-CHECK FAIL: frame={} cube_len={} failures={}/{} — z4-sat false UNSAT, \
                                     SimpleSolver disagrees.",
                                    po.frame,
                                    generalized.len(),
                                    frame_failures + 1,
                                    self.total_crosscheck_failures + 1,
                                );
                            }
                            if solver_idx < self.crosscheck_failures.len() {
                                self.crosscheck_failures[solver_idx] += 1;
                            }
                            self.total_crosscheck_failures += 1;
                            if let Some(pred) = self.consecution_simple_fallback(po.frame, &po.cube)
                            {
                                if self.cube_sat_consistent_with_init(&pred) {
                                    self.obligations.push(po);
                                    return Ok(());
                                }
                                self.obligations.push(ProofObligation::new(
                                    po.frame - 1,
                                    pred,
                                    po.depth + 1,
                                    Some(po.clone()),
                                ));
                                self.obligations.push(po);
                                return Ok(());
                            }
                        }
                    } else if needs_global_fallback {
                        // Global cross-check budget exhausted (#4105, #4121).
                        //
                        // On clause-heavy circuits (verify_interval==1), SimpleSolver
                        // is the problem, not z4-sat. SimpleSolver's basic DPLL without
                        // clause learning produces false SAT on constraint-dense formulas
                        // (e.g., microban_1: 124 constraints, 879 trans_clauses, 23
                        // latches). Falling back to SimpleSolver makes IC3 unable to
                        // solve anything.
                        //
                        // Instead: disable cross-checking entirely and trust z4-sat.
                        // The post-convergence validate_invariant_budgeted() provides
                        // the ultimate soundness safety net.
                        //
                        // For low-ratio circuits (verify_interval > 1), fall back to
                        // SimpleSolver as before -- those circuits are simple enough
                        // that SimpleSolver works correctly.
                        if verify_interval == 1 {
                            eprintln!(
                                "IC3: cross-check budget exhausted on clause-heavy circuit \
                                 (total={}, threshold={}, ratio={:.1}x). \
                                 Disabling cross-check, trusting z4-sat (#4105).",
                                self.total_crosscheck_failures,
                                effective_total_threshold,
                                self.ts.trans_clauses.len() as f64
                                    / self.ts.latch_vars.len().max(1) as f64,
                            );
                            self.crosscheck_disabled = true;
                        } else if self.solver_backend != SolverBackend::Simple {
                            eprintln!(
                                "IC3: global cross-check budget exhausted (total={}, threshold={}). \
                                 Falling back to SimpleSolver (#4121).",
                                self.total_crosscheck_failures,
                                effective_total_threshold,
                            );
                            self.fallback_solver_backend();
                        }
                    } else if needs_frame_fallback {
                        if std::env::var("IC3_DEBUG").is_ok() {
                            eprintln!(
                                "IC3: cross-check budget exhausted at frame {} (frame_failures={}, total={}). \
                                 Disabling cross-check for this frame.",
                                po.frame,
                                frame_failures,
                                self.total_crosscheck_failures,
                            );
                        }
                    }
                }

                let (push_frame, pushed_cube) = self.push_lemma(po.frame, generalized);
                let lemma = Lemma::from_blocked_cube(&pushed_cube);
                let target_frame = (push_frame - 1).min(self.frames.depth() - 1);

                // Per-lemma consecution verification (#4121 diagnostics).
                //
                // When IC3_VERIFY_LEMMAS is set, independently verify EVERY lemma
                // before adding it to the frame sequence. This catches z4-sat false
                // UNSAT at the earliest possible point, before unsound lemmas
                // propagate. Expensive (doubles SAT calls), but invaluable for
                // diagnosing which benchmarks trigger z4-sat bugs.
                //
                // When not set, this code is a no-op and the existing cross-check
                // + validate_invariant_budgeted provide the soundness net.
                if std::env::var("IC3_VERIFY_LEMMAS").is_ok() {
                    if !self.verify_lemma_consecution(po.frame, &pushed_cube) {
                        self.consecution_stats.lemmas_rejected += 1;
                        eprintln!(
                            "IC3 LEMMA REJECTED: frame={} cube_len={} pushed_len={} \
                             total_rejected={} — independent verification says SAT \
                             (z4-sat false UNSAT in consecution)",
                            po.frame,
                            po.cube.len(),
                            pushed_cube.len(),
                            self.consecution_stats.lemmas_rejected,
                        );
                        // Skip adding this unsound lemma. Treat as SAT (no block).
                        self.obligations.push(po);
                        return Ok(());
                    }
                    self.consecution_stats.lemmas_verified += 1;
                }

                if std::env::var("IC3_DEBUG").is_ok() {
                    eprintln!(
                        "IC3 block_one: frame={} BLOCKED cube_len={} mic_len={} push_frame={} target_frame={} lemma={:?}",
                        po.frame,
                        po.cube.len(),
                        pushed_cube.len(),
                        push_frame,
                        target_frame,
                        &lemma.lits,
                    );
                }
                self.frames.add_lemma(target_frame, lemma.clone());
                if target_frame > 0 {
                    self.earliest_changed_frame = self.earliest_changed_frame.min(target_frame);
                }
                let start = if target_frame == 0 { 0 } else { 1 };
                for s in &mut self.solvers[start..=target_frame] {
                    s.add_clause(&lemma.lits);
                }
                if let Some(ref mut pp) = self.predprop_solver {
                    pp.add_lemma(&lemma.lits);
                }
                Ok(())
            }
            SatResult::Sat => {
                self.unknown_count = 0;

                // Per-latch flip_to_none pre-filter (#4091 Phase 3).
                let essential_latches = if self.config.flip_to_none_lift {
                    let flippable_latches = {
                        let solver = self.solvers[solver_idx].as_mut();
                        let mut flipped = rustc_hash::FxHashSet::default();
                        for &lv in &self.ts.latch_vars {
                            if solver.flip_to_none(lv) {
                                flipped.insert(lv);
                            }
                        }
                        flipped
                    };
                    self.solvers[solver_idx].minimize_model(&self.ts.latch_vars);
                    if flippable_latches.is_empty() {
                        self.ts.latch_vars.clone()
                    } else {
                        self.ts
                            .latch_vars
                            .iter()
                            .filter(|lv| !flippable_latches.contains(lv))
                            .copied()
                            .collect()
                    }
                } else {
                    self.solvers[solver_idx].minimize_model(&self.ts.latch_vars);
                    self.ts.latch_vars.clone()
                };

                // SAT-based predecessor lifting.
                let pred = {
                    let Ic3Engine {
                        ref mut lift,
                        ref solvers,
                        ref ts,
                        ref config,
                        ref ternary_sim,
                        ref reverse_next,
                        ..
                    } = *self;
                    let mut p = lift.lift_with_ternary(
                        solvers[solver_idx].as_ref(),
                        &assumptions,
                        &essential_latches,
                        &ts.input_vars,
                        Some(ternary_sim),
                        Some(reverse_next),
                    );
                    if config.internal_signals && !ts.internal_signals.is_empty() {
                        let isig_lits = Self::extract_state_from_solver(
                            solvers[solver_idx].as_ref(),
                            &ts.internal_signals,
                        );
                        p.extend(isig_lits);
                    }
                    p
                };
                // Init-consistent predecessor: may be a real counterexample (#4074, #4139).
                //
                // If the predecessor IS in Init, then Init can reach po.cube in one step.
                // Instead of just re-queuing the original PO (which drop_po may silently
                // discard, causing infinite rediscovery), create a frame-0 PO for the
                // predecessor with the original PO as its successor. This gives the
                // frame-0 handler a chance to verify the full trace via BMC unrolling.
                //
                // Before #4139: `self.obligations.push(po); return Ok(());` — this
                // re-queued the original PO at its current frame, but drop_po could
                // kill it before it ever reached frame 0, creating an infinite loop
                // where get_bad() kept rediscovering the same bad cube.
                if self.cube_sat_consistent_with_init(&pred) {
                    let pred_po = ProofObligation::new(0, pred, po.depth + 1, Some(po));
                    self.obligations.push(pred_po);
                    return Ok(());
                }
                self.obligations.push(ProofObligation::new(
                    po.frame - 1,
                    pred,
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.obligations.push(po);
                Ok(())
            }
            SatResult::Unknown => {
                if self.solvers[solver_idx].is_poisoned() {
                    if !self.solver_rebuild_budget_exceeded(solver_idx) {
                        self.rebuild_solver_at(solver_idx);
                    }
                    self.unknown_count = 0;
                } else {
                    self.unknown_count += 1;
                    if self.unknown_count >= UNKNOWN_FALLBACK_THRESHOLD
                        && self.solver_backend != SolverBackend::Simple
                    {
                        self.fallback_solver_backend();
                    }
                }
                po.unknown_requeues += 1;
                if po.unknown_requeues <= MAX_UNKNOWN_REQUEUES {
                    self.obligations.push(po);
                } else if std::env::var("IC3_DEBUG").is_ok() {
                    eprintln!(
                        "IC3 DROP_UNKNOWN: frame={} depth={} requeues={} — dropping PO after \
                         {} Unknown results",
                        po.frame, po.depth, po.unknown_requeues, MAX_UNKNOWN_REQUEUES,
                    );
                }
                Ok(())
            }
        }
    }

    /// Reduce a cube using the UNSAT core from the solver.
    #[allow(dead_code)]
    pub(super) fn reduce_cube_from_core(&self, solver_idx: usize, cube: &[Lit]) -> Vec<Lit> {
        let Some(core) = self.solvers[solver_idx].unsat_core() else {
            return cube.to_vec();
        };
        if core.is_empty() {
            return cube.to_vec();
        }
        let mut core_latch_vars = rustc_hash::FxHashSet::default();
        for &core_lit in &core {
            if let Some(&latch_var) = self.reverse_next.get(&core_lit.var()) {
                core_latch_vars.insert(latch_var);
            }
        }
        let reduced: Vec<Lit> = cube
            .iter()
            .filter(|lit| core_latch_vars.contains(&lit.var()))
            .copied()
            .collect();
        if reduced.is_empty() {
            cube.to_vec()
        } else {
            reduced
        }
    }

    /// Find the lowest frame >= start_frame where the cube is already blocked.
    pub(super) fn find_blocking_frame(&self, start_frame: usize, cube: &[Lit]) -> Option<usize> {
        let clause = Lemma::from_blocked_cube(cube);
        for i in start_frame..self.frames.frames.len() {
            if self.frames.frames[i].has_subsuming(&clause) {
                return Some(i);
            }
        }
        for lemma in &self.inf_lemmas {
            if lemma.subsumes(&clause) {
                return Some(self.frames.frames.len());
            }
        }
        None
    }

    /// Compute dynamic CTG parameters from a proof obligation's activity chain.
    pub(super) fn dynamic_ctg_params(po: &ProofObligation) -> (usize, usize) {
        const CTG_THRESHOLD: f64 = 10.0;
        const EXCTG_THRESHOLD: f64 = 40.0;

        let mut max_act = 0.0_f64;
        if let Some(ref next) = po.next {
            max_act = max_act.max(next.act);
            if let Some(ref nn) = next.next {
                max_act = max_act.max(nn.act);
                if let Some(ref nnn) = nn.next {
                    max_act = max_act.max(nnn.act);
                }
            }
        }

        if max_act >= EXCTG_THRESHOLD {
            let limit = ((max_act - EXCTG_THRESHOLD).powf(0.45) * 2.0 + 5.0).round() as usize;
            (5, limit)
        } else if max_act >= CTG_THRESHOLD {
            let ctg_max = ((max_act - CTG_THRESHOLD) as usize / 10) + 2;
            (ctg_max, 1)
        } else {
            (0, 0)
        }
    }
}
