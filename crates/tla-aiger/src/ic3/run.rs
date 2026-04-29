// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 main loop: check(), init checks, frame extension, bad-state discovery,
//! state extraction, trace extraction/verification, and public entry points.

use rustc_hash::FxHashMap;

use super::config::{GetBadResult, Ic3Config, Ic3Result, MAX_BAD_CUBE_REPEATS};
use super::engine::Ic3Engine;
use super::propagate::{ConvergenceProof, PropagateOutcome};
use crate::sat_types::{Lit, SatResult, Var};
use crate::transys::Transys;

use super::obligation::ProofObligation;

impl Ic3Engine {
    /// Run the IC3 algorithm.
    pub fn check(&mut self) -> Ic3Result {
        let clause_to_latch_ratio = if self.ts.latch_vars.is_empty() {
            0.0
        } else {
            self.ts.trans_clauses.len() as f64 / self.ts.latch_vars.len() as f64
        };
        let verify_interval = super::config::consecution_verify_interval_full(
            self.ts.trans_clauses.len(),
            self.ts.constraint_lits.len(),
            self.ts.latch_vars.len(),
        );
        let constraint_ratio = if self.ts.latch_vars.is_empty() {
            0.0
        } else {
            self.ts.constraint_lits.len() as f64 / self.ts.latch_vars.len() as f64
        };
        eprintln!(
            "IC3: {} latches, {} inputs, {} constraints, {} init_clauses, {} trans_clauses, {} bad \
             (trans/latch: {:.1}x, constraint/latch: {:.1}x, consec_verify: {}, crosscheck_disabled: {}, predprop: {})",
            self.ts.latch_vars.len(),
            self.ts.input_vars.len(),
            self.ts.constraint_lits.len(),
            self.ts.init_clauses.len(),
            self.ts.trans_clauses.len(),
            self.ts.bad_lits.len(),
            clause_to_latch_ratio,
            constraint_ratio,
            verify_interval,
            self.crosscheck_disabled,
            self.predprop_solver.is_some(),
        );

        // Handle degenerate cases: no bad properties, or all bad lits are constant FALSE.
        if self.ts.bad_lits.is_empty() {
            return Ic3Result::Safe {
                depth: 0,
                lemmas: Vec::new(),
            };
        }
        if self.ts.bad_lits.iter().all(|&l| l == Lit::FALSE) {
            return Ic3Result::Safe {
                depth: 0,
                lemmas: Vec::new(),
            };
        }

        // Step 1: Check if Init => !Bad.
        if self.init_implies_bad() {
            return Ic3Result::Unsafe {
                depth: 0,
                trace: vec![self.init_state()],
            };
        }

        let rebuild_threshold = self.rebuild_threshold();

        // Cross-depth repeated bad cube detection (#4139): track how many times
        // each bad cube is returned by get_bad() across ALL depths. This catches
        // infinite loops where drop_po silently discards proof obligations without
        // blocking the bad state, causing get_bad() to rediscover the same cube
        // at every depth level. The per-depth tracking alone is insufficient
        // because IC3 advances through thousands of depths, hitting the per-depth
        // limit at each one.
        let mut global_seen_bad_cubes: FxHashMap<Vec<Lit>, usize> = FxHashMap::default();
        // Dynamic cross-depth and per-depth repeated bad cube limits (#4105).
        // High-constraint circuits (constraint/latch > 3.0) need many more IC3
        // iterations at each depth to accumulate enough frame-0 lemmas for
        // consecution at frame 1 to return UNSAT. The old fixed limits (global=20,
        // per-depth=10) caused premature Unknown on UNSAT benchmarks like microban_1
        // (ratio 5.4x). Scale both limits with constraint ratio; low-constraint
        // circuits keep the original limits.
        let (max_bad_cube_repeats, global_bad_cube_limit) = if constraint_ratio > 3.0 {
            let per_depth = ((MAX_BAD_CUBE_REPEATS as f64) * constraint_ratio) as usize;
            let per_depth = per_depth.max(MAX_BAD_CUBE_REPEATS).min(500);
            let global = (20.0 * constraint_ratio * constraint_ratio) as usize;
            let global = global.min(5000);
            (per_depth, global)
        } else {
            (MAX_BAD_CUBE_REPEATS, 20)
        };
        if constraint_ratio > 3.0 {
            eprintln!(
                "IC3: dynamic limits: per_depth={} global={} (constraint_ratio={:.1}x)",
                max_bad_cube_repeats, global_bad_cube_limit, constraint_ratio,
            );
        }

        // Maximum convergence validation failures before giving up (#4074).
        // After this many failed validation attempts, IC3 returns Unknown.
        // Each failure purges all frame lemmas and re-derives from scratch.
        // Setting this > 1 gives the SAT backend a chance to produce sound
        // results on a different query pattern after the purge.
        const MAX_CONVERGENCE_FAILURES: usize = 3;
        let mut convergence_failures = 0usize;

        // Main IC3 loop.
        loop {
            if self.is_cancelled() {
                self.log_domain_stats();
                return Ic3Result::Unknown {
                    reason: "cancelled".into(),
                };
            }

            self.extend();
            let depth = self.frames.depth();
            let lemma_counts: Vec<usize> =
                self.frames.frames.iter().map(|f| f.lemmas.len()).collect();
            let total_lemmas: usize = lemma_counts.iter().sum();
            eprintln!(
                "IC3 depth={depth} lemmas={lemma_counts:?} total={total_lemmas} inf={}",
                self.inf_lemmas.len()
            );

            // Blocking phase.
            // Blocking budget (#4072): on arithmetic circuits with many latches,
            // the blocking phase may never terminate because the number of distinct
            // bad cubes is exponential. The budget forces advancement to the next
            // depth level, where additional frame lemmas may enable convergence.
            let blocking_budget = self.config.blocking_budget;
            let mut blocked_count = 0usize;
            // Repeated bad cube detection (#4139): track how many times each
            // bad cube is returned by get_bad(). When drop_po silently discards
            // a proof obligation without blocking the bad state, get_bad()
            // rediscovers the same cube, creating an infinite loop. If any cube
            // is seen more than MAX_BAD_CUBE_REPEATS times, advance to the next
            // depth instead of looping forever.
            let mut seen_bad_cubes: FxHashMap<Vec<Lit>, usize> = FxHashMap::default();
            // #4310 → #4317 soundness gate: track whether this blocking phase
            // exited because F_top ∧ bad is UNSAT (get_bad() returned None).
            // Only the `None => break` arm constructs a `ConvergenceProof`.
            // Early-out paths (blocking_budget, #4139 repeated cube, drop_po,
            // cancellation) leave this `None`. propagate()'s trivially-safe
            // convergence shortcut (#4247) is sound only when the witness is
            // `Some(..)`, and since `ConvergenceProof::from_natural_exit` is
            // the sole constructor, the type system now prevents other break
            // paths from enabling the shortcut.
            let mut blocking_witness: Option<ConvergenceProof> = None;
            loop {
                if self.is_cancelled() {
                    self.log_domain_stats();
                    return Ic3Result::Unknown {
                        reason: "cancelled".into(),
                    };
                }
                // Budget check: stop blocking at this depth and advance.
                if blocking_budget > 0 && blocked_count >= blocking_budget {
                    eprintln!(
                        "IC3 depth={depth} blocking_budget={blocking_budget} exhausted after {blocked_count} bad cubes — advancing"
                    );
                    break;
                }
                match self.get_bad() {
                    Some(GetBadResult::Bad(cube)) => {
                        // Per-depth repeated bad cube check (#4139).
                        let repeat_count = seen_bad_cubes.entry(cube.clone()).or_insert(0);
                        *repeat_count += 1;
                        if *repeat_count > max_bad_cube_repeats {
                            eprintln!(
                                "IC3 depth={depth} bad cube repeated {} times (cube_len={}) — \
                                 advancing to next depth (#4139)",
                                *repeat_count,
                                cube.len(),
                            );
                            break;
                        }
                        // Cross-depth repeated bad cube check (#4139).
                        let global_count = global_seen_bad_cubes.entry(cube.clone()).or_insert(0);
                        *global_count += 1;
                        if *global_count > global_bad_cube_limit {
                            eprintln!(
                                "IC3 bad cube seen {} times across all depths (cube_len={}) — \
                                 returning Unknown (#4139)",
                                *global_count,
                                cube.len(),
                            );
                            self.log_domain_stats();
                            return Ic3Result::Unknown {
                                reason: "repeated bad cube across depths (#4139)".into(),
                            };
                        }
                        // Standard forward check: bad state at top frame.
                        blocked_count += 1;
                        self.obligations
                            .push(ProofObligation::new(depth, cube, 0, None));
                        match self.block_all() {
                            Ok(()) => {}
                            Err(result) => {
                                self.log_domain_stats();
                                return result;
                            }
                        }
                    }
                    Some(GetBadResult::Predecessor(cube)) => {
                        // Predprop backward analysis: predecessor of bad (#4065).
                        // This state is NOT bad itself but transitions to bad.
                        //
                        // If the predecessor is consistent with Init, we have a
                        // real depth-1 counterexample: Init can reach a bad state
                        // in one step.
                        //
                        // SOUNDNESS FIX (#4104): Use precise SAT-based check, not
                        // the fast over-approximation. The fast check only considers
                        // unit init clauses. For circuits with non-unit init clauses
                        // (binary equivalence from non-standard latch resets), the
                        // fast check would incorrectly report the cube as init-
                        // consistent, causing a false Unsafe verdict.
                        if self.cube_sat_consistent_with_init(&cube) {
                            // Build a 2-state trace: [init_predecessor, bad_successor].
                            // The predecessor is in Init and transitions to a bad state.
                            // We need to simulate one step to get the bad successor for
                            // the witness verifier (#4101).
                            if let Some(successor) = self.simulate_one_step(&cube) {
                                let pred_state: Vec<(Var, bool)> =
                                    cube.iter().map(|l| (l.var(), l.is_positive())).collect();
                                self.log_domain_stats();
                                return Ic3Result::Unsafe {
                                    depth: 1,
                                    trace: vec![pred_state, successor],
                                };
                            }
                            // Simulation failed (spurious): fall through to normal flow.
                        }
                        // Non-init predecessor: process through normal IC3 flow.
                        // The cube is a predecessor of bad that is not reachable
                        // from Init in one step, so it needs the full block/
                        // generalize treatment.
                        // Per-depth repeated predecessor cube check (#4139).
                        let repeat_count = seen_bad_cubes.entry(cube.clone()).or_insert(0);
                        *repeat_count += 1;
                        if *repeat_count > max_bad_cube_repeats {
                            eprintln!(
                                "IC3 depth={depth} predecessor cube repeated {} times (cube_len={}) — \
                                 advancing to next depth (#4139)",
                                *repeat_count,
                                cube.len(),
                            );
                            break;
                        }
                        // Cross-depth repeated predecessor check (#4139).
                        let global_count = global_seen_bad_cubes.entry(cube.clone()).or_insert(0);
                        *global_count += 1;
                        if *global_count > global_bad_cube_limit {
                            eprintln!(
                                "IC3 predecessor cube seen {} times across all depths (cube_len={}) — \
                                 returning Unknown (#4139)",
                                *global_count,
                                cube.len(),
                            );
                            self.log_domain_stats();
                            return Ic3Result::Unknown {
                                reason: "repeated predecessor cube across depths (#4139)".into(),
                            };
                        }
                        blocked_count += 1;
                        self.obligations
                            .push(ProofObligation::new(depth, cube, 0, None));
                        match self.block_all() {
                            Ok(()) => {}
                            Err(result) => {
                                self.log_domain_stats();
                                return result;
                            }
                        }
                    }
                    None => {
                        // Natural exit: F_top ∧ bad is UNSAT at this depth.
                        // This is the ONLY path that mints a
                        // `ConvergenceProof`, which is the soundness witness
                        // required to enable propagate()'s #4247
                        // trivially-safe convergence shortcut (#4310, #4317).
                        blocking_witness = Some(ConvergenceProof::from_natural_exit());
                        break;
                    }
                }
            }
            eprintln!(
                "IC3 depth={depth} blocked={blocked_count} natural_exit={}",
                blocking_witness.is_some()
            );

            // Periodic solver rebuild to clear accumulated internal state.
            // Track cumulative blocked count (each blocked cube triggers multiple
            // SAT calls via MIC). Use adaptive threshold based on circuit size.
            self.solve_count = self.solve_count.saturating_add(blocked_count);
            if self.solve_count >= rebuild_threshold {
                self.rebuild_solvers();
            }

            // Propagate lemmas forward.
            // #4310 → #4317: pass the typed `ConvergenceProof` witness (Some
            // iff the blocking loop exited naturally) so propagate()'s #4247
            // trivially-safe convergence shortcut is gated at the type level.
            if matches!(
                self.propagate(blocking_witness),
                PropagateOutcome::Converged
            ) {
                let conv_depth = self.frames.depth();
                eprintln!("IC3 CONVERGED at depth={conv_depth}");
                self.log_domain_stats();
                // Tiered invariant validation (#4106): gate validation by circuit size.
                //
                // rIC3 doesn't validate invariants at all — it trusts the IC3
                // algorithm's incremental per-lemma consecution checks. Our
                // validate_invariant is defense-in-depth, but SimpleSolver creates
                // exponential overhead on circuits with 157+ latches (e.g., qspiflash
                // p130). Tiered approach:
                //
                // - Small circuits (<80 latches): full validation (all 3 checks).
                //   SimpleSolver is fast enough here and catches z4-sat false UNSAT.
                // - Medium circuits (80-200 latches): skip full validation, rely on
                //   per-lemma incremental checks during IC3 main loop. The consecution
                //   cross-check (verify_lemma_consecution) already validates each lemma
                //   as it's learned. Trust the algorithm.
                // - Large circuits (>200 latches): skip validation entirely. These
                //   circuits are far beyond SimpleSolver's capability and even
                //   Z4NoPreprocess validation can timeout, wasting portfolio time.
                //
                // The config's validation_strategy still takes precedence: if it's
                // already set to None or SkipConsecution, those are respected inside
                // validate_invariant_budgeted(). This tier only affects the Auto path.
                let num_latches = self.ts.latch_vars.len();
                let validation_result = if num_latches > 200 {
                    // Large circuit: skip validation entirely, trust incremental checks.
                    eprintln!(
                        "IC3 validate: SKIPPING validation (large circuit: {} latches > 200 threshold, #4106)",
                        num_latches,
                    );
                    Some(true)
                } else if num_latches > 80 {
                    // Medium circuit: skip full validation. Per-lemma incremental
                    // consecution checks during IC3 main loop provide soundness.
                    eprintln!(
                        "IC3 validate: SKIPPING full validation (medium circuit: {} latches, 80-200 range, #4106)",
                        num_latches,
                    );
                    Some(true)
                } else {
                    // Small circuit: full validation with SimpleSolver.
                    self.validate_invariant_budgeted()
                };
                match validation_result {
                    Some(true) => {
                        // Collect all invariant lemmas for portfolio-level validation (#4216).
                        let mut all_lemmas: Vec<Vec<Lit>> = Vec::new();
                        for frame in &self.frames.frames {
                            for lemma in &frame.lemmas {
                                all_lemmas.push(lemma.lits.clone());
                            }
                        }
                        for lemma in &self.inf_lemmas {
                            all_lemmas.push(lemma.lits.clone());
                        }
                        return Ic3Result::Safe {
                            depth: conv_depth,
                            lemmas: all_lemmas,
                        };
                    }
                    Some(false) => {
                        // Invariant validation failed: z4-sat produced false UNSAT
                        // during consecution, creating unsound lemmas that don't
                        // actually hold under the transition relation.
                        //
                        // Recovery strategy (#4074): instead of giving up immediately,
                        // purge ALL frame lemmas (they may be tainted by false UNSAT)
                        // and continue IC3. The algorithm will re-derive lemmas from
                        // scratch. If the SAT backend produces sound results on the
                        // new query pattern, IC3 may converge on a valid invariant.
                        //
                        // This gives each IC3 config a second chance, which is
                        // especially valuable in the portfolio where different configs
                        // exercise different SAT query patterns — the bug may not
                        // reproduce on the re-derivation path.
                        //
                        // After MAX_CONVERGENCE_FAILURES, give up with Unknown to
                        // avoid infinite loops where z4-sat is systematically unsound
                        // on this circuit.
                        convergence_failures += 1;
                        eprintln!(
                            "IC3 SOUNDNESS ERROR: invariant validation FAILED at depth={conv_depth} \
                             (failure {convergence_failures}/{MAX_CONVERGENCE_FAILURES})"
                        );
                        if convergence_failures >= MAX_CONVERGENCE_FAILURES {
                            eprintln!(
                                "IC3: {MAX_CONVERGENCE_FAILURES} convergence failures — \
                                 returning Unknown"
                            );
                            return Ic3Result::Unknown {
                                reason:
                                    "invariant validation failed repeatedly (unsound convergence)"
                                        .into(),
                            };
                        }
                        // Purge all frame lemmas and rebuild solvers.
                        let purged: usize = self.frames.frames.iter().map(|f| f.lemmas.len()).sum();
                        for f in &mut self.frames.frames {
                            f.lemmas.clear();
                        }
                        self.inf_lemmas.clear();
                        self.rebuild_solvers();
                        self.earliest_changed_frame = 1;
                        eprintln!(
                            "IC3: purged {purged} frame lemmas after validation failure, \
                             continuing from depth={conv_depth}"
                        );
                    }
                    None => {
                        // Budget exceeded. Don't return Safe (unvalidated) and don't
                        // return Unknown (may just be slow). Continue IC3 exploration.
                        eprintln!(
                            "IC3 validate: budget exceeded at depth={conv_depth}, continuing IC3..."
                        );
                    }
                }
            }
        }
    }

    /// Check if the initial state satisfies the bad property.
    pub(super) fn init_implies_bad(&self) -> bool {
        let mut solver = self.make_solver();

        // Constrain the constant variable: Var(0) = false.
        solver.add_clause(&[Lit::TRUE]); // Lit::TRUE = neg(Var(0)) = "Var(0) is false"

        for clause in &self.ts.init_clauses {
            solver.add_clause(&clause.lits);
        }
        for clause in &self.ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }
        for &constraint in &self.ts.constraint_lits {
            solver.add_clause(&[constraint]);
        }

        for &bad_lit in &self.ts.bad_lits {
            if solver.solve(&[bad_lit]) == SatResult::Sat {
                return true;
            }
        }
        false
    }

    /// Extract the initial state as a (Var, bool) vector.
    pub(super) fn init_state(&self) -> Vec<(Var, bool)> {
        self.ts
            .latch_vars
            .iter()
            .map(|&var| {
                for clause in &self.ts.init_clauses {
                    if clause.lits.len() == 1 {
                        let lit = clause.lits[0];
                        if lit.var() == var {
                            return (var, lit.is_positive());
                        }
                    }
                }
                (var, false)
            })
            .collect()
    }

    /// Add a new frame level with a fresh SAT solver.
    ///
    /// The new solver starts with ONLY the base formula (Trans + constraints +
    /// next-state linking + infinity lemmas). Per-frame lemmas are NOT pre-loaded.
    ///
    /// In IC3, frames satisfy F_1 >= F_2 >= ... >= F_k (decreasing state sets).
    /// A new frame F_{k+1} starts as the weakest possible (no blocking lemmas).
    /// Lemmas get propagated UP from lower frames by `propagate()`.
    ///
    /// Reference: rIC3 `extend()` clones `inf_solver` which has only Trans +
    /// constraints + infinity lemmas. No per-frame lemmas are pre-loaded.
    ///
    /// ## Solver cloning optimization (#4062)
    ///
    /// Instead of building a new solver from scratch and replaying all transition
    /// relation, constraint, and linking clauses, we clone the infinity solver.
    /// The inf_solver already contains exactly the clauses a new frame needs:
    /// Trans + constraints + next-linking + infinity lemmas. Cloning carries
    /// forward the solver's learned clause database, avoiding redundant work.
    ///
    /// This matches rIC3's approach: `let solver = self.inf_solver.clone()`.
    /// For Z4SatCdclSolver, cloning replays the clause_log into a fresh solver.
    /// For SimpleSolver, it does a direct struct clone. If cloning fails (e.g.,
    /// poisoned solver), we fall back to building from scratch.
    pub(super) fn extend(&mut self) {
        // Clone the infinity solver as a base for the new frame (#4062).
        // clone_or_build_base_solver() handles fallback and cancellation wiring.
        let mut solver = self.clone_or_build_base_solver();

        // CRITICAL (#4074): When creating frame 0, add Init constraints.
        //
        // In IC3, F_0 = Init. Solver[0] must contain Init so that consecution
        // at frame 0 (Init(x) AND Trans(x,x') AND c'(x')) correctly determines
        // whether Init can reach cube c in one step. Without Init, solver[0]
        // only has Trans, so consecution returns SAT for almost any cube,
        // producing init-inconsistent predecessors that get blocked at frame 0
        // but never generate lemmas for frame 1 — causing infinite loops.
        //
        // Reference: rIC3 `ic3/mod.rs:182-199` adds init constraints as
        // frame-0 lemmas when `self.level() == 0`.
        let is_frame_zero = self.solvers.is_empty();
        if is_frame_zero {
            for clause in &self.ts.init_clauses {
                solver.add_clause(&clause.lits);
            }
        }

        self.solvers.push(solver);
        self.frames.push_new();
        // Grow cross-check failure tracker to match the new frame count.
        while self.crosscheck_failures.len() < self.solvers.len() {
            self.crosscheck_failures.push(0);
        }
        // Grow rebuild counter to match the new frame count (#4105).
        while self.rebuild_counts.len() < self.solvers.len() {
            self.rebuild_counts.push(0);
        }

        // Rebuild predprop solver on frame extension (#4101).
        // Mirrors rIC3's `predprop.extend(inf_lemmas)` which reconstructs the
        // backward solver with all infinity lemmas on each frame extension.
        // This keeps the backward analysis synchronized with the current state
        // of IC3's invariant — as new lemmas are proven, the predprop solver
        // gets more constrained, finding fewer (more relevant) predecessors.
        if let Some(ref mut pp) = self.predprop_solver {
            let inf_lemma_clauses: Vec<Vec<Lit>> =
                self.inf_lemmas.iter().map(|l| l.lits.clone()).collect();
            pp.rebuild(&inf_lemma_clauses);
        }
    }

    /// Check if a bad state is reachable from the top frame.
    ///
    /// Returns `GetBadResult::Bad(cube)` for a standard bad state (from F_k AND bad),
    /// or `GetBadResult::Predecessor(cube)` for a backward-analysis predecessor
    /// (from predprop). The caller must handle these differently: bad states get
    /// POs at the current depth, while predecessors may need special routing
    /// (e.g., direct frame-0 PO if init-consistent).
    pub(super) fn get_bad(&mut self) -> Option<GetBadResult> {
        // Predicate propagation path (#4065): backward analysis.
        // Query the predprop solver first — it finds predecessors of bad that
        // the standard forward check might miss when frames are coarse.
        if let Some(ref mut pp) = self.predprop_solver {
            let use_isig = self.config.internal_signals && !self.ts.internal_signals.is_empty();
            if let Some(mut cube) = pp.get_bad_predecessor(use_isig) {
                if self.config.ternary_reduce {
                    cube = self.ternary_sim.ternary_reduce_cube(&cube);
                }
                return Some(GetBadResult::Predecessor(cube));
            }
        }

        // Standard forward path: check F_k AND bad.
        let top = self.solvers.len() - 1;

        // Recover from poisoned top-frame solver before querying (#4040).
        // A poisoned solver returns Unknown for all queries, meaning we'd
        // never find bad states at this frame — silently losing IC3 completeness.
        if self.solvers[top].is_poisoned() {
            self.rebuild_solver_at(top);
        }

        // Domain restriction for bad-state queries (#4306, Phase 2).
        //
        // TL168 wired z4-sat native domain BCP on 3 IC3 hot paths
        // (propagation_blocked, is_inductive, propagate_to_inf) but the
        // forward get_bad() query runs against the top-frame solver with
        // every `Trans ∪ constraints ∪ next-linking` clause active. The
        // bad literal's cone-of-influence is typically a small subset of
        // the total latch set, so restricting BCP and VSIDS branching to
        // that COI gives the same speedup as the other paths. rIC3's
        // GipSAT does this unconditionally; we mirror the pattern here.
        //
        // Soundness: the clause set is unchanged — set_domain only narrows
        // watcher propagation and branching heuristics. Every literal in
        // the bad fanin is in the domain, every reached latch's full COI
        // is in the domain (including next-state vars), and constraint
        // COIs are included.
        //
        // small_circuit_mode (#4259, z4#8802): skip set_domain so z4-sat
        // uses plain BCP on small circuits where active_domain is slower
        // than standard propagation (TL53's workaround for the Tier 1
        // benchmarks while z4#8802 is outstanding).
        let use_domain = !self.config.small_circuit_mode
            && self.ts.latch_vars.len() >= 20
            && !self.ts.bad_lits.is_empty();
        let domain_vars: Vec<Var> = if use_domain {
            let domain = self.domain_computer.compute_bad_domain(
                &self.ts.bad_lits,
                &self.next_vars,
                &self.ts,
            );
            (0..=self.max_var)
                .filter(|&i| domain.contains(Var(i)))
                .map(Var)
                .collect()
        } else {
            Vec::new()
        };

        let solver = &mut self.solvers[top];
        if use_domain && !domain_vars.is_empty() {
            solver.set_domain(&domain_vars);
        }

        let mut found: Option<GetBadResult> = None;
        for &bad_lit in &self.ts.bad_lits {
            if solver.solve(&[bad_lit]) == SatResult::Sat {
                let mut cube =
                    Self::extract_state_from_solver(solver.as_ref(), &self.ts.latch_vars);
                if self.config.internal_signals && !self.ts.internal_signals.is_empty() {
                    let isig_lits =
                        Self::extract_state_from_solver(solver.as_ref(), &self.ts.internal_signals);
                    cube.extend(isig_lits);
                }
                if self.config.ternary_reduce {
                    cube = self.ternary_sim.ternary_reduce_cube(&cube);
                }
                found = Some(GetBadResult::Bad(cube));
                break;
            }
        }

        if use_domain && !domain_vars.is_empty() {
            solver.clear_domain();
        }

        found
    }

    /// Extract a state (cube over latch variables) from a SAT model.
    #[allow(dead_code)]
    pub(super) fn extract_state_from_solver(
        solver: &dyn SatSolver,
        latch_vars: &[Var],
    ) -> Vec<Lit> {
        let mut cube = Vec::new();
        for &latch_var in latch_vars {
            let pos = Lit::pos(latch_var);
            match solver.value(pos) {
                Some(true) => cube.push(pos),
                Some(false) => cube.push(Lit::neg(latch_var)),
                None => {}
            }
        }
        cube
    }

    /// Extract a cube from a solver, including internal signal vars if configured.
    pub(super) fn extract_full_state_from_solver(&self, solver: &dyn SatSolver) -> Vec<Lit> {
        let mut cube = Self::extract_state_from_solver(solver, &self.ts.latch_vars);
        if self.config.internal_signals && !self.ts.internal_signals.is_empty() {
            let isig_lits = Self::extract_state_from_solver(solver, &self.ts.internal_signals);
            cube.extend(isig_lits);
        }
        cube
    }

    /// Map a cube over current-state latch variables to fresh next-state variables.
    pub(super) fn prime_cube(&self, cube: &[Lit]) -> Vec<Lit> {
        let mut assumptions = Vec::new();
        for &lit in cube {
            let var = lit.var();
            if let Some(&next_var) = self.next_vars.get(&var) {
                if lit.is_positive() {
                    assumptions.push(Lit::pos(next_var));
                } else {
                    assumptions.push(Lit::neg(next_var));
                }
            }
        }
        assumptions
    }

    /// Check if a cube is consistent with the initial state.
    ///
    /// Fast path: check individual literals against `init_map` (O(|cube|), no SAT call).
    /// If any literal contradicts a unit init clause, the cube is definitely inconsistent.
    /// This catches the common case without a SAT call.
    ///
    /// For the "maybe consistent" case, the fast path returns true. This is an
    /// over-approximation — the cube might still be inconsistent due to non-unit
    /// init clauses or interactions between variables. The SAT-based check in
    /// `block_one` handles frame-0 counterexample verification precisely.
    pub(super) fn cube_consistent_with_init(&self, cube: &[Lit]) -> bool {
        for &lit in cube {
            if let Some(&init_polarity) = self.init_map.get(&lit.var()) {
                if lit.is_positive() != init_polarity {
                    return false;
                }
            }
        }
        true
    }

    /// Precise SAT-based init consistency check (#4104, #4148).
    ///
    /// Unlike `cube_consistent_with_init()` which only checks unit init clauses
    /// (fast O(|cube|) but over-approximates for non-unit init clauses),
    /// this method uses a SAT solver with ALL init clauses to precisely determine
    /// whether `Init AND cube` is satisfiable.
    ///
    /// When internal signals are enabled (#4148), also loads the AND-gate
    /// definitions (trans_clauses) so that internal signal literals in the cube
    /// are constrained by the combinational logic. Without this, a cube like
    /// `[latch_A=0, isig_G=1]` where `G = AND(A, B)` would falsely appear
    /// init-consistent because `G` is unconstrained by init_clauses alone.
    ///
    /// Returns true if `Init AND cube` is SAT (cube is genuinely in Init).
    /// Returns false if `Init AND cube` is UNSAT (cube is NOT in Init).
    pub(super) fn cube_sat_consistent_with_init(&self, cube: &[Lit]) -> bool {
        // Fast path: if the unit-clause check already says inconsistent, no SAT needed.
        if !self.cube_consistent_with_init(cube) {
            return false;
        }

        // Determine if we need a SAT check:
        // 1. Non-unit init clauses require SAT to check interactions.
        // 2. Internal signals require AND-gate definitions to constrain their values.
        let has_non_unit = self.ts.init_clauses.iter().any(|c| c.lits.len() > 1);
        let has_isig_in_cube =
            self.config.internal_signals && !self.ts.internal_signals.is_empty() && {
                let isig_set: rustc_hash::FxHashSet<Var> =
                    self.ts.internal_signals.iter().copied().collect();
                cube.iter().any(|l| isig_set.contains(&l.var()))
            };

        // If all init clauses are unit AND no internal signals in cube,
        // the fast path is exact — no SAT needed.
        if !has_non_unit && !has_isig_in_cube {
            return true;
        }

        // SAT check: Init AND (optionally Trans) AND cube is satisfiable?
        let mut solver = crate::sat_types::SimpleSolver::new();
        solver.ensure_vars(self.max_var + 1);
        solver.add_clause(&[Lit::TRUE]);
        for clause in &self.ts.init_clauses {
            solver.add_clause(&clause.lits);
        }
        // When internal signals are in the cube, add AND-gate definitions so
        // internal signal values are constrained by the combinational logic.
        if has_isig_in_cube {
            for clause in &self.ts.trans_clauses {
                solver.add_clause(&clause.lits);
            }
        }
        // Add cube literals as unit assumptions.
        solver.solve(cube) == SatResult::Sat
    }

    /// Extract a counterexample trace from the proof obligation chain.
    ///
    /// The PO chain follows .next from frame 0 (init) toward the top frame
    /// (bad state). The trace is returned in forward order: trace[0] = init
    /// state, trace[last] = bad state. This matches the convention expected
    /// by verify_witness and BMC trace format.
    pub(super) fn extract_trace(&self, po: &ProofObligation) -> Vec<Vec<(Var, bool)>> {
        let mut trace = Vec::new();
        let mut current = Some(po);
        while let Some(obligation) = current {
            let state: Vec<(Var, bool)> = obligation
                .cube
                .iter()
                .map(|&lit| (lit.var(), lit.is_positive()))
                .collect();
            trace.push(state);
            current = obligation.next.as_deref();
        }
        // The chain is already in forward order (init -> bad), no reverse needed.
        trace
    }

    /// Verify a counterexample trace using BMC-style unrolling.
    ///
    /// IC3's proof obligations use partial cubes (minimized by lift solver).
    /// Different completions of a partial cube may have different transition
    /// behaviors, so the obligation chain can be spurious even when each
    /// individual step was found SAT by the frame solvers.
    ///
    /// This method verifies the ENTIRE trace at once by unrolling the transition
    /// relation `k` times and checking:
    ///   Init(s_0) AND T(s_0,s_1) AND ... AND T(s_{k-1},s_k) AND Bad(s_k)
    /// where the partial cubes constrain (but don't fully determine) each state.
    ///
    /// Returns true if the trace is genuine (the formula is SAT).
    pub(super) fn verify_trace(&self, po: &ProofObligation) -> bool {
        // Collect the obligation chain (predecessor -> ... -> bad state).
        let mut cubes: Vec<&[Lit]> = Vec::new();
        let mut current = Some(po);
        while let Some(obligation) = current {
            cubes.push(&obligation.cube);
            current = obligation.next.as_deref();
        }
        // cubes[0] = frame-0 predecessor (should be init)
        // cubes[last] = bad state at top frame

        if cubes.is_empty() {
            return true;
        }

        let n_steps = cubes.len();
        let vars_per_step = self.max_var + 1;

        // We need n_steps copies of state variables.
        // Step i uses variables: base + i * vars_per_step + original_var
        // Step 0 uses the original variables (base offset = 0).
        let total_vars = vars_per_step * (n_steps as u32);
        let mut solver = self.make_solver();
        solver.add_clause(&[Lit::TRUE]);

        // Helper: shift a literal to time step `step`.
        // Var(0) is the AIGER constant (always false) — never shifted.
        let shift = |lit: Lit, step: usize| -> Lit {
            if step == 0 || lit.var().0 == 0 {
                return lit;
            }
            let offset = (step as u32) * vars_per_step;
            let new_var = Var(lit.var().0 + offset);
            if lit.is_positive() {
                Lit::pos(new_var)
            } else {
                Lit::neg(new_var)
            }
        };

        // Ensure solver has enough variables.
        let dummy_var = Var(total_vars);
        solver.add_clause(&[Lit::pos(dummy_var), Lit::neg(dummy_var)]);

        // Step 0: Init constraints.
        for clause in &self.ts.init_clauses {
            solver.add_clause(&clause.lits);
        }

        // For each step: transition + constraints + cube partial assignment.
        for step in 0..n_steps {
            // Constraint literals at this step.
            for &constraint in &self.ts.constraint_lits {
                solver.add_clause(&[shift(constraint, step)]);
            }

            // Partial cube assignment at this step (as unit clauses).
            for &lit in cubes[step] {
                solver.add_clause(&[shift(lit, step)]);
            }

            // Transition relation from step to step+1 (except last step).
            if step + 1 < n_steps {
                // Trans clauses (AND gate definitions, etc.) shifted to this step.
                for clause in &self.ts.trans_clauses {
                    let shifted: Vec<Lit> = clause.lits.iter().map(|&l| shift(l, step)).collect();
                    solver.add_clause(&shifted);
                }

                // Next-state linking clauses shifted to this step.
                // These define next_var <-> next_state_expr at this step's variables.
                for clause in &self.next_link_clauses {
                    let shifted: Vec<Lit> = clause.iter().map(|&l| shift(l, step)).collect();
                    solver.add_clause(&shifted);
                }

                // Cross-step link: next_var@step <-> latch_var@(step+1).
                for (&latch_var, &next_var) in &self.next_vars {
                    let nv_step = shift(Lit::pos(next_var), step);
                    let lv_next = shift(Lit::pos(latch_var), step + 1);
                    solver.add_clause(&[!nv_step, lv_next]);
                    solver.add_clause(&[nv_step, !lv_next]);
                }
            }
        }

        // Bad state at the last step.
        let last = n_steps - 1;
        if !self.ts.bad_lits.is_empty() {
            let bad_assumptions: Vec<Lit> =
                self.ts.bad_lits.iter().map(|&l| shift(l, last)).collect();
            solver.add_clause(&bad_assumptions);
        }

        solver.solve(&[]) == SatResult::Sat
    }

    /// Simulate one transition step from a predecessor cube to get the successor state.
    ///
    /// Used by predprop to construct a proper 2-state counterexample trace when
    /// it finds an init-consistent predecessor of bad. The predecessor itself is
    /// NOT bad (predprop enforces !bad(s)), so we need to simulate one step to
    /// find the bad successor state for the witness verifier.
    ///
    /// Encodes: Init AND cube(s) AND Trans(s, s') AND bad(s') and extracts s'.
    /// Returns `None` if the formula is UNSAT (spurious predecessor).
    pub(super) fn simulate_one_step(&self, cube: &[Lit]) -> Option<Vec<(Var, bool)>> {
        let mut solver = self.make_solver();
        solver.add_clause(&[Lit::TRUE]);

        // Init constraints.
        for clause in &self.ts.init_clauses {
            solver.add_clause(&clause.lits);
        }

        // Current-state cube assignment.
        for &lit in cube {
            solver.add_clause(&[lit]);
        }

        // Transition relation.
        for clause in &self.ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }

        // Constraints.
        for &constraint in &self.ts.constraint_lits {
            solver.add_clause(&[constraint]);
        }

        // Next-state linking.
        for clause in &self.next_link_clauses {
            solver.add_clause(clause);
        }

        // Bad on successor state (via next-state variables).
        let bad_assumptions: Vec<Lit> = self
            .ts
            .bad_lits
            .iter()
            .filter_map(|&bad_lit| {
                let var = bad_lit.var();
                if let Some(&next_var) = self.next_vars.get(&var) {
                    Some(if bad_lit.is_positive() {
                        Lit::pos(next_var)
                    } else {
                        Lit::neg(next_var)
                    })
                } else {
                    Some(bad_lit)
                }
            })
            .collect();

        if solver.solve(&bad_assumptions) != SatResult::Sat {
            return None;
        }

        // Extract successor state from next-state variables, mapped back to latch vars.
        let successor: Vec<(Var, bool)> = self
            .ts
            .latch_vars
            .iter()
            .filter_map(|&latch_var| {
                let next_var = self.next_vars.get(&latch_var)?;
                let pos = Lit::pos(*next_var);
                match solver.value(pos) {
                    Some(true) => Some((latch_var, true)),
                    Some(false) => Some((latch_var, false)),
                    None => Some((latch_var, false)), // default to false for unassigned
                }
            })
            .collect();

        Some(successor)
    }
}

use crate::sat_types::SatSolver;

/// Convenience function: check an AIGER circuit using IC3 with the built-in SAT solver.
///
/// Applies full preprocessing (COI reduction + variable compaction) to
/// remove irrelevant variables and compact the variable numbering for
/// better SAT solver cache behavior.
pub fn check_ic3(circuit: &crate::types::AigerCircuit) -> Ic3Result {
    check_ic3_with_config(circuit, Ic3Config::default())
}

/// Check an AIGER circuit with a specific IC3 configuration.
pub fn check_ic3_with_config(circuit: &crate::types::AigerCircuit, config: Ic3Config) -> Ic3Result {
    let (mut ts, stats) = Transys::from_aiger(circuit).preprocess();
    eprintln!("{stats}");
    eprintln!(
        "Post-preprocess: {} constraints, {} bad, {} init_clauses, max_var={}",
        ts.constraint_lits.len(),
        ts.bad_lits.len(),
        ts.init_clauses.len(),
        ts.max_var,
    );

    // Quick BMC pre-check: run BMC for a few steps to catch shallow bugs.
    // IC3's frame-by-frame invariant construction is expensive for bugs
    // reachable in 1-5 steps. BMC finds these instantly. This is standard
    // practice in competitive IC3 solvers (rIC3 runs BMC in the portfolio,
    // ABC does "BMC then IC3").
    //
    // Only do this for circuits with latches (pure combinational circuits
    // are already handled by init_implies_bad in the IC3 engine).
    if !ts.latch_vars.is_empty() && !ts.bad_lits.is_empty() {
        let bmc_depth = 10; // Shallow check only — deep bugs are IC3's strength
        let mut bmc = crate::bmc::BmcEngine::new(ts.clone(), 1);
        let bmc_result = bmc.check(bmc_depth);
        if let crate::check_result::CheckResult::Unsafe { depth, trace } = bmc_result {
            eprintln!("IC3: BMC pre-check found bug at depth {depth}");
            // Convert BMC trace (FxHashMap<String, bool>) to IC3 trace ((Var, bool)).
            let ic3_trace: Vec<Vec<(Var, bool)>> = trace
                .into_iter()
                .map(|state| {
                    state
                        .into_iter()
                        .filter_map(|(name, val)| {
                            // Parse "vN" format back to Var
                            name.strip_prefix('v')
                                .and_then(|s| s.parse::<u32>().ok())
                                .map(|id| (Var(id), val))
                        })
                        .collect()
                })
                .collect();
            // Only use the BMC result if we got a non-trivial trace.
            // Some BMC configurations may return empty traces; in that case
            // fall through to IC3 which produces better traces.
            if !ic3_trace.is_empty() && ic3_trace.iter().all(|s| !s.is_empty()) {
                return Ic3Result::Unsafe {
                    depth,
                    trace: ic3_trace,
                };
            }
        }
    }

    if config.internal_signals {
        ts.select_internal_signals();
    }
    let mut engine = Ic3Engine::with_config(ts, config);
    engine.check()
}

/// Check an AIGER circuit WITHOUT COI reduction (for debugging).
#[cfg(test)]
pub fn check_ic3_no_coi(circuit: &crate::types::AigerCircuit) -> Ic3Result {
    let ts = Transys::from_aiger(circuit);
    let mut engine = Ic3Engine::with_config(ts, Ic3Config::default());
    engine.check()
}
