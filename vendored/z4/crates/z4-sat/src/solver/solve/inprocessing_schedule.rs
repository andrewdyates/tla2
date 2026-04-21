// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing pass scheduling facade.
//!
//! `run_restart_inprocessing` orchestrates the inprocessing pipeline that runs
//! at decision level 0 after restarts. The pass ordering and interleaving
//! logic follows CaDiCaL's probe.cpp / elim.cpp pipeline with Z4-specific
//! tuning.
//!
//! Implementation is split across sibling modules:
//! - `inprocessing_maintenance`: garbage drain and gate checks
//! - `inprocessing_equivalence`: vivify, subsume, probe, congruence, HTR
//! - `inprocessing_elimination`: BVE, factor, BCE, CCE, condition, transred, sweep
//! - `inprocessing_round_end`: invariant checks, telemetry, scheduling

use super::super::*;

impl Solver {
    /// Run inprocessing immediately after a restart.
    ///
    /// Returns `true` if UNSAT was derived at decision level 0.
    #[inline]
    pub(in crate::solver) fn run_restart_inprocessing(&mut self) -> bool {
        // Check interrupt before running any inprocessing (#3638).
        if self.is_interrupted() {
            return false;
        }

        // ── Lightweight maintenance (runs at level 0 after every restart) ──
        // Drain deferred HBR garbage has a fixpoint guard (O(1) when nothing
        // changed) and must run at every level-0 opportunity for correctness:
        // stale pending-garbage marks from probing BCP block watch list
        // integrity (#3971). L0 GC is deferred past the inprocessing gate
        // below to avoid O(clauses) scans on every level-0 restart.
        if self.decision_level == 0 {
            self.drain_all_pending_garbage();
            if self.propagate_check_unsat() {
                return true;
            }
        }

        // ── Inprocessing pass gate (#7135) ────────────────────────────
        if self.num_conflicts == 0 {
            return false;
        }
        if self.num_conflicts < self.cold.next_inprobe_conflict {
            return false;
        }

        // ── Reduction gate (#5130) ───────────────────────────────────
        if self.cold.last_inprobe_reduction > 0
            && self.cold.num_reductions == self.cold.last_inprobe_reduction
        {
            return false;
        }

        // ── Level 0 requirement (#4719) ──────────────────────────────
        if self.decision_level != 0 {
            return false;
        }

        // ── Level-0 garbage collection (deferred past inprocessing gate) ──
        // CaDiCaL runs mark_satisfied_clauses_as_garbage() inside collect()
        // which is called from reduce(), not on every restart. On large
        // formulas (4M+ clauses), the O(clauses) scan of
        // collect_level0_garbage consumed ~19% of search time when called
        // at every level-0 restart opportunity. Deferring it past the
        // inprocessing gate means it only fires when inprocessing passes
        // will actually run.
        if self.collect_level0_garbage() {
            return true;
        }
        if self.propagate_check_unsat() {
            return true;
        }

        // Trail must be fully propagated before inprocessing techniques.
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: unpropagated literals at inprocessing entry (qhead={} trail={})",
            self.qhead,
            self.trail.len(),
        );

        // Reset minimal trail rewind tracker (#8095). Individual inprocessing
        // passes update this when they derive new units or delete reason clauses.
        // rebuild_watches() reads it to set qhead precisely.
        self.earliest_affected_trail_pos = None;

        // ── Per-round overhead tracking (#8099) ──────────────────────────
        // Capture wall-clock start and per-pass timing baseline so we can
        // compute infrastructure overhead = total_round_time - sum(pass_times).
        let round_start = std::time::Instant::now();
        let pass_time_baseline: [u64; solver_stats::INPROCESS_TIMING_LABELS.len()] =
            self.stats.inprocessing_time_ns;

        // ── JIT caching: defer invalidation to structural passes (#8128) ──
        // Instead of blanket-invalidating the compiled formula before ALL
        // inprocessing, we snapshot the current state and lazily invalidate
        // only when a structural pass runs (one that modifies clause literals
        // or structure). Deletion-only passes (BCE, CCE, condition, transred,
        // probe, congruence, backbone, reorder) are handled by guard bits in
        // the compiled code and do not require recompilation.
        let had_compiled_formula = self.has_compiled_formula();

        // ── Pass scheduling section ───────────────────────────────────
        // CaDiCaL probe.cpp:933-952 inprobe ordering:
        //   decompose → ternary → decompose → probe → decompose →
        //   extract_gates → decompose → backbone → sweep → decompose →
        //   vivify → transred → backbone → factor
        // Z4 currently keeps BVE/subsume/BCE/factor/transred/sweep in the
        // separate elimination pipeline and runs the assumption-based backbone
        // pass once after that block, immediately before vivification.
        let skip_gate_dependent_passes = self.is_uniform_nonbinary_irredundant_formula();
        // Use active (live) clause count for inprocessing gates. arena.num_clauses()
        // is cumulative (includes deleted), causing false skips on formulas like
        // FmlaEquivChain (4.7M parsed → 362K active after preprocessing, but
        // num_clauses() still reports ~4.7M). CaDiCaL gates on stats.current.irredundant
        // + stats.current.redundant which excludes deleted clauses.
        let active_clauses = self.arena.active_clause_count();
        let skip_expensive_equivalence_passes = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            || active_clauses > PREPROCESS_EXPENSIVE_MAX_CLAUSES;
        // Congruence + decompose share a clause threshold (CONGRUENCE_MAX_CLAUSES = 3M).
        let skip_congruence_inproc = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            || active_clauses > CONGRUENCE_MAX_CLAUSES;
        // CaDiCaL probe.cpp:936: clean duplicate binaries at inprobe start.
        // Techniques that produce binary clauses (decompose, probe HBR,
        // congruence, factor) can create duplicates between inprocessing rounds.
        if self.inproc_ctrl.decompose.enabled && self.deduplicate_binary_clauses() {
            return true;
        }

        // Capture clause count and BCP telemetry baselines for per-round diagnostic.
        let clauses_before = self.num_clauses();
        let bcp_blocker_before = self.stats.bcp_blocker_fastpath_hits;
        let bcp_binary_before = self.stats.bcp_binary_path_hits;
        let bcp_scan_before = self.stats.bcp_replacement_scan_steps;
        let preproc_lits_before = self.stats.preprocess_level0_literals_removed;
        let preproc_sat_before = self.stats.preprocess_level0_satisfied_deleted;

        // Track actually-executed passes for diagnostic telemetry (#4781).
        let mut passes_run: Vec<&'static str> = Vec::new();

        // Kissat reorder.c: clause-weighted variable reorder.
        // Non-destructive (no clause modifications), runs before clause-modifying
        // passes. In focused mode, rebuilds VMTF queue by importance. In stable
        // mode, folds clause weights into EVSIDS scores. Lightweight: O(vars +
        // irredundant_clauses). Uses growing backoff like other inprocessing passes.
        if self.should_reorder() {
            self.run_timed_diagnostic_inprocessing_pass(
                DiagnosticPass::Reorder,
                Self::reorder_variables,
            );
            passes_run.push("reorder");
            self.inproc_ctrl.reorder.reschedule_growing(
                self.num_conflicts,
                REORDER_INTERVAL,
                3,
                2,
                REORDER_MAX_INTERVAL,
            );
        }
        // BISECT: validate after reorder
        #[cfg(debug_assertions)]
        self.validate_watch_invariants();

        // CaDiCaL probe.cpp:920-921: decompose at inprobe start.
        // Normalizes the binary implication graph (SCC + variable substitution)
        // before any analysis. Gated by should_decompose() so the growing
        // backoff schedule (#7480 D3) controls frequency: unproductive calls
        // grow the interval 1.5×, productive calls reset to base.
        // On large residuals (>3M clauses), decompose's clause substitution
        // pass is O(total_literals) which is expensive (#7135).
        if self.should_decompose() && !skip_congruence_inproc {
            self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Decompose, Self::decompose);
            passes_run.push("decompose");
            if self.propagate_check_unsat() {
                return true;
            }
        }
        // BISECT: validate after decompose-1
        #[cfg(debug_assertions)]
        self.validate_watch_invariants();

        // HTR (hyper-ternary resolution): resolve ternary clause pairs to derive
        // binary and ternary resolvents. CaDiCaL runs ternary() BEFORE probe()
        // (probe.cpp:938-939) so that HTR-derived binary clauses enrich the
        // implication graph for failed literal probing and SCC decomposition.
        // HTR's rebuild() scan is O(clauses) — same order as decompose's SCC
        // traversal and congruence's gate scan. Uses the congruence threshold
        // (5M) rather than the expensive-pass threshold (3M) so HTR runs on
        // formulas like FmlaEquivChain (4.7M clauses) where HTR-derived
        // binaries are critical for probe and decompose effectiveness (#7279).
        if self.should_htr() && !skip_congruence_inproc {
            self.jit_invalidate_for_structural_pass(); // HTR: structural (#8128)
            let produced_binary =
                self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::HTR, Self::htr);
            passes_run.push("htr");
            if self.propagate_check_unsat() {
                return true;
            }

            // CaDiCaL probe.cpp:939: re-runs decompose when ternary produces
            // binary resolvents (new implication graph edges may reveal new SCCs).
            // Gated by should_decompose() to respect growing backoff (#7480 D3).
            if produced_binary && self.should_decompose() {
                self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
                self.run_timed_diagnostic_inprocessing_pass(
                    DiagnosticPass::Decompose,
                    Self::decompose,
                );
                passes_run.push("decompose");
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        } else if self.should_htr() && skip_congruence_inproc {
            self.inproc_ctrl
                .htr
                .reschedule(self.num_conflicts, HTR_INTERVAL);
        }
        // BISECT: validate after htr
        #[cfg(debug_assertions)]
        self.validate_watch_invariants();

        if self.is_interrupted() {
            return false;
        }

        if self.should_subsume() {
            self.jit_invalidate_for_structural_pass(); // subsume: structural (#8128)
            self.set_diagnostic_pass(DiagnosticPass::Subsume);
            self.subsume();
            self.clear_diagnostic_pass();
            passes_run.push("subsume");
            // Subsumption can strengthen clauses into units. These units are
            // not watched, so we must propagate here.
            if self.propagate_check_unsat() {
                return true;
            }
        }

        // BISECT: targeted validation after subsume
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after subsume");

        if self.is_interrupted() {
            return false;
        }

        if self.should_probe() {
            let failed_before = self.inproc.prober.stats().failed;
            self.set_diagnostic_pass(DiagnosticPass::Probe);
            // Probing returns true only on proven UNSAT (level-0 conflict).
            if self.probe() {
                self.clear_diagnostic_pass();
                return true;
            }
            self.clear_diagnostic_pass();
            passes_run.push("probe");
            // Drain deferred HBR subsumption deletions created during probing (#4761).
            // Probing BCP marks subsumed clauses as pending_garbage, and the lazy
            // watch removal during subsequent search_propagate leaves those clauses
            // without watches. Drain them now before further inprocessing.
            self.drain_all_pending_garbage();
            let probe_found_failed = self.inproc.prober.stats().failed > failed_before;
            if probe_found_failed {
                // Post-probe: probing_mode already cleared — search variant.
                // Re-propagate any units derived from failed literals.
                if let Some(conflict_ref) = self.search_propagate() {
                    self.record_level0_conflict_chain(conflict_ref);
                    return true;
                }
            }

            // CaDiCaL re-runs decompose after probing (probe.cpp:940-941).
            // Failed literal units produce new binary implications for SCC.
            // Gated by should_decompose() to respect growing backoff (#7480 D3).
            if probe_found_failed && self.should_decompose() {
                self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
                self.set_diagnostic_pass(DiagnosticPass::Decompose);
                self.decompose();
                self.clear_diagnostic_pass();
                passes_run.push("decompose");
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        }
        // BISECT: targeted validation after probe
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after probe");

        // Congruence closure: detect equivalent variables via gate structure.
        // Runs before decompose so that gate equivalences feed into SCC.
        // CaDiCaL: `if (extract_gates(true)) decompose();` — congruence only
        // adds binary equivalence clauses; decompose handles all clause rewriting.
        // Guard: congruence REQUIRES decompose to consume its equivalences.
        // Without decompose, congruence binary clauses remain unsubstituted
        // and BVE may eliminate variables with active equivalence binaries,
        // causing reconstruction to produce invalid models (#5752, #5937).
        // Regression timeline: b5f8a5234 removed this guard → FlatZinc accap
        // returned false UNSAT; 3e7738b95 restored it.
        let mut congruence_found_equivalences = false;
        if self.inproc_ctrl.gate.enabled
            && self.should_congruence()
            && self.inproc_ctrl.decompose.enabled
            && !skip_gate_dependent_passes
            && !skip_congruence_inproc
        {
            // congruence: deletion-only (only adds binary clauses, no structural modification)
            self.set_diagnostic_pass(DiagnosticPass::Congruence);
            congruence_found_equivalences = self.congruence();
            self.clear_diagnostic_pass();
            passes_run.push("congruence");
            if self.propagate_check_unsat() {
                return true;
            }
        } else if self.should_congruence()
            && (skip_gate_dependent_passes
                || skip_congruence_inproc
                || !self.inproc_ctrl.decompose.enabled
                || !self.inproc_ctrl.gate.enabled)
        {
            // Skipped: use growing backoff so we don't re-check quickly (#7135).
            self.inproc_ctrl.congruence.reschedule_growing(
                self.num_conflicts,
                CONGRUENCE_INTERVAL,
                2,
                1,
                CONGRUENCE_MAX_INTERVAL,
            );
        }

        // Decompose: SCC-based equivalent literal substitution.
        // CaDiCaL pattern (internal.cpp:767): `if (extract_gates(true)) decompose();`
        // When congruence found equivalences AND decompose is enabled, decompose
        // runs to rewrite all clauses using the binary equivalences. Without this,
        // reason-protected clauses retain pre-substitution literals (#5237).
        // Decompose is now enabled in LRAT mode with probe-based hints (#4606).
        if !skip_congruence_inproc
            && (self.should_decompose()
                || (congruence_found_equivalences && self.inproc_ctrl.decompose.enabled))
        {
            self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
            self.set_diagnostic_pass(DiagnosticPass::Decompose);
            self.decompose();
            self.clear_diagnostic_pass();
            passes_run.push("decompose");
            if self.propagate_check_unsat() {
                return true;
            }
        }

        // BISECT: targeted validation after congruence + decompose-2
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after congruence+decompose-2");

        if self.is_interrupted() {
            return false;
        }

        // Elimination back-half: BVE interleaved with subsumption/BCE,
        // factor, standalone BCE/CCE, condition, transred, sweep + decompose,
        // compact.
        if self.run_elimination_passes(
            &mut passes_run,
            skip_gate_dependent_passes,
            skip_expensive_equivalence_passes,
        ) {
            return true;
        }
        // BISECT: targeted validation after elimination
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after elimination");

        // Backbone computation: identify literals fixed in every model.
        // Initial implementation uses bounded assumption-based probing, so run
        // it after the elimination block has simplified the formula and before
        // vivification strengthens clauses against the updated root assignment.
        // CaDiCaL enforces a round limit: `backbonemaxrounds = 1000` (options.hpp:30).
        // Skip backbone entirely once the phase count exceeds this limit.
        if self.should_backbone()
            && !skip_expensive_equivalence_passes
            && self.cold.backbone_phases < BACKBONE_MAX_ROUNDS
        {
            let bb_found = self
                .run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Backbone, Self::backbone);
            passes_run.push("backbone");
            if bb_found {
                self.inproc_ctrl
                    .backbone
                    .reschedule(self.num_conflicts, BACKBONE_INTERVAL);
                if self.has_empty_clause {
                    return true;
                }
                if self.propagate_check_unsat() {
                    return true;
                }
            } else {
                // CaDiCaL runs backbone every inprobe without growing backoff,
                // using tick-based effort limits instead. Use gentle 1.5x growth
                // (3/2) so backbone fires frequently enough to catch new backbone
                // literals revealed by BVE/subsumption/vivification.
                self.inproc_ctrl.backbone.reschedule_growing(
                    self.num_conflicts,
                    BACKBONE_INTERVAL,
                    3,
                    2,
                    BACKBONE_MAX_INTERVAL,
                );
            }
        } else if self.should_backbone() && skip_expensive_equivalence_passes {
            self.inproc_ctrl.backbone.reschedule_growing(
                self.num_conflicts,
                BACKBONE_INTERVAL,
                3,
                2,
                BACKBONE_MAX_INTERVAL,
            );
        }

        // BISECT: targeted validation after backbone
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after backbone");

        // CaDiCaL probe.cpp:949: vivify runs after sweep (resets watches).
        // Vivify strengthens clauses by re-propagating their literals.
        // Running after sweep means sweep equivalences are substituted first,
        // giving vivify a cleaner formula to work with.
        if self.should_vivify() {
            self.jit_invalidate_for_structural_pass(); // vivify: structural (#8128)
            if self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Vivify, Self::vivify) {
                return true;
            }
            passes_run.push("vivify");

            // Post-vivification subsumption (#7393): vivification marks
            // strengthened/deleted clause variables dirty. A follow-up
            // subsumption pass can exploit shorter clauses from vivification
            // to subsume other clauses. CaDiCaL achieves this via mark_added
            // in vivify_strengthen and new_clause_as, then the next subsume
            // round picks up the dirty variables.
            if false && self.inproc_ctrl.subsume.enabled { // TEMPORARY: disable post-vivify subsume
                self.set_diagnostic_pass(DiagnosticPass::Subsume);
                self.subsume();
                self.clear_diagnostic_pass();
                passes_run.push("subsume");
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        }

        // NOTE: CaDiCaL runs backbone twice per inprobe (probe.cpp:945,951).
        // Z4's CDCL-based backbone is more expensive than CaDiCaL's binary-clause
        // backbone. A second pass was tested but added 2+ seconds of overhead
        // without proportional search speedup on FmlaEquivChain. Deferred until
        // Z4 implements CaDiCaL's lightweight binary-clause backbone.

        // Postcondition: inprocessing must leave the solver at level 0
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: run_restart_inprocessing exiting at decision level {}",
            self.decision_level,
        );
        // Trail must be fully propagated after inprocessing
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: unpropagated literals after inprocessing (qhead={} trail={})",
            self.qhead,
            self.trail.len(),
        );

        #[cfg(debug_assertions)]
        self.validate_watch_invariants();

        // #5012 Family A: reason clause protection invariant.
        // Every trail reason must reference a live clause containing the variable.
        // CaDiCaL equivalent: elim.cpp:440 post-condition.
        #[cfg(debug_assertions)]
        self.validate_reason_clause_integrity();

        // #5012 Family B: proof system coherence invariant.
        // Forward checker and solver clause DB must agree on live set.
        // CaDiCaL equivalent: checker.cpp aggregate consistency checks.
        #[cfg(debug_assertions)]
        self.validate_proof_coherence();

        // #5012 Family C: reconstruction stack coherence invariant.
        // Every witness literal must appear in its clause.
        // CaDiCaL equivalent: external.cpp:208-230 validity check.
        #[cfg(debug_assertions)]
        self.validate_reconstruction_stack();

        // Always-on release-mode soundness guards (#4994):

        // Fix 1: Proof I/O error check. ProofOutput::has_io_error() exists in
        // release builds (bool field on DRAT/LRAT writer). Catches truncated or
        // corrupted proofs from disk-full or broken-pipe mid-solve. O(1) cost.
        if let Some(ref manager) = self.proof_manager {
            assert!(
                !manager.has_io_error(),
                "BUG: proof I/O error detected at inprocessing boundary"
            );
        }

        // Fix 2: Pending-garbage drain check. pending_garbage_count is a u32
        // on Solver (not cfg(debug_assertions)). Non-zero at inprocessing exit
        // means BCP will encounter stale clauses — a reliability bug. O(1) cost.
        assert_eq!(
            self.pending_garbage_count, 0,
            "BUG [Family A]: {} pending-garbage clauses at inprocessing exit",
            self.pending_garbage_count,
        );

        // ── Per-round overhead computation (#8099) ────────────────────────
        // Infrastructure overhead = total round wall time - sum of individual
        // pass times recorded by run_timed_diagnostic_inprocessing_pass.
        let round_elapsed_ns = round_start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        let pass_time_delta_ns: u64 = self
            .stats
            .inprocessing_time_ns
            .iter()
            .zip(pass_time_baseline.iter())
            .map(|(now, before)| now.saturating_sub(*before))
            .sum();
        let overhead_ns = round_elapsed_ns.saturating_sub(pass_time_delta_ns);
        self.cold.last_inprocessing_overhead_ms = overhead_ns as f64 / 1_000_000.0;

        // Update per-round stats (#8099).
        self.stats.inprocessing_rounds += 1;
        let clauses_after = self.num_clauses();
        let round_simplifications = clauses_before.saturating_sub(clauses_after) as u64
            + self
                .stats
                .preprocess_level0_literals_removed
                .saturating_sub(preproc_lits_before)
            + self
                .stats
                .preprocess_level0_satisfied_deleted
                .saturating_sub(preproc_sat_before);
        self.stats.inprocessing_simplifications = self
            .stats
            .inprocessing_simplifications
            .saturating_add(round_simplifications);

        tracing::debug!(
            num_clauses = clauses_after,
            num_vars = self.num_vars,
            trail_len = self.trail.len(),
            overhead_ms = format_args!("{:.2}", self.cold.last_inprocessing_overhead_ms),
            round = self.stats.inprocessing_rounds,
            simplifications = round_simplifications,
            "inprocessing: round complete"
        );

        // Emit per-round diagnostic summary (#4674, #4781).
        // Uses passes_run (actually executed) instead of collect_enabled_passes().
        let telemetry = crate::diagnostic_trace::InprocessingRoundTelemetry {
            bcp_blocker_fastpath_hits: self
                .stats
                .bcp_blocker_fastpath_hits
                .saturating_sub(bcp_blocker_before),
            bcp_binary_path_hits: self
                .stats
                .bcp_binary_path_hits
                .saturating_sub(bcp_binary_before),
            bcp_replacement_scan_steps: self
                .stats
                .bcp_replacement_scan_steps
                .saturating_sub(bcp_scan_before),
            preprocess_level0_literals_removed: self
                .stats
                .preprocess_level0_literals_removed
                .saturating_sub(preproc_lits_before),
            preprocess_level0_satisfied_deleted: self
                .stats
                .preprocess_level0_satisfied_deleted
                .saturating_sub(preproc_sat_before),
        };
        self.emit_diagnostic_inprocessing_round(
            clauses_before,
            clauses_after,
            &passes_run,
            &telemetry,
        );

        // CaDiCaL probe.cpp:987: last.inprobe.reductions = stats.reductions
        self.cold.last_inprobe_reduction = self.cold.num_reductions;

        // CaDiCaL probe.cpp:979-981: update inprobe conflict limit.
        // delta = 25 * inprobeint * log10(phases + 9)
        // With INPROBE_INTERVAL=100: phase 0 → delta=2385, phase 91 → delta=5000.
        // This logarithmic growth naturally widens the inprobe interval as
        // search progresses, reducing per-round overhead on large residuals (#7135).
        //
        // On large residuals (>3M clauses), the O(clauses) setup cost of even
        // lightweight passes (watch sorting, candidate building, occurrence
        // lists) dominates per-round time. Scale the interval by
        // log10(clauses/1M) to reduce round frequency proportionally (#7135).
        self.cold.inprobe_phases += 1;
        let log_factor = ((self.cold.inprobe_phases + 9) as f64).log10();
        let base_delta = (25.0 * INPROBE_INTERVAL as f64 * log_factor) as u64;
        // Scale interval on large formulas using sqrt of (clauses / 1M).
        // Linear scaling (from #7135) was too aggressive: 4.7M clauses → 4.7x,
        // throttling beneficial subsumption/BVE on FmlaEquivChain (#7279).
        // sqrt scaling: 3M → 1.7x, 5M → 2.2x, 10M → 3.2x. This still
        // compensates for O(clauses) setup cost while allowing more frequent
        // inprocessing than the linear version.
        let active_count = self.arena.active_clause_count();
        let clause_scale = if active_count > PREPROCESS_EXPENSIVE_MAX_CLAUSES {
            (active_count as f64 / 1_000_000.0).sqrt().max(1.0)
        } else {
            1.0
        };
        let delta = (base_delta as f64 * clause_scale) as u64;
        let delta = delta.max(INPROBE_INTERVAL);
        self.cold.next_inprobe_conflict = self.num_conflicts.saturating_add(delta);

        // CaDiCaL reduce.cpp:250: use dynamic irredundant count for reduce
        // interval scaling. O(1) via incremental counter (#7476).
        self.num_original_clauses = self.arena.irredundant_count();
        debug_assert_eq!(
            self.num_original_clauses,
            self.arena
                .active_indices()
                .filter(|&idx| !self.arena.is_learned(idx))
                .count(),
            "BUG: irredundant_count drift (#7476)"
        );

        // Invalidate the uniform formula cache after any inprocessing round
        // that ran passes (#7905). Passes like BVE, subsumption, vivification,
        // decompose, and factorization can add/delete/strengthen irredundant
        // clauses, changing the uniform formula property.
        if !passes_run.is_empty() {
            self.invalidate_uniform_formula_cache();
        }

        // ── JIT recompilation: conditional rebuild after inprocessing (#8128) ──
        // If no structural pass ran (only deletion-only passes like BCE, CCE,
        // condition, transred, probe, congruence, backbone, reorder), the
        // compiled formula remains valid — guard bits handle clause deletion.
        // Skip recompilation to save 1-5ms per round.
        {
            let needs_recompile = had_compiled_formula && !self.has_compiled_formula();
            let deletion_only_round = had_compiled_formula && self.has_compiled_formula();

            if deletion_only_round && !passes_run.is_empty() {
                // Deletion-only round: compiled formula still valid, skip recompile.
                self.stats.jit_recompilations_skipped += 1;
                tracing::debug!(
                    passes = ?passes_run,
                    "jit: skipped recompilation (deletion-only round, guard bits handle deletion)"
                );
            } else if needs_recompile {
                // Structural pass invalidated the formula: full recompile needed.
                self.stats.jit_recompilations += 1;
                match self.compile_static_clauses() {
                    Ok(count) if count > 0 => {
                        tracing::debug!(
                            compiled_clauses = count,
                            "jit: recompiled formula after structural inprocessing"
                        );
                        // Detach compiled clause watchers after recompilation to
                        // avoid double-processing. Mirrors the initial compilation
                        // site in solve/mod.rs.
                        let removed = self.detach_jit_compiled_watches();
                        if removed > 0 {
                            tracing::debug!(
                                removed,
                                "jit: detached compiled (len 3-5) watchers after inprocessing"
                            );
                        }
                    }
                    Ok(_) => {}
                    Err(e) => {
                        tracing::warn!(
                            error = %e,
                            "jit: recompilation failed after inprocessing, continuing without JIT"
                        );
                    }
                }
            }
        }

        false
    }
}
