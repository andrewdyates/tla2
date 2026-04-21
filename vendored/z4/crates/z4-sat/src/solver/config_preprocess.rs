// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Initial preprocessing pipeline split from `config.rs` for file-size compliance (#5142).

use super::mutate::ReasonPolicy;
use super::*;

impl Solver {
    /// Run initial preprocessing to reduce the search space
    ///
    /// Quick-path pipeline (matches CaDiCaL internal.cpp:742-792) with an
    /// early symmetry pass inserted before destructive rewrites:
    ///   symmetry → congruence → backbone → sweep → decompose → factor → fastelim (BVE)
    /// Heavy passes (HTR, probing, conditioning, subsumption) are deferred to
    /// inprocessing where they fire in the first round at ~2K conflicts.
    ///
    /// Returns true if UNSAT was detected during preprocessing.
    pub(super) fn preprocess(&mut self) -> bool {
        let _preprocess_start = std::time::Instant::now();
        // Must be at level 0 for preprocessing
        if self.decision_level != 0 {
            return false;
        }

        // NOTE: Preprocessing is NOT blanket-disabled in proof mode. All
        // enabled techniques emit valid DRAT records. Factorization now uses
        // the same DRAT transaction path as inprocessing and performs its own
        // LRAT-only runtime guard inside `factorize()`.
        //
        // CaDiCaL runs all preprocessing with proof logging enabled.

        // Clause deletions are lazy: stale watch entries are compacted in a
        // single linear pass before running level-0 inprocessing.
        let _t_flush0 = std::time::Instant::now();
        self.flush_watches();
        let _t_flush_done = _t_flush0.elapsed();

        // Classify the original irredundant formula once per preprocess call.
        // Large uniform non-binary formulas (random k-SAT) rarely contain
        // useful gate structure; skip gate-dependent passes to avoid
        // pathological preprocessing overhead (#3411).
        let skip_gate_dependent_passes = self.is_uniform_nonbinary_irredundant_formula();
        let skip_expensive_preprocessing_passes = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            || self.arena.num_clauses() > PREPROCESS_EXPENSIVE_MAX_CLAUSES;
        // Density-based skip for large dense formulas (#8136).
        let active_cls = self.arena.active_clause_count();
        let active_vars_est = self.num_vars.saturating_sub(self.trail.len());
        let formula_density = if active_vars_est > 0 { active_cls as f64 / active_vars_est as f64 } else { 0.0 };
        let skip_dense_formula = active_cls > PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD && formula_density > PREPROCESS_BVE_SKIP_DENSITY;
        let skip_expensive_preprocessing_passes = skip_expensive_preprocessing_passes || skip_dense_formula;
        // Congruence + decompose use the same threshold (CONGRUENCE_MAX_CLAUSES).
        // On shuffling-2 (4.7M clauses), congruence finds 0 substitutions and
        // decompose finds 0 equivalences, but together take 3-8s.
        let skip_congruence = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            || self.arena.num_clauses() > CONGRUENCE_MAX_CLAUSES
            || !self.inproc_ctrl.congruence.enabled
            || skip_dense_formula;
        let skip_expensive_gate_preprocessing =
            skip_gate_dependent_passes || skip_expensive_preprocessing_passes;

        // CaDiCaL defaults to 0 full preprocessing rounds (internal.cpp:805).
        // Quick path (internal.cpp:742-792): gates, decompose, backbone,
        // sweep, factor, fastelim. Heavy passes (HTR, probing, conditioning,
        // subsumption) are deferred to inprocessing (first round at ~2K
        // conflicts) where they still fire, so no simplification is lost.
        let preprocessing_quick_mode = self.preprocessing_quick_mode;

        // Permanently disable techniques that are counterproductive on random
        // k-SAT (#3814). The `enabled` flag persists across inprocessing rounds
        // in the main CDCL loop, so we don't need separate inprocessing guards.
        //
        // - HTR: produces resolvents from uniform ternary clauses that bloat
        //   the clause DB without useful structure.
        // - Conditioning: removes clauses whose absence is equisatisfiable, but
        //   on uniform formulas this disrupts CDCL search heuristics.
        if skip_gate_dependent_passes {
            self.inproc_ctrl.htr.enabled = false;
            self.inproc_ctrl.condition.enabled = false;
        }

        // Proof modes require disabling incompatible techniques (#4397, #4557).
        // - `proof_override = true`: disabled in ALL proof modes (DRAT + LRAT)
        // - `lrat_override = true`: disabled only in LRAT mode
        if self.cold.lrat_enabled {
            let ctrl = self.inproc_ctrl.clone();
            self.inproc_ctrl = ctrl.with_proof_overrides(true);
        }

        // Run 1 full preprocessing round. CaDiCaL defaults to 0 full rounds
        // (fastelim only), with 1 round in SAT-COMP configuration (-P1).
        // 3 rounds caused preprocessing to hang on large instances (#6926):
        // all per-technique limits fire 3x, and the fixed-point exit only
        // triggers when zero variables are eliminated (rare on large formulas).
        // Inprocessing re-fires techniques after search progress, so 1 round
        // is sufficient. Ref: CaDiCaL internal.cpp:795-811.
        // Track whether watches are valid after preprocessing. When BVE
        // disconnects/reconnects watches and no subsequent pass modifies clause
        // literals in-place, the post-preprocessing watch rebuild in
        // solve_no_assumptions can be skipped. On large instances (4.7M clauses),
        // this avoids a redundant O(clauses) pass that costs ~6 seconds.
        let mut bve_rebuilt_watches = false;
        let mut watches_invalidated_after_bve = false;
        let mut _t1_cong: u128 = 0;
        let mut _t2_bb: u128 = 0;
        let mut _t3_decomp: u128 = 0;
        let mut _t4_factor: u128 = 0;
        let mut _t5_bve: u128 = 0;
        let mut _t6_probe: u128 = 0;

        for _round in 0..1 {
            // Check interrupt at the start of each preprocessing round (#3638).
            if self.is_interrupted() {
                return false;
            }

            // Level-0 garbage collection at the start of each round ensures
            // all techniques operate on clean clauses (no stale false literals).
            // On large formulas (>200K vars) with few fixed variables (<50%),
            // use lightweight GC that only checks for all-false clauses.
            // Full GC on 1M+ clause formulas costs 12s+ due to per-clause
            // watch manipulation. When many variables are fixed (>50%), full
            // GC is needed: clause shortening triggers unit propagation
            // cascades that are essential for UNSAT detection.
            let _t_gc0 = std::time::Instant::now();
            let fixed_ratio = if self.num_vars > 0 {
                self.count_fixed_vars() as f64 / self.num_vars as f64
            } else {
                0.0
            };
            if skip_congruence && fixed_ratio < 0.50 {
                if self.collect_level0_garbage_lightweight() {
                    return true;
                }
            } else if self.collect_level0_garbage() {
                return true;
            }
            let _t_gc_done = _t_gc0.elapsed();
            let _t_bcp0 = std::time::Instant::now();
            if self.propagate_check_unsat() {
                return true;
            }
            let _t_bcp_done = _t_bcp0.elapsed();

            let (symmetry_unsat, symmetry_changed) = self.preprocess_symmetry();
            if symmetry_unsat {
                return true;
            }
            if symmetry_changed && self.propagate_check_unsat() {
                return true;
            }

            let vars_before = self.num_vars - self.count_fixed_vars();

            let _t0 = _preprocess_start;

            // 1. Congruence closure must run before decompose so Tarjan SCC can
            //    consume new equivalence binaries; skipping decompose here can
            //    break reconstruction when BVE later eliminates those variables (#5752).
            if self.is_interrupted() {
                return false;
            }
            let _t_cong_start = std::time::Instant::now();
            if self.inproc_ctrl.gate.enabled
                && self.inproc_ctrl.congruence.enabled
                && self.inproc_ctrl.decompose.enabled
                && !skip_gate_dependent_passes
                && !skip_congruence
            {
                self.set_diagnostic_pass(DiagnosticPass::Congruence);
                self.congruence();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }
            let _t_cong_wall = _t_cong_start.elapsed();
            tracing::debug!(
                "[preprocess-breakdown] flush={:.1}ms gc={:.1}ms bcp={:.1}ms cong_wall={:.1}ms",
                _t_flush_done.as_secs_f64() * 1000.0,
                _t_gc_done.as_secs_f64() * 1000.0,
                _t_bcp_done.as_secs_f64() * 1000.0,
                _t_cong_wall.as_secs_f64() * 1000.0,
            );

            _t1_cong = _t0.elapsed().as_millis();

            // 1b. Backbone literal computation.
            if self.is_interrupted() {
                return false;
            }
            // CaDiCaL runs backbone during preprocessing (internal.cpp:769)
            // after gates+decompose. Z4's backbone uses CDCL-based probing which
            // is O(probes * BCP_cost_per_probe). On medium formulas (438K clauses)
            // this costs 4s despite the 5K conflict budget. CaDiCaL's backbone
            // uses lightweight binary-clause propagation. Only run during
            // preprocessing on small formulas (≤10K clauses) where BCP is cheap.
            // Larger formulas defer to inprocessing where BVE has reduced the
            // formula size.
            if self.inproc_ctrl.backbone.enabled
                && !skip_expensive_preprocessing_passes
                && self.arena.num_clauses() <= 10_000
            {
                self.set_diagnostic_pass(DiagnosticPass::Backbone);
                self.backbone();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }
            _t2_bb = _t0.elapsed().as_millis();

            // 1c. SAT sweeping (equivalence merging + unit detection).
            //     CaDiCaL runs sweep during preprocessing (sweep.cpp), finding
            //     equivalent variables via SCC analysis and discovering units.
            //     On crn_11_99_u, sweep finds 45 units — the single largest
            //     contributor to CaDiCaL's fixed-var count.
            if self.is_interrupted() {
                return false;
            }
            // Z4's sweep uses kitten-based COI probing (CaDiCaL sweep.cpp
            // pattern) with random simulation fallback (#6868). On uniform
            // formulas with no binary clauses, COI probing may find nothing,
            // but random simulation discovers candidates by assigning random
            // values, forward-propagating, and grouping variables by signature.
            // The skip_gate_dependent_passes guard avoids the O(clauses)
            // iteration cost when sweep is unlikely to find anything.
            if self.inproc_ctrl.sweep.enabled && !skip_expensive_gate_preprocessing {
                self.set_diagnostic_pass(DiagnosticPass::Sweep);
                if self.sweep() {
                    self.clear_diagnostic_pass();
                    return true;
                }
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }

            // 2. Decompose (SCC equivalent literal substitution).
            //    Runs after congruence + backbone + sweep so Tarjan can leverage
            //    new binary implication edges from congruence equivalence binaries
            //    and any new units discovered by backbone/sweep.
            //    Decompose is enabled in both DRAT and LRAT modes: probe-based
            //    equivalence binary hints (#4606) provide proper LRAT chains.
            if self.is_interrupted() {
                return false;
            }
            if self.inproc_ctrl.decompose.enabled && !skip_congruence {
                self.set_diagnostic_pass(DiagnosticPass::Decompose);
                self.decompose();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }
            _t3_decomp = _t0.elapsed().as_millis();
            let _t_htr_start = std::time::Instant::now();

            // 2b. HTR (hyper-ternary resolution).
            //     CaDiCaL pattern (probe.cpp:936-948):
            //       decompose(); if (ternary()) decompose();
            //     HTR resolves ternary clause pairs to derive binary resolvents
            //     that create new implication graph edges for decompose.
            if self.is_interrupted() {
                return false;
            }
            if self.inproc_ctrl.htr.enabled
                && !skip_expensive_preprocessing_passes
                && !preprocessing_quick_mode
            {
                self.set_diagnostic_pass(DiagnosticPass::HTR);
                let produced_binary = self.htr();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }

                // Re-run decompose if HTR produced binary clauses (new SCC edges).
                if produced_binary && self.inproc_ctrl.decompose.enabled {
                    self.set_diagnostic_pass(DiagnosticPass::Decompose);
                    self.decompose();
                    self.clear_diagnostic_pass();
                    if self.propagate_check_unsat() {
                        return true;
                    }
                }
            }

            let _t_htr_wall = _t_htr_start.elapsed();
            let _t_probe_start = std::time::Instant::now();

            // 3. Probing (failed literal detection).
            //    Runs after decompose so the binary implication graph is simplified,
            //    yielding more effective root-literal probes.
            //    LRAT hints are collected via collect_probe_conflict_lrat_hints
            //    before backtracking, so probing works in both DRAT and LRAT modes.
            //    Deferred from preprocessing quick path — fires in first inprocessing
            //    round at ~2K conflicts (CaDiCaL internal.cpp:695-739).
            if self.is_interrupted() {
                return false;
            }
            if self.inproc_ctrl.probe.enabled
                && !preprocessing_quick_mode
                && !skip_expensive_preprocessing_passes
            {
                // Ensure level-0 unit proof IDs before probe hint collection.
                // In preprocessing, backbone/decompose may not have run (if disabled),
                // so probe must ensure IDs itself. Fixes #7108.
                // Deferred from expensive preprocessing -- fires in first
                // inprocessing round at ~2K conflicts (#8084).
                if self.run_preprocess_probe_pass(skip_congruence) {
                    return true;
                }
            }

            let _t_probe_wall = _t_probe_start.elapsed();
            let _t_factor_start = std::time::Instant::now();

            // 4. Factorization (extension variable compression).
            //    CaDiCaL runs factoring BEFORE fastelim (internal.cpp:774-778).
            //    On clique formulas, factorization introduces extension variables
            //    that compress binary clause patterns, enabling fastelim to
            //    cascade through extension variables for 70%+ clause reduction.
            if self.is_interrupted() {
                return false;
            }
            if self.should_preprocess_factor() && !skip_expensive_preprocessing_passes {
                self.set_diagnostic_pass(DiagnosticPass::Factor);
                self.factorize();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }
            let _t_factor_wall = _t_factor_start.elapsed();
            tracing::debug!(
                "[preprocess-phases] htr={:.1}ms probe={:.1}ms factor={:.1}ms",
                _t_htr_wall.as_secs_f64() * 1000.0,
                _t_probe_wall.as_secs_f64() * 1000.0,
                _t_factor_wall.as_secs_f64() * 1000.0,
            );
            _t4_factor = _t0.elapsed().as_millis();

            // 4c. Pre-BVE subsumption: CaDiCaL elim.cpp:1043-1044.
            //     Subsumption reduces occurrence counts after factorization,
            //     enabling more profitable fastelim eliminations on structured
            //     formulas. On clique formulas, factorization introduces extension
            //     variables that compress binary clause patterns -- subsumption
            //     removes the resulting redundancy (#7178 Gap A).
            if self.is_interrupted() {
                return false;
            }
            if self.inproc_ctrl.subsume.enabled {
                self.set_diagnostic_pass(DiagnosticPass::Subsume);
                self.subsume();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }

            // 4d. BVE / fastelim (witness-based reconstruction, CaDiCaL approach).
            //     Preprocessing uses fastelimbound=8 and bypasses conflict-interval
            //     scheduling because num_conflicts=0 would otherwise suppress BVE (#4209).
            if self.is_interrupted() {
                return false;
            }
            if self.inproc_ctrl.bve.enabled {
                let bve_outcome = self.run_preprocess_bve(
                    skip_gate_dependent_passes,
                    skip_expensive_preprocessing_passes,
                );
                bve_rebuilt_watches = bve_outcome.rebuilt_watches;
                if bve_outcome.found_unsat {
                    return true;
                }
            }
            _t5_bve = _t0.elapsed().as_millis();

            // 4e. Post-BVE probing: CaDiCaL runs probing AFTER fastelim/BVE
            //     during the quick preprocessing path (internal.cpp:788, probe.cpp).
            //     On structured BMC formulas, post-BVE probing finds backbone
            //     variables that collapse the remaining search space. CaDiCaL's
            //     log shows the 'P' line AFTER all 'e' (BVE) lines.
            //     Previously Z4 deferred probing from quick mode (#6926), but
            //     this skips the post-BVE probing step that CaDiCaL includes.
            //     On stric-bmc-ibm-10, this is the difference between SAT (0.35s)
            //     and Unknown (timeout) when factor+sweep are both enabled (#3366).
            if self.is_interrupted() {
                return false;
            }
            if self.inproc_ctrl.probe.enabled
                && !skip_expensive_preprocessing_passes
                && self.run_preprocess_probe_pass(skip_congruence)
            {
                // Post-BVE probing deferred on large formulas -- fires in first
                // inprocessing round at ~2K conflicts (#8084).
                return true;
            }
            _t6_probe = _t0.elapsed().as_millis();

            // 5. Conditioning (GBCE): globally blocked clause elimination.
            //    CaDiCaL runs conditioning only in full preprocessing rounds
            //    (internal.cpp:695-739), not in the quick path. Deferred from
            //    preprocessing quick mode.
            if self.is_interrupted() {
                return false;
            }
            if self.inproc_ctrl.condition.enabled
                && !preprocessing_quick_mode
                && !skip_expensive_preprocessing_passes
            {
                // Conditioning deferred on large formulas -- fires in first
                // inprocessing round at ~2K conflicts (#8084).
                self.set_diagnostic_pass(DiagnosticPass::Condition);
                self.condition();
                self.clear_diagnostic_pass();
                if self.has_empty_clause {
                    return true;
                }
            }

            // 6. Subsumption + strengthening.
            //    CaDiCaL runs subsumption only within full BVE rounds
            //    (elim.cpp:1043), not in the quick preprocessing path.
            //    Deferred from preprocessing quick mode.
            //    Bug fix: previously only subsumed clauses were deleted but
            //    strengthening results (literal removal) were silently discarded.
            if self.is_interrupted() {
                return false;
            }
            if self.inproc_ctrl.subsume.enabled
                && !preprocessing_quick_mode
                && !skip_expensive_preprocessing_passes
            {
                // Post-loop subsumption + strengthening deferred on large
                // formulas -- fires in first inprocessing round (#8084).
                self.set_diagnostic_pass(DiagnosticPass::Subsume);
                self.inproc.subsumer.ensure_num_vars(self.num_vars);
                self.inproc.subsumer.rebuild(&self.arena);
                // CaDiCaL subsume.cpp:349-362: during preprocessing,
                // propagations.search=0 so budget = max(subsumemineff=0,
                // 2*active()). Match this effort limit for large formulas.
                let active_vars = (self.num_vars - self.count_fixed_vars()) as u64;
                self.inproc.subsumer.set_check_limit(2 * active_vars);
                let num_clauses = self.arena.num_clauses();
                let result = self.inproc.subsumer.run_subsumption(
                    &mut self.arena,
                    &self.cold.freeze_counts,
                    0,
                    num_clauses,
                );

                // Apply strengthening (self-subsumption) BEFORE forward
                // subsumption deletions.  LRAT correctness requires that
                // subsumer clause IDs are still alive when used as resolution
                // hints.  If forward subsumption deletes a clause that is also
                // a subsumer for strengthening, the batched LRAT deletion is
                // flushed before the strengthening add step, causing "ERROR:
                // using DELETED hint clause" (#4398).
                self.ensure_reason_clause_marks_current();
                for (clause_idx, new_lits, subsumer_idx) in &result.strengthened {
                    let subsumer_hints = if self.cold.lrat_enabled {
                        vec![self.clause_id(ClauseRef(*subsumer_idx as u32))]
                    } else {
                        Vec::new()
                    };
                    self.replace_clause_with_explicit_lrat_hints(
                        *clause_idx,
                        new_lits,
                        &subsumer_hints,
                    );
                }
                // Strengthening modifies clause literals in-place, invalidating
                // watch pointers that reference the old literal positions.
                if !result.strengthened.is_empty() {
                    watches_invalidated_after_bve = true;
                }

                // Delete forward-subsumed clauses AFTER strengthening.
                // During preprocessing all clauses are irredundant (no CDCL
                // search yet), so irredundant-subsumes-irredundant is safe
                // and we don't need the learned-only guard that inprocessing
                // uses.  ReasonPolicy::Skip protects reason clauses created
                // by level-0 unit propagation in earlier preprocessing passes.
                for &(clause_idx, _) in &result.subsumed {
                    self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
                }
                self.clear_diagnostic_pass();

                // Propagate any units discovered by strengthening.
                if self.propagate_check_unsat() {
                    return true;
                }
            }

            // Check if we reached a fixed point
            let vars_after = self.num_vars - self.count_fixed_vars();
            if vars_after == vars_before {
                break;
            }
        }

        // Preprocessing summary: CaDiCaL-style fixed/eliminated/substituted/factored totals.
        self.emit_preprocess_summary(
            _preprocess_start,
            _t1_cong,
            _t2_bb,
            _t3_decomp,
            _t4_factor,
            _t5_bve,
            _t6_probe,
        );

        let _t7_loop_done = _preprocess_start.elapsed().as_millis();

        // Final GC: remove clauses that still mention eliminated variables after cross-pass cleanup (#7083).
        self.finalize_preprocess_clause_cleanup();

        // Signal to solve_no_assumptions whether watches are still valid.
        // BVE disconnects/reconnects watches as its last step. If no subsequent
        // pass modified clause literals in-place, the caller can skip the
        // redundant O(clauses) watch rebuild. The final GC pass above uses
        // lazy deletion (delete_clause_checked) which doesn't invalidate
        // watch pointers — stale entries are cleaned up during BCP.
        self.cold.preprocess_watches_valid = bve_rebuilt_watches && !watches_invalidated_after_bve;

        let _t_final = _preprocess_start.elapsed();
        tracing::debug!(
            "[preprocess-final] total={:.1}ms cong={_t1_cong}ms bb={_t2_bb}ms decomp={_t3_decomp}ms factor={_t4_factor}ms bve={_t5_bve}ms probe={_t6_probe}ms gc={:.1}ms",
            _t_final.as_secs_f64() * 1000.0,
            _t_final.as_millis().saturating_sub(_t7_loop_done) as f64,
        );

        false
    }

    /// Helper: count the number of fixed (assigned at level 0) variables.
    /// Uses trail.len() which is O(1) (#3758 Phase 3).
    pub(super) fn count_fixed_vars(&self) -> usize {
        self.trail.len()
    }
}

#[cfg(test)]
#[path = "config_preprocess_tests.rs"]
mod tests;
