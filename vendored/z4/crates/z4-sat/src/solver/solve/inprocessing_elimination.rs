// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing elimination back-half:
//! BVE interleaved with subsumption/BCE, factor, standalone BCE/CCE,
//! condition, transred, sweep, compact.

use super::super::*;

impl Solver {
    /// Run the elimination back half of inprocessing.
    ///
    /// Returns `true` if UNSAT was derived. Appends pass names to `passes_run`.
    pub(in crate::solver) fn run_elimination_passes(
        &mut self,
        passes_run: &mut Vec<&'static str>,
        skip_gate_dependent_passes: bool,
        skip_expensive_equivalence_passes: bool,
    ) -> bool {
        // ── Interleaved elimination phase (CaDiCaL elim.cpp:1050-1109) ──
        //
        // CaDiCaL runs BVE as a multi-round phase interleaved with subsumption
        // and BCE between rounds. The cascade effect is critical: BVE produces
        // resolvents → subsumption simplifies/removes them → creates new BVE
        // candidates → repeat. Without interleaving, each technique reaches
        // only a local fixpoint within its own round.
        // Density-based BVE skip for very large dense formulas (#8136).
        let active_cls_for_bve = self.arena.active_clause_count();
        let active_vars_for_bve = self.num_vars.saturating_sub(self.var_lifecycle.count_removed());
        let bve_density = if active_vars_for_bve > 0 { active_cls_for_bve as f64 / active_vars_for_bve as f64 } else { 0.0 };
        let skip_bve_dense = active_cls_for_bve > PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD && bve_density > PREPROCESS_BVE_SKIP_DENSITY;
        let mut bce_ran_in_elim_phase = false;
        if self.should_bve() && !skip_gate_dependent_passes && !skip_bve_dense {
            self.jit_invalidate_for_structural_pass(); // BVE: structural (#8128)
            let clauses_before_elim_phase = self.arena.active_clause_count();

            // CaDiCaL elim.cpp:1050: disconnect watches for the entire
            // elimination phase. BVE uses occurrence lists, subsume_round()
            // uses one-watch occ-lists, BCE uses occurrence lists. None need
            // the 2WL watch graph. Reconnecting once at the end (instead of
            // per-subsumption-round) saves O(clauses) work per interleave
            // iteration — a major win on large formulas like FmlaEquivChain.
            self.watches.clear();
            self.watches_disconnected = true;

            let mut elim_derived_unsat = false;
            for elim_round in 0..ELIM_INTERLEAVE_ROUNDS {
                // BVE can derive UNSAT directly (empty resolvent).
                if self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BVE, Self::bve) {
                    elim_derived_unsat = true;
                    break;
                }
                passes_run.push("bve");

                // CaDiCaL defers post-BVE propagation to after the loop
                // (elim.cpp:1134-1138). BVE units are enqueued via enqueue()
                // which sets vals[], so subsequent BVE/subsumption rounds
                // correctly see the unit's truth value. Full BCP propagation
                // (which requires watches) runs once after reconnection.
                if self.has_empty_clause {
                    elim_derived_unsat = true;
                    break;
                }

                if self.is_interrupted() {
                    break;
                }

                // Between BVE rounds: try subsumption and BCE to create new
                // elimination candidates (CaDiCaL elim.cpp:1084-1098).
                // Exit the interleaving loop if neither produces new candidates.
                let marked_before = self.cold.bve_marked;
                let fixed_before = self.fixed_count;

                // Inter-round subsumption: subsume_round() operates without
                // watch management (CaDiCaL subsume_round() pattern). Watches
                // are already disconnected above; reconnection is deferred to
                // after the loop. Propagation is also deferred — subsumption
                // units are on the trail (vals set) and BVE sees them.
                if self.inproc_ctrl.subsume.enabled {
                    self.run_timed_diagnostic_inprocessing_pass(
                        DiagnosticPass::Subsume,
                        Self::subsume,
                    );
                    passes_run.push("subsume");
                    if self.has_empty_clause {
                        elim_derived_unsat = true;
                        break;
                    }
                }

                // Inter-round BCE: blocked clause removal opens new BVE
                // opportunities (CaDiCaL block() in the interleaved loop).
                if self.inproc_ctrl.bce.enabled && !self.cold.has_been_incremental {
                    self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BCE, Self::bce);
                    passes_run.push("bce");
                    bce_ran_in_elim_phase = true;
                }

                // Check if subsumption or BCE produced new BVE candidates.
                // CaDiCaL's feedback signal: subsume_round() returns true
                // when old_marked < stats.mark.elim.
                let new_candidates =
                    self.cold.bve_marked != marked_before || self.fixed_count != fixed_before;

                if !new_candidates || elim_round + 1 >= ELIM_INTERLEAVE_ROUNDS {
                    break;
                }

                // Reset BVE fixpoint guards so the next bve() call re-fires.
                // The subsumption between rounds incremented bve_marked; we
                // want bve() to see that and process the new candidates.
                self.cold.last_bve_fixed = self.fixed_count;
                self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);
            }

            // CaDiCaL elim.cpp:1125-1128: reconnect watches once after
            // the entire elimination phase. This replaces per-round
            // watch attach/detach that was O(resolvents + deletions) × rounds.
            // BVE adds/deletes clauses in bulk; full re-propagation needed (#8095).
            self.mark_trail_affected(0);
            self.watches_disconnected = false;
            self.rebuild_watches();

            // Deferred propagation: catch units derived by BVE and subsumption
            // during the interleave loop (CaDiCaL elim.cpp:1134-1138).
            if elim_derived_unsat {
                return true;
            }
            if self.propagate_check_unsat() {
                return true;
            }

            // Record the stricter re-entry threshold for BVE (#7178).
            self.update_bve_growth_guard(clauses_before_elim_phase);
            // CaDiCaL elim.cpp:1026: stats.elimphases++ once per elim() call.
            // The entire interleaving loop (multiple elim_round + subsume_round)
            // is ONE phase. Incrementing once here (not per bve() sub-round)
            // prevents 3x interval growth inflation (#7393).
            self.cold.bve_phases += 1;
        } else if self.should_bve() && skip_gate_dependent_passes {
            // BVE skipped: keep fixpoint/schedule state in sync so BVE can
            // re-fire when the formula classification changes (#7135).
            self.cold.last_bve_fixed = self.fixed_count;
            self.cold.last_bve_marked = self.cold.bve_marked;
            self.inproc_ctrl
                .bve
                .reschedule(self.num_conflicts, BVE_INTERVAL_BASE);
        }

        // Factorization: introduce extension variables to compress clause structure.
        // CaDiCaL runs factoring after BVE (factor.cpp:928).
        // Guard: factorize builds O(clauses) occurrence lists BEFORE applying the
        // effort limit. On large residuals (>3M clauses), this costs 10+ seconds.
        // Matches preprocessing guard (config_preprocess.rs:340).
        if self.should_factor() && !skip_expensive_equivalence_passes {
            self.jit_invalidate_for_structural_pass(); // factor: structural (#8128)
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Factor, Self::factorize);
            passes_run.push("factor");
            if self.propagate_check_unsat() {
                return true;
            }
        } else if self.should_factor() && skip_expensive_equivalence_passes {
            self.inproc_ctrl
                .factor
                .reschedule(self.num_conflicts, FACTOR_INTERVAL);
        }

        // CaDiCaL factor.cpp:966: factor may create duplicate divider clauses.
        if self.inproc_ctrl.decompose.enabled && self.deduplicate_binary_clauses() {
            return true;
        }

        // Standalone BCE: only if it wasn't already run in the interleaved
        // elimination phase above. This ensures BCE fires on its own schedule
        // even when BVE doesn't fire.
        // Gate: BCE builds occurrence lists O(clauses) before the effort limit.
        // On large residuals (>3M clauses), this setup cost dominates (#7135).
        if self.should_bce() && !bce_ran_in_elim_phase && !skip_expensive_equivalence_passes {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BCE, Self::bce);
            passes_run.push("bce");
        }

        // Covered clause elimination (ACCE): strictly subsumes BCE.
        // CaDiCaL: cover() after block() in the elimination pipeline.
        // Default OFF (CaDiCaL opts.cover=false). Same reconstruction as BCE.
        if self.should_cce() && !self.cold.has_been_incremental {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::CCE, Self::cce);
            passes_run.push("cce");
        }

        // Conditioning (GBCE) after BCE: globally blocked clause elimination.
        // Reference: CaDiCaL condition.cpp; Kiesl, Heule, Biere -- ATVA 2019.
        // Guard: conditioning builds a total assignment over all vars and iterates
        // all clauses. On large residuals, this is O(clauses) before the check.
        // Matches preprocessing guard (config_preprocess.rs:416).
        if self.should_condition() && !skip_expensive_equivalence_passes {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Condition, Self::condition);
            passes_run.push("condition");
        } else if self.should_condition() && skip_expensive_equivalence_passes {
            self.inproc_ctrl
                .condition
                .reschedule(self.num_conflicts, CONDITION_INTERVAL);
        }

        if self.should_transred() {
            // Transred removes transitive binary clauses.
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::TransRed, Self::transred);
            passes_run.push("transred");
            // Post-transred: no probing/vivify -- search variant.
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return true;
            }
        }

        if self.should_sweep() && !skip_expensive_equivalence_passes {
            self.jit_invalidate_for_structural_pass(); // sweep: structural (#8128)
            // SAT sweeping detects equivalences via SCC on implication graph.
            if self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Sweep, Self::sweep) {
                return true;
            }
            passes_run.push("sweep");
            // Post-sweep: no probing/vivify -- search variant.
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return true;
            }

            // CaDiCaL re-runs decompose after sweep (probe.cpp:947-948).
            // Sweep equivalences produce new binary clauses for SCC.
            if self.inproc_ctrl.decompose.enabled {
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
        } else if self.should_sweep() && skip_expensive_equivalence_passes {
            self.inproc_ctrl
                .sweep
                .reschedule(self.num_conflicts, SWEEP_INTERVAL);
        }

        // Variable compaction: remap active variables to a contiguous range
        // after BVE/substitution creates holes in variable-indexed arrays.
        // Guards: level 0, non-incremental, no proof output, sufficient inactives.
        if self.compacting() {
            self.compact();
            passes_run.push("compact");
        }

        false
    }
}
