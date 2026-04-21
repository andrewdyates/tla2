// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Failed literal probing and hyper-binary resolution.

use super::super::*;

impl Solver {
    /// Run failed literal probing (wrapper: always reschedules).
    ///
    /// Returns `true` only if UNSAT is proven (level-0 conflict after learning
    /// a derived unit). Returns `false` otherwise.
    pub(in crate::solver) fn probe(&mut self) -> bool {
        let result = self.probe_body();
        self.inproc_ctrl
            .probe
            .reschedule(self.num_conflicts, PROBE_INTERVAL);
        result
    }

    /// Probe body — early returns are safe; wrapper handles rescheduling.
    ///
    /// For each candidate probe literal, temporarily assign it and propagate.
    /// If a conflict is found, the literal is "failed" and its negation must be true.
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn probe_body(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        // Ensure all level-0 BCP-propagated variables have unit proof IDs
        // before collecting LRAT hints. Without this, collect_probe_conflict_lrat_hints
        // falls back to multi-literal reason clause IDs, which the LRAT checker
        // rejects (NonUnit: 2+ unfalsified literals). Same guard as backbone.rs:48,
        // condition.rs:45, decompose.rs:195. Fixes #7108.
        self.ensure_level0_unit_proof_ids();

        // CaDiCaL probe.cpp:816-817: if leftover probes exist from the
        // previous round (cut short by tick limit), flush and re-filter them.
        // Only regenerate from scratch when the candidate list is empty.
        if self.inproc.prober.has_probes() {
            self.inproc
                .prober
                .flush_probes(&self.arena, &self.vals, self.fixed_count);
        }

        // Reset propfixed BEFORE the loop (CaDiCaL probe.cpp:819-824).
        // This must happen after flush (which uses old propfixed to filter)
        // but before generate/loop (so all candidates are re-probable).
        // "We reset propfixed since there was at least another conflict thus
        // a new learned clause, which might produce new propagations."
        self.inproc.prober.reset_propfixed();

        if !self.inproc.prober.has_probes() {
            self.inproc
                .prober
                .generate_probes(&self.arena, &self.vals, self.fixed_count);
        }
        self.inproc.prober.record_round();

        // Compute tick-proportional effort budget.
        // CaDiCaL probe.cpp:796-832: effort = (search_ticks_delta) * probeeffort / 1000
        // probeeffort=8 (0.8% of search ticks), min 10K ticks.
        // Budget and consumption both in tick units (#3758).
        const PROBE_EFFORT_PERMILLE: u64 = 8; // CaDiCaL options.hpp:164
        const PROBE_MIN_EFFORT: u64 = 10_000;
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.inproc.prober.last_search_ticks());
        let effort = (ticks_delta * PROBE_EFFORT_PERMILLE / 1000).max(PROBE_MIN_EFFORT);
        let tick_limit = self.cold.probe_ticks.saturating_add(effort);

        // Probe each candidate
        while let Some(probe_lit) = self.inproc.prober.next_probe() {
            // Tick-proportional effort limit (#3758).
            // CaDiCaL probeeffort=8: 0.8% of search tick delta, measured in ticks.
            if self.cold.probe_ticks >= tick_limit {
                break;
            }

            // Skip if already assigned or removed by inprocessing
            let probe_var = probe_lit.variable().index();
            if self.var_is_assigned(probe_var) || self.var_lifecycle.is_removed(probe_var) {
                continue;
            }

            self.inproc.prober.record_probed();

            // Precondition: probe literal must be unassigned
            debug_assert!(
                !self.var_is_assigned(probe_var),
                "BUG: probe deciding already-assigned literal {probe_lit:?}",
            );
            // Make probe as decision at level 1
            self.decide(probe_lit);

            // Clear probe_parent for decision literal (#3419).
            // CaDiCaL probe.cpp:338: probe_assign(lit, 0) — parent = 0 for decision.
            self.probe_parent[probe_var] = None;

            // Enter probing mode for level-1 parent tracking and HBR plumbing.
            // CaDiCaL probe.cpp:405,485 tracks probe parents for probing
            // regardless of whether HBR binary clauses are emitted.
            self.probing_mode = true;

            // Propagate (with HBR if enabled)
            let conflict_ref = self.probe_propagate();

            // Exit probing mode
            self.probing_mode = false;

            if let Some(conflict_ref) = conflict_ref {
                // Found conflict - this is a failed literal
                self.inproc.prober.record_failed();

                // CaDiCaL-style failed-literal UIP: use dominator extraction.
                // Parent-chain processing is needed only when both HBR and LRAT
                // are disabled; otherwise the chain is unused and can be skipped.
                let need_parent_chain = !self.hbr_enabled && !self.cold.lrat_enabled;
                let dom_result = if need_parent_chain {
                    failed_literal_dominator(
                        self.arena.literals(conflict_ref.0 as usize),
                        probe_lit,
                        &self.trail,
                        &self.var_data,
                        &self.probe_parent,
                        &self.arena,
                    )
                } else {
                    crate::probe::failed_literal_dominator_forced_only(
                        self.arena.literals(conflict_ref.0 as usize),
                        probe_lit,
                        &self.trail,
                        &self.var_data,
                        &self.probe_parent,
                        &self.arena,
                    )
                };
                let crate::probe::FailedLiteralDominatorResult {
                    forced: dom_forced,
                    parent_chain: dom_parent_chain,
                    failure: dom_failure,
                } = dom_result;
                let parent_chain = if need_parent_chain && dom_forced.is_some() {
                    dom_parent_chain
                } else {
                    Vec::new()
                };
                // Fall back to legacy trail-walk UIP only for legitimate
                // dominator failures (NoDominator, ParentChainCycle).
                // MissingMetadata is a probe_parent contract violation —
                // debug_assert fires in failed_literal_dominator; still fall
                // back in release for safety, but log the contract break.
                let forced = dom_forced.or_else(|| {
                    if dom_failure == Some(crate::probe::DominatorFailure::MissingMetadata) {
                        debug_assert!(
                            false,
                            "BUG: probe_parent metadata missing — dominator path returned MissingMetadata for probe {probe_lit:?}",
                        );
                    }
                    find_failed_literal_uip(
                        self.arena.literals(conflict_ref.0 as usize),
                        &self.trail,
                        &self.var_data,
                        &self.arena,
                        self.inproc.prober.uip_seen_mut(),
                    )
                    .forced
                });
                // LRAT probe hint collection currently proves the failed
                // literal path (`probe_lit => conflict`) via a forward BCP
                // trace. Dominator/UIP-derived units stronger than
                // `probe_lit.negated()` need CaDiCaL-style specialized chains
                // (`probe_dominator_lrat` / `probehbr_chains`), which Z4 does
                // not maintain yet. In LRAT mode, learn the weaker but sound
                // failed literal until that proof path exists (#7108, #6270).
                let forced = if self.cold.lrat_enabled {
                    Some(probe_lit.negated())
                } else {
                    forced
                };
                // Collect LRAT hints BEFORE backtracking so level-1 trail
                // entries and their reason clauses are still accessible.
                // Mirrors the preprocessing probe pattern (config.rs:281).
                let lrat_hints =
                    self.collect_probe_conflict_lrat_hints(conflict_ref, probe_lit, forced);

                // Backtrack to level 0
                self.backtrack(0);
                debug_assert_eq!(
                    self.decision_level, 0,
                    "BUG: probe backtrack did not reach level 0"
                );

                if let Some(unit_lit) = forced {
                    // Learn the unit clause (proof emit + clause DB + enqueue + propagate).
                    if self.learn_derived_unit(unit_lit, &lrat_hints) {
                        // Conflict at level 0 - UNSAT
                        return true;
                    }
                    // After learning a probe-derived unit, BCP at level 0 may
                    // add new trail entries without unit_proof_ids (#7108).
                    if self.cold.lrat_enabled {
                        self.ensure_level0_unit_proof_ids();
                    }

                    // Process failed-literal parent chain (CaDiCaL probe.cpp:565-585):
                    // already-true parent => clash; unassigned => force negation.
                    //
                    // CaDiCaL asserts !opts.probehbr at lines 571,576: Phase 4
                    // is mutually exclusive with HBR. When HBR is enabled, BCP
                    // already handles parent-chain implications via binary clauses.
                    // Gate on !lrat_enabled because we lack probehbr_chains cache
                    // for LRAT proof hints (CaDiCaL lines 572,577: get_probehbr_lrat).
                    if !self.hbr_enabled && !self.cold.lrat_enabled {
                        for parent in parent_chain {
                            match self.lit_val(parent) {
                                // Clashing parent implies immediate contradiction.
                                1 => {
                                    self.mark_empty_clause();
                                    return true;
                                }
                                // Parent unassigned: derive and propagate unit `¬parent`.
                                0 => {
                                    let parent_unit = parent.negated();
                                    if self.learn_derived_unit(parent_unit, &[]) {
                                        return true;
                                    }
                                }
                                // Already false: nothing to do.
                                _ => {}
                            }
                        }
                    }
                }
            } else {
                // No conflict - backtrack and continue
                self.backtrack(0);
                debug_assert_eq!(
                    self.decision_level, 0,
                    "BUG: probe backtrack (no-conflict) did not reach level 0"
                );
            }

            // Mark this literal as probed at current fixed point
            self.inproc.prober.mark_probed(probe_lit, self.fixed_count);
        }

        // Record ticks for next effort computation.
        self.inproc
            .prober
            .set_last_search_ticks(self.search_ticks[0] + self.search_ticks[1]);

        // Post-condition: probe must always leave the solver at level 0.
        // If this fails, the solver's clause database state is inconsistent
        // and subsequent inprocessing or search will be unsound.
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: probe() did not restore decision level to 0"
        );

        // No UNSAT detected. Failed literals (if any) are tracked in
        // prober.stats().failed and their derived units are already propagated.
        false
    }
}
