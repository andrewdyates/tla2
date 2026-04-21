// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//\! Congruence closure for equivalence merging.

use super::super::*;

mod rup_probing;

impl Solver {
    ///
    /// Extracts gates from the formula, then iteratively merges outputs of
    /// gates with the same type and equivalent inputs. Adds binary equivalence
    /// clauses to the clause DB for BCP and decompose's SCC to pick up.
    ///
    /// CaDiCaL architecture (#5237): congruence only discovers equivalences
    /// and adds binary implication clauses. All clause-level substitution
    /// (rewriting, deletion, variable marking, reconstruction) is handled by
    /// decompose() which runs after congruence in the inprocessing pipeline.
    /// CaDiCaL: congruence.cpp (gate rewriting only) + decompose.cpp (SCC
    /// clause DB substitution). internal.cpp: `if (extract_gates(true)) decompose();`
    ///
    /// Returns `true` if equivalences were found and decompose should run
    /// to perform the actual clause rewriting.
    ///
    /// Must be called at decision level 0.
    pub(in crate::solver) fn congruence(&mut self) -> bool {
        let equivs_before = self.inproc.congruence.stats().equivalences_found;
        let result = self.congruence_body();
        let equivs_after = self.inproc.congruence.stats().equivalences_found;
        let yield_this_round = equivs_after - equivs_before;

        // CaDiCaL congruence.cpp:7871-7874 uses a Delay mechanism:
        //   - No merges: bump_delay (interval += 1, limit = interval)
        //   - Merges found: reduce_delay (interval /= 2, limit = interval)
        // Translated to Z4's conflict-interval scheduling:
        //   - No equivs: 2x growth (existing backoff)
        //   - Few equivs (<50): 1.5x growth (diminishing returns — O(clauses)
        //     gate extraction for ~10 equivs is poor ROI on 360K-clause formulas)
        //   - Many equivs (>=50): halve interval (high yield, rescan soon)
        // On FmlaEquivChain (4.7M clauses), this reduces congruence from 28
        // rounds (~5s overhead) to ~10 rounds while still capturing the 301
        // total equivalences that drive decompose substitution (#7279).
        const CONGRUENCE_HIGH_YIELD: u64 = 50;

        if yield_this_round >= CONGRUENCE_HIGH_YIELD {
            // High yield — halve the interval for timely follow-up.
            self.inproc_ctrl.congruence.reschedule_growing(
                self.num_conflicts,
                CONGRUENCE_INTERVAL,
                1,
                2, // halve
                CONGRUENCE_MAX_INTERVAL,
            );
        } else if yield_this_round > 0 {
            // Low yield — grow interval 1.5x (still productive but diminishing).
            self.inproc_ctrl.congruence.reschedule_growing(
                self.num_conflicts,
                CONGRUENCE_INTERVAL,
                3,
                2, // 1.5x growth
                CONGRUENCE_MAX_INTERVAL,
            );
        } else {
            // No equivalences — 2x exponential backoff (CaDiCaL pattern).
            // On large residuals (shuffling-2: 4.9M clauses), congruence is
            // O(clauses) and finds nothing repeatedly. 2× growth from 2K:
            // 2K → 4K → 8K → 16K → 32K → 64K limits total calls (#7135).
            self.inproc_ctrl.congruence.reschedule_growing(
                self.num_conflicts,
                CONGRUENCE_INTERVAL,
                2,
                1,
                CONGRUENCE_MAX_INTERVAL,
            );
        }
        if result {
            // Congruence-discovered equivalences must be rewritten immediately
            // by the following decompose pass, even if decompose already ran
            // earlier in the same inprocessing round.
            self.inproc_ctrl.decompose.next_conflict = 0;
        }
        result
    }

    /// Congruence body — early returns are safe; wrapper handles rescheduling.
    fn congruence_body(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        // Defense-in-depth: congruence equivalences are consumed by decompose
        // (push_equivalence_reconstruction + clause rewriting), which cannot
        // operate in incremental mode. Matches condition()/decompose() (#3662).
        if self.cold.has_been_incremental {
            return false;
        }

        // LRAT override handled centrally by inproc_ctrl.with_proof_overrides() (#4557).

        self.inproc.congruence.ensure_num_vars(self.num_vars);

        // V5 lifecycle guard (#3906 wave-2 D6): build a frozen bitmask instead
        // of cloning the full Vec<u32> freeze_counts (#5079 Finding 3). A variable
        // is frozen if it has a non-zero freeze_count OR is inactive (Eliminated,
        // Substituted, Fixed). Frozen variables are excluded from gate extraction
        // to prevent reconstruction order conflicts (BVE witnesses replay before
        // congruence equivalences).
        let congruence_frozen: Vec<bool> = (0..self.num_vars)
            .map(|i| {
                let explicitly_frozen =
                    i < self.cold.freeze_counts.len() && self.cold.freeze_counts[i] > 0;
                let lifecycle_frozen =
                    i < self.var_lifecycle.len() && self.var_lifecycle.is_inactive(i);
                explicitly_frozen || lifecycle_frozen
            })
            .collect();

        // Congruence-level gate rewriting consumes root assignments from the
        // live solver state. This re-enables the vals-aware simplification path
        // after the XOR polarity regression (#6997) that originally forced the
        // blanket disable in #3413.
        let result =
            self.inproc
                .congruence
                .run(&mut self.arena, Some(&self.vals), &congruence_frozen);

        // Contradiction detected by congruence closure (e.g., XOR odd-cycle).
        // Soundness gate (#7137): only accept RUP-verified contradiction units.
        // Non-RUP units are skipped to prevent false UNSAT from wrong congruence
        // claims (e.g., asconhash-m5_6: 97K gates, 0 conflicts, false UNSAT).
        if result.is_unsat {
            debug_assert!(
                !result.units.is_empty(),
                "BUG: congruence UNSAT must provide contradiction unit witness(es)"
            );
            let mut any_enqueued = false;
            for unit in &result.units {
                let proof_unit = self.pick_congruence_contradiction_unit(*unit);
                let unit_hints = self.collect_rup_unit_lrat_hints(proof_unit);
                if self.has_empty_clause {
                    break;
                }
                let rup_pass = if unit_hints.is_empty() {
                    self.is_rup_unit_under_negation(proof_unit)
                } else {
                    true
                };
                if !rup_pass {
                    // Unit is not RUP — congruence claim is unsound. Skip it.
                    self.inproc
                        .congruence
                        .stats_mut()
                        .non_rup_contradiction_units += 1;
                    continue;
                }
                let proof_kind = if unit_hints.is_empty() {
                    ProofAddKind::TrustedTransform
                } else {
                    ProofAddKind::Derived
                };
                self.proof_emit_unit(proof_unit, &unit_hints, proof_kind);
                if !self.var_is_assigned(proof_unit.variable().index()) {
                    self.enqueue(proof_unit, None);
                    any_enqueued = true;
                }
            }
            if any_enqueued {
                // Let BCP detect the contradiction so record_level0_conflict_chain
                // builds proper LRAT hints for the empty clause (#4596).
                if !self.propagate_check_unsat() {
                    self.mark_empty_clause_with_level0_hints();
                }
                self.inproc_ctrl.congruence.next_conflict = u64::MAX;
                return false;
            }
            // ALL contradiction units failed RUP — reject the is_unsat claim.
            // Fall through to equivalence path (if any equivalences exist).
        }

        // Process non-contradiction units discovered by gate simplification cascade.
        // CaDiCaL congruence.cpp:4848-4896: units from AND(false input) → output false,
        // AND(all true) → output true, complementary pair → output false, etc.
        // These units are discovered WITHIN congruence closure but are NOT contradiction
        // witnesses — they're forced by the gate structure. Enqueue them as level-0
        // assignments and propagate. Design: #3366 congruence-gate-simplification.md.
        //
        // Soundness gate (#7137): skip non-RUP units to prevent wrong assignments
        // from corrupting the trail and causing false UNSAT via subsequent BCP.
        if !result.is_unsat && !result.units.is_empty() {
            for &unit in &result.units {
                // Skip variables already assigned (including by side-effect propagation
                // from a prior iteration's collect_rup_unit_lrat_hints).
                if self.var_is_assigned(unit.variable().index()) {
                    continue;
                }
                // collect_rup_unit_lrat_hints calls probe_has_root_conflict() which
                // drains pending level-0 BCP. This side-effect propagation can assign
                // additional variables (including `unit`'s variable) and may discover
                // a root-level conflict. Re-check assignment after hint collection.
                let unit_hints = self.collect_rup_unit_lrat_hints(unit);
                if self.has_empty_clause {
                    return false;
                }
                // Re-check: hint collection's side-effect BCP may have assigned this var.
                if self.var_is_assigned(unit.variable().index()) {
                    continue;
                }
                if unit_hints.is_empty() && !self.is_rup_unit_under_negation(unit) {
                    self.inproc.congruence.stats_mut().non_rup_units += 1;
                    continue;
                }
                let proof_kind = if unit_hints.is_empty() {
                    ProofAddKind::TrustedTransform
                } else {
                    ProofAddKind::Derived
                };
                self.proof_emit_unit(unit, &unit_hints, proof_kind);
                // Re-check: collect_rup_unit_lrat_hints → probe_has_root_conflict
                // → search_propagate does permanent level-0 BCP that can assign
                // this variable between the check at line 426 and here.
                if self.var_is_assigned(unit.variable().index()) {
                    continue;
                }
                self.enqueue(unit, None);
            }
            // Level-0 BCP after unit enqueue: new units may cause conflict.
            // Use record_level0_conflict_chain to build proper LRAT hints (#4596).
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return false;
            }
        }

        // Set up watches for new binary clauses from hyper-ternary resolution.
        // These are RUP: (a,b,c) + (¬a,b) → (b,c) verified by setting ¬b,¬c
        // which forces a from the ternary, then ¬a→b from the binary conflicts.
        for &(clause_idx, lit0, lit1) in &result.new_binary_clauses {
            let off_header = clause_idx;
            if self.arena.is_empty_clause(off_header) {
                continue;
            }
            // HTR binary clauses are RUP by construction: (a,b,c) + (¬a,b) → (b,c).
            // Emit as Derived with LRAT hints when available (#5419).
            // When hints are empty (e.g., literal already true at level 0),
            // fall back to TrustedTransform in DRAT mode only. LRAT mode
            // cannot emit a non-unit clause with empty hints, so drop the
            // binary from the active DB instead of leaving behind an
            // unprovable reason clause.
            let htr_hints = self.collect_rup_binary_lrat_hints(lit0, lit1);
            if self.cold.lrat_enabled && htr_hints.is_empty() {
                self.arena.mark_garbage_keep_data(off_header);
                continue;
            }
            let htr_kind = if htr_hints.is_empty() {
                ProofAddKind::TrustedTransform
            } else {
                ProofAddKind::Derived
            };
            let proof_id = self
                .proof_emit_add(&[lit0, lit1], &htr_hints, htr_kind)
                .unwrap_or(0);
            // Register proof ID so later deletions emit correct LRAT ID (#5005).
            if self.cold.lrat_enabled && proof_id != 0 {
                if clause_idx >= self.cold.clause_ids.len() {
                    self.cold.clause_ids.resize(clause_idx + 1, 0);
                }
                self.cold.clause_ids[clause_idx] = proof_id;
            }
            let cref = ClauseRef(clause_idx as u32);
            let mut watched_lits = [lit0, lit1];
            let watched = self
                .prepare_watched_literals(&mut watched_lits, WatchOrderPolicy::Preserve)
                .expect("binary congruence clauses must expose two watch literals");
            self.attach_clause_watches(cref, watched, true);
        }

        if !result.found_equivalences {
            return false;
        }

        // Proof gate (#4575, #5419): validate RUP and collect LRAT hints for
        // each equivalence edge. In DRAT mode this is a pure RUP check; in LRAT
        // mode the hints collected here are passed to proof_emit_add so the LRAT
        // checker can verify each binary. Non-RUP edges cause the entire batch
        // to be skipped (same as the original DRAT safety gate).
        //
        // Hint collection reuses the probe infrastructure already paid for in
        // congruence_edges_are_rup() — the only added cost is chain bookkeeping.
        let mut edge_hints: Vec<(Vec<u64>, Vec<u64>)> = Vec::new();
        // Per-edge RUP mask: true = edge passed RUP, false = non-RUP (skip).
        // In the proof-manager path, non-RUP is encoded as empty hints on
        // a non-trivial/non-dedup edge. In the no-proof path, this mask is
        // the explicit filter. (#7137 Phase 2: per-edge RUP filtering)
        let mut rup_mask: Vec<bool> = Vec::new();
        if self.proof_manager.is_some() {
            let saved_propagations = self.num_propagations;
            let saved_decisions = self.num_decisions;

            let mut seen = std::collections::HashSet::new();
            for &(lhs, rhs) in &result.equivalence_edges {
                if lhs == rhs {
                    rup_mask.push(true);
                    edge_hints.push((Vec::new(), Vec::new()));
                    continue;
                }
                let key = if lhs.index() <= rhs.index() {
                    (lhs, rhs)
                } else {
                    (rhs, lhs)
                };
                if !seen.insert(key) {
                    rup_mask.push(true);
                    edge_hints.push((Vec::new(), Vec::new()));
                    continue;
                }

                // Per-edge RUP filtering (#7137 Phase 2): accept edges
                // individually. Non-RUP edges are skipped during emission.
                // CaDiCaL never produces unprovable edges (constructive proof
                // chains), but Z4's post-hoc RUP check can reject some edges
                // from ambiguous XOR/ITE extraction.
                if !self.cold.lrat_enabled {
                    let fwd_rup = self.is_rup_binary_under_negation(lhs.negated(), rhs);
                    let bwd_rup = self.is_rup_binary_under_negation(lhs, rhs.negated());
                    if !fwd_rup || !bwd_rup {
                        self.inproc.congruence.stats_mut().non_rup_equivalences += 1;
                        rup_mask.push(false);
                        edge_hints.push((Vec::new(), Vec::new()));
                        continue;
                    }
                    rup_mask.push(true);
                    edge_hints.push((Vec::new(), Vec::new()));
                } else {
                    let fwd_hints = self.collect_rup_binary_lrat_hints(lhs.negated(), rhs);
                    let bwd_hints = self.collect_rup_binary_lrat_hints(lhs, rhs.negated());
                    if fwd_hints.is_empty() || bwd_hints.is_empty() {
                        self.inproc.congruence.stats_mut().non_rup_equivalences += 1;
                        rup_mask.push(false);
                        edge_hints.push((Vec::new(), Vec::new()));
                        continue;
                    }
                    rup_mask.push(true);
                    edge_hints.push((fwd_hints, bwd_hints));
                }
            }

            // Restore counters to keep scheduling deterministic.
            self.num_propagations = saved_propagations;
            self.num_decisions = saved_decisions;
        } else {
            // No proof manager: trust gate extraction without RUP checking.
            // CaDiCaL never does post-hoc RUP on equivalence edges — it trusts
            // that gate extraction produces correct equivalences. Z4's gate
            // extraction is sound when XOR parity is correct (#7137 parity fix
            // in gates.rs). XOR/ITE equivalences are RAT (not RUP), so RUP
            // checking unconditionally rejects them even though they're correct.
            // Skipping the RUP gate for no-proof mode matches CaDiCaL's design.
            rup_mask.resize(result.equivalence_edges.len(), true);
            edge_hints.resize(result.equivalence_edges.len(), (Vec::new(), Vec::new()));
        }

        // Add binary implication clauses for each direct merge edge.
        // CaDiCaL congruence.cpp: merge_literals() / really_merge_literals()
        // adds equivalence binaries to the clause DB. These become edges in
        // the binary implication graph that decompose's SCC will discover.
        //
        // Proof status by gate type (#4575):
        // - AND equivalences: the binaries ARE RUP.
        // - XOR/ITE equivalences: the binaries are RAT but NOT RUP.
        // Per-edge RUP filtering (#7137 Phase 2): non-RUP edges are skipped
        // via rup_mask. Only RUP-verified edges are emitted as Derived with
        // LRAT hints (#5419).
        {
            let mut emitted_pairs = std::collections::HashSet::new();
            for (edge_idx, &(lhs, rhs)) in result.equivalence_edges.iter().enumerate() {
                if lhs == rhs {
                    continue;
                }
                // Skip non-RUP edges (#7137 Phase 2).
                if !rup_mask[edge_idx] {
                    continue;
                }
                let key = if lhs.index() <= rhs.index() {
                    (lhs, rhs)
                } else {
                    (rhs, lhs)
                };
                if !emitted_pairs.insert(key) {
                    continue;
                }
                let (ref fwd_hints, ref bwd_hints) = edge_hints[edge_idx];
                // Equivalence: lhs = rhs. Emit both implication directions.
                let id_fwd =
                    self.proof_emit_add(&[lhs.negated(), rhs], fwd_hints, ProofAddKind::Derived);
                let id_bwd =
                    self.proof_emit_add(&[lhs, rhs.negated()], bwd_hints, ProofAddKind::Derived);

                // CaDiCaL congruence.cpp:3075: equivalence binaries must be
                // watched clauses in the clause DB for BCP propagation, not just
                // proof emissions. Without this, congruence-derived units fail
                // RUP checks and manual enqueue corrupts solver state (#5107).
                let proof_ids = [id_fwd.unwrap_or(0), id_bwd.unwrap_or(0)];
                for (i, lits) in [[lhs.negated(), rhs], [lhs, rhs.negated()]]
                    .into_iter()
                    .enumerate()
                {
                    let idx = self.arena.add(&lits, false);
                    // Register proof ID so later deletions emit correct LRAT
                    // clause ID (#5005 chain tracking).
                    if self.cold.lrat_enabled && proof_ids[i] != 0 {
                        if idx >= self.cold.clause_ids.len() {
                            self.cold.clause_ids.resize(idx + 1, 0);
                        }
                        self.cold.clause_ids[idx] = proof_ids[i];
                    }
                    let cref = ClauseRef(idx as u32);
                    let mut watched_lits = lits;
                    let watched = self
                        .prepare_watched_literals(&mut watched_lits, WatchOrderPolicy::Preserve)
                        .expect("equivalence binary must expose two watch literals");
                    self.attach_clause_watches(cref, watched, true);
                }
            }
        }

        // Drain level-0 BCP: equivalence binaries may imply units (#5107).
        // Use record_level0_conflict_chain to build proper LRAT hints (#4596).
        if let Some(conflict_ref) = self.search_propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            return false;
        }

        // Mark clause_db as modified so incremental rebuild triggers.
        if !result.equivalence_edges.is_empty() {
            self.cold.inprocessing_modified_clause_db = true;
        }

        // Forward subsumption with equivalence-aware representatives.
        // CaDiCaL congruence.cpp:4955-5073. Must run AFTER proof emission
        // because RUP checks need gate-defining clauses alive.
        //
        // LRAT mode currently lacks the reconstruction/proof plumbing needed
        // for representative-based deletion of irredundant clauses. On
        // manol-pipe-c9 this pass can delete an original clause without a
        // matching reconstruction step, causing SAT finalization to fail
        // closed with InvalidSatModel before the proof checker even reaches
        // the learned-clause bug we are trying to verify (#6270).
        let subsumed = if self.cold.lrat_enabled {
            0
        } else {
            self.inproc
                .congruence
                .forward_subsume_with_equivalences(&mut self.arena, &result.equivalence_edges)
        };
        if subsumed > 0 {
            self.cold.inprocessing_modified_clause_db = true;
        }

        // All clause-level substitution (rewriting, deletion, variable marking,
        // reconstruction entry pushing) is deferred to decompose(), which runs
        // after congruence in the inprocessing pipeline. decompose's SCC finds
        // the equivalences through the binary clauses added above and rewrites
        // ALL clauses uniformly — including reason-protected clauses that
        // replace_clause_checked would skip (#5237).

        true
    }
}
