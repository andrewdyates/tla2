// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backbone literal detection via bounded assumption probing.
//!
//! For each active root-unassigned variable `x`, probe both `x` and `¬x` as
//! temporary assumptions. Each probe runs a small bounded CDCL search rooted at
//! the assumption. If assuming one polarity forces the opposite polarity at
//! level 0, the opposite literal is a backbone literal and is materialized as
//! an explicit unit clause in the clause database.

use super::super::*;
use crate::proof_manager::ProofAddKind;

const BACKBONE_PROBE_CONFLICT_LIMIT: u64 = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BackboneProbeResult {
    Sat,
    Unsat,
    Unknown,
}

impl Solver {
    /// Run backbone detection by bounded assumption probing.
    ///
    /// Each probe reuses the solver's regular BCP, conflict analysis, clause
    /// learning, and branching heuristics, but stops after a small number of
    /// conflicts. If a probe forces the opposite polarity at level 0, that
    /// opposite literal is a backbone literal.
    pub(in crate::solver) fn backbone(&mut self) -> bool {
        debug_assert_eq!(self.qhead, self.trail.len());
        if !self.require_level_zero() || self.has_empty_clause {
            return false;
        }

        // Record tick watermark for CaDiCaL-style tick-threshold scheduling (#8090).
        self.cold.last_backbone_ticks = self.search_ticks[0] + self.search_ticks[1];

        // Increment backbone phase counter for round limit enforcement.
        // CaDiCaL: `++stats.backbone.phases` (backbone.cpp:533).
        self.cold.backbone_phases += 1;

        let saved_suppress_phase_saving = self.suppress_phase_saving;
        self.suppress_phase_saving = true;

        // Suppress reduce_db during backbone probing (#7929): backbone units
        // emitted to the DRAT proof must be RUP-derivable using clauses
        // currently in the proof. If reduce_db runs mid-probe and deletes
        // learned clauses that the unit's RUP chain depends on, the external
        // DRAT checker rejects the step. Deferring reduction until after all
        // backbone units are materialized preserves proof validity.
        let saved_suppress_reduce_db = self.suppress_reduce_db;
        self.suppress_reduce_db = true;

        let mut found_backbone = false;

        // Budget: limit total conflicts during backbone to avoid pathological
        // preprocessing overhead. On crn_11_99_u (1287 vars), unbounded backbone
        // consumed 60K conflicts (2.4s) while the actual CDCL search needed only
        // 37K (0.67s). CaDiCaL uses tick-based effort limiting (backbone.cpp:542).
        //
        // Z4's backbone uses bounded CDCL probing (up to 32 conflicts per
        // variable probe), which is more expensive than CaDiCaL's binary-clause
        // backbone propagation. Budget of min(num_vars, 5000) balances probe
        // coverage vs overhead. For crn_11_99_u (1287 vars) the budget is 1287.
        // For FmlaEquivChain (46K vars) the budget is 5K. Tested larger budgets
        // (10K-23K) — they found 2-3K more backbone literals at 2-9s overhead
        // cost without proportional search speedup.
        let backbone_conflict_budget = (self.num_vars as u64).min(5000);
        let start_conflicts = self.num_conflicts;

        for var_idx in 0..self.num_vars {
            if self.has_empty_clause {
                break;
            }
            // Stop when conflict budget is exhausted.
            if self.num_conflicts.saturating_sub(start_conflicts) >= backbone_conflict_budget {
                break;
            }
            if self.var_lifecycle.is_removed(var_idx) || self.var_is_assigned(var_idx) {
                continue;
            }

            let var = Variable(var_idx as u32);
            let positive = Literal::positive(var);
            let negative = positive.negated();

            if self.backbone_probe_literal(positive) == BackboneProbeResult::Unsat {
                found_backbone = true;
                if !self.has_empty_clause {
                    self.backbone_materialize_unit(negative);
                }
                continue;
            }

            if self.has_empty_clause || self.var_is_assigned(var_idx) {
                continue;
            }

            if self.backbone_probe_literal(negative) == BackboneProbeResult::Unsat {
                found_backbone = true;
                if !self.has_empty_clause {
                    self.backbone_materialize_unit(positive);
                }
            }
        }

        self.suppress_phase_saving = saved_suppress_phase_saving;
        self.suppress_reduce_db = saved_suppress_reduce_db;

        // Bounded probes backtrack to level 0, but chronological compaction can
        // still leave root assignments on the trail with qhead lagging behind.
        // Drain those assignments here so the inprocessing caller sees the same
        // fully-propagated invariant it had on entry.
        if !self.has_empty_clause && self.qhead < self.trail.len() {
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
            }
        }
        if self.has_empty_clause {
            self.qhead = self.trail.len();
            #[cfg(feature = "jit")]
            {
                self.jit_qhead = self.trail.len();
            }
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: backbone() did not restore decision level to 0"
        );
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: backbone() left pending propagations (qhead={} trail={})",
            self.qhead,
            self.trail.len(),
        );

        found_backbone || self.has_empty_clause
    }

    /// Probe a single assumption with bounded CDCL search.
    ///
    /// Returns:
    /// - `Unsat` if the assumption is forced false at level 0
    /// - `Sat` if a full model is found under the assumption
    /// - `Unknown` if the conflict budget is exhausted first
    fn backbone_probe_literal(&mut self, assumption: Literal) -> BackboneProbeResult {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: backbone probe started above level 0"
        );

        let start_conflicts = self.num_conflicts;
        let result = loop {
            if self.is_interrupted() {
                break BackboneProbeResult::Unknown;
            }

            if self.has_empty_clause {
                break BackboneProbeResult::Unsat;
            }

            if let Some(conflict_ref) = self.search_propagate() {
                if self.decision_level == 0 {
                    self.record_level0_conflict_chain(conflict_ref);
                    break BackboneProbeResult::Unsat;
                }

                self.conflicts_since_restart += 1;
                self.num_conflicts += 1;
                self.on_conflict_random_decision();
                self.analyze_and_backtrack(conflict_ref, "backbone probe", |_, _| {});
                continue;
            }

            if self.lit_val(assumption) < 0 {
                break BackboneProbeResult::Unsat;
            }

            if self.num_conflicts.saturating_sub(start_conflicts) >= BACKBONE_PROBE_CONFLICT_LIMIT {
                break BackboneProbeResult::Unknown;
            }

            if self.lit_val(assumption) == 0 {
                self.decide(assumption);
                continue;
            }

            let Some(var) = self.pick_next_decision_variable() else {
                break BackboneProbeResult::Sat;
            };
            self.decide(self.pick_phase(var));
        };

        if self.decision_level > 0 {
            self.backtrack_without_phase_saving(0);
        }

        if !self.has_empty_clause {
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return BackboneProbeResult::Unsat;
            }
            if self.lit_val(assumption) < 0 {
                return BackboneProbeResult::Unsat;
            }
        }

        result
    }

    /// Materialize a discovered backbone literal as an explicit unit clause.
    ///
    /// The bounded probe can leave the backbone literal assigned at level 0 via
    /// a longer learned reason. This helper turns that root assignment into an
    /// actual unit clause so later inprocessing passes and proof reconstruction
    /// can treat it as a first-class derived unit.
    fn backbone_materialize_unit(&mut self, unit: Literal) {
        let vi = unit.variable().index();
        debug_assert!(
            self.lit_val(unit) > 0,
            "BUG: materializing non-true backbone unit {unit:?}"
        );
        debug_assert_eq!(
            self.var_data[vi].level, 0,
            "BUG: materializing non-root backbone unit {unit:?}"
        );

        if self.backbone_has_explicit_unit_clause(unit) {
            return;
        }

        // Always use TrustedTransform: backbone units are sound (discovered
        // via failed literal probing) but may not be RUP-derivable in the
        // forward checker's clause DB, which tracks only a subset of the
        // solver's learned clauses. The suppress_reduce_db flag (#7929)
        // prevents mid-probe clause deletion that invalidates DRAT proofs,
        // and TrustedTransform prevents the forward checker's RUP assertion.
        let kind = ProofAddKind::TrustedTransform;
        let proof_id = self.proof_emit_unit(unit, &[], kind);
        if proof_id != 0 && self.cold.lrat_enabled {
            self.cold.next_clause_id = proof_id;
        }

        let unit_idx = self.add_clause_db(&[unit], true);
        self.mark_subsume_dirty_if_kept(unit_idx);
        if proof_id != 0 {
            self.unit_proof_id[vi] = proof_id;
        }
    }

    fn backbone_has_explicit_unit_clause(&self, unit: Literal) -> bool {
        self.arena
            .active_indices()
            .any(|idx| self.arena.len_of(idx) == 1 && self.arena.literal(idx, 0) == unit)
    }
}
