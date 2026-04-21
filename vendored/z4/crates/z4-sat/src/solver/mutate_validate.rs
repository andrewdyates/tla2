// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Debug-mode validation helpers for clause mutation invariants.
//!
//! Split from `mutate.rs` for file-size compliance (#5142).
//! Contains `#[cfg(debug_assertions)]` validators for:
//! - Family A: reason clause integrity
//! - Family B: proof system coherence
//! - Family C: reconstruction stack coherence
//! - Watch list invariants

use super::*;

impl Solver {
    /// Debug-only: validate Family A invariant — every reason clause is alive and
    /// contains the variable it explains (CaDiCaL `elim.cpp:440`).
    ///
    /// Called at inprocessing exit to catch dangling reason references early.
    /// This is the central check for #5012 Family A (reason clause protection).
    #[cfg(debug_assertions)]
    pub(super) fn validate_reason_clause_integrity(&self) {
        for &lit in &self.trail {
            let var_idx = lit.variable().index();
            let Some(reason_ref) = self.var_reason(var_idx) else {
                continue; // decision variable — no reason clause
            };
            let ci = reason_ref.0 as usize;

            // Reason clause must have data intact. Clauses marked garbage by
            // eager subsumption (mark_garbage_keep_data) retain their literal
            // data and remain valid reasons — only fully deleted clauses
            // (is_active == false) indicate a dangling reason reference.
            debug_assert!(
                self.arena.is_active(ci),
                "BUG [Family A]: reason clause {ci} for var {var_idx} (trail lit {}) is fully deleted",
                lit.to_dimacs(),
            );
            debug_assert!(
                !self.arena.is_pending_garbage(ci),
                "BUG [Family A]: reason clause {ci} for var {var_idx} (trail lit {}) is pending-garbage",
                lit.to_dimacs(),
            );

            // Reason clause must contain the propagated literal.
            let lits = self.arena.literals(ci);
            debug_assert!(
                lits.iter().any(|&l| l.variable() == lit.variable()),
                "BUG [Family A]: reason clause {ci} for var {var_idx} (trail lit {}) \
                 does not contain variable; clause=[{}]",
                lit.to_dimacs(),
                lits.iter()
                    .map(|l| l.to_dimacs().to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
        }

        // No pending garbage should remain at inprocessing exit.
        debug_assert_eq!(
            self.pending_garbage_count, 0,
            "BUG [Family A]: {} pending-garbage clauses remain at inprocessing exit",
            self.pending_garbage_count,
        );
    }

    /// Debug-only: validate Family C invariant — reconstruction stack coherence.
    ///
    /// For each witness entry, at least one witness literal's variable must
    /// appear in the clause. This is the weakest correct invariant because:
    /// - BVE/BCE entries have a single witness that IS in the clause
    /// - Conditioning entries store the full autarky set (CaDiCaL condition.cpp:787-790)
    ///   which includes variables NOT in the clause, but at least the autarky
    ///   literal that made the clause globally blocked IS in it
    ///
    /// Called at inprocessing exit and SAT finalization to catch reconstruction
    /// stack corruption early. This is the central check for #5012 Family C
    /// (BVE / model reconstruction).
    #[cfg(debug_assertions)]
    pub(super) fn validate_reconstruction_stack(&self) {
        for (i, step) in self.inproc.reconstruction.iter_steps().enumerate() {
            match step {
                crate::reconstruct::ReconstructionStep::Witness(wc) => {
                    // At least one witness literal's variable must appear in the
                    // clause. For BVE/BCE (single witness), this is strict. For
                    // conditioning (full autarky set), the globally-blocking
                    // autarky literal is always in both sets.
                    debug_assert!(
                        wc.witness
                            .iter()
                            .any(|w| wc.clause.iter().any(|&l| l.variable() == w.variable())),
                        "BUG [Family C]: reconstruction step {i}: no witness variable \
                         found in clause; witnesses=[{}], clause=[{}]",
                        wc.witness
                            .iter()
                            .map(|l| l.to_dimacs().to_string())
                            .collect::<Vec<_>>()
                            .join(", "),
                        wc.clause
                            .iter()
                            .map(|l| l.to_dimacs().to_string())
                            .collect::<Vec<_>>()
                            .join(", "),
                    );
                    // Clause and witness must not be empty.
                    debug_assert!(
                        !wc.clause.is_empty(),
                        "BUG [Family C]: reconstruction step {i}: empty clause",
                    );
                    debug_assert!(
                        !wc.witness.is_empty(),
                        "BUG [Family C]: reconstruction step {i}: empty witness",
                    );
                }
                crate::reconstruct::ReconstructionStep::Sweep { num_vars, lit_map } => {
                    debug_assert!(
                        lit_map.len() >= *num_vars * 2,
                        "BUG [Family C]: reconstruction step {i}: sweep lit_map len {} < 2*num_vars {}",
                        lit_map.len(),
                        *num_vars * 2,
                    );
                }
            }
        }
    }

    /// Debug-only: validate that every non-empty clause with 2+ literals has watch entries.
    ///
    /// Called after inprocessing to catch watch list corruption early.
    /// Skips `pending_garbage` clauses: their watches are intentionally lazily removed
    /// during BCP (#4761) and the clauses will be deleted on the next drain pass.
    #[cfg(debug_assertions)]
    pub(super) fn validate_watch_invariants(&self) {
        for ci in self.arena.active_indices() {
            if self.arena.len_of(ci) < 2
                || self.arena.is_garbage(ci)
                || self.arena.is_pending_garbage(ci)
            {
                continue;
            }
            let (lit0, lit1) = self.arena.watched_literals(ci);
            let cref = ClauseRef(ci as u32);

            let has_w0 = (0..self.watches.get_watches(lit0).len())
                .any(|i| self.watches.get_watches(lit0).clause_ref(i) == cref);
            let has_w1 = (0..self.watches.get_watches(lit1).len())
                .any(|i| self.watches.get_watches(lit1).clause_ref(i) == cref);

            debug_assert!(
                has_w0,
                "clause {ci} missing watch on lit0 {}: lits=[{}], learned={}",
                lit0.to_dimacs(),
                self.arena
                    .literals(ci)
                    .iter()
                    .map(|l| l.to_dimacs().to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                self.arena.is_learned(ci),
            );
            debug_assert!(
                has_w1,
                "clause {ci} missing watch on lit1 {}: lits=[{}], learned={}",
                lit1.to_dimacs(),
                self.arena
                    .literals(ci)
                    .iter()
                    .map(|l| l.to_dimacs().to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                self.arena.is_learned(ci),
            );
        }
    }

    /// BISECT ONLY: fast watch validation that panics with the pass name.
    /// Checks all clauses (same as validate_watch_invariants) but includes
    /// the pass label in the panic message to identify the culprit.
    #[cfg(debug_assertions)]
    pub(super) fn bisect_validate_watches(&self, pass: &str) {
        for ci in self.arena.active_indices() {
            if self.arena.len_of(ci) < 2
                || self.arena.is_garbage(ci)
                || self.arena.is_pending_garbage(ci)
            {
                continue;
            }
            let (lit0, lit1) = self.arena.watched_literals(ci);
            let cref = ClauseRef(ci as u32);

            let has_w0 = (0..self.watches.get_watches(lit0).len())
                .any(|i| self.watches.get_watches(lit0).clause_ref(i) == cref);
            let has_w1 = (0..self.watches.get_watches(lit1).len())
                .any(|i| self.watches.get_watches(lit1).clause_ref(i) == cref);

            if !has_w0 {
                panic!(
                    "BISECT[{pass}]: clause {ci} missing watch on lit0 {}: lits=[{}], learned={}",
                    lit0.to_dimacs(),
                    self.arena
                        .literals(ci)
                        .iter()
                        .map(|l| l.to_dimacs().to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    self.arena.is_learned(ci),
                );
            }
            if !has_w1 {
                panic!(
                    "BISECT[{pass}]: clause {ci} missing watch on lit1 {}: lits=[{}], learned={}",
                    lit1.to_dimacs(),
                    self.arena
                        .literals(ci)
                        .iter()
                        .map(|l| l.to_dimacs().to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    self.arena.is_learned(ci),
                );
            }
        }
    }

    /// Debug-only: validate Family B invariant — proof system coherence.
    ///
    /// The solver's clause DB and the proof manager's forward checker must
    /// agree on the live clause set. This is the aggregate check that
    /// complements the per-operation forward checker RUP validation.
    ///
    /// Checks:
    /// 1. No dangling forward-check obligation (`pending_forward_check`)
    /// 2. No LRAT chain verification failures
    /// 3. No proof I/O errors (fail-close pattern)
    /// 4. Forward checker live count ≥ solver irredundant count
    ///    (checker includes both original + derived; solver count excludes
    ///    unit clauses consumed as assignments, so checker ≥ solver is
    ///    the expected relationship)
    ///
    /// This is the central check for #5012 Family B (proof system coherence).
    #[cfg(debug_assertions)]
    pub(super) fn validate_proof_coherence(&self) {
        // 1. No dangling forward-check obligation.
        debug_assert!(
            self.cold.pending_forward_check.is_none(),
            "BUG [Family B]: pending_forward_check={:?} at inprocessing boundary \
             (a proof_emit_add_prechecked was not followed by add_clause_db_checked)",
            self.cold.pending_forward_check,
        );

        // Remaining checks require an active proof manager.
        let Some(ref manager) = self.proof_manager else {
            return;
        };

        // 2. No LRAT chain verification failures.
        let lrat_failures = manager.lrat_failures();
        debug_assert_eq!(
            lrat_failures, 0,
            "BUG [Family B]: {lrat_failures} LRAT chain verification failure(s) detected",
        );

        // 3. No proof I/O errors.
        debug_assert!(
            !manager.has_io_error(),
            "BUG [Family B]: proof I/O error detected at inprocessing boundary",
        );

        // 4. Forward checker live count should be ≥ solver active clause count.
        // The checker sees all originals and derived clauses. We must count
        // only active (non-deleted) clauses in the arena — arena.len() includes
        // deleted clause slots that still occupy offsets. Unit clauses consumed
        // as propagations at level 0 may not be in the checker's clause list
        // (they become assignments), so a small shortfall is acceptable.
        let checker_live = manager.checker_live_clause_count();
        let solver_active = self
            .arena
            .indices()
            .filter(|&i| {
                let off = i;
                !self.arena.is_empty_clause(off) && !self.arena.is_garbage(off)
            })
            .count();
        // Allow a deficit of up to 10% of solver_active or 10 clauses,
        // whichever is larger. This catches gross proof emission gaps (like
        // #4966 where entire HBR clause categories were not emitted).
        let tolerance = (solver_active / 10).max(10);
        assert!(
            solver_active <= checker_live + tolerance,
            "BUG [Family B]: forward checker live count ({checker_live}) \
             is {} below solver active count ({solver_active}); \
             tolerance={tolerance}. This suggests clauses were added to \
             the solver DB without being emitted to the proof stream.",
            solver_active.saturating_sub(checker_live),
        );
    }
}
