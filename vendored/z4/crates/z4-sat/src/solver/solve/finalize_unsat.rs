// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UNSAT declaration and proof finalization.
//!
//! Centralizes UNSAT proof output: empty clause emission, LRAT chain
//! verification, and the `declare_unsat` / `declare_unsat_assume` API
//! methods.

use super::super::*;
use crate::kani_compat::det_hash_set_new;
use crate::solver_log::solver_log;

impl Solver {
    /// Finalize UNSAT proof by writing the empty clause
    ///
    /// This method centralizes UNSAT proof finalization. All UNSAT return sites
    /// MUST call this method before returning `SatResult::Unsat`.
    ///
    /// # DRAT/LRAT format
    ///
    /// The empty clause (`0`) marks the final derivation of contradiction in
    /// DRAT/LRAT proofs. External proof checkers (e.g., drat-trim) require
    /// this to validate the proof is complete.
    ///
    /// # Debug verification
    ///
    /// Declare the formula unsatisfiable: emit the TLA+ trace step,
    /// finalize the DRAT/LRAT proof, and return `SatResult::Unsat`.
    ///
    /// This is the UNSAT counterpart to [`declare_sat_from_current_assignment`].
    #[inline]
    pub(in crate::solver) fn declare_unsat(&mut self) -> SatResult {
        if self.cold.trace_ext_conflict {
            eprintln!(
                "[DECLARE_UNSAT] conflicts={} decisions={} dl={} has_empty_clause={} trail_len={}",
                self.num_conflicts,
                self.num_decisions,
                self.decision_level,
                self.has_empty_clause,
                self.trail.len()
            );
            // Print the trail
            for (i, &lit) in self.trail.iter().enumerate() {
                let var = lit.variable();
                let level = self.var_data[var.index()].level;
                eprintln!(
                    "[DECLARE_UNSAT]   trail[{}]: var={} pos={} level={}",
                    i,
                    var.index(),
                    lit.is_positive(),
                    level
                );
            }
        }
        self.tla_trace_step("UNSAT", Some("DeclareUnsat"));
        self.finalize_unsat_proof();
        let proof_steps = self
            .proof_manager
            .as_ref()
            .map_or(0, ProofManager::added_count);
        solver_log!(
            self,
            "UNSAT: {} conflicts, {} decisions, {} proof steps",
            self.num_conflicts,
            self.num_decisions,
            proof_steps
        );
        tracing::info!(
            num_conflicts = self.num_conflicts,
            num_decisions = self.num_decisions,
            proof_steps,
            "solve: unsat"
        );
        self.emit_diagnostic_unsat_summary();
        SatResult::Unsat
    }

    /// Run backward LRAT proof reconstruction (#8105, primary path).
    ///
    /// This is the PRIMARY LRAT proof path. After the solver determines UNSAT,
    /// this method walks the clause dependency graph backward from the empty
    /// clause and produces proof steps for only the reachable learned clauses.
    ///
    /// With forward chain collection removed from the conflict analysis hot
    /// path (#8105), this backward reconstruction is the sole source of LRAT
    /// hint information. The forward path emits no additions during solving
    /// (IDs are reserved but not written), and this method writes the actual
    /// LRAT addition lines with proper hints.
    fn run_backward_proof_reconstruction(&mut self) {
        if !self.cold.lrat_enabled {
            return;
        }
        let backward = self.reconstruct_lrat_backward();
        tracing::info!(
            steps = backward.steps.len(),
            complete = backward.complete,
            "backward LRAT proof reconstruction (primary path)"
        );

        // Write backward-reconstructed steps to the proof file.
        // Steps are in emission order (reverse topological: deepest deps first).
        // The last step is the empty clause, which we skip here -- finalize_unsat_proof
        // writes the empty clause separately via mark_empty_clause_with_hints.
        if let Some(ref mut manager) = self.proof_manager {
            for step in &backward.steps {
                // Skip the empty clause step (clause_id == 0, empty literals).
                // The finalize_unsat_proof path handles empty clause emission.
                if step.literals.is_empty() {
                    continue;
                }
                let _ = manager.emit_backward_step(step.clause_id, &step.literals, &step.hints);
            }
        }
    }

    /// In debug builds, this method verifies that at least one clause was added
    /// to the proof (the empty clause itself). This catches bugs where UNSAT is
    /// returned without proper proof derivation. For full external verification,
    /// use `Solver::with_proof()` and verify with drat-trim.
    pub(in crate::solver) fn finalize_unsat_proof(&mut self) {
        // Run backward proof reconstruction alongside the forward path (#8072).
        // This is diagnostic-only during the transition phase — the forward path
        // still produces the actual LRAT proof output.
        self.run_backward_proof_reconstruction();

        // Keep ClauseTrace's UNSAT marker consistent with UNSAT returns even when
        // the solver exits at decision level 0 without explicitly learning/adding
        // an empty clause. This is required for SMT-level proof reconstruction.
        if let Some(ref mut trace) = self.cold.clause_trace {
            trace.mark_empty();
        }

        if self.proof_manager.is_some() || self.cold.forward_checker.is_some() {
            if let Some(ref mut manager) = self.proof_manager {
                manager.clear_last_add();
            }
            // Write empty clause to indicate final derivation of contradiction,
            // unless mark_empty_clause already wrote it (#4123).
            if !self.cold.empty_clause_in_proof {
                // In LRAT mode, build hints for the empty clause from
                // level-0 trail state (#7108). Without hints, external LRAT
                // checkers reject the empty clause derivation.
                #[allow(unused_mut)] // mut needed in debug builds for assumption hint prepend
                let mut hints = if self.cold.lrat_enabled {
                    self.ensure_level0_unit_proof_ids();
                    self.build_finalize_empty_clause_hints()
                } else {
                    Vec::new()
                };
                #[cfg(debug_assertions)]
                for &axiom_id in &self.cold.scope_selector_axiom_ids {
                    if axiom_id != 0 && !hints.contains(&axiom_id) {
                        hints.push(axiom_id);
                    }
                }
                self.mark_empty_clause_with_hints(&hints);
            }
        }
        if let Some(ref mut manager) = self.proof_manager {
            let _ = manager.flush();

            // Detect silently truncated proofs caused by I/O errors during solve.
            // Without this check, a disk-full or broken-pipe produces a corrupted
            // proof that drat-trim rejects with no diagnosis path back to the solver.
            // The I/O error state is tracked internally (CaDiCaL-style) — call sites
            // use `let _ =` to avoid aborting mid-solve, but the error is captured.
            assert!(
                !manager.has_io_error(),
                "BUG: proof I/O failed during solve - proof stream is truncated/corrupted"
            );

            // Verify proof has at least the empty clause.
            // For trivial UNSAT (e.g., x AND NOT x), the empty clause alone is valid.
            // For non-trivial UNSAT, learned clauses + empty clause form the proof.
            // Full external verification (drat-trim) is done in integration tests.
            // Always-on: checking a counter is O(1) and catching a missing empty clause
            // prevents producing a structurally invalid proof.
            // Note: added_count() only counts successful writes, so this also catches
            // cases where the empty clause write itself failed.
            // Check LRAT chain verifier for accumulated failures (#4172).
            // In debug builds, individual failures fire debug_assert! at each
            // emit_add call. This post-solve check is defense-in-depth: if any
            // failure was somehow swallowed, catch it here.
            let lrat_fail_count = manager.lrat_failures();
            if lrat_fail_count > 0 {
                tracing::error!(
                    failures = lrat_fail_count,
                    "LRAT chain verifier detected failures during solve"
                );
                debug_assert!(
                    lrat_fail_count == 0,
                    "BUG: LRAT chain verifier detected {lrat_fail_count} failures during solve"
                );
            }

            // Post-UNSAT derivation chain integrity check (#5005).
            // Walks backward from the empty clause through all LRAT hint
            // references, verifying they form a valid chain terminating at
            // original (axiom) clauses. Always-on in both debug and release.
            // verify_unsat_chain asserts internally if the chain is invalid.
            manager.verify_unsat_chain();

            let added = manager.added_count();
            tracing::debug!(
                proof_steps = added,
                empty_clause_written = self.cold.empty_clause_in_proof,
                lrat_mode = manager.is_lrat(),
                "proof: finalization complete"
            );

            if !manager.lrat_blocked_by_theory_lemmas() {
                assert!(
                    added >= 1,
                    "BUG: UNSAT proof finalization failed - empty clause not written"
                );
            }

            // Always-on structural chain integrity check (#5005).
            // Verifies LRAT ID tracking is consistent after proof finalization.
            manager.verify_unsat_chain();
        }
    }

    /// Build LRAT hints for the empty clause when `finalize_unsat_proof`
    /// reaches the fallback path (no prior `mark_empty_clause_with_hints`).
    ///
    /// Strategy: find a clause in the arena that is falsified under the current
    /// level-0 assignment and use `collect_resolution_chain` to build the full
    /// derivation chain. If no falsified clause is found (shouldn't happen for
    /// a genuine UNSAT), fall back to collecting all level-0 unit proof IDs.
    pub(in crate::solver) fn build_finalize_empty_clause_hints(&mut self) -> Vec<u64> {
        use crate::watched::ClauseRef;

        // Strategy 1: find a falsified clause and build resolution chain.
        let mut falsified_ref = None;
        for offset in self.arena.active_indices() {
            let lits = self.arena.literals(offset);
            if !lits.is_empty() && lits.iter().all(|lit| self.lit_val(*lit) < 0) {
                falsified_ref = Some(ClauseRef(offset as u32));
                break;
            }
        }
        if let Some(seed) = falsified_ref {
            // NOTE: W23 (293e96bd5) added a collect_forward_bcp_lrat_hints()
            // call for non-root trails, but the method definition was never
            // committed. Fall through to collect_resolution_chain for all
            // cases until the missing method is implemented (#7175).
            let chain = self.collect_resolution_chain(seed, None, &det_hash_set_new());
            return Self::lrat_reverse_hints(&chain);
        }

        // Strategy 2: collect all level-0 unit proof IDs.
        // Every level-0 trail variable with a unit_proof_id contributes a hint.
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        let mut hints = Vec::new();
        for i in 0..level0_end {
            let vi = self.trail[i].variable().index();
            if let Some(id) = self.visible_unit_proof_id_of_var_index(vi) {
                hints.push(id);
            } else if let Some(id) = self.level0_var_proof_id(vi) {
                hints.push(id);
            }
        }
        hints
    }

    /// Declare UNSAT for assumption-based solving, returning the given unsat core.
    ///
    /// Parallel to [`declare_unsat()`] but returns [`AssumeResult::Unsat`].
    /// Includes TLA tracing and proof finalization.
    #[inline]
    pub(in crate::solver) fn declare_unsat_assume(&mut self, core: Vec<Literal>) -> AssumeResult {
        self.tla_trace_step("UNSAT", Some("DeclareUnsat"));
        self.finalize_unsat_proof();
        self.emit_diagnostic_unsat_summary();
        AssumeResult::Unsat(core)
    }
}
