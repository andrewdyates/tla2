// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Factorization: extension variable compression.

use super::super::mutate::ReasonPolicy;
use super::super::*;
use crate::factor::{FactorResult, FACTOR_SIZE_LIMIT};

const FACTOR_CANDIDATE_FILTER_ROUNDS: usize = 2;

impl Solver {
    // ==================== Factorization (Extension Variable Compression) ====================

    /// Run factorization with growing backoff scheduling.
    ///
    /// Uses growing backoff when unproductive (0 factored clauses): the
    /// interval grows 1.5× per idle call, up to FACTOR_MAX_INTERVAL.
    /// Productive calls reset to base interval.
    pub(in crate::solver) fn factorize(&mut self) {
        let productive = self.factorize_body();
        if productive {
            self.inproc_ctrl
                .factor
                .reschedule(self.num_conflicts, FACTOR_INTERVAL);
        } else {
            self.inproc_ctrl.factor.reschedule_growing(
                self.num_conflicts,
                FACTOR_INTERVAL,
                3,
                2, // 1.5× growth
                FACTOR_MAX_INTERVAL,
            );
        }
    }

    /// Factorization body — early returns are safe; wrapper handles rescheduling.
    ///
    /// Identifies groups of clauses differing in exactly one literal (the "factor")
    /// and introduces fresh extension variables to replace `f*q` clauses with `f+q`.
    ///
    /// Uses an iterative feedback loop: after each pass applies factoring results
    /// to the clause DB, the occ list is rebuilt and a new pass discovers cascading
    /// opportunities from the newly-created divider/quotient clauses. This matches
    /// CaDiCaL's `update_factored` priority-queue re-insertion (factor.cpp:698-748).
    ///
    /// Reference: CaDiCaL `factor.cpp`.
    /// Returns `true` if any clauses were factored.
    /// Must be called at decision level 0.
    fn factorize_body(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        // Skip in incremental mode: factorization introduces extension variables
        // and rewrites clauses, which cannot be reversed across solve boundaries (#5031, #5166).
        if self.cold.has_been_incremental {
            return false;
        }

        // LRAT override handled centrally by inproc_ctrl.with_proof_overrides() (#4557).
        let drat_proof = self.proof_manager.is_some();

        // Compute tick-proportional effort limit (CaDiCaL factor.cpp:962-964).
        // Budget = (search_ticks_delta * factoreffort / 1000) + initial bonus on first call.
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.cold.last_factor_ticks);
        let mut effort = ticks_delta * FACTOR_EFFORT_PERMILLE / 1000;
        if self.cold.factor_rounds == 0 {
            effort = effort.saturating_add(FACTOR_INIT_TICKS);
        }
        let effort = effort.min(FACTOR_MAX_EFFORT);

        // Iterative feedback loop: each pass applies results to the clause DB,
        // then the next pass discovers cascading opportunities from newly-created
        // divider/quotient clauses. Shared effort budget across all passes.
        //
        // CaDiCaL uses incremental occurrence list updates with priority queue
        // re-insertion (factor.cpp:698-748), giving each newly-created clause
        // immediate visibility. Our multi-pass approximation gives each pass the
        // full remaining budget (no geometric decay) and caps the pass count.
        // CaDiCaL: factorcandrounds=2 (options.hpp:119). Z4's multi-pass
        // approximation rebuilds occ lists from scratch each pass, making
        // late passes expensive for diminishing returns. On FmlaEquivChain,
        // 10 passes produced 128 internal rounds for only 10% more factors
        // than CaDiCaL's 2-round approach (13595 vs 12335). Cap at 3 to
        // balance cascading discovery against occ-rebuild overhead (#7399).
        const MAX_FACTOR_PASSES: usize = 3;
        let mut remaining_effort = effort;
        let mut any_completed = false;
        let mut any_factored = false;
        let mut pass_count = 0usize;

        loop {
            // Build occurrence lists from current clause database.
            self.inproc.factor_engine.ensure_num_vars(self.num_vars);
            let occ = self.build_factor_occ();

            // CaDiCaL factor.cpp:118: capture the current BVE elimination
            // bound. Factoring only fires when clause reduction exceeds this
            // bound, ensuring BVE cannot profitably undo the factoring.
            let elim_bound = self.inproc.bve.growth_bound() as i64;

            let factor_config = crate::factor::FactorConfig {
                next_var_id: self.num_vars,
                effort_limit: remaining_effort,
                elim_bound,
            };
            let mut result = self.inproc.factor_engine.run(
                &self.arena,
                &occ,
                &self.vals,
                self.var_lifecycle.as_slice(),
                &factor_config,
            );
            self.consume_factor_candidate_marks(&result.consumed_candidates);

            self.cold.factor_rounds += 1;
            self.cold.factor_factored_total += result.factored_count as u64;
            self.cold.factor_extension_vars_total += result.extension_vars_needed as u64;

            // Validate structured application data against flattened result.
            assert_eq!(
                result.applications.len() + result.self_subsuming.len(),
                result.factored_count
            );
            for app in &result.applications {
                assert_eq!(app.blocked_clause.len(), 1 + app.factors.len());
                assert_eq!(app.divider_clauses.len(), app.factors.len());
                assert!(app.fresh_var.index() < self.num_vars + result.extension_vars_needed);
                assert_eq!(
                    app.to_delete.len(),
                    app.factors.len() * app.quotient_clauses.len()
                );
            }

            // Decrement shared effort budget by candidates consumed this pass.
            remaining_effort =
                remaining_effort.saturating_sub(result.consumed_candidates.len() as u64);

            if result.completed {
                any_completed = true;
            }
            if result.factored_count > 0 {
                any_factored = true;
            }

            if result.factored_count == 0 || remaining_effort == 0 {
                break;
            }

            // Apply this pass's results to the clause DB.
            self.apply_factor_result(&mut result, drat_proof);
            if self.has_empty_clause {
                break;
            }

            // After applying results, the clause DB has new divider/quotient
            // clauses that may create cascading factoring opportunities. Even
            // when `completed == true` (candidate schedule exhausted for THIS
            // pass's occ list), the rebuilt occ list from the new clauses may
            // yield fresh candidates. CaDiCaL discovers cascading opportunities
            // through incremental occ-list updates (factor.cpp:698-748); our
            // multi-pass approximation must rebuild and retry.
            //
            // Only break when no factoring occurred (factored_count == 0, handled
            // above) or when the pass count limit is reached.
            pass_count += 1;
            if pass_count >= MAX_FACTOR_PASSES {
                break;
            }
        }

        self.cold.last_factor_ticks = self.search_ticks[0] + self.search_ticks[1];

        if any_completed {
            self.cold.factor_last_completed_epoch = self.cold.factor_marked_epoch;
        }

        // Report whether any clauses were factored in this call.
        any_factored
    }

    fn build_factor_occ(&self) -> crate::occ_list::OccList {
        // CaDiCaL factor.cpp:factor_mode() keeps all binary clauses but filters
        // larger candidates before building the hot occurrence lists. Clauses
        // containing a literal that appears only once across the remaining
        // binary+large candidate pool cannot participate in factoring, so
        // dropping them shrinks the scans in `find_next_factor` (#7399).
        let mut occ = crate::occ_list::OccList::new(self.num_vars);
        let mut binary_counts = vec![0u32; self.num_vars * 2];
        let mut large_counts = vec![0u32; self.num_vars * 2];
        let mut candidates: Vec<usize> = Vec::new();

        for ci in self.arena.active_indices() {
            if self.arena.is_learned(ci) {
                continue;
            }
            let lits = self.arena.literals(ci);
            match lits.len() {
                2 => {
                    for &lit in lits {
                        binary_counts[lit.index()] += 1;
                    }
                    occ.add_clause(ci, lits);
                }
                3..=FACTOR_SIZE_LIMIT => {
                    candidates.push(ci);
                    for &lit in lits {
                        large_counts[lit.index()] += 1;
                    }
                }
                _ => {}
            }
        }

        if candidates.is_empty() {
            return occ;
        }

        for _ in 0..FACTOR_CANDIDATE_FILTER_ROUNDS {
            let prev_len = candidates.len();
            let mut next_large_counts = vec![0u32; self.num_vars * 2];
            candidates.retain(|&ci| {
                let lits = self.arena.literals(ci);
                let keep = lits
                    .iter()
                    .all(|lit| binary_counts[lit.index()] + large_counts[lit.index()] >= 2);
                if keep {
                    for &lit in lits {
                        next_large_counts[lit.index()] += 1;
                    }
                }
                keep
            });
            large_counts = next_large_counts;
            if candidates.len() == prev_len {
                break;
            }
        }

        for ci in candidates {
            let lits = self.arena.literals(ci);
            occ.add_clause(ci, lits);
        }

        occ
    }

    /// Apply a single factor pass's results to the clause DB.
    fn apply_factor_result(&mut self, result: &mut FactorResult, drat_proof: bool) {
        // Create extension variables (unfrozen, CaDiCaL parity).
        let ext_var_start = self.num_vars;
        for _ in 0..result.extension_vars_needed {
            self.new_var_internal();
        }
        // Bury extension vars in VSIDS: zero activity so search doesn't
        // branch on them before BVE eliminates them.
        // CaDiCaL: factor.cpp:769-839 `adjust_scores_and_phases_of_fresh_variables`.
        for vi in ext_var_start..self.num_vars {
            self.vsids.set_activity(Variable(vi as u32), 0.0);
        }

        // NOTE: CaDiCaL does NOT push reconstruction entries for factored
        // clauses (factor.cpp has no push_clause_on_extension_stack calls).

        if drat_proof {
            // DRAT proof transaction per FactorApplication, following CaDiCaL's
            // factor.cpp:595-663 proof sequence. Order matters for checker:
            //   1. Add divider clauses  (fresh ∨ f_j)        — RAT on fresh
            //   2. Add blocked clause   (¬fresh ∨ ¬f_1 ∨ …)  — RAT on ¬fresh (proof-only)
            //   3. Add quotient clauses (¬fresh ∨ Q_i)       — RUP derivable
            //   4. Delete blocked clause from proof stream
            //   5. Delete original clauses from proof stream + clause DB
            for app in &result.applications {
                #[cfg(debug_assertions)]
                {
                    let num_vars = self.num_vars;
                    let check_proof_clause = |lits: &[Literal], label: &str| {
                        debug_assert!(
                            !lits.is_empty(),
                            "BUG: empty {label} clause in factorization proof"
                        );
                        debug_assert!(
                            lits.iter().all(|l| l.variable().index() < num_vars),
                            "BUG: {label} clause variable out of range \
                             (num_vars={num_vars}): {lits:?}"
                        );
                        let mut codes: Vec<u32> = lits.iter().map(|l| l.0).collect();
                        codes.sort_unstable();
                        debug_assert!(
                            codes.windows(2).all(|w| w[0] != w[1]),
                            "BUG: duplicate literal in {label} clause: {lits:?}"
                        );
                    };
                    for div in &app.divider_clauses {
                        check_proof_clause(div, "divider");
                    }
                    check_proof_clause(&app.blocked_clause, "blocked");
                    for quot in &app.quotient_clauses {
                        check_proof_clause(quot, "quotient");
                    }
                }
                for div in &app.divider_clauses {
                    let _ = self.proof_emit_add(div, &[], ProofAddKind::TrustedTransform);
                }
                let blocked_id = self
                    .proof_emit_add(&app.blocked_clause, &[], ProofAddKind::TrustedTransform)
                    .ok()
                    .filter(|&id| id != 0);
                for quot in &app.quotient_clauses {
                    let _ = self.proof_emit_add(quot, &[], ProofAddKind::TrustedTransform);
                }
                if let Some(blocked_id) = blocked_id {
                    let _ = self.proof_emit_delete(&app.blocked_clause, blocked_id);
                }
            }

            // Self-subsuming proof emissions: resolvents are RUP
            // (derivable from the two complementary parent clauses).
            for app in &result.self_subsuming {
                for resolvent in &app.resolvents {
                    let _ = self.proof_emit_add(resolvent, &[], ProofAddKind::TrustedTransform);
                }
            }

            // Add new clauses to clause DB (no proof emit — already done above).
            for mut lits in std::mem::take(&mut result.new_clauses) {
                self.add_clause_watched(&mut lits);
                if self.has_empty_clause {
                    return;
                }
            }

            // Delete originals from clause DB.
            self.ensure_reason_clause_marks_current();
            for &clause_idx in &result.to_delete {
                self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
            }
        } else {
            // Non-proof path: delete originals first (order doesn't matter).
            self.ensure_reason_clause_marks_current();
            for &clause_idx in &result.to_delete {
                self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
            }

            for mut lits in std::mem::take(&mut result.new_clauses) {
                self.add_clause_watched(&mut lits);
                if self.has_empty_clause {
                    return;
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "factorize_tests.rs"]
mod tests;
