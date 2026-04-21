// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `check()` pipeline for the LRA theory solver.

use super::*;

impl LraSolver {
    pub(super) fn check_impl(&mut self) -> TheoryResult {
        self.check_count += 1;
        let debug = self.debug_lra;
        self.pending_bound_refinements.clear();

        tracing::debug!(
            asserted = self.asserted.len(),
            dirty = self.dirty,
            vars = self.vars.len(),
            rows = self.rows.len(),
            "LRA check"
        );

        // Per-atom unsupported check (#6167): only return Unknown if at least one
        // currently-asserted atom has unsupported sub-expressions. Atoms that are
        // not asserted (e.g., popped or never asserted) don't affect the result.
        let has_asserted_unsupported = !self.persistent_unsupported_atoms.is_empty()
            && self
                .persistent_unsupported_atoms
                .iter()
                .any(|a| self.asserted.contains_key(a));

        if debug {
            safe_eprintln!(
                "[LRA] check() called, dirty={}, persistent_unsupported_atoms={}, asserted_unsupported={}",
                self.dirty,
                self.persistent_unsupported_atoms.len(),
                has_asserted_unsupported,
            );
        }

        if !self.dirty {
            if debug {
                safe_eprintln!("[LRA] Not dirty, returning early");
            }
            if !has_asserted_unsupported {
                // Soundness gate: even on the "not dirty" early-return path,
                // verify all variable values still satisfy their bounds (#6210).
                #[cfg(debug_assertions)]
                self.debug_assert_bounds_satisfied();
            }
            return if has_asserted_unsupported {
                TheoryResult::Unknown
            } else {
                TheoryResult::Sat
            };
        }
        // NOTE: Do NOT clear self.dirty here. If check() returns Unsat and the
        // SAT solver backtracks, we need dirty=true so the next check() re-runs
        // the simplex. Clearing dirty is done below, only on Sat/Unknown paths.
        // See #5537 for the false-SAT bug caused by premature dirty-flag clearing.

        // Snapshot tableau size before atom processing, so we can detect if new
        // rows were added (which requires the simplex to incorporate them).
        self.rows_at_check_start = self.rows.len();

        // Process newly-asserted atoms: parse, assert bounds, collect disequalities.
        let (disequalities, parsed_count, skipped_count) = match self.process_check_atoms(debug) {
            Ok(stats) => (stats.disequalities, stats.parsed_count, stats.skipped_count),
            Err(conflict) => return *conflict,
        };

        // Inject floor axioms for to_int terms (#5944).
        self.inject_to_int_axioms();

        // Run simplex
        if debug {
            safe_eprintln!(
                "[LRA] Atom processing: parsed={}, skipped={}, total_asserted={}, disequalities={}",
                parsed_count,
                skipped_count,
                parsed_count + skipped_count,
                disequalities.len()
            );
            // Approach G diagnostic (#4919): count bounded variables before simplex.
            // Compares against Z3's initial bound count to identify where the gap is.
            let mut free = 0u32;
            let mut lb_only = 0u32;
            let mut ub_only = 0u32;
            let mut both = 0u32;
            for info in self.vars.iter() {
                match (info.lower.is_some(), info.upper.is_some()) {
                    (false, false) => free += 1,
                    (true, false) => lb_only += 1,
                    (false, true) => ub_only += 1,
                    (true, true) => both += 1,
                }
            }
            safe_eprintln!(
                "[LRA] BEFORE simplex (check #{}): free={}, lb_only={}, ub_only={}, both={}, total={}, touched_rows={}",
                self.check_count, free, lb_only, ub_only, both, self.vars.len(), self.touched_rows.len()
            );
        }
        // Simplex-skip optimization (#4919): if no bounds were tightened and no
        // new tableau rows were added during atom processing, the previous simplex
        // solution is still feasible. Skip the full simplex call — the current
        // model is still valid.
        let new_rows_added = self.rows.len() > self.rows_at_check_start;
        let need_simplex = self.bounds_tightened_since_simplex
            || new_rows_added
            || self.trivial_conflict.is_some()
            || !self.last_simplex_feasible;
        // Soundness guard (#6256): when the last simplex returned non-Sat
        // (Unsat/Unknown), variable values may be left in an infeasible state.
        // Re-run simplex instead of skipping so we preserve soundness without
        // blocking DPLL from learning the current conflict (#6209).
        let simplex_result = if need_simplex {
            self.bounds_tightened_since_simplex = false;
            let result = self.dual_simplex();
            self.last_simplex_feasible = matches!(result, TheoryResult::Sat);
            result
        } else {
            // No bounds changed, no new rows, last simplex was feasible.
            if debug {
                safe_eprintln!("[LRA] Skipping simplex: no bounds tightened, no new rows");
            }
            TheoryResult::Sat
        };
        let simplex_is_sat = matches!(simplex_result, TheoryResult::Sat);
        info!(
            target: "z4::lra",
            parsed_count,
            skipped_count,
            disequalities = disequalities.len(),
            vars = self.vars.len(),
            rows = self.rows.len(),
            simplex_sat = simplex_is_sat,
            unsupported_atoms = self.persistent_unsupported_atoms.len(),
            "LRA check"
        );
        if debug {
            safe_eprintln!(
                "[LRA] simplex result: {:?}, unsupported_atoms={}",
                simplex_result,
                self.persistent_unsupported_atoms.len(),
            );
        }

        // Post-simplex: derive implied bounds, wake compound atoms, queue
        // propagations. Must run before disequality checking (#4919).
        if matches!(simplex_result, TheoryResult::Sat) {
            self.run_post_simplex_propagation(need_simplex, debug, false);
        }

        // Recompute has_asserted_unsupported after atom processing (new atoms
        // may have been added to persistent_unsupported_atoms during parsing).
        let has_asserted_unsupported = !self.persistent_unsupported_atoms.is_empty()
            && self
                .persistent_unsupported_atoms
                .iter()
                .any(|a| self.asserted.contains_key(a));

        // If simplex returned Sat, check disequalities
        // IMPORTANT: Only check disequalities when we have complete information.
        // If any asserted atom is unsupported, the model is incomplete (e.g., ITE
        // terms created unconstrained slack variables), so we can't trust the model.
        //
        // Optimization (#4919): skip disequality evaluation when the model is unchanged
        // AND the previous evaluation found all disequalities satisfied. When need_simplex
        // was false AND no new atoms were parsed, the variable values are identical to the
        // previous check() call, so satisfied disequalities remain satisfied.
        //
        // CRITICAL (#4919): if the previous disequality check found a violation (returned
        // NeedDisequalitySplit or NeedExpressionSplit), we MUST re-check even when the model
        // hasn't changed. The violation persists and suppressing it causes false SAT results
        // that fail model validation (sc-6, sc-8, simple_startup_5 benchmarks).
        let model_may_have_changed =
            need_simplex || parsed_count > 0 || self.last_diseq_check_had_violation;
        if matches!(simplex_result, TheoryResult::Sat)
            && !disequalities.is_empty()
            && !has_asserted_unsupported
            && model_may_have_changed
        {
            if let Some(result) = self.check_disequalities(&disequalities, debug) {
                return result;
            }
        }

        // Check shared disequalities from Nelson-Oppen (#5228).
        // These have reason-literal vectors instead of a single atom.
        if matches!(simplex_result, TheoryResult::Sat)
            && !self.shared_disequality_trail.is_empty()
            && !has_asserted_unsupported
        {
            if let Some(result) = self.check_shared_disequalities(debug) {
                return result;
            }
        }

        let mut result = match simplex_result {
            TheoryResult::Sat if has_asserted_unsupported => {
                if debug {
                    safe_eprintln!(
                        "[LRA] Returning Unknown (sat with unsupported): {} unsupported atoms, {} asserted",
                        self.persistent_unsupported_atoms.len(),
                        self.persistent_unsupported_atoms
                            .iter()
                            .filter(|a| self.asserted.contains_key(*a))
                            .count(),
                    );
                }
                TheoryResult::Unknown
            }
            // #6812: When unsupported atoms are asserted, a simplex UNSAT may be
            // spurious — the contradiction could depend on bounds from atoms that
            // LRA cannot fully interpret (e.g., ITE atoms in QF_UFLRA). Converting
            // to Unknown lets the DPLL(T) loop try other Boolean assignments rather
            // than accepting a potentially wrong UNSAT.
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                if has_asserted_unsupported =>
            {
                if debug {
                    safe_eprintln!(
                        "[LRA] Returning Unknown (unsat with unsupported): {} unsupported atoms, {} asserted",
                        self.persistent_unsupported_atoms.len(),
                        self.persistent_unsupported_atoms
                            .iter()
                            .filter(|a| self.asserted.contains_key(*a))
                            .count(),
                    );
                }
                TheoryResult::Unknown
            }
            other => other,
        };
        if matches!(result, TheoryResult::Sat) {
            self.queue_model_seeded_propagations(debug);
            // Collect equality requests from both fixed-term and offset equality mechanisms.
            let mut all_requests = Vec::new();
            if self.pending_fixed_term_equalities.len() > 1 {
                all_requests.extend(self.take_pending_fixed_term_model_equalities());
            }
            if !self.pending_offset_equalities.is_empty() {
                all_requests.extend(self.take_pending_offset_equalities());
            }
            // Model-value equality detection (Z3's assume_eqs): group shared
            // variables by their model value and suggest equalities. This is
            // critical for benchmarks with many equality comparisons (#8901).
            if all_requests.is_empty() {
                let model_eqs = self.discover_model_value_equalities();
                if debug && !model_eqs.is_empty() {
                    safe_eprintln!(
                        "[LRA] assume_eqs: discovered {} model-value equalities",
                        model_eqs.len()
                    );
                }
                all_requests.extend(model_eqs);
            }
            if !all_requests.is_empty() {
                result = if all_requests.len() == 1 {
                    TheoryResult::NeedModelEquality(
                        all_requests
                            .into_iter()
                            .next()
                            .expect("invariant: len() == 1"),
                    )
                } else {
                    TheoryResult::NeedModelEqualities(all_requests)
                };
            }
        }
        if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            // eprintln!("[LRA-DEBUG] check() returning UNSAT/UnsatWithFarkas (simplex passthrough)");
            self.conflict_count += 1;
            // Leave dirty=true so next check() re-runs the simplex after
            // backtrack. Without this, backtrack without pop causes check()
            // to skip the simplex and return false Sat (#5537).
        } else {
            // Sat or Unknown: simplex state is consistent, safe to cache.
            self.dirty = false;
        }

        // Soundness gate: when returning Sat, verify all variable values satisfy
        // their bounds. This catches false-SAT bugs at the point of origin before
        // the result propagates to the DPLL loop. Ref: design doc Gap 1, #6210.
        #[cfg(debug_assertions)]
        if matches!(result, TheoryResult::Sat) {
            self.debug_assert_bounds_satisfied();
        }

        result
    }

    /// Lightweight BCP-time check: run arithmetic consistency and post-simplex
    /// propagation, but defer disequality/model-only work to the final check.
    pub(super) fn check_during_propagate_impl(&mut self) -> TheoryResult {
        self.check_count += 1;
        let debug = self.debug_lra;
        self.pending_bound_refinements.clear();

        let has_asserted_unsupported = !self.persistent_unsupported_atoms.is_empty()
            && self
                .persistent_unsupported_atoms
                .iter()
                .any(|a| self.asserted.contains_key(a));

        if !self.dirty {
            #[cfg(debug_assertions)]
            if !has_asserted_unsupported {
                self.debug_assert_bounds_satisfied();
            }
            return if has_asserted_unsupported {
                TheoryResult::Unknown
            } else {
                TheoryResult::Sat
            };
        }

        self.rows_at_check_start = self.rows.len();

        match self.process_check_atoms_bcp(debug) {
            Ok(_stats) => {}
            Err(conflict) => return *conflict,
        }

        self.inject_to_int_axioms();

        let new_rows_added = self.rows.len() > self.rows_at_check_start;
        let need_simplex = self.bounds_tightened_since_simplex
            || new_rows_added
            || self.trivial_conflict.is_some()
            || !self.last_simplex_feasible;
        // #8901: Reduce BCP simplex budget after many conflicts OR checks.
        // Z3 does NOT run simplex during propagate() — only during
        // final_check_eh(). For equality-heavy benchmarks (simple_startup,
        // sc, uart), running the full simplex budget on every BCP call is
        // wasteful. After enough conflicts OR total BCP checks, use a
        // minimal budget that catches only trivial conflicts (1-2 pivots).
        // Deeper conflicts are deferred to full check().
        // Budget exhaustion already returns Sat (handled by
        // dual_simplex_with_max_iters).
        //
        // SOUNDNESS: only clear bounds_tightened_since_simplex when simplex
        // runs to completion. When budget exhausts (Unknown->Sat), keep the
        // flag TRUE so the full check_impl() will re-run simplex.
        //
        // Two thresholds trigger reduced budget:
        // 1. Conflict-count: after 20 theory conflicts, most useful conflicts
        //    are shallow (1-2 pivots). Deep conflicts can wait for full check.
        // 2. Check-count: after 200 total BCP checks, even without conflicts,
        //    the simplex overhead per call dominates. sc-6 had 7125 checks
        //    with only ~2400 conflicts; the first 100 calls were unbounded.
        const BCP_CONFLICT_THRESHOLD: u64 = 20;
        const BCP_CHECK_COUNT_THRESHOLD: u64 = 200;
        let use_reduced_budget = (self.conflict_count >= BCP_CONFLICT_THRESHOLD
            || self.check_count >= BCP_CHECK_COUNT_THRESHOLD)
            && self.trivial_conflict.is_none();
        let simplex_result = if need_simplex {
            let result = if use_reduced_budget {
                self.bcp_simplex_skips += 1;
                let raw = self.dual_simplex_with_max_iters(10);
                if matches!(raw, TheoryResult::Unknown) {
                    // Budget exhausted — do NOT clear bounds_tightened.
                    TheoryResult::Sat
                } else {
                    self.bounds_tightened_since_simplex = false;
                    self.last_simplex_feasible = matches!(raw, TheoryResult::Sat);
                    raw
                }
            } else {
                self.bounds_tightened_since_simplex = false;
                let r = self.dual_simplex_propagate();
                self.last_simplex_feasible = matches!(r, TheoryResult::Sat);
                r
            };
            result
        } else {
            TheoryResult::Sat
        };

        // #7982: Conflict-based propagation throttle, ported from Z3.
        // Z3 disables bound propagation and equality propagation after
        // m_arith_propagation_threshold (default 1000) conflicts. After many
        // conflicts the theory is exploring deeply and propagation overhead
        // dominates. Simplex still runs for conflict detection (correctness).
        // Reference: Z3 theory_lra.cpp:3315 propagation_mode(),
        //            Z3 smt_params.cpp:314  m_arith_propagation_threshold = 1000.
        //
        // #8901: Dual threshold for BCP propagation throttle.
        // Z3 uses threshold=1000 but does NOT run simplex during BCP — only
        // during final_check_eh(). Since z4 runs both simplex AND bound
        // propagation during BCP, the per-call cost is much higher and the
        // threshold must be lower. We use the same dual-threshold pattern as
        // the simplex budget: disable after either enough conflicts OR enough
        // total BCP checks. Bound propagation still runs at full check_impl().
        const PROPAGATION_CONFLICT_THRESHOLD: u64 = 50;
        const PROPAGATION_CHECK_COUNT_THRESHOLD: u64 = 100;
        let bound_propagation_active = self.conflict_count < PROPAGATION_CONFLICT_THRESHOLD
            && self.check_count < PROPAGATION_CHECK_COUNT_THRESHOLD;

        if matches!(simplex_result, TheoryResult::Sat) {
            if bound_propagation_active {
                self.run_post_simplex_propagation(need_simplex, debug, true);
            } else {
                self.propagation_throttle_skips += 1;
                // Still clear touched_rows tracking so we don't re-enter
                // compute_implied_bounds needlessly on the next call.
                self.propagate_direct_touched_rows_pending = false;
            }
        }

        let has_asserted_unsupported = !self.persistent_unsupported_atoms.is_empty()
            && self
                .persistent_unsupported_atoms
                .iter()
                .any(|a| self.asserted.contains_key(a));

        let result = match simplex_result {
            TheoryResult::Sat if has_asserted_unsupported => TheoryResult::Unknown,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                if has_asserted_unsupported =>
            {
                TheoryResult::Unknown
            }
            other => other,
        };

        let has_deferred_disequalities =
            !self.disequality_trail.is_empty() || !self.shared_disequality_trail.is_empty();
        let has_deferred_full_check_work = has_deferred_disequalities
            || !self.pending_fixed_term_equalities.is_empty()
            || !self.pending_offset_equalities.is_empty();

        if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            self.conflict_count += 1;
        } else {
            // Preserve deferred full-check work: the final check() must revisit
            // skipped disequality/model-equality logic even when the arithmetic
            // state itself is already simplex-feasible.
            self.dirty = has_deferred_full_check_work;
            if has_deferred_disequalities {
                self.last_diseq_check_had_violation = true;
            }
        }

        #[cfg(debug_assertions)]
        if matches!(result, TheoryResult::Sat) {
            self.debug_assert_bounds_satisfied();
        }

        result
    }
}
