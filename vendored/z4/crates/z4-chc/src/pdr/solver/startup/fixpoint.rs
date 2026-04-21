// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Startup fixpoint discovery loop.
//!
//! Runs iterative discovery passes (bounds, equalities, BV ranges, etc.)
//! until frame[1] converges or a small cap is reached.

use super::super::{PdrResult, PdrSolver};

impl PdrSolver {
    /// Run the startup fixpoint discovery loop.
    ///
    /// Forward invariant discovery: find invariants proactively.
    /// This is more efficient than discovering them through blocking.
    ///
    /// STARTUP FIXPOINT LOOP (#1398): Some invariants are only self-inductive once
    /// prerequisite invariants are added to frame[1]. We iterate until convergence
    /// (or a small cap) to allow dependent invariants to be discovered.
    ///
    /// Example (gj2007_m_3): The init equality C=G is only self-inductive after
    /// the prerequisite equality A=B is discovered, because the loop's conditional
    /// update (C' = ite(B >= k*G, C+1, C)) is only a no-op when A=B forces B < k*G.
    ///
    /// The fixpoint loop runs: bounds -> fact conjuncts -> joint bounds -> multi-linear
    /// -> equalities -> error-implied. Error-implied is included because conditional
    /// invariants like (A >= 5*C) => (B = 5*C) often need prerequisite equalities.
    pub(in crate::pdr::solver) fn run_fixpoint_discovery(&mut self) -> Option<PdrResult> {
        let _t_fixpoint = std::time::Instant::now();
        // Adaptive fixpoint depth (#1398): for multi-predicate phase-chains,
        // invariants must propagate hop-by-hop from init to the deepest predicate.
        // A chain of N predicates may need up to N-1 hops. Use max(3, num_preds)
        // so single-predicate problems still use 3 iterations.
        let num_preds = self.problem.predicates().len();
        let max_fixpoint_iters = num_preds.max(3);
        for fixpoint_iter in 0..max_fixpoint_iters {
            let frame1_before = self.frames.get(1).map_or(0, |f| f.lemmas.len());

            // Core discovery passes that can create dependent invariants.
            // Cancellation checks between each pass ensure cooperative timeouts
            // are respected even when individual passes are slow.

            // 1. Bound invariants: basic constraints like E >= 1 from init
            self.discover_bound_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 1a. BV range invariants: extract BV comparison atoms from transition
            // clauses and test inductiveness (#5877). Runs after Int bounds so that
            // any Int-side lemmas are available for mixed-sort problems.
            self.discover_bv_range_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 1a2. BV bit-group invariants (#7044): discover equality, constant,
            // per-bit bound, and ordering invariants over BV groups reconstructed
            // from BvToBool metadata. Runs after BV range invariants.
            if !self.config.bv_bit_groups.is_empty() {
                self.discover_bv_group_equalities();
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
                self.discover_bv_group_constants();
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
                self.discover_bv_group_bit_bounds();
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
                self.discover_bv_group_ordering();
                if self.is_cancelled() {
                    return Some(self.finish_with_result_trace(PdrResult::Unknown));
                }
            }

            // 1b. Edge summary invariants: MBP-projected entry constraints for derived predicates (#1429)
            // This runs after bound invariants so source predicates have frame lemmas to project.
            self.discover_edge_summary_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 2. Promote inductive fact-constraint conjuncts (e.g., three_dots_moving_2)
            self.discover_fact_clause_conjunct_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 3. Bootstrap mutually-inductive lower bounds (e.g., yz_plus_minus_2)
            self.discover_joint_init_shifted_lower_bounds();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 4. Multi-linear invariants via CEX-guided refinement (#1525)
            self.discover_multi_linear_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5. Equality invariants: discovers prerequisites like A=B
            self.discover_equality_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5b. Propagate newly-discovered symbolic equalities to derived predicates (#2248).
            // This enables equalities discovered by discover_equality_invariants() to feed
            // into phase-chain benchmarks where derived predicates need the equality constraint.
            self.propagate_symbolic_equalities_to_derived_predicates();

            // #1402: Cross-predicate invariant propagation (linear head-arg mapping).
            // This runs inside the startup fixpoint loop so propagated prerequisites can
            // enable subsequent discovery passes in the same run.
            let _propagated = self.propagate_frame1_invariants_to_users();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5b2. Difference-bound invariants from self-loop step constants (#1362).
            // For transitions with a stepped variable (a' = a + c) and an unchanged
            // variable (b' = b), generate candidates like `a < b + c`. This discovers
            // relational invariants that standard bound/equality passes miss.
            self.discover_step_difference_bound_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5c. Retry deferred entry-inductive invariants (#5970).
            // After cross-predicate propagation, predecessor frames may now contain
            // upper bounds that enable previously-failed weakened inequalities.
            self.retry_deferred_entry_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 5d. Retry deferred self-inductive invariants with frame strengthening.
            // Invariants like (>= p4 p1) from init may not be independently
            // self-inductive but become inductive relative to other frame lemmas.
            self.retry_deferred_self_inductive_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // 6. Error-implied invariants: conditional invariants from error clauses
            // e.g., (A >= 5*C) => (B = 5*C) needs A=B to be self-inductive
            self.discover_error_implied_invariants();
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }

            // Check convergence
            let frame1_after = self.frames.get(1).map_or(0, |f| f.lemmas.len());
            if frame1_after == frame1_before {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Startup fixpoint converged after {} iteration(s)",
                        fixpoint_iter + 1
                    );
                }
                self.startup_converged = true;
                break;
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Startup fixpoint iter {}: {} -> {} lemmas",
                    fixpoint_iter,
                    frame1_before,
                    frame1_after
                );
            }
            if self.is_cancelled() {
                return Some(self.finish_with_result_trace(PdrResult::Unknown));
            }
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Startup fixpoint loop took {:?}",
                _t_fixpoint.elapsed()
            );
        }

        // Expensive O(n^2) bound passes (scaled difference, sum bounds, loop exit,
        // entry guard) that don't depend on other frame lemmas. Run once here
        // instead of per-fixpoint-iteration to avoid redundant SMT work.
        self.discover_bound_invariants_post_fixpoint();
        if self.is_cancelled() {
            return Some(self.finish_with_result_trace(PdrResult::Unknown));
        }

        None
    }
}
