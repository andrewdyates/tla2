// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! IMC (Interpolation-based Model Checking) engine for CHC problems.
//!
//! Port of Golem's IMC engine (`reference/golem/src/engine/IMC.cc`) for Z4's
//! `TransitionSystem` abstraction. Part of #1904.
//!
//! MVP scope: single-predicate, linear CHC transition systems only.

use crate::engine_config::ChcEngineConfig;
use crate::engine_result::{build_single_pred_model, skeleton_counterexample};
use crate::engine_utils::{check_sat_with_timeout, search_budget_exhausted};
use crate::interpolant_validation::{
    collect_conjuncts_for_interpolation, is_valid_interpolant_with_check_sat,
    validate_inductive_invariant,
};
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::smt::SmtResult;
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcProblem, ChcSort};
use std::time::{Duration, Instant};

/// IMC solver result (type alias for unified ChcEngineResult).
pub(crate) type ImcResult = crate::engine_result::ChcEngineResult;

/// IMC solver configuration.
///
/// Internal — only `Default::default()` is used in production.
#[derive(Debug, Clone)]
pub struct ImcConfig {
    /// Common engine settings (verbose, cancellation).
    pub base: ChcEngineConfig,
    /// Maximum unrolling depth k (default: 100).
    pub max_k: usize,
    /// Maximum iterations per unrolling depth (default: 100).
    pub max_iters_per_k: usize,
    /// Timeout per SMT query.
    pub query_timeout: Duration,
    /// Total solver timeout.
    pub total_timeout: Duration,
}

impl Default for ImcConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_k: 50,
            max_iters_per_k: 100,
            query_timeout: Duration::from_secs(5),
            total_timeout: Duration::from_secs(30),
        }
    }
}

/// IMC solver.
pub(crate) struct ImcSolver {
    problem: ChcProblem,
    config: ImcConfig,
}

impl Drop for ImcSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl ImcSolver {
    pub(crate) fn new(problem: ChcProblem, config: ImcConfig) -> Self {
        Self { problem, config }
    }

    pub(crate) fn solve(&self) -> ImcResult {
        let start = Instant::now();

        let ts = match TransitionSystem::from_chc_problem(&self.problem) {
            Ok(ts) => ts,
            Err(err) => {
                if self.config.base.verbose {
                    safe_eprintln!("IMC: Not applicable: {}", err);
                }
                return ImcResult::NotApplicable;
            }
        };

        // Sort precheck: IMC interpolation only supports arithmetic sorts (Int, Real).
        // Reject Bool, BitVec, Array, and Uninterpreted sorts early (#1940).
        // The interpolation guard rejects Bool (#5877) and passes BV/Array for
        // portfolio attempts (#5644). IMC's Craig interpolation cannot handle
        // non-arithmetic sorts. The shared guard catches Bool, Uninterpreted;
        // the local guard below catches BitVec as defense-in-depth.
        // Reference: Golem's IMC also rejects arrays (reference/golem/src/engine/IMC.cc:26).
        if let Some(bad_sort) = ts.find_unsupported_interpolation_state_sort() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "IMC: Not applicable: state variable has unsupported sort {}",
                    bad_sort
                );
            }
            return ImcResult::NotApplicable;
        }
        // IMC-local guard: reject Bool and BitVec state sorts. The shared guard
        // now rejects Bool (#5660) but still accepts BitVec. Defense-in-depth — Bool/BV
        // variables produce spurious counterexamples (init AND query SAT check
        // loses initialization constraints for non-arithmetic sorts).
        for var in ts.state_vars() {
            if matches!(&var.sort, ChcSort::Bool | ChcSort::BitVec(_)) {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "IMC: Not applicable: state variable has non-arithmetic sort {}",
                        var.sort
                    );
                }
                return ImcResult::NotApplicable;
            }
        }

        // Precheck: SAT(init ∧ query) => unsafe at depth 0.
        let init_and_query = ChcExpr::and(ts.init.clone(), ts.query.clone());
        let precheck = self.check_sat(&init_and_query);
        if precheck.is_sat() {
            return ImcResult::Unsafe(skeleton_counterexample(&self.problem, 0));
        } else if !precheck.is_unsat() {
            return ImcResult::Unknown;
        }

        let boundary_vars_t1 = ts.state_var_names_at(1);
        let prefix = ts.transition_at(0);

        for k in 1..=self.config.max_k {
            if search_budget_exhausted(&self.config.base, start, self.config.total_timeout) {
                return ImcResult::Unknown;
            }

            let suffix = Self::build_suffix(&ts, k);
            let mut b_constraints = Vec::new();
            collect_conjuncts_for_interpolation(&suffix, &mut b_constraints);
            let b_flat = ChcExpr::and_all(b_constraints.iter().cloned());
            let mut moving_init = ts.init.clone();
            let mut reached = ts.init.clone();

            if self.config.base.verbose {
                safe_eprintln!("IMC: k={} starting", k);
            }

            for _iter in 0..self.config.max_iters_per_k {
                if search_budget_exhausted(&self.config.base, start, self.config.total_timeout) {
                    return ImcResult::Unknown;
                }

                let a = ChcExpr::and(moving_init.clone(), prefix.clone());
                let full = ChcExpr::and(a.clone(), suffix.clone());

                let full_result = self.check_sat(&full);
                if full_result.is_sat() {
                    // Real counterexample only if we started from the true init image.
                    if moving_init == ts.init {
                        return ImcResult::Unsafe(skeleton_counterexample(&self.problem, k));
                    }
                    // Spurious: try larger k.
                    break;
                } else if full_result.is_unknown() {
                    return ImcResult::Unknown;
                }

                // UNSAT: compute interpolant
                let mut a_constraints = Vec::new();
                collect_conjuncts_for_interpolation(&a, &mut a_constraints);

                let itp_t1 = match interpolating_sat_constraints(
                    &a_constraints,
                    &b_constraints,
                    &boundary_vars_t1,
                ) {
                    InterpolatingSatResult::Unsat(i) => i,
                    InterpolatingSatResult::Unknown => break,
                };

                // Validate Craig conditions before using the interpolant.
                let a_flat = ChcExpr::and_all(a_constraints.iter().cloned());
                if !is_valid_interpolant_with_check_sat(
                    &a_flat,
                    &b_flat,
                    &itp_t1,
                    &boundary_vars_t1,
                    |q| self.check_sat(q),
                ) {
                    break;
                }

                let itp = ts.shift_versioned_state_vars(&itp_t1, -1);

                // Fixpoint: if itp ⇒ reached, we're done.
                let itp_and_not_reached = ChcExpr::and(itp.clone(), ChcExpr::not(reached.clone()));
                let fixpoint_result = self.check_sat(&itp_and_not_reached);
                if fixpoint_result.is_unsat() {
                    return self.build_safe_result(&ts, &reached);
                } else if fixpoint_result.is_unknown() {
                    return ImcResult::Unknown;
                }

                moving_init = itp.clone();
                reached = ChcExpr::or(reached, itp);
            }
        }

        ImcResult::Unknown
    }

    fn check_sat(&self, constraint: &ChcExpr) -> SmtResult {
        check_sat_with_timeout(constraint, self.config.query_timeout)
    }

    fn build_suffix(ts: &TransitionSystem, k: usize) -> ChcExpr {
        let mut conjuncts = Vec::new();
        for i in 1..k {
            conjuncts.push(ts.transition_at(i));
        }
        conjuncts.push(ts.query_at(k));
        ChcExpr::and_all(conjuncts)
    }

    fn build_safe_result(&self, ts: &TransitionSystem, reached: &ChcExpr) -> ImcResult {
        let mut inv = reached.clone();

        // If inv intersects query, try strengthening with ¬query.
        let inv_and_query = ChcExpr::and(inv.clone(), ts.query.clone());
        match self.check_sat(&inv_and_query) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            SmtResult::Sat(_) => {
                inv = ChcExpr::and(inv, ChcExpr::not(ts.query.clone()));
            }
            SmtResult::Unknown => return ImcResult::Unknown,
        }

        if validate_inductive_invariant(ts, &inv, |q| self.check_sat(q)).is_some() {
            return ImcResult::Unknown;
        }

        build_single_pred_model(&self.problem, inv).map_or(ImcResult::Unknown, ImcResult::Safe)
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
