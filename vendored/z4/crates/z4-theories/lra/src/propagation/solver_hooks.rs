// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Debug-only assertion that all variable values satisfy their current bounds.
    ///
    /// This is the core of design doc Gap 1: verify_model() for the LRA solver.
    /// Called before every Sat return path in check() to catch false-SAT bugs
    /// at their origin, before the result propagates to the DPLL loop.
    ///
    /// Uses InfRational comparison which encodes strict bounds as epsilon offsets:
    ///   non-strict lb: value >= (lb, 0)
    ///   strict lb:     value >= (lb, +1)  i.e. value > lb
    ///   non-strict ub: value <= (ub, 0)
    ///   strict ub:     value <= (ub, -1)  i.e. value < ub
    #[cfg(debug_assertions)]
    pub(crate) fn debug_assert_bounds_satisfied(&self) {
        use num_traits::One;
        for (vi, info) in self.vars.iter().enumerate() {
            if let Some(ref lb) = info.lower {
                let lb_inf = if lb.strict {
                    InfRational::new(lb.value_big(), BigRational::one())
                } else {
                    InfRational::from_rational(lb.value_big())
                };
                debug_assert!(
                    info.value >= lb_inf,
                    "LRA check() false-SAT: var {} value {:?} violates lower bound {} (strict={})",
                    vi,
                    info.value,
                    lb.value,
                    lb.strict
                );
            }
            if let Some(ref ub) = info.upper {
                let ub_inf = if ub.strict {
                    InfRational::new(ub.value_big(), -BigRational::one())
                } else {
                    InfRational::from_rational(ub.value_big())
                };
                debug_assert!(
                    info.value <= ub_inf,
                    "LRA check() false-SAT: var {} value {:?} violates upper bound {} (strict={})",
                    vi,
                    info.value,
                    ub.value,
                    ub.strict
                );
            }
        }
    }

    /// No-op: LRA has no integer learned cuts to replay.
    /// Required by `solve_incremental_split_loop_pipeline!` macro (line 164).
    pub fn replay_learned_cuts(&mut self) {
        // LRA does not accumulate learned cuts (that's LIA's branch-and-bound).
    }

    /// Identity: return self as the LRA solver.
    /// Required by `pipeline_map_incremental_split_conflict_clause!` macro
    /// which calls `$theory.lra_solver().collect_all_bound_conflicts(true)`.
    pub fn lra_solver(&self) -> &Self {
        self
    }

    /// Refresh simplex feasibility for propagate-time row analysis (#6987).
    ///
    /// Z3's `propagate_core()` runs `make_feasible()` before deriving LP-backed
    /// implications (reference/z3/src/smt/theory_lra.cpp:2254). Z4's `propagate()`
    /// was running `compute_implied_bounds()` against a stale basis when BCP
    /// tightened bounds between check() calls.
    ///
    /// Returns `true` when the simplex state is feasible (safe to run row analysis).
    /// Returns `false` when infeasible (caller should skip row analysis and interval
    /// propagation — `check()` will report the actual conflict).
    pub(crate) fn refresh_simplex_for_propagate(&mut self) -> bool {
        if !self.bounds_tightened_since_simplex && self.last_simplex_feasible {
            return true;
        }
        // Bounds were tightened since last simplex — refresh feasibility.
        // Use propagation-time budget (#8003): tighter cap avoids unbounded
        // simplex during propagation. Budget exhaustion → Sat → skip row analysis.
        self.bounds_tightened_since_simplex = false;
        let result = self.dual_simplex_propagate();
        self.last_simplex_feasible = matches!(result, TheoryResult::Sat);
        // Do not package conflicts here — check() owns conflict reporting.
        self.last_simplex_feasible
    }
}
