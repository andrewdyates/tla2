// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Predicate propagation for IC3 backward analysis.
//!
//! rIC3's `PredProp` module (127 LOC) provides an alternative bad-state
//! discovery mechanism. Instead of the standard forward `get_bad()` which asks
//! "is there a bad state reachable in F_k?", predicate propagation constructs
//! a *backward* solver that asks "what states can reach a bad state in one
//! transition step?".
//!
//! The backward solver adds `!bad` as a constraint to the transition system,
//! then checks whether there exist states whose successors violate the property.
//! This complements forward IC3: benchmarks with small backward reachable sets
//! converge faster with predprop even when forward IC3 struggles.
//!
//! Reference: rIC3 `ic3/predprop.rs` — `PredProp` struct.
//! Reference: rIC3 `ic3/block.rs:87-125` — `pred_prop_get_bad()`.

use crate::sat_types::{Lit, SatResult, SatSolver, Var};
use crate::transys::Transys;
use rustc_hash::FxHashMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// Backward analysis solver for predicate propagation.
///
/// Encodes: Trans(s, s') AND bad(s') AND !bad(s) AND constraints.
/// A SAT result yields a state `s` that is NOT bad itself but whose successor
/// IS bad — the "one-step predecessor of bad" that standard `get_bad()` would
/// find at the top frame.
///
/// Unlike standard `get_bad()` which queries `F_k AND bad`, predprop queries
/// the transition relation directly, bypassing the frame approximation. This
/// finds bad predecessors that frame-based analysis might miss when frames are
/// too coarse.
///
/// The solver is periodically rebuilt (via `rebuild()`) to incorporate new
/// lemmas from IC3's infinity frame. This mirrors rIC3's `predprop.extend()`
/// which reconstructs the backward solver on each frame extension.
pub(crate) struct PredPropSolver {
    /// Backward analysis solver encoding Trans AND bad' AND !bad AND constraints.
    solver: Box<dyn SatSolver>,
    /// Bad-state literals to assume during solving.
    bad_assumptions: Vec<Lit>,
    /// Current-state latch variables for extracting predecessor cubes.
    latch_vars: Vec<Var>,
    /// Internal signal variables (if enabled).
    internal_signals: Vec<Var>,
    /// Accumulated lemmas (as clauses) added to the backward solver.
    /// Stored so that `rebuild()` can reconstruct the solver from scratch
    /// with all previously learned constraints.
    accumulated_lemmas: Vec<Vec<Lit>>,
    /// Solver backend for reconstruction.
    solver_backend: crate::sat_types::SolverBackend,
    /// Maximum variable index for solver allocation.
    max_var: u32,
    /// Cached transition relation clauses for rebuild.
    trans_clauses_cache: Vec<Vec<Lit>>,
    /// Cached next-link clauses for rebuild.
    next_link_clauses_cache: Vec<Vec<Lit>>,
    /// Cached constraint literals for rebuild.
    constraint_lits_cache: Vec<Lit>,
    /// Cached negated bad literals (current-state) for rebuild.
    neg_bad_lits_cache: Vec<Lit>,
    /// Cancellation flag for cooperative shutdown.
    cancelled: Option<Arc<AtomicBool>>,
}

impl PredPropSolver {
    /// Build a new predicate propagation solver from the transition system.
    ///
    /// Encodes:
    /// 1. Transition relation clauses
    /// 2. Next-state linking (next_var <=> next_expr)
    /// 3. Bad property on NEXT-state variables (bad(s'))
    /// 4. Negated bad on CURRENT-state variables (!bad(s)) — prevents trivial solutions
    /// 5. Constraints on current state
    pub(crate) fn new(
        ts: &Transys,
        next_vars: &FxHashMap<Var, Var>,
        max_var: u32,
        next_link_clauses: &[Vec<Lit>],
        solver_backend: crate::sat_types::SolverBackend,
    ) -> Self {
        // Cache the base formula for rebuild().
        let trans_clauses_cache: Vec<Vec<Lit>> =
            ts.trans_clauses.iter().map(|c| c.lits.clone()).collect();
        let next_link_clauses_cache: Vec<Vec<Lit>> = next_link_clauses.to_vec();
        let constraint_lits_cache: Vec<Lit> = ts.constraint_lits.clone();
        let neg_bad_lits_cache: Vec<Lit> = ts.bad_lits.iter().map(|&l| !l).collect();

        // IC3 predprop solver: full IC3 mode (#4306 Patch B, #4102).
        // The predprop solver participates in the same IC3 driver loop as
        // the frame solvers, so it shares the short-incremental-query shape
        // and benefits equally from the per-query reset savings.
        let mut solver = solver_backend.make_solver_ic3_mode(max_var);

        // Constant variable: Var(0) = false.
        solver.add_clause(&[Lit::TRUE]);

        // Transition relation.
        for clause in &trans_clauses_cache {
            solver.add_clause(clause);
        }

        // Next-state linking.
        for clause in &next_link_clauses_cache {
            solver.add_clause(clause);
        }

        // Constraints on current state.
        for &constraint in &constraint_lits_cache {
            solver.add_clause(&[constraint]);
        }

        // !bad on current state — prevents finding states that are themselves bad.
        // We want predecessors of bad, not bad states themselves.
        for &neg_bad in &neg_bad_lits_cache {
            solver.add_clause(&[neg_bad]);
        }

        // Build bad assumptions on next-state variables.
        // bad(s') means: for each bad literal, substitute current vars with next vars.
        let bad_assumptions: Vec<Lit> = ts
            .bad_lits
            .iter()
            .filter_map(|&bad_lit| {
                let var = bad_lit.var();
                // If the bad literal references a latch variable, map to its next-state var.
                if let Some(&next_var) = next_vars.get(&var) {
                    Some(if bad_lit.is_positive() {
                        Lit::pos(next_var)
                    } else {
                        Lit::neg(next_var)
                    })
                } else {
                    // Bad literal references a non-latch variable (input, AND gate).
                    // Keep as-is since these are combinational and shared between
                    // current and next state in the transition formula.
                    Some(bad_lit)
                }
            })
            .collect();

        PredPropSolver {
            solver,
            bad_assumptions,
            latch_vars: ts.latch_vars.clone(),
            internal_signals: ts.internal_signals.clone(),
            accumulated_lemmas: Vec::new(),
            solver_backend,
            max_var,
            trans_clauses_cache,
            next_link_clauses_cache,
            constraint_lits_cache,
            neg_bad_lits_cache,
            cancelled: None,
        }
    }

    /// Query the backward solver for a predecessor of bad.
    ///
    /// Returns `Some(cube)` where `cube` is a current-state assignment that
    /// leads to a bad successor in one step, or `None` if no such state exists
    /// (meaning the property is one-step inductive from the current constraints).
    pub(crate) fn get_bad_predecessor(&mut self, use_internal_signals: bool) -> Option<Vec<Lit>> {
        let result = self.solver.solve(&self.bad_assumptions);
        if result != SatResult::Sat {
            return None;
        }

        // Extract predecessor state from current-state latch variables.
        let mut cube = Vec::new();
        for &latch_var in &self.latch_vars {
            let pos = Lit::pos(latch_var);
            match self.solver.value(pos) {
                Some(true) => cube.push(pos),
                Some(false) => cube.push(Lit::neg(latch_var)),
                None => {}
            }
        }

        // Include internal signals if configured.
        if use_internal_signals {
            for &isig_var in &self.internal_signals {
                let pos = Lit::pos(isig_var);
                match self.solver.value(pos) {
                    Some(true) => cube.push(pos),
                    Some(false) => cube.push(Lit::neg(isig_var)),
                    None => {}
                }
            }
        }

        Some(cube)
    }

    /// Add a blocking lemma to the backward solver.
    ///
    /// When IC3 blocks a cube at some frame, predprop should also learn this:
    /// the negated cube (as a clause) constrains the backward solver so it
    /// doesn't rediscover the same predecessor pattern.
    ///
    /// The lemma is also stored in `accumulated_lemmas` so that `rebuild()`
    /// can reconstruct the solver with all learned constraints.
    pub(crate) fn add_lemma(&mut self, lemma_lits: &[Lit]) {
        self.solver.add_clause(lemma_lits);
        self.accumulated_lemmas.push(lemma_lits.to_vec());
    }

    /// Set the cancellation flag for cooperative shutdown.
    pub(crate) fn set_cancelled(&mut self, cancelled: Arc<AtomicBool>) {
        self.solver.set_cancelled(cancelled.clone());
        self.cancelled = Some(cancelled);
    }

    /// Rebuild the backward solver from scratch with all accumulated lemmas.
    ///
    /// Called on frame extension and periodic solver rebuild to clear learned
    /// clause bloat and re-synchronize with IC3's current lemma set.
    ///
    /// This mirrors rIC3's `predprop.extend(inf_lemmas)` which reconstructs
    /// the backward TransysSolver on each frame extension.
    ///
    /// Optionally accepts additional lemmas (e.g., infinity frame lemmas from
    /// the IC3 engine) to add on top of the accumulated lemmas.
    pub(crate) fn rebuild(&mut self, extra_lemmas: &[Vec<Lit>]) {
        // Full IC3 mode — see constructor for rationale (#4306 Patch B).
        let mut solver = self.solver_backend.make_solver_ic3_mode(self.max_var);

        // Constant variable.
        solver.add_clause(&[Lit::TRUE]);

        // Base formula: Trans + next-linking + constraints + !bad.
        for clause in &self.trans_clauses_cache {
            solver.add_clause(clause);
        }
        for clause in &self.next_link_clauses_cache {
            solver.add_clause(clause);
        }
        for &constraint in &self.constraint_lits_cache {
            solver.add_clause(&[constraint]);
        }
        for &neg_bad in &self.neg_bad_lits_cache {
            solver.add_clause(&[neg_bad]);
        }

        // Re-add all accumulated lemmas.
        for lemma in &self.accumulated_lemmas {
            solver.add_clause(lemma);
        }

        // Add extra lemmas (e.g., infinity frame lemmas).
        for lemma in extra_lemmas {
            solver.add_clause(lemma);
        }

        // Wire cancellation flag.
        if let Some(ref cancelled) = self.cancelled {
            solver.set_cancelled(cancelled.clone());
        }

        self.solver = solver;
    }

    /// Return the number of accumulated lemmas for diagnostics.
    pub(crate) fn lemma_count(&self) -> usize {
        self.accumulated_lemmas.len()
    }

    /// Update the solver backend (e.g., after fallback from z4-sat to SimpleSolver).
    /// The next `rebuild()` call will use the new backend.
    pub(crate) fn set_solver_backend(&mut self, backend: crate::sat_types::SolverBackend) {
        self.solver_backend = backend;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;
    use crate::transys::Transys;

    #[test]
    fn test_predprop_toggle_finds_predecessor() {
        // Toggle circuit: latch starts at 0, next = NOT latch, bad = latch.
        // State 0 (latch=0) transitions to state 1 (latch=1) which is bad.
        // PredProp should find state 0 as a predecessor of bad.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::default(),
        );

        let pred = pp.get_bad_predecessor(false);
        assert!(pred.is_some(), "predprop should find a predecessor of bad");
        let cube = pred.expect("predecessor exists");
        // The predecessor of bad (latch=1) is latch=0 (which negates to NOT latch).
        assert!(
            !cube.is_empty(),
            "predecessor cube should have at least one literal"
        );
    }

    #[test]
    fn test_predprop_safe_circuit_no_predecessor() {
        // Safe circuit: latch stays at 0, bad = latch. No predecessor of bad exists
        // because no state can transition to latch=1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::default(),
        );

        let pred = pp.get_bad_predecessor(false);
        assert!(
            pred.is_none(),
            "safe circuit should have no predecessor of bad"
        );
    }

    #[test]
    fn test_predprop_add_lemma_blocks_predecessor() {
        // Toggle circuit. After finding the predecessor, add a blocking lemma
        // and verify it's no longer found.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::default(),
        );

        // First query: should find predecessor.
        let pred = pp.get_bad_predecessor(false);
        assert!(pred.is_some(), "should find predecessor before lemma");

        // Add a blocking lemma that negates the predecessor cube.
        let cube = pred.expect("exists");
        let negated: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        pp.add_lemma(&negated);

        // Second query: predecessor should be blocked.
        let pred2 = pp.get_bad_predecessor(false);
        assert!(pred2.is_none(), "predecessor should be blocked after lemma");
    }

    #[test]
    fn test_predprop_rebuild_preserves_lemmas() {
        // Toggle circuit: after adding a blocking lemma and rebuilding,
        // the lemma should still be effective.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::default(),
        );

        // Find predecessor and block it.
        let pred = pp.get_bad_predecessor(false);
        assert!(pred.is_some(), "should find predecessor initially");
        let cube = pred.expect("exists");
        let negated: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        pp.add_lemma(&negated);
        assert_eq!(pp.lemma_count(), 1);

        // Rebuild from scratch (simulating frame extension).
        pp.rebuild(&[]);

        // After rebuild, the lemma should still block the predecessor.
        let pred_after = pp.get_bad_predecessor(false);
        assert!(
            pred_after.is_none(),
            "predecessor should still be blocked after rebuild"
        );
        assert_eq!(pp.lemma_count(), 1, "lemma count preserved after rebuild");
    }

    #[test]
    fn test_predprop_rebuild_with_extra_lemmas() {
        // Toggle circuit: rebuild with extra lemmas (simulating infinity frame).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::default(),
        );

        // Find predecessor first.
        let pred = pp.get_bad_predecessor(false);
        assert!(pred.is_some(), "should find predecessor initially");
        let cube = pred.expect("exists");
        let negated: Vec<Lit> = cube.iter().map(|l| !*l).collect();

        // Rebuild with the blocking lemma as an "extra" (infinity frame lemma).
        pp.rebuild(&[negated]);

        // After rebuild with extra lemma, predecessor should be blocked.
        let pred_after = pp.get_bad_predecessor(false);
        assert!(
            pred_after.is_none(),
            "predecessor should be blocked by extra lemma after rebuild"
        );
    }

    #[test]
    fn test_predprop_sequential_rebuilds_preserve_lemmas() {
        // Verify that accumulated lemmas persist across multiple consecutive
        // rebuilds — simulates IC3's repeated frame extensions where each
        // extension triggers a predprop rebuild (run.rs:508).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::default(),
        );

        // Find and block predecessor.
        let pred = pp.get_bad_predecessor(false);
        assert!(pred.is_some(), "should find predecessor initially");
        let cube = pred.unwrap();
        let negated: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        pp.add_lemma(&negated);
        assert_eq!(pp.lemma_count(), 1);

        // Rebuild 1: simulating first frame extension.
        pp.rebuild(&[]);
        assert_eq!(pp.lemma_count(), 1, "lemma count after rebuild 1");
        assert!(
            pp.get_bad_predecessor(false).is_none(),
            "blocked after rebuild 1"
        );

        // Rebuild 2: simulating second frame extension.
        pp.rebuild(&[]);
        assert_eq!(pp.lemma_count(), 1, "lemma count after rebuild 2");
        assert!(
            pp.get_bad_predecessor(false).is_none(),
            "blocked after rebuild 2"
        );

        // Rebuild 3: simulating third frame extension with extra lemmas.
        // Extra lemma is a tautology (just ensures the extra path works
        // alongside accumulated lemmas).
        let extra = vec![Lit::TRUE]; // clause [TRUE] is always satisfied
        pp.rebuild(&[extra]);
        assert_eq!(pp.lemma_count(), 1, "accumulated count unchanged by extras");
        assert!(
            pp.get_bad_predecessor(false).is_none(),
            "blocked after rebuild 3 with extras"
        );
    }

    #[test]
    fn test_predprop_accumulated_plus_extra_lemmas_combined() {
        // Verifies the pattern from engine.rs:744-748 where rebuild() is called
        // with infinity frame lemmas as extras on top of accumulated lemmas.
        // Both accumulated and extra lemmas must be active in the rebuilt solver.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::Simple,
        );

        // Add accumulated lemma (blocking clause from frame blocking).
        let pred = pp.get_bad_predecessor(false);
        assert!(pred.is_some(), "should find predecessor initially");
        let cube = pred.unwrap();
        let negated: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        pp.add_lemma(&negated.clone());
        assert_eq!(pp.lemma_count(), 1);

        // Verify blocked before rebuild.
        assert!(
            pp.get_bad_predecessor(false).is_none(),
            "blocked before rebuild"
        );

        // Rebuild with the same clause as an extra lemma (simulating it
        // appearing in the infinity frame). This is redundant but exercises
        // the code path where both accumulated and extra lemmas contain
        // the blocking constraint.
        pp.rebuild(&[negated]);

        // Both paths should keep the predecessor blocked.
        assert!(
            pp.get_bad_predecessor(false).is_none(),
            "blocked after rebuild with accumulated + extra"
        );
        // Accumulated count should not include extras.
        assert_eq!(pp.lemma_count(), 1, "extra lemmas not in accumulated count");
    }

    #[test]
    fn test_predprop_backend_switch_preserves_lemmas() {
        // Simulates the fallback_solver_backend() pattern from engine.rs:956-991:
        // set_solver_backend(Simple) then rebuild(). This is the recovery path
        // when z4-sat produces persistent FINALIZE_SAT_FAIL errors.
        //
        // Key invariant: accumulated lemmas survive the backend switch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        // Start with default backend (Z4Sat in production, Simple in tests).
        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::default(),
        );

        // Add a blocking lemma.
        let pred = pp.get_bad_predecessor(false);
        assert!(pred.is_some(), "should find predecessor initially");
        let cube = pred.unwrap();
        let negated: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        pp.add_lemma(&negated);
        assert_eq!(pp.lemma_count(), 1);

        // Switch backend to SimpleSolver (the panic fallback path).
        pp.set_solver_backend(crate::sat_types::SolverBackend::Simple);

        // Rebuild with the new backend.
        pp.rebuild(&[]);

        // Accumulated lemma must still be effective with the new backend.
        assert!(
            pp.get_bad_predecessor(false).is_none(),
            "predecessor should be blocked after backend switch + rebuild"
        );
        assert_eq!(
            pp.lemma_count(),
            1,
            "lemma count preserved after backend switch"
        );
    }

    #[test]
    fn test_predprop_rebuild_lemma_count_monotonic() {
        // Verifies that lemma_count() only grows via add_lemma(), not via
        // rebuild(). Extra lemmas passed to rebuild() must NOT inflate the
        // accumulated count — they are ephemeral (re-passed on each rebuild
        // from the engine's inf_lemmas vec).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse");
        let ts = Transys::from_aiger(&circuit);

        let mut next_var_id = ts.max_var + 1;
        let mut next_vars = FxHashMap::default();
        for &latch_var in &ts.latch_vars {
            next_vars.insert(latch_var, Var(next_var_id));
            next_var_id += 1;
        }
        let max_var = next_var_id.saturating_sub(1).max(ts.max_var);

        let mut next_link_clauses = Vec::new();
        for &latch_var in &ts.latch_vars {
            if let (Some(&next_var), Some(&next_expr)) =
                (next_vars.get(&latch_var), ts.next_state.get(&latch_var))
            {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                next_link_clauses.push(vec![nv_neg, next_expr]);
                next_link_clauses.push(vec![nv_pos, !next_expr]);
            }
        }

        let mut pp = PredPropSolver::new(
            &ts,
            &next_vars,
            max_var,
            &next_link_clauses,
            crate::sat_types::SolverBackend::Simple,
        );
        assert_eq!(pp.lemma_count(), 0, "starts at 0");

        // Add one accumulated lemma.
        let pred = pp.get_bad_predecessor(false).unwrap();
        let negated: Vec<Lit> = pred.iter().map(|l| !*l).collect();
        pp.add_lemma(&negated.clone());
        assert_eq!(pp.lemma_count(), 1, "after add_lemma");

        // Rebuild with 3 extra lemmas. Count should stay at 1.
        pp.rebuild(&[negated.clone(), negated.clone(), negated.clone()]);
        assert_eq!(pp.lemma_count(), 1, "extras don't inflate count");

        // Add another accumulated lemma after rebuild. Count should be 2.
        pp.add_lemma(&[Lit::TRUE]);
        assert_eq!(pp.lemma_count(), 2, "add_lemma after rebuild increments");

        // Rebuild again — count stays at 2.
        pp.rebuild(&[]);
        assert_eq!(pp.lemma_count(), 2, "count stable across rebuilds");
    }
}
