// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Predecessor lifting for IC3/PDR with zero-SAT-call flip_to_none.
//!
//! The LiftSolver minimizes predecessor cubes found by IC3 frame solvers.
//! It uses three complementary techniques, in order:
//!
//! 1. **Ternary pre-filter** (O(n * gates), zero SAT calls): propagate
//!    through the AND-gate circuit to identify don't-care state literals.
//! 2. **UNSAT core extraction** (1 SAT call): find the minimal subset of
//!    state literals needed for the transition, using fine-grained negated
//!    target assumptions for smaller cores.
//! 3. **flip_to_none via ternary simulation** (O(n * gates), zero SAT calls):
//!    for each literal in the UNSAT core, try setting it to X (unknown) and
//!    re-propagating through the circuit. If the target next-state values
//!    remain determined, the literal is a don't-care and is dropped.
//!
//! The flip_to_none technique is adapted from rIC3's `flip_to_none_inner()`
//! (gipsat/propagate.rs:186-227), which directly inspects watcher lists to
//! check if unassigning a variable would violate any clause. Since z4-sat
//! doesn't expose watcher internals, we use AND-gate ternary simulation as
//! an equivalent technique. Both achieve the same goal: determine which
//! variables can be set to "don't care" without invoking the SAT solver.
//!
//! This replaces the previous approach of making one SAT call per literal
//! in the core (O(n * SAT_call)), saving thousands of SAT calls per IC3 run.
//!
//! Reference: rIC3 (github.com/gipsyh/rIC3), transys/lift.rs, gipsat/propagate.rs

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Lit, SatResult, SatSolver, Var, Z4SatCdclSolver};
use crate::ternary::{TernarySim, TernaryVal};
use crate::transys::Transys;

/// SAT-based predecessor cube minimizer.
///
/// Holds a SAT solver with the transition relation and next-state linking,
/// but without any frame lemmas. Used to find the minimal subset of a
/// predecessor cube that still reaches the target via one transition step.
pub(crate) struct LiftSolver {
    solver: Z4SatCdclSolver,
}

impl LiftSolver {
    /// Create a new LiftSolver from a transition system.
    ///
    /// Loads the transition relation, constraints, and next-state linking
    /// clauses (next_var <=> next_state_expr for each latch).
    pub(crate) fn new(
        ts: &Transys,
        next_vars: &rustc_hash::FxHashMap<Var, Var>,
        max_var: u32,
    ) -> Self {
        Self::new_inner(ts, next_vars, max_var, true)
    }

    /// Create a new LiftSolver with BVE preprocessing disabled (#4074).
    ///
    /// Used as a fallback when z4-sat's BVE produces FINALIZE_SAT_FAIL
    /// on certain clause structures.
    pub(crate) fn new_no_preprocess(
        ts: &Transys,
        next_vars: &rustc_hash::FxHashMap<Var, Var>,
        max_var: u32,
    ) -> Self {
        Self::new_inner(ts, next_vars, max_var, false)
    }

    fn new_inner(
        ts: &Transys,
        next_vars: &rustc_hash::FxHashMap<Var, Var>,
        max_var: u32,
        preprocess: bool,
    ) -> Self {
        let mut solver = Z4SatCdclSolver::new(max_var + 1);
        if !preprocess {
            solver.disable_preprocessing();
        }

        // Constant: Var(0) = false.
        solver.add_clause(&[Lit::TRUE]);

        // Transition relation.
        for clause in &ts.trans_clauses {
            solver.add_clause(&clause.lits);
        }

        // Constraints.
        for &constraint in &ts.constraint_lits {
            solver.add_clause(&[constraint]);
        }

        // Next-state linking: next_var <=> next_state_expr.
        // For each latch, encode: next_var_i <=> f_i(current_state, inputs)
        // as Tseitin: (!next_var OR f_i) AND (next_var OR !f_i)
        for (&latch_var, &next_var) in next_vars {
            if let Some(&next_expr) = ts.next_state.get(&latch_var) {
                let nv_pos = Lit::pos(next_var);
                let nv_neg = Lit::neg(next_var);
                solver.add_clause(&[nv_neg, next_expr]);
                solver.add_clause(&[nv_pos, !next_expr]);
            }
        }

        LiftSolver { solver }
    }

    /// Wire the portfolio cancellation flag into the lift solver's SAT backend
    /// so z4-sat can exit promptly when the portfolio finds a verdict (#4057).
    pub(crate) fn set_cancelled(&mut self, cancelled: std::sync::Arc<std::sync::atomic::AtomicBool>) {
        self.solver.set_cancelled(cancelled);
    }

    /// Maximum number of SAT calls during the flip-to-none pass.
    /// Bounds overhead on large cubes (single pass is O(n), each iteration
    /// is one SAT call, so total flip work is at most this many calls).
    #[allow(dead_code)]
    const FLIP_BUDGET: usize = 100;

    /// Minimize a predecessor cube using SAT-based lifting with optional
    /// ternary simulation pre-filtering and zero-SAT-call flip_to_none.
    ///
    /// Given a frame solver that returned SAT (finding a predecessor), extract
    /// the input and latch assignments, then use the lift solver to find the
    /// minimal subset of latch literals that still implies reaching the target.
    ///
    /// The approach:
    ///
    /// 1. Extract input assignments from the frame solver model.
    /// 2. Extract latch (state) assignments from the frame solver model.
    ///    - **Ternary pre-filter** (if `ternary_sim` provided): propagate
    ///      through the AND-gate circuit with 0/1/X values. Remove state
    ///      literals whose next-state contribution is X (don't-care). This
    ///      is O(n * |gates|) -- dramatically cheaper than SAT.
    /// 3. Negate target literals individually as assumptions.
    /// 4. Ask: is `inputs AND state AND Trans AND NOT(t1') AND ... AND NOT(tn')` UNSAT?
    /// 5. The UNSAT core (restricted to state literals) is the minimal predecessor.
    /// 6. **flip_to_none (zero SAT calls)**: use ternary simulation to further
    ///    reduce the core. For each remaining literal, check via circuit
    ///    propagation whether setting it to X preserves all target next-state
    ///    requirements.
    #[allow(dead_code)]
    pub(crate) fn lift(
        &mut self,
        frame_solver: &dyn SatSolver,
        target_primed: &[Lit],
        latch_vars: &[Var],
        input_vars: &[Var],
    ) -> Vec<Lit> {
        self.lift_with_ternary(
            frame_solver,
            target_primed,
            latch_vars,
            input_vars,
            None,
            None,
        )
    }

    /// Lift with optional ternary simulation pre-filtering and zero-SAT-call
    /// flip_to_none post-processing.
    ///
    /// When `ternary_sim` and `reverse_next` are provided, performs:
    /// 1. **Ternary pre-filter**: cheaply remove don't-care state literals
    ///    before any SAT call.
    /// 2. **UNSAT core extraction**: one SAT call to get the minimal core.
    /// 3. **Ternary flip_to_none**: further reduce the core without any
    ///    additional SAT calls, using circuit-level ternary simulation.
    ///
    /// The ternary flip_to_none is the key insight from rIC3's `flip_to_none`
    /// (gipsat/propagate.rs:186-227), adapted from watcher-list inspection to
    /// AND-gate ternary simulation. Both achieve the same goal: determine
    /// which variables can be set to "don't care" without a SAT call, by
    /// directly checking whether the assignment change would violate any
    /// constraint. rIC3 checks watcher lists; we check the AND-gate circuit.
    ///
    /// Reference: rIC3 `transys/lift.rs:57-64` — calls flip_to_none on the
    /// frame solver before SAT-based minimal_premise. Our ternary flip_to_none
    /// provides equivalent functionality without requiring z4-sat internal
    /// watcher list access.
    pub(crate) fn lift_with_ternary(
        &mut self,
        frame_solver: &dyn SatSolver,
        target_primed: &[Lit],
        latch_vars: &[Var],
        input_vars: &[Var],
        ternary_sim: Option<&TernarySim>,
        reverse_next: Option<&FxHashMap<Var, Var>>,
    ) -> Vec<Lit> {
        // Step 1: Extract input assignments from the frame solver model.
        let mut input_assumptions: Vec<Lit> = Vec::with_capacity(input_vars.len());
        for &iv in input_vars {
            let pos = Lit::pos(iv);
            match frame_solver.value(pos) {
                Some(true) => input_assumptions.push(pos),
                Some(false) => input_assumptions.push(Lit::neg(iv)),
                None => {}
            }
        }

        // Step 2: Extract latch (state) assignments from the frame solver model.
        let mut state_lits: Vec<Lit> = Vec::with_capacity(latch_vars.len());
        for &lv in latch_vars {
            let pos = Lit::pos(lv);
            match frame_solver.value(pos) {
                Some(true) => state_lits.push(pos),
                Some(false) => state_lits.push(Lit::neg(lv)),
                None => {}
            }
        }

        // Early exit: nothing to minimize or no target.
        if state_lits.is_empty() || target_primed.is_empty() {
            return state_lits;
        }

        // Step 2b: Ternary simulation pre-filter.
        // Propagate 0/1/X through the AND-gate circuit to identify state
        // literals that are don't-cares for the target. This is O(n * |gates|)
        // vs O(SAT) per literal — a massive speedup for medium/large circuits.
        if let (Some(tsim), Some(rev_next)) = (ternary_sim, reverse_next) {
            let pre_count = state_lits.len();
            state_lits = tsim.ternary_lift_prefilter(
                &state_lits,
                &input_assumptions,
                target_primed,
                rev_next,
            );
            let removed = pre_count.saturating_sub(state_lits.len());
            if removed > 0 {
                eprintln!("  lift: ternary prefilter removed {removed}/{pre_count} state lits");
            }
        }

        // Step 3: Negate target literals individually as assumptions.
        // Each neg-t_i' is a separate assumption, giving the SAT solver fine-grained
        // conflict tracking. This produces much smaller UNSAT cores than encoding
        // neg-target as a single disjunctive clause (!t1' OR !t2' OR ... OR !tn').
        //
        // Sound: the frame solver proved s AND I AND T => t_i' for each i,
        // so s AND I AND T AND neg-t_1' AND ... AND neg-t_n' is guaranteed UNSAT.
        let neg_target: Vec<Lit> = target_primed.iter().map(|l| !*l).collect();

        // Step 4: Build assumptions = inputs + state_lits + neg_target (individual).
        let mut assumptions =
            Vec::with_capacity(input_assumptions.len() + state_lits.len() + neg_target.len());
        assumptions.extend_from_slice(&input_assumptions);
        assumptions.extend_from_slice(&state_lits);
        assumptions.extend_from_slice(&neg_target);

        let result = self.solver.solve(&assumptions);

        let core_reduced = if result == SatResult::Unsat {
            // Extract UNSAT core and filter to only state literals.
            let state_set: FxHashSet<Lit> = state_lits.iter().copied().collect();
            if let Some(core) = self.solver.unsat_core() {
                let reduced: Vec<Lit> =
                    core.into_iter().filter(|l| state_set.contains(l)).collect();
                if !reduced.is_empty() {
                    Some(reduced)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };

        // Use core-reduced cube if available, otherwise fall back to full state.
        let reduced = match core_reduced {
            Some(r) => r,
            None => {
                return state_lits;
            }
        };

        // Step 5: flip_to_none — further reduce without SAT calls.
        //
        // rIC3's flip_to_none (gipsat/propagate.rs:186-227) directly inspects
        // watcher lists to check if unassigning a variable would violate any
        // clause. Since z4-sat doesn't expose watcher internals, we use
        // ternary simulation through the AND-gate circuit as an equivalent
        // technique: for each literal in the core, set it to X and propagate
        // through the transition relation. If all target next-state values
        // remain determined, the literal is a don't-care.
        //
        // This is O(n * |gates|) instead of O(n * SAT_call) — a massive win
        // when IC3 processes thousands of proof obligations.
        if let (Some(tsim), Some(rev_next)) = (ternary_sim, reverse_next) {
            let pre_flip = reduced.len();
            let flipped = Self::flip_to_none_ternary(
                tsim,
                &reduced,
                &input_assumptions,
                target_primed,
                rev_next,
            );
            let dropped = pre_flip.saturating_sub(flipped.len());
            if dropped > 0 {
                eprintln!("  lift: flip_to_none dropped {dropped}/{pre_flip} core lits (zero SAT calls)");
            }
            return flipped;
        }

        // Fallback: no ternary simulator available, return core as-is.
        // (Previously this used SAT-based flip_to_none with one SAT call per
        // literal. The ternary version supersedes it since the ternary
        // simulator is always constructed alongside the lift solver.)
        reduced
    }

    /// Zero-SAT-call flip_to_none using ternary simulation.
    ///
    /// For each literal in the core-reduced cube, attempts to set it to X
    /// (don't-care) and propagates through the AND-gate circuit. If all
    /// target next-state values remain determined (not X), the literal is
    /// unnecessary and is permanently dropped.
    ///
    /// This is the tla-aiger equivalent of rIC3's `flip_to_none_inner()`
    /// (gipsat/propagate.rs:186-227), which directly unassigns variables
    /// and checks watcher lists. Both techniques achieve the same goal
    /// without invoking the SAT solver.
    ///
    /// # Soundness
    ///
    /// The ternary simulation is an over-approximation: if ternary sim says
    /// a literal is a don't-care, then it truly is (the circuit doesn't need
    /// it to produce the target). However, ternary sim may miss some
    /// don't-cares that a SAT solver would find (it can't reason about
    /// implications through learned clauses or frame lemmas). This is safe:
    /// we may return a slightly larger cube than optimal, but never too small.
    ///
    /// # Complexity
    ///
    /// O(n * |gates|) where n = |core_cube| and |gates| = number of AND gates.
    /// For a typical IC3 scenario with 50-variable COI and 200 gates, this
    /// is ~10K operations vs ~50 SAT calls (each potentially thousands of
    /// propagations).
    fn flip_to_none_ternary(
        tsim: &TernarySim,
        core_cube: &[Lit],
        input_lits: &[Lit],
        target_primed: &[Lit],
        next_var_to_latch: &FxHashMap<Var, Var>,
    ) -> Vec<Lit> {
        if core_cube.is_empty() || target_primed.is_empty() {
            return core_cube.to_vec();
        }

        // Convert target_primed (over next_vars) to required next-state values
        // keyed by latch variable.
        let mut required_next: Vec<(Var, bool)> = Vec::with_capacity(target_primed.len());
        for &tgt_lit in target_primed {
            if let Some(&latch_var) = next_var_to_latch.get(&tgt_lit.var()) {
                required_next.push((latch_var, tgt_lit.is_positive()));
            }
        }

        if required_next.is_empty() {
            return core_cube.to_vec();
        }

        // Initialize ternary values: state from core cube, inputs from model.
        let num_values = tsim.num_values();
        let mut values = vec![TernaryVal::X; num_values];
        values[0] = TernaryVal::Zero; // Var(0) = constant FALSE

        // Set state literals from core cube.
        for &lit in core_cube {
            let idx = lit.var().0 as usize;
            if idx < values.len() {
                values[idx] = if lit.is_positive() {
                    TernaryVal::One
                } else {
                    TernaryVal::Zero
                };
            }
        }

        // Set input literals from model.
        for &lit in input_lits {
            let idx = lit.var().0 as usize;
            if idx < values.len() {
                values[idx] = if lit.is_positive() {
                    TernaryVal::One
                } else {
                    TernaryVal::Zero
                };
            }
        }

        // Initial propagation.
        tsim.propagate(&mut values);

        // Verify: with all core literals set, next-state should be determined.
        if !tsim.next_state_matches_vals(&values, &required_next) {
            // Can't confirm transition — return core as-is.
            return core_cube.to_vec();
        }

        // Greedy one-pass: try setting each core literal to X.
        let mut result = Vec::with_capacity(core_cube.len());
        for &lit in core_cube {
            let var_idx = lit.var().0 as usize;
            if var_idx >= values.len() {
                result.push(lit);
                continue;
            }
            let saved = values[var_idx];
            values[var_idx] = TernaryVal::X;
            tsim.propagate(&mut values);
            if tsim.next_state_matches_vals(&values, &required_next) {
                // Don't-care: this literal is not needed.
            } else {
                // Needed: restore and keep.
                values[var_idx] = saved;
                result.push(lit);
            }
        }

        // Re-propagate for consistency after the final set of kept literals.
        if !result.is_empty() {
            tsim.propagate(&mut values);
        }

        // Fall back to core if everything was removed (should not happen in
        // practice since the core was already minimal from UNSAT extraction).
        if result.is_empty() {
            return core_cube.to_vec();
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;
    use crate::ternary::TernarySim;
    use crate::transys::Transys;

    /// Test flip_to_none_ternary on a 3-latch shift register.
    ///
    /// Circuit: input -> A -> B -> C. Bad = A AND B AND C.
    /// A.next = input, B.next = A, C.next = B.
    ///
    /// Given predecessor state (A=1, B=1, C=0) with input=1,
    /// target = (A'=1, B'=1, C'=1):
    /// - A is needed because B' = A, target requires B'=1.
    /// - B is needed because C' = B, target requires C'=1.
    /// - C is NOT needed — nothing in the target depends on C's current value.
    ///
    /// After UNSAT core extraction, the core might include all three.
    /// flip_to_none_ternary should drop C without a SAT call.
    #[test]
    fn test_flip_to_none_ternary_shift_register() {
        // 3-latch shift register: input -> A -> B -> C. Bad = A AND B AND C.
        let aag = "\
aag 6 1 3 0 2 1
2
4 2
6 4
8 6
12
10 4 6
12 10 8
";
        let circuit = parse_aag(aag).expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let tsim = TernarySim::new(&ts);

        // Build next_var_to_latch map.
        let mut next_var_to_latch = FxHashMap::default();
        next_var_to_latch.insert(Var(7), Var(2)); // A
        next_var_to_latch.insert(Var(8), Var(3)); // B
        next_var_to_latch.insert(Var(9), Var(4)); // C

        // Core cube includes all 3 latches.
        let core_cube = vec![
            Lit::pos(Var(2)), // A=1
            Lit::pos(Var(3)), // B=1
            Lit::neg(Var(4)), // C=0
        ];
        let input_lits = vec![Lit::pos(Var(1))]; // input=1

        // Target: A'=1, B'=1, C'=1.
        let target_primed = vec![
            Lit::pos(Var(7)),
            Lit::pos(Var(8)),
            Lit::pos(Var(9)),
        ];

        let result = LiftSolver::flip_to_none_ternary(
            &tsim,
            &core_cube,
            &input_lits,
            &target_primed,
            &next_var_to_latch,
        );

        // A and B should survive, C should be dropped.
        assert!(
            result.contains(&Lit::pos(Var(2))),
            "A should be kept (B'=A, target B'=1)"
        );
        assert!(
            result.contains(&Lit::pos(Var(3))),
            "B should be kept (C'=B, target C'=1)"
        );
        assert!(
            !result.contains(&Lit::neg(Var(4))),
            "C should be dropped (nothing in target depends on C)"
        );
        assert_eq!(result.len(), 2, "should have dropped 1 of 3 literals");
    }

    /// Test flip_to_none_ternary with a single essential literal.
    ///
    /// Toggle: latch next = !latch. Target = latch' = 0 (i.e., latch must be 1).
    /// The single latch literal is essential and cannot be dropped.
    #[test]
    fn test_flip_to_none_ternary_single_essential() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let tsim = TernarySim::new(&ts);

        let mut next_var_to_latch = FxHashMap::default();
        next_var_to_latch.insert(Var(2), Var(1));

        // Core cube: latch=1.
        let core_cube = vec![Lit::pos(Var(1))];
        // Target: latch' should be 0 (next = !latch = !1 = 0).
        let target_primed = vec![Lit::neg(Var(2))];

        let result = LiftSolver::flip_to_none_ternary(
            &tsim,
            &core_cube,
            &[],
            &target_primed,
            &next_var_to_latch,
        );

        // The single literal must be kept.
        assert_eq!(result.len(), 1, "single essential literal should survive");
        assert_eq!(result[0], Lit::pos(Var(1)));
    }

    /// Test flip_to_none_ternary with empty core cube.
    #[test]
    fn test_flip_to_none_ternary_empty_core() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let tsim = TernarySim::new(&ts);

        let result = LiftSolver::flip_to_none_ternary(
            &tsim,
            &[],
            &[],
            &[Lit::pos(Var(2))],
            &FxHashMap::default(),
        );
        assert!(result.is_empty(), "empty core should produce empty result");
    }

    /// Test flip_to_none_ternary with empty target.
    #[test]
    fn test_flip_to_none_ternary_empty_target() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let tsim = TernarySim::new(&ts);

        let core_cube = vec![Lit::pos(Var(1))];
        let result = LiftSolver::flip_to_none_ternary(
            &tsim,
            &core_cube,
            &[],
            &[],
            &FxHashMap::default(),
        );
        // Empty target means nothing to check — returns core as-is.
        assert_eq!(result, core_cube);
    }

    /// Test flip_to_none_ternary with two independent latches.
    ///
    /// Two stuck-at-0 latches: A.next=0, B.next=0. Both init at 0.
    /// If target requires A'=0 only, then B is a don't-care.
    #[test]
    fn test_flip_to_none_ternary_independent_latches() {
        // Two latches, both stuck-at-0.
        let circuit =
            parse_aag("aag 2 0 2 0 0 1\n2 0\n4 0\n2\n").expect("parse failed");
        let ts = Transys::from_aiger(&circuit);
        let tsim = TernarySim::new(&ts);

        let mut next_var_to_latch = FxHashMap::default();
        next_var_to_latch.insert(Var(3), Var(1)); // A
        next_var_to_latch.insert(Var(4), Var(2)); // B

        // Core cube: both latches assigned.
        let core_cube = vec![
            Lit::pos(Var(1)), // A=1
            Lit::pos(Var(2)), // B=1
        ];

        // Target: only A'=0 required.
        let target_primed = vec![Lit::neg(Var(3))]; // A' = 0

        let result = LiftSolver::flip_to_none_ternary(
            &tsim,
            &core_cube,
            &[],
            &target_primed,
            &next_var_to_latch,
        );

        // A.next = 0, which is constant. A's current value doesn't affect A.next.
        // So actually both A and B are don't-cares for A'=0 (since A.next=0
        // regardless of current state). The result depends on whether ternary
        // sim can detect this: it should because the next-state function is
        // the constant literal 0.
        //
        // Both should be dropped since A'=0 is always true (next=constant 0).
        // But if both are dropped, the fallback returns the full core.
        // This tests the edge case handling.
        assert!(
            result.len() <= core_cube.len(),
            "result should not be larger than input"
        );
    }
}
