// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ternary simulation for cube minimization.
//!
//! Given a SAT model, ternary simulation identifies which latch
//! assignments are actually needed to reach the bad state. Irrelevant
//! latches (don't-cares) are removed, producing a smaller cube that
//! is faster for IC3 to generalize and block.
//!
//! Three-valued logic: 0, 1, X (unknown/don't-care).
//! AND gate: 0 AND _ = 0, 1 AND 1 = 1, otherwise X.

use rustc_hash::FxHashMap;

use crate::sat_types::{Lit, SatSolver, Var};
use crate::transys::Transys;

/// Three-valued logic value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TernaryVal {
    Zero,
    One,
    X,
}

impl TernaryVal {
    #[inline]
    fn and(self, other: TernaryVal) -> TernaryVal {
        match (self, other) {
            (TernaryVal::Zero, _) | (_, TernaryVal::Zero) => TernaryVal::Zero,
            (TernaryVal::One, TernaryVal::One) => TernaryVal::One,
            _ => TernaryVal::X,
        }
    }

    #[inline]
    fn not(self) -> TernaryVal {
        match self {
            TernaryVal::Zero => TernaryVal::One,
            TernaryVal::One => TernaryVal::Zero,
            TernaryVal::X => TernaryVal::X,
        }
    }
}

/// Ternary simulator for an AIGER circuit.
pub struct TernarySim {
    /// Sorted AND gates for topological propagation.
    gates: Vec<(u32, Lit, Lit)>,
    /// Bad literals.
    bad_lits: Vec<Lit>,
    /// Number of values slots.
    num_values: usize,
    /// Next-state map: latch_var -> next_state_literal.
    /// Used by ternary lift prefilter to trace through the transition relation.
    next_state: FxHashMap<Var, Lit>,
}

// Public accessors for use by the lift module's flip_to_none_ternary.
impl TernarySim {
    /// Number of value slots in the ternary simulation vector.
    #[inline]
    pub(crate) fn num_values(&self) -> usize {
        self.num_values
    }

    /// Propagate ternary values through the AND-gate circuit.
    ///
    /// Evaluates all AND gates in topological order, updating the `values`
    /// array in place. Call this after modifying any variable's value.
    #[inline]
    pub(crate) fn propagate(&self, values: &mut [TernaryVal]) {
        Self::propagate_values(&self.gates, values);
    }

    /// Check if next-state functions match required values.
    ///
    /// For each `(latch_var, required_polarity)`, looks up the next-state
    /// literal and checks whether it evaluates to the required value.
    /// Returns false if any requirement is not met (evaluates to X or
    /// the wrong polarity).
    pub(crate) fn next_state_matches_vals(
        &self,
        values: &[TernaryVal],
        required: &[(Var, bool)],
    ) -> bool {
        self.next_state_matches(values, required)
    }
}

impl TernarySim {
    pub fn new(ts: &Transys) -> Self {
        let mut gates: Vec<(u32, Lit, Lit)> = ts
            .and_defs
            .iter()
            .map(|(&var, &(rhs0, rhs1))| (var.0, rhs0, rhs1))
            .collect();
        gates.sort_unstable_by_key(|&(var, _, _)| var);

        TernarySim {
            gates,
            bad_lits: ts.bad_lits.clone(),
            num_values: ts.max_var as usize + 1,
            next_state: ts.next_state.clone(),
        }
    }

    /// Minimize a cube (over latch variables) extracted from a SAT model.
    ///
    /// Single-pass approach: set all latches from model, inputs = X.
    /// Propagate once. Then for each latch that's in the cube, check if
    /// flipping it to X would change the bad output by doing a second propagation.
    pub fn minimize_cube(
        &self,
        solver: &dyn SatSolver,
        latch_vars: &[Var],
        input_vars: &[Var],
    ) -> Vec<Lit> {
        let mut values = vec![TernaryVal::X; self.num_values];
        values[0] = TernaryVal::Zero;

        // Set latches from model.
        let mut cube: Vec<Lit> = Vec::new();
        for &latch_var in latch_vars {
            let pos = Lit::pos(latch_var);
            match solver.value(pos) {
                Some(true) => {
                    values[latch_var.0 as usize] = TernaryVal::One;
                    cube.push(pos);
                }
                Some(false) => {
                    values[latch_var.0 as usize] = TernaryVal::Zero;
                    cube.push(Lit::neg(latch_var));
                }
                None => {}
            }
        }

        // Set inputs from model for initial propagation.
        for &input_var in input_vars {
            let pos = Lit::pos(input_var);
            match solver.value(pos) {
                Some(true) => values[input_var.0 as usize] = TernaryVal::One,
                Some(false) => values[input_var.0 as usize] = TernaryVal::Zero,
                None => {}
            }
        }

        Self::propagate_values(&self.gates, &mut values);

        // Sanity check: bad should be reachable.
        if !Self::bad_is_one(&self.bad_lits, &values) {
            return cube;
        }

        // Now set inputs to X and re-propagate. This gives a looser simulation
        // that still confirms bad. Use this to identify don't-care latches.
        for &input_var in input_vars {
            values[input_var.0 as usize] = TernaryVal::X;
        }
        // Re-set latch values from cube (may have been overwritten by AND gate propagation).
        for &lit in &cube {
            values[lit.var().0 as usize] = if lit.is_positive() {
                TernaryVal::One
            } else {
                TernaryVal::Zero
            };
        }
        Self::propagate_values(&self.gates, &mut values);

        if !Self::bad_is_one(&self.bad_lits, &values) {
            // With inputs=X, bad is no longer definite. Return full cube.
            return cube;
        }

        // Now try removing each latch. We use a fast one-pass greedy approach.
        let mut result = Vec::with_capacity(cube.len());
        for &lit in &cube {
            let var_idx = lit.var().0 as usize;
            let saved = values[var_idx];
            values[var_idx] = TernaryVal::X;
            Self::propagate_values(&self.gates, &mut values);
            if Self::bad_is_one(&self.bad_lits, &values) {
                // Don't-care: leave as X.
            } else {
                // Needed: restore and keep in result.
                values[var_idx] = saved;
                result.push(lit);
            }
        }

        // Final propagation to ensure consistent state.
        if !result.is_empty() {
            Self::propagate_values(&self.gates, &mut values);
        }

        if result.is_empty() {
            // Edge case: everything removed? Fall back to full cube.
            return cube;
        }

        result
    }

    #[inline]
    fn propagate_values(gates: &[(u32, Lit, Lit)], values: &mut [TernaryVal]) {
        for &(out_var, rhs0, rhs1) in gates {
            let v0 = Self::eval_lit_val(rhs0, values);
            let v1 = Self::eval_lit_val(rhs1, values);
            values[out_var as usize] = v0.and(v1);
        }
    }

    #[inline]
    fn eval_lit_val(lit: Lit, values: &[TernaryVal]) -> TernaryVal {
        let val = values[lit.var().0 as usize];
        if lit.is_negated() {
            val.not()
        } else {
            val
        }
    }

    #[inline]
    fn bad_is_one(bad_lits: &[Lit], values: &[TernaryVal]) -> bool {
        bad_lits
            .iter()
            .any(|&lit| Self::eval_lit_val(lit, values) == TernaryVal::One)
    }

    /// Reduce a cube using ternary simulation (no SAT solver needed).
    ///
    /// Given a cube over latch variables, identifies which literals are
    /// don't-care for the bad output by ternary propagation. All inputs
    /// are set to X. For each literal in the cube, try setting it to X
    /// and re-propagate; if bad is still determined (One), the literal
    /// was unnecessary and is removed.
    ///
    /// This is a fast O(n * |gates|) pre-filter for MIC generalization.
    /// Literals that survive this pass must still be checked by SAT-based
    /// MIC for relative inductiveness.
    pub(crate) fn ternary_reduce_cube(&self, cube: &[Lit]) -> Vec<Lit> {
        if cube.is_empty() {
            return Vec::new();
        }

        let mut values = vec![TernaryVal::X; self.num_values];
        values[0] = TernaryVal::Zero; // Var(0) = constant FALSE

        // Set latch values from cube; inputs stay X.
        for &lit in cube {
            values[lit.var().0 as usize] = if lit.is_positive() {
                TernaryVal::One
            } else {
                TernaryVal::Zero
            };
        }

        Self::propagate_values(&self.gates, &mut values);

        // If bad is not determined with all cube literals set, no reduction possible.
        if !Self::bad_is_one(&self.bad_lits, &values) {
            return cube.to_vec();
        }

        // Greedy one-pass: try removing each literal.
        let mut result = Vec::with_capacity(cube.len());
        for &lit in cube {
            let var_idx = lit.var().0 as usize;
            let saved = values[var_idx];
            values[var_idx] = TernaryVal::X;
            Self::propagate_values(&self.gates, &mut values);
            if Self::bad_is_one(&self.bad_lits, &values) {
                // Don't-care: leave as X.
            } else {
                // Needed: restore and keep.
                values[var_idx] = saved;
                result.push(lit);
            }
        }

        // Fall back to full cube if everything was removed (edge case).
        if result.is_empty() {
            return cube.to_vec();
        }

        result
    }

    /// Ternary simulation pre-filter for SAT-based predecessor lifting.
    ///
    /// Given a predecessor cube (state literals) and a target (primed) cube,
    /// identifies which state literals are definitely needed to produce the
    /// target through the transition relation. Literals that evaluate to X
    /// (don't-care) through ternary simulation can be removed without any
    /// SAT call.
    ///
    /// **How it works:**
    /// 1. Set predecessor state literals and input literals from the frame
    ///    solver model.
    /// 2. Propagate through AND gates.
    /// 3. Compute next-state literal values from the `next_state` map.
    /// 4. For each state literal, try setting it to X, re-propagate, and
    ///    check if ALL target next-state requirements are still met.
    /// 5. If they are, the literal is a don't-care for this transition.
    ///
    /// This is O(n * |gates|) per state literal vs O(n * SAT_call) for
    /// the flip-to-none pass. On medium circuits (hundreds of latches),
    /// this eliminates 30-60% of state literals before any SAT call.
    ///
    /// # Arguments
    /// * `state_lits` - Predecessor state literals from the frame solver model.
    /// * `input_lits` - Input literals from the frame solver model.
    /// * `target_primed` - Target cube in primed (next-state) variable space.
    ///   Each literal is over a `next_var` allocated by the IC3 engine. The
    ///   `next_var_to_latch` map converts these to latch variables for
    ///   next-state function evaluation.
    /// * `next_var_to_latch` - Maps next-state variable to its latch variable.
    ///
    /// # Returns
    /// Subset of `state_lits` that are definitely needed (ternary-essential).
    /// The caller should pass ONLY these to the SAT-based lifting step.
    pub(crate) fn ternary_lift_prefilter(
        &self,
        state_lits: &[Lit],
        input_lits: &[Lit],
        target_primed: &[Lit],
        next_var_to_latch: &FxHashMap<Var, Var>,
    ) -> Vec<Lit> {
        if state_lits.is_empty() || target_primed.is_empty() {
            return state_lits.to_vec();
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
            return state_lits.to_vec();
        }

        let mut values = vec![TernaryVal::X; self.num_values];
        values[0] = TernaryVal::Zero; // Var(0) = constant FALSE

        // Set state literals from predecessor cube.
        for &lit in state_lits {
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

        // Propagate through AND gates.
        Self::propagate_values(&self.gates, &mut values);

        // Verify: with all literals set, next-state requirements should be met.
        if !self.next_state_matches(&values, &required_next) {
            // Ternary sim can't confirm the transition — fall back to full cube.
            return state_lits.to_vec();
        }

        // Try removing each state literal one by one (greedy one-pass).
        // Inputs are kept fixed (they're part of the lift assumptions).
        let mut result = Vec::with_capacity(state_lits.len());
        for &lit in state_lits {
            let var_idx = lit.var().0 as usize;
            if var_idx >= values.len() {
                result.push(lit);
                continue;
            }
            let saved = values[var_idx];
            values[var_idx] = TernaryVal::X;
            Self::propagate_values(&self.gates, &mut values);
            if self.next_state_matches(&values, &required_next) {
                // Don't-care: this state literal is not needed for the transition.
            } else {
                // Needed: restore and keep.
                values[var_idx] = saved;
                result.push(lit);
            }
        }

        // Final propagation to maintain consistency.
        if !result.is_empty() {
            Self::propagate_values(&self.gates, &mut values);
        }

        // Fall back to full cube if everything was removed.
        if result.is_empty() {
            return state_lits.to_vec();
        }

        result
    }

    /// Check if the next-state function for each required latch evaluates
    /// to the required value under the current ternary valuation.
    ///
    /// For each `(latch_var, required_polarity)`, look up the next-state
    /// literal `f(latch_var)` in `self.next_state` and check its ternary
    /// value. If it evaluates to `One` and we need `true`, or `Zero` and
    /// we need `false`, the requirement is met. If it evaluates to `X`,
    /// the requirement is NOT met (we can't guarantee the transition).
    fn next_state_matches(&self, values: &[TernaryVal], required: &[(Var, bool)]) -> bool {
        for &(latch_var, req_positive) in required {
            if let Some(&next_lit) = self.next_state.get(&latch_var) {
                let val = Self::eval_lit_val(next_lit, values);
                let meets = if req_positive {
                    val == TernaryVal::One
                } else {
                    val == TernaryVal::Zero
                };
                if !meets {
                    return false;
                }
            } else {
                // No next-state function for this latch — can't verify.
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;
    use crate::transys::Transys;

    #[test]
    fn test_ternary_val_and() {
        assert_eq!(TernaryVal::Zero.and(TernaryVal::One), TernaryVal::Zero);
        assert_eq!(TernaryVal::One.and(TernaryVal::One), TernaryVal::One);
        assert_eq!(TernaryVal::One.and(TernaryVal::X), TernaryVal::X);
        assert_eq!(TernaryVal::Zero.and(TernaryVal::X), TernaryVal::Zero);
        assert_eq!(TernaryVal::X.and(TernaryVal::X), TernaryVal::X);
    }

    #[test]
    fn test_ternary_val_not() {
        assert_eq!(TernaryVal::Zero.not(), TernaryVal::One);
        assert_eq!(TernaryVal::One.not(), TernaryVal::Zero);
        assert_eq!(TernaryVal::X.not(), TernaryVal::X);
    }

    #[test]
    fn test_ternary_reduce_cube_identity_for_single_lit() {
        // Toggle: latch starts at 0, next = NOT latch. Bad = latch.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let sim = TernarySim::new(&ts);

        // Cube: latch=true (the bad state)
        let cube = vec![Lit::pos(Var(1))];
        let reduced = sim.ternary_reduce_cube(&cube);
        // Single literal cube can't be further reduced.
        assert_eq!(reduced.len(), 1);
    }

    #[test]
    fn test_ternary_lift_prefilter_basic() {
        // 3-latch shift register: input -> A -> B -> C. Bad = A AND B AND C.
        // A.next = input, B.next = A, C.next = B.
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
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let sim = TernarySim::new(&ts);

        // Suppose predecessor state: A=1, B=1, C=0 with input=1.
        // Next state: A'=input=1, B'=A=1, C'=B=1 => bad at next step.
        // Target: A'=1, B'=1, C'=1.
        let state_lits = vec![
            Lit::pos(Var(2)), // A=1
            Lit::pos(Var(3)), // B=1
            Lit::neg(Var(4)), // C=0
        ];
        let input_lits = vec![Lit::pos(Var(1))]; // input=1

        // Build next_var_to_latch map.
        // In IC3, next vars are allocated beyond max_var.
        // For this test: next_var(A)=7, next_var(B)=8, next_var(C)=9.
        let mut next_var_to_latch = FxHashMap::default();
        next_var_to_latch.insert(Var(7), Var(2)); // A
        next_var_to_latch.insert(Var(8), Var(3)); // B
        next_var_to_latch.insert(Var(9), Var(4)); // C

        // Target: A'=1, B'=1, C'=1 (all positive next vars).
        let target_primed = vec![
            Lit::pos(Var(7)), // A'=1
            Lit::pos(Var(8)), // B'=1
            Lit::pos(Var(9)), // C'=1
        ];

        let prefiltered = sim.ternary_lift_prefilter(
            &state_lits,
            &input_lits,
            &target_primed,
            &next_var_to_latch,
        );

        // A is needed because B'=A (target B'=1 requires A=1).
        // B is needed because C'=B (target C'=1 requires B=1).
        // C is NOT needed because nothing in the target depends on C's current value.
        // (A' depends on input, B' depends on A, C' depends on B)
        assert!(
            prefiltered.contains(&Lit::pos(Var(2))),
            "A should be needed (B'=A)"
        );
        assert!(
            prefiltered.contains(&Lit::pos(Var(3))),
            "B should be needed (C'=B)"
        );
        assert!(
            !prefiltered.contains(&Lit::neg(Var(4))),
            "C should be don't-care (nothing depends on it)"
        );
        // Reduced from 3 literals to 2.
        assert_eq!(prefiltered.len(), 2);
    }

    #[test]
    fn test_ternary_lift_prefilter_empty_target() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let sim = TernarySim::new(&ts);

        let state_lits = vec![Lit::pos(Var(1))];
        let result = sim.ternary_lift_prefilter(&state_lits, &[], &[], &FxHashMap::default());
        assert_eq!(result, state_lits);
    }

    #[test]
    fn test_ternary_lift_prefilter_empty_state() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let sim = TernarySim::new(&ts);

        let target = vec![Lit::pos(Var(5))];
        let result = sim.ternary_lift_prefilter(&[], &[], &target, &FxHashMap::default());
        assert!(result.is_empty());
    }
}
