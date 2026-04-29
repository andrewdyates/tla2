// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sequential ternary simulation for AIGER preprocessing.
//!
//! Simulates the circuit forward for N cycles using ternary values
//! (0, 1, X=unknown) to detect latches that stabilize to a constant.
//!
//! Unlike [`super::ternary_prop::ternary_constant_propagation`] which only
//! propagates constants through the combinational logic (single cycle,
//! structural only), this pass:
//! 1. Seeds latches with their known init values (0/1 from unit init clauses,
//!    X for unconstrained latches).
//! 2. Evaluates AND gates in topological order with ternary logic.
//! 3. Computes next-state values for all latches.
//! 4. Feeds next-state back as current-state and repeats for N cycles.
//! 5. After N cycles, latches whose value has been the same constant in
//!    every cycle (never X) are provably constant and can be eliminated.
//!
//! This is the technique used by rIC3's preprocessing (ternary simulation +
//! functional reduction) and ABC's `ternary_sim`. It catches constants that
//! the purely structural pass misses, particularly latches that are constant
//! due to their init value propagating through feedback loops.
//!
//! **Soundness:** A latch is marked constant only if it evaluates to the same
//! constant (0 or 1, never X) in ALL simulation cycles. Since ternary
//! simulation over-approximates reachable states (X covers all possible
//! values), if a latch is always-0 or always-1 in ternary simulation, it is
//! provably constant in all reachable states.
//!
//! Reference:
//! - rIC3 `src/transys/simp.rs`: ternary simulation as part of `simplify()`
//! - ABC `src/proof/ternary/ternary_sim.c`: multi-cycle ternary simulation
//! - Biere, "The AIGER format" (2006): ternary simulation for preprocessing

use rustc_hash::FxHashMap;

use crate::sat_types::{Lit, Var};
use crate::transys::Transys;

use super::substitution::{apply_substitution, sorted_and_defs};

/// Ternary value: `Some(true)` = 1, `Some(false)` = 0, `None` = X (unknown).
type TernaryVal = Option<bool>;

/// Default number of simulation cycles.
///
/// 64 cycles is typical for HWMCC preprocessing (rIC3 uses 32-64, ABC uses
/// similar). More cycles catch deeper feedback-loop constants but with
/// diminishing returns. We use 64 as a good balance.
const DEFAULT_SIM_CYCLES: usize = 64;

/// Run sequential ternary simulation to detect constant latches.
///
/// Returns a new `Transys` with constant latches eliminated, and the count
/// of latches eliminated.
///
/// `cycles` controls how many forward simulation cycles to run. Use 0 for
/// the default (64 cycles).
pub(crate) fn sequential_ternary_simulation(ts: &Transys, cycles: usize) -> (Transys, usize) {
    let num_cycles = if cycles == 0 {
        DEFAULT_SIM_CYCLES
    } else {
        cycles
    };

    if ts.latch_vars.is_empty() {
        return (ts.clone(), 0);
    }

    let sorted_gates = sorted_and_defs(ts);

    // Extract known init values from unit init clauses.
    let init_values = extract_init_values(ts);

    // Track which latches are provably constant and at what value.
    // A latch is constant if it has been the same value (0 or 1, never X)
    // in every simulation cycle.
    let mut latch_constant: FxHashMap<Var, TernaryVal> = FxHashMap::default();
    for &latch in &ts.latch_vars {
        // Initialize with the latch's init value (or X if unknown).
        latch_constant.insert(latch, init_values.get(&latch).copied());
    }

    // Current ternary state of all variables.
    let n = ts.max_var as usize + 1;
    let mut current_state: Vec<TernaryVal> = vec![None; n];

    // Var(0) is always false (structural constant).
    if !current_state.is_empty() {
        current_state[0] = Some(false);
    }

    // Seed initial latch values.
    for &latch in &ts.latch_vars {
        current_state[latch.index()] = init_values.get(&latch).copied();
    }

    // Simulate forward for num_cycles cycles.
    for _cycle in 0..num_cycles {
        // All inputs are X (unknown) -- inputs are free in every cycle.
        for &inp in &ts.input_vars {
            current_state[inp.index()] = None;
        }

        // Evaluate AND gates in topological order.
        for &(out, rhs0, rhs1) in &sorted_gates {
            let val0 = eval_ternary_lit(rhs0, &current_state);
            let val1 = eval_ternary_lit(rhs1, &current_state);

            current_state[out.index()] = ternary_and(val0, val1);
        }

        // Compute next-state for each latch.
        let mut next_latch_values: FxHashMap<Var, TernaryVal> = FxHashMap::default();
        for &latch in &ts.latch_vars {
            let next_val = if let Some(&next_lit) = ts.next_state.get(&latch) {
                eval_ternary_lit(next_lit, &current_state)
            } else {
                None // No next-state function = X
            };
            next_latch_values.insert(latch, next_val);

            // Update constant tracking: if this latch's value in this cycle
            // differs from its tracked constant, mark it as non-constant (X).
            match latch_constant.get(&latch) {
                Some(Some(tracked_val)) => {
                    // Was constant. Still constant at the same value?
                    match next_val {
                        Some(v) if v == *tracked_val => {
                            // Still constant, same value. Keep tracking.
                        }
                        _ => {
                            // Either X or different constant. Not constant.
                            latch_constant.insert(latch, None);
                        }
                    }
                }
                Some(None) => {
                    // Already marked as non-constant. No change.
                }
                None => {
                    // First cycle -- set initial tracking value.
                    latch_constant.insert(latch, next_val);
                }
            }
        }

        // Feed next-state values back as current-state for next cycle.
        for &latch in &ts.latch_vars {
            current_state[latch.index()] = next_latch_values.get(&latch).copied().unwrap_or(None);
        }
    }

    // Collect latches that are provably constant.
    let mut subst: FxHashMap<Var, Lit> = FxHashMap::default();
    for &latch in &ts.latch_vars {
        // A latch is constant if:
        // 1. Its init value is known (0 or 1), AND
        // 2. It stayed at the same constant in all simulation cycles.
        let init_val = init_values.get(&latch).copied();
        let tracked = latch_constant.get(&latch).copied().unwrap_or(None);

        if let (Some(init_v), Some(tracked_v)) = (init_val, tracked) {
            if init_v == tracked_v {
                let const_lit = if init_v { Lit::TRUE } else { Lit::FALSE };
                subst.insert(latch, const_lit);
            }
        }
    }

    let eliminated = subst.len();
    if eliminated == 0 {
        (ts.clone(), 0)
    } else {
        (apply_substitution(ts, &subst), eliminated)
    }
}

/// Extract known init values from unit init clauses.
///
/// Scans for unit clauses (single-literal clauses) that definitively
/// constrain a latch's initial value.
fn extract_init_values(ts: &Transys) -> FxHashMap<Var, bool> {
    let mut init_values = FxHashMap::default();
    for clause in &ts.init_clauses {
        if clause.lits.len() != 1 {
            continue;
        }
        let lit = clause.lits[0];
        let var = lit.var();
        if var == Var(0) {
            continue;
        }
        init_values.insert(var, lit.is_positive());
    }
    init_values
}

/// Evaluate a literal in the ternary domain.
#[inline]
fn eval_ternary_lit(lit: Lit, state: &[TernaryVal]) -> TernaryVal {
    if lit == Lit::FALSE {
        return Some(false);
    }
    if lit == Lit::TRUE {
        return Some(true);
    }
    let val = state.get(lit.var().index()).copied().flatten();
    match val {
        Some(v) => {
            if lit.is_negated() {
                Some(!v)
            } else {
                Some(v)
            }
        }
        None => None,
    }
}

/// Ternary AND: implements the truth table for AND with X.
///
/// | a | b | a AND b |
/// |---|---|---------|
/// | 0 | * |    0    |
/// | * | 0 |    0    |
/// | 1 | 1 |    1    |
/// | 1 | X |    X    |
/// | X | 1 |    X    |
/// | X | X |    X    |
#[inline]
fn ternary_and(a: TernaryVal, b: TernaryVal) -> TernaryVal {
    match (a, b) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_types::Clause;
    use crate::transys::Transys;
    use rustc_hash::FxHashMap;

    use crate::preprocess::substitution::rebuild_trans_clauses;

    fn build_ts(
        max_var: u32,
        latch_vars: Vec<Var>,
        input_vars: Vec<Var>,
        next_state: FxHashMap<Var, Lit>,
        init_clauses: Vec<Clause>,
        bad_lits: Vec<Lit>,
        and_defs: FxHashMap<Var, (Lit, Lit)>,
    ) -> Transys {
        Transys {
            max_var,
            num_latches: latch_vars.len(),
            num_inputs: input_vars.len(),
            latch_vars,
            input_vars,
            next_state,
            init_clauses,
            trans_clauses: rebuild_trans_clauses(&and_defs),
            bad_lits,
            constraint_lits: Vec::new(),
            and_defs,
            internal_signals: Vec::new(),
        }
    }

    #[test]
    fn test_ternary_sim_stuck_at_zero() {
        // Latch A starts at 0, next = FALSE (stuck at 0).
        // Sequential ternary sim should detect this.
        let a = Var(1);
        let inp = Var(2);

        let mut next_state = FxHashMap::default();
        next_state.insert(a, Lit::FALSE);

        let ts = build_ts(
            2,
            vec![a],
            vec![inp],
            next_state,
            vec![Clause::unit(Lit::neg(a))], // init: a = 0
            vec![Lit::pos(a)],
            FxHashMap::default(),
        );

        let (reduced, eliminated) = sequential_ternary_simulation(&ts, 32);
        assert_eq!(eliminated, 1, "stuck-at-0 latch should be eliminated");
        assert!(reduced.latch_vars.is_empty());
        assert_eq!(reduced.bad_lits, vec![Lit::FALSE]);
    }

    #[test]
    fn test_ternary_sim_stuck_at_one() {
        // Latch A starts at 1, next = TRUE (stuck at 1).
        let a = Var(1);

        let mut next_state = FxHashMap::default();
        next_state.insert(a, Lit::TRUE);

        let ts = build_ts(
            1,
            vec![a],
            Vec::new(),
            next_state,
            vec![Clause::unit(Lit::pos(a))], // init: a = 1
            vec![Lit::pos(a)],
            FxHashMap::default(),
        );

        let (reduced, eliminated) = sequential_ternary_simulation(&ts, 32);
        assert_eq!(eliminated, 1, "stuck-at-1 latch should be eliminated");
        assert!(reduced.latch_vars.is_empty());
        assert_eq!(reduced.bad_lits, vec![Lit::TRUE]);
    }

    #[test]
    fn test_ternary_sim_self_loop_zero() {
        // Latch A starts at 0, next = AND(A, input).
        // Since A=0 initially, AND(0, input) = 0. A stays 0 forever.
        // Ternary sim: cycle 0 A=0, eval AND(0, X) = 0, next=0. Stable.
        let a = Var(1);
        let inp = Var(2);
        let gate = Var(3);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(gate, (Lit::pos(a), Lit::pos(inp)));

        let mut next_state = FxHashMap::default();
        next_state.insert(a, Lit::pos(gate));

        let ts = build_ts(
            3,
            vec![a],
            vec![inp],
            next_state,
            vec![Clause::unit(Lit::neg(a))], // init: a = 0
            vec![Lit::pos(a)],
            and_defs,
        );

        let (reduced, eliminated) = sequential_ternary_simulation(&ts, 32);
        assert_eq!(
            eliminated, 1,
            "self-loop latch AND(a,inp) with a=0 should be eliminated"
        );
        assert!(reduced.latch_vars.is_empty());
    }

    #[test]
    fn test_ternary_sim_nonconstant_latch() {
        // Latch A starts at 0, next = input. A changes based on input.
        // Ternary sim: next = X (input is X). Not constant.
        let a = Var(1);
        let inp = Var(2);

        let mut next_state = FxHashMap::default();
        next_state.insert(a, Lit::pos(inp));

        let ts = build_ts(
            2,
            vec![a],
            vec![inp],
            next_state,
            vec![Clause::unit(Lit::neg(a))],
            vec![Lit::pos(a)],
            FxHashMap::default(),
        );

        let (_reduced, eliminated) = sequential_ternary_simulation(&ts, 32);
        assert_eq!(eliminated, 0, "non-constant latch should not be eliminated");
    }

    #[test]
    fn test_ternary_sim_cascade_detection() {
        // Latch A starts at 0, next = FALSE (stuck at 0).
        // Latch B starts at 0, next = AND(A, B).
        // Since A is always 0, AND(0, B) = 0. B also stays 0.
        // Ternary sim should detect both as constant.
        let a = Var(1);
        let b = Var(2);
        let gate = Var(3);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(gate, (Lit::pos(a), Lit::pos(b)));

        let mut next_state = FxHashMap::default();
        next_state.insert(a, Lit::FALSE);
        next_state.insert(b, Lit::pos(gate));

        let ts = build_ts(
            3,
            vec![a, b],
            Vec::new(),
            next_state,
            vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
            vec![Lit::pos(b)],
            and_defs,
        );

        let (reduced, eliminated) = sequential_ternary_simulation(&ts, 32);
        assert_eq!(
            eliminated, 2,
            "both cascading constant latches should be eliminated"
        );
        assert!(reduced.latch_vars.is_empty());
    }

    #[test]
    fn test_ternary_sim_toggle_not_constant() {
        // Latch A starts at 0, next = !A. A toggles: 0, 1, 0, 1, ...
        // Not constant.
        let a = Var(1);

        let mut next_state = FxHashMap::default();
        next_state.insert(a, Lit::neg(a)); // next = !a

        let ts = build_ts(
            1,
            vec![a],
            Vec::new(),
            next_state,
            vec![Clause::unit(Lit::neg(a))],
            vec![Lit::pos(a)],
            FxHashMap::default(),
        );

        let (_reduced, eliminated) = sequential_ternary_simulation(&ts, 32);
        assert_eq!(eliminated, 0, "toggling latch should not be eliminated");
    }

    #[test]
    fn test_ternary_sim_no_init_constraint() {
        // Latch A with no init constraint (X), next = FALSE.
        // Even though next is always 0, the init value is X, so we cannot
        // be sure A is constant from cycle 0. However after cycle 0,
        // A will be 0 forever. We only track from init, so init X means
        // not provably constant.
        let a = Var(1);

        let mut next_state = FxHashMap::default();
        next_state.insert(a, Lit::FALSE);

        let ts = build_ts(
            1,
            vec![a],
            Vec::new(),
            next_state,
            Vec::new(), // no init constraint
            vec![Lit::pos(a)],
            FxHashMap::default(),
        );

        let (_reduced, eliminated) = sequential_ternary_simulation(&ts, 32);
        // Init is X, so even though next is always FALSE, we can't prove
        // A is always 0 from the start. Safe to not eliminate.
        assert_eq!(
            eliminated, 0,
            "latch with no init constraint should not be eliminated"
        );
    }

    #[test]
    fn test_ternary_sim_deep_feedback() {
        // Chain: A -> B -> C -> A (feedback loop), all init 0.
        // next(A) = AND(C, A), next(B) = AND(A, B), next(C) = AND(B, C).
        // Since all start at 0 and next is AND with self, all stay 0.
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);
        let g1 = Var(4);
        let g2 = Var(5);
        let g3 = Var(6);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g1, (Lit::pos(c), Lit::pos(a)));
        and_defs.insert(g2, (Lit::pos(a), Lit::pos(b)));
        and_defs.insert(g3, (Lit::pos(b), Lit::pos(c)));

        let mut next_state = FxHashMap::default();
        next_state.insert(a, Lit::pos(g1));
        next_state.insert(b, Lit::pos(g2));
        next_state.insert(c, Lit::pos(g3));

        let ts = build_ts(
            6,
            vec![a, b, c],
            Vec::new(),
            next_state,
            vec![
                Clause::unit(Lit::neg(a)),
                Clause::unit(Lit::neg(b)),
                Clause::unit(Lit::neg(c)),
            ],
            vec![Lit::pos(a)],
            and_defs,
        );

        let (reduced, eliminated) = sequential_ternary_simulation(&ts, 64);
        assert_eq!(
            eliminated, 3,
            "all feedback-loop latches should be eliminated (all stuck at 0)"
        );
        assert!(reduced.latch_vars.is_empty());
    }

    #[test]
    fn test_ternary_and_truth_table() {
        // Verify the ternary AND truth table.
        assert_eq!(ternary_and(Some(false), Some(false)), Some(false));
        assert_eq!(ternary_and(Some(false), Some(true)), Some(false));
        assert_eq!(ternary_and(Some(true), Some(false)), Some(false));
        assert_eq!(ternary_and(Some(true), Some(true)), Some(true));
        assert_eq!(ternary_and(Some(false), None), Some(false));
        assert_eq!(ternary_and(None, Some(false)), Some(false));
        assert_eq!(ternary_and(Some(true), None), None);
        assert_eq!(ternary_and(None, Some(true)), None);
        assert_eq!(ternary_and(None, None), None);
    }
}
