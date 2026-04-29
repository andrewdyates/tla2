// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SAT-based init state enumeration, forward simulation, and direct equivalence.
//!
//! Two complementary approaches for SCORR candidate generation:
//!
//! 1. **Signature-based** (`latch_signatures_sat_seeded`): Enumerates valid
//!    initial states by solving init constraints with z4-sat, then forward-
//!    simulates for multiple steps to generate per-latch signatures. This is
//!    strictly more powerful than unit-clause init seeding because it handles
//!    non-unit init constraints and exposes reachable-state equivalences.
//!
//! 2. **Direct SAT equivalence** (`sat_init_equivalence_candidates`): Pairwise
//!    checks `latch_a XOR latch_b` under init constraints. If UNSAT, the
//!    latches are provably init-equivalent — guaranteed to pass SCORR's init
//!    verification phase. No false negatives from unlucky random patterns.
//!
//! Reference: rIC3 `transys/sim.rs` — `init_simulation(count)` enumerates
//! valid initial states, `rt_simulation(&init, steps)` forward-simulates.
//! rIC3 `scorr.rs` — `solve_with_restart_limit([], ..., 10)` for budgeted
//! SAT-based init equivalence checking.

use rustc_hash::FxHashMap;

use crate::sat_types::{Lit, SatResult, SatSolver, Var, Z4SatCdclSolver};
use crate::transys::Transys;

use super::simulation::{
    latch_signatures_init_seeded, random_pattern, simulate_multi_round, SimSig,
};
use super::substitution::sorted_and_defs;

/// Number of valid init states to enumerate via SAT for init-seeded SCORR.
/// rIC3 uses 1 (`init_simulation(1)`). We use 4 to get slightly richer
/// coverage of the init state space without excessive SAT overhead.
const SAT_INIT_STATES: usize = 4;

/// Number of forward simulation steps from each SAT-enumerated init state.
/// rIC3 uses 10 (`rt_simulation(&init, 10)`).
const FORWARD_SIM_STEPS: usize = 10;

/// Enumerate valid initial states by solving the init constraints with z4-sat.
///
/// Returns up to `max_states` initial state assignments. Each assignment is
/// a map from latch variable to its boolean value in that init state.
///
/// This is richer than `extract_init_values` (unit-clause extraction) because
/// it handles non-unit init constraints (e.g., binary clauses from non-constant
/// resets like `latch_a <=> other_lit`). The SAT solver finds full satisfying
/// assignments of all init constraints.
///
/// After finding each state, a blocking clause is added to prevent re-discovering
/// the same state, enabling enumeration of diverse init states.
///
/// Reference: rIC3 `transys/sim.rs` — `init_simulation(count)` uses the init
/// solver to enumerate valid initial states.
fn enumerate_init_states(ts: &Transys, max_states: usize) -> Vec<FxHashMap<Var, bool>> {
    if ts.latch_vars.is_empty() || ts.init_clauses.is_empty() {
        return Vec::new();
    }

    let mut solver = Z4SatCdclSolver::new(ts.max_var + 1);
    solver.ensure_vars(ts.max_var);

    // Load init constraints.
    for clause in &ts.init_clauses {
        solver.add_clause(&clause.lits);
    }

    // Also load constraint literals (environment assumptions).
    for &constraint in &ts.constraint_lits {
        solver.add_clause(&[constraint]);
    }

    let mut states = Vec::new();

    for _ in 0..max_states {
        match solver.solve(&[]) {
            SatResult::Sat => {
                let mut state = FxHashMap::default();
                let mut blocking_clause = Vec::new();

                for &latch in &ts.latch_vars {
                    let val = solver.value(Lit::pos(latch)).unwrap_or(false);
                    state.insert(latch, val);

                    // Build blocking clause: negate this assignment to
                    // force the solver to find a different state next time.
                    if val {
                        blocking_clause.push(Lit::neg(latch));
                    } else {
                        blocking_clause.push(Lit::pos(latch));
                    }
                }

                states.push(state);
                solver.add_clause(&blocking_clause);
            }
            SatResult::Unsat | SatResult::Unknown => break,
        }
    }

    states
}

/// Evaluate a single boolean literal given a value assignment.
#[inline]
fn eval_bool_lit(lit: Lit, values: &FxHashMap<Var, bool>) -> bool {
    let base = values.get(&lit.var()).copied().unwrap_or(false);
    if lit.is_negated() {
        !base
    } else {
        base
    }
}

/// Forward-simulate one step from a state through the AND gate graph.
///
/// Given current latch values and random input values, computes the
/// next-state values by:
/// 1. Setting latch and input values
/// 2. Evaluating AND gates in topological order
/// 3. Computing next-state latch values from next_state mapping
///
/// Returns the next state (latch var -> bool).
fn forward_simulate_step(
    ts: &Transys,
    latch_values: &FxHashMap<Var, bool>,
    step: usize,
    state_idx: usize,
) -> FxHashMap<Var, bool> {
    // Evaluate all variables in the combinational circuit.
    let mut values: FxHashMap<Var, bool> = FxHashMap::default();

    // Set latch values.
    for (&var, &val) in latch_values {
        values.insert(var, val);
    }

    // Set random input values (deterministic based on step and state index).
    let seed_base = (state_idx as u64).wrapping_mul(0x517C_C1B7_2722_0A95)
        ^ (step as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
        ^ 0xDEAD_BEEF_0000_CAFE;
    for &var in &ts.input_vars {
        let r = random_pattern(seed_base ^ (var.0 as u64));
        values.insert(var, r & 1 != 0);
    }

    // Evaluate AND gates in topological order (sorted by output var index).
    for (out, rhs0, rhs1) in sorted_and_defs(ts) {
        let v0 = eval_bool_lit(rhs0, &values);
        let v1 = eval_bool_lit(rhs1, &values);
        values.insert(out, v0 && v1);
    }

    // Compute next-state latch values.
    let mut next_latch_values = FxHashMap::default();
    for &latch in &ts.latch_vars {
        if let Some(&next_lit) = ts.next_state.get(&latch) {
            next_latch_values.insert(latch, eval_bool_lit(next_lit, &values));
        } else {
            // No next-state function: keep current value.
            next_latch_values.insert(latch, latch_values.get(&latch).copied().unwrap_or(false));
        }
    }

    next_latch_values
}

/// Direct SAT-based init equivalence candidate generation.
///
/// For each pair of latches, uses the init SAT solver to check whether
/// `latch_a XOR latch_b` is satisfiable under init constraints. If UNSAT,
/// the two latches are provably equivalent in all initial states and become
/// SCORR candidates.
///
/// Also checks negated equivalence: `latch_a XNOR latch_b` (i.e., whether
/// they are always complementary under init).
///
/// This is strictly stronger than simulation-based candidate generation
/// because it provides a *complete* answer for init equivalence — no false
/// negatives from unlucky random patterns. Candidates generated here are
/// guaranteed to pass SCORR's init-check phase, meaning the only remaining
/// verification is the inductive step.
///
/// Uses a conflict budget per query to bound worst-case time. Pairs that
/// exceed the budget are skipped (treated as non-equivalent).
///
/// Reference: rIC3's `solve_with_restart_limit([], ..., 10)` uses budgeted
/// SAT for init-state equivalence checking during SCORR candidate refinement.
pub(crate) fn sat_init_equivalence_candidates(ts: &Transys) -> Vec<(Var, Var, bool)> {
    if ts.latch_vars.len() < 2 || ts.init_clauses.is_empty() {
        return Vec::new();
    }

    // Build init solver with all init constraints + environment constraints.
    let mut solver = Z4SatCdclSolver::new(ts.max_var + 1);
    solver.ensure_vars(ts.max_var);
    for clause in &ts.init_clauses {
        solver.add_clause(&clause.lits);
    }
    for &constraint in &ts.constraint_lits {
        solver.add_clause(&[constraint]);
    }

    // Conflict budget per equivalence query. Keep this small since we're
    // testing O(n^2) pairs. 50 conflicts is enough for most init constraint
    // structures (typically unit/binary clauses).
    const CONFLICT_BUDGET: u64 = 50;

    // Limit the number of pairs tested to avoid quadratic blowup.
    // For circuits with many latches, only test the first MAX_PAIRS pairs.
    const MAX_PAIRS: usize = 2048;

    let latches = &ts.latch_vars;
    let n = latches.len();
    let mut candidates = Vec::new();
    let mut pairs_tested = 0usize;

    for i in 0..n {
        if pairs_tested >= MAX_PAIRS {
            break;
        }
        for j in (i + 1)..n {
            if pairs_tested >= MAX_PAIRS {
                break;
            }
            pairs_tested += 1;

            let a = latches[i];
            let b = latches[j];

            // Check positive equivalence: is (a XOR b) satisfiable under init?
            // a XOR b = (a AND !b) OR (!a AND b). If both are UNSAT, a == b under init.
            let case1 = solver.solve_with_budget(&[Lit::pos(a), Lit::neg(b)], CONFLICT_BUDGET);
            if case1 == SatResult::Unknown {
                continue; // Budget exceeded, skip this pair.
            }
            if case1 == SatResult::Unsat {
                let case2 = solver.solve_with_budget(&[Lit::neg(a), Lit::pos(b)], CONFLICT_BUDGET);
                if case2 == SatResult::Unsat {
                    // a == b in all init states.
                    candidates.push((a, b, false));
                    continue;
                }
                if case2 == SatResult::Unknown {
                    continue;
                }
            }

            // Check negated equivalence: is (a XNOR b) satisfiable under init?
            // a XNOR b = (a AND b) OR (!a AND !b). If both are UNSAT, a == !b under init.
            let neg_case1 = solver.solve_with_budget(&[Lit::pos(a), Lit::pos(b)], CONFLICT_BUDGET);
            if neg_case1 == SatResult::Unknown {
                continue;
            }
            if neg_case1 == SatResult::Unsat {
                let neg_case2 =
                    solver.solve_with_budget(&[Lit::neg(a), Lit::neg(b)], CONFLICT_BUDGET);
                if neg_case2 == SatResult::Unsat {
                    // a == !b in all init states.
                    candidates.push((a, b, true));
                }
            }
        }
    }

    candidates.sort_unstable_by_key(|(x, y, negated)| (y.0, x.0, *negated as u8));
    candidates
}

/// Generate latch signatures from SAT-enumerated init states + forward simulation.
///
/// Enumerates up to `SAT_INIT_STATES` valid initial states via z4-sat, then
/// forward-simulates each for `FORWARD_SIM_STEPS` steps. The accumulated
/// state vectors form per-latch signatures for SCORR candidate detection.
///
/// This is strictly more powerful than unit-clause init seeding because:
/// 1. It handles non-unit init constraints (binary/ternary clauses from
///    non-constant resets).
/// 2. Forward simulation exposes reachable-state equivalences that single-step
///    simulation misses.
/// 3. Multiple init states cover more of the init state space.
///
/// Reference: rIC3 `scorr.rs:69-73`:
/// ```text
/// let init = self.ts.init_simulation(1);
/// let mut rt = self.ts.rt_simulation(&init, 10);
/// ```
pub(crate) fn latch_signatures_sat_seeded(ts: &Transys) -> FxHashMap<Var, SimSig> {
    let init_states = enumerate_init_states(ts, SAT_INIT_STATES);
    if init_states.is_empty() {
        // Fall back to unit-clause seeded simulation.
        return latch_signatures_init_seeded(ts);
    }

    let n = ts.max_var as usize + 1;
    let mut sigs = vec![0u64; n];

    // For each init state, forward simulate and accumulate signatures.
    for (state_idx, init_state) in init_states.iter().enumerate() {
        let mut current_state = init_state.clone();

        // Include the init state itself in the signature.
        let state_mix = random_pattern(state_idx as u64 ^ 0xCAFE_BABE_DEAD_BEEF);
        for &latch in &ts.latch_vars {
            let val = current_state.get(&latch).copied().unwrap_or(false);
            let bit = if val { u64::MAX } else { 0u64 };
            sigs[latch.index()] = sigs[latch.index()]
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(bit ^ state_mix);
        }

        // Forward simulate for FORWARD_SIM_STEPS.
        for step in 0..FORWARD_SIM_STEPS {
            current_state = forward_simulate_step(ts, &current_state, step, state_idx);

            let step_mix = random_pattern(
                (state_idx as u64).wrapping_mul(0x1234_5678_9ABC_DEF0)
                    ^ (step as u64 + 1).wrapping_mul(0xFEDC_BA98_7654_3210),
            );
            for &latch in &ts.latch_vars {
                let val = current_state.get(&latch).copied().unwrap_or(false);
                let bit = if val { u64::MAX } else { 0u64 };
                sigs[latch.index()] = sigs[latch.index()]
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .wrapping_add(bit ^ step_mix);
            }
        }
    }

    // Also run regular random simulation to combine with SAT-seeded results.
    // This ensures we don't lose discrimination from random patterns.
    let random_sigs = simulate_multi_round(ts);
    for i in 0..n.min(random_sigs.len()) {
        sigs[i] = sigs[i]
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(random_sigs[i]);
    }

    // Extract latch signatures (keyed by next-state function, like other methods).
    let mut result = FxHashMap::default();
    for &latch in &ts.latch_vars {
        if let Some(&next_lit) = ts.next_state.get(&latch) {
            let sig = sigs.get(next_lit.var().index()).copied().unwrap_or(0);
            let sig = if next_lit.is_negated() { !sig } else { sig };
            result.insert(latch, sig);
        }
    }
    result
}
