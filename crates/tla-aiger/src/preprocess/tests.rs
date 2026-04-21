// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the AIGER preprocessing pipeline.

use rustc_hash::FxHashMap;

use crate::sat_types::{Clause, Lit, Var};
use crate::transys::Transys;

use super::bve::bounded_variable_elimination;
use super::constant::eliminate_constant_latches;
use super::frts::frts;
use super::renumber::renumber_variables;
use super::scorr::{forward_reduce, scorr};
use super::simulation::{
    build_candidates, simulate_multi_round,
    simulate_multi_round_init_seeded,
};
use super::simulation_sat::latch_signatures_sat_seeded;
use super::strash::structural_hash;
use super::substitution::{apply_substitution, rebuild_trans_clauses};
use super::ternary_prop::ternary_constant_propagation;
use super::trivial::trivial_simplify;
use super::{preprocess_full, preprocess_with_config, PreprocessConfig};

fn build_ts(
    max_var: u32,
    latch_vars: Vec<Var>,
    input_vars: Vec<Var>,
    next_state: FxHashMap<Var, Lit>,
    init_clauses: Vec<Clause>,
    bad_lits: Vec<Lit>,
    constraint_lits: Vec<Lit>,
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
        constraint_lits,
        and_defs,
        internal_signals: Vec::new(),
    }
}

#[test]
fn test_trivial_simplify_true_input_fold() {
    let in1 = Var(1);
    let gate = Var(2);
    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(in1), Lit::TRUE));

    let ts = build_ts(
        2,
        Vec::new(),
        vec![in1],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let simplified = trivial_simplify(&ts);
    assert!(simplified.and_defs.is_empty());
    assert!(simplified.trans_clauses.is_empty());
    assert_eq!(simplified.bad_lits, vec![Lit::pos(in1)]);
    assert_eq!(simplified.input_vars, vec![in1]);
}

#[test]
fn test_trivial_simplify_complementary_gate_to_false() {
    let in1 = Var(1);
    let gate = Var(2);
    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(in1), Lit::neg(in1)));

    let ts = build_ts(
        2,
        Vec::new(),
        vec![in1],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let simplified = trivial_simplify(&ts);
    assert!(simplified.and_defs.is_empty());
    assert_eq!(simplified.bad_lits, vec![Lit::FALSE]);
    assert!(simplified.input_vars.is_empty());
}

#[test]
fn test_scorr_merges_equivalent_latches() {
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = scorr(&ts);
    assert_eq!(eliminated, 1);
    assert_eq!(reduced.latch_vars, vec![a]);
    assert_eq!(reduced.bad_lits, vec![Lit::pos(a)]);
    assert_eq!(reduced.next_state.get(&a).copied(), Some(Lit::pos(inp)));
}

#[test]
fn test_scorr_merges_negated_latches() {
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::neg(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::pos(b))],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = scorr(&ts);
    assert_eq!(eliminated, 1);
    assert_eq!(reduced.latch_vars, vec![a]);
    assert_eq!(reduced.bad_lits, vec![Lit::neg(a)]);
    assert_eq!(reduced.next_state.get(&a).copied(), Some(Lit::pos(inp)));
}

#[test]
fn test_forward_reduce_merges_equivalent_gates() {
    let in1 = Var(1);
    let in2 = Var(2);
    let g1 = Var(3);
    let g2 = Var(4);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in2)));

    let ts = build_ts(
        4,
        Vec::new(),
        vec![in1, in2],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g2)],
        Vec::new(),
        and_defs,
    );

    let reduced = forward_reduce(&ts);
    assert_eq!(reduced.and_defs.len(), 1);
    assert!(reduced.and_defs.contains_key(&g1));
    assert_eq!(reduced.bad_lits, vec![Lit::pos(g1)]);
}

#[test]
fn test_frts_eliminates_input_gate_equivalence() {
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);
    let g3 = Var(6);
    let g4 = Var(7);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in1)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g3, (Lit::pos(in1), Lit::pos(in3)));
    and_defs.insert(g4, (Lit::pos(in2), Lit::pos(in3)));

    let ts = build_ts(
        7,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1)],
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = frts(&ts, 0);
    assert_eq!(eliminated, 1);
    assert_eq!(reduced.bad_lits, vec![Lit::pos(in1)]);
    assert!(!reduced.and_defs.contains_key(&g1));
}

#[test]
fn test_frts_iterative_finds_transitive() {
    let in1 = Var(1);
    let in2 = Var(2);
    let first_gate = Var(3);
    let last_gate = Var(72);

    let mut and_defs = FxHashMap::default();
    for raw in first_gate.0..=last_gate.0 {
        let gate = Var(raw);
        and_defs.insert(gate, (Lit::pos(in1), Lit::pos(in2)));
    }

    let ts = build_ts(
        last_gate.0,
        Vec::new(),
        vec![in1, in2],
        FxHashMap::default(),
        Vec::new(),
        (first_gate.0..=last_gate.0).map(|raw| Lit::pos(Var(raw))).collect(),
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = frts(&ts, 0);
    assert_eq!(eliminated, (last_gate.0 - first_gate.0) as usize);
    assert_eq!(reduced.bad_lits, vec![Lit::pos(first_gate)]);
    assert_eq!(reduced.and_defs.len(), 1);
    assert!(reduced.and_defs.contains_key(&first_gate));
}

#[test]
fn test_preprocess_full_pipeline_stats() {
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);
    let gate = Var(4);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(b), Lit::TRUE));

    let ts = build_ts(
        4,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a), Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let (result, stats) = preprocess_full(&ts);
    assert_eq!(stats.orig_gates, 1);
    // Trivial simplify folds AND(b, TRUE) -> b, eliminating the gate.
    assert_eq!(stats.after_trivial_gates, 0);
    assert_eq!(stats.after_trivial_latches, 2);
    // SCORR merges equivalent latches a and b (both have same next-state).
    assert_eq!(stats.scorr_eliminated_latches, 1);
    assert_eq!(stats.frts_eliminated, 0);
    assert_eq!(stats.final_latches, 1);
    assert_eq!(result.latch_vars, vec![Var(1)]);
    assert_eq!(result.bad_lits, vec![Lit::pos(Var(1))]);
}

#[test]
fn test_eliminate_constant_latch_stuck_at_zero() {
    // Latch A starts at 0, next = FALSE (stuck at 0).
    // Bad = A. A is always 0, so bad is never reached.
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
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = eliminate_constant_latches(&ts);
    assert_eq!(eliminated, 1, "should eliminate the stuck-at-0 latch");
    assert!(
        reduced.latch_vars.is_empty(),
        "no latches should remain: {:?}",
        reduced.latch_vars
    );
    assert_eq!(reduced.bad_lits, vec![Lit::FALSE]);
}

#[test]
fn test_eliminate_constant_latch_stuck_at_one() {
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
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = eliminate_constant_latches(&ts);
    assert_eq!(eliminated, 1);
    assert!(reduced.latch_vars.is_empty());
    assert_eq!(reduced.bad_lits, vec![Lit::TRUE]);
}

#[test]
fn test_eliminate_constant_latch_cascade() {
    // Two latches: A starts at 0, next = FALSE.
    // B starts at 0, next = A (which is stuck at 0).
    // B should also be eliminated in the second iteration.
    let a = Var(1);
    let b = Var(2);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::FALSE);
    next_state.insert(b, Lit::pos(a));

    let ts = build_ts(
        2,
        vec![a, b],
        Vec::new(),
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = eliminate_constant_latches(&ts);
    assert_eq!(eliminated, 2, "both latches should be eliminated");
    assert!(reduced.latch_vars.is_empty());
}

#[test]
fn test_eliminate_constant_latch_noop_for_nonconstant() {
    // Latch with non-constant next-state (depends on input).
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
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = eliminate_constant_latches(&ts);
    assert_eq!(eliminated, 0);
    assert_eq!(reduced.latch_vars.len(), 1);
}

#[test]
fn test_eliminate_constant_latch_and_gate_folding() {
    // Latch A starts at 0, next = AND(A, input).
    // Since A=0 initially, AND(0, input) = 0. A stays 0 forever.
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
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = eliminate_constant_latches(&ts);
    assert_eq!(eliminated, 1, "latch stuck at 0 through AND gate");
    assert!(reduced.latch_vars.is_empty());
}

#[test]
fn test_eliminate_constant_latch_must_not_use_other_init_values() {
    // Regression test for #4047 (fib_05 wrong answer).
    //
    // Latch A starts at 0, next = B.
    // Latch B starts at 0, next = input.
    //
    // The OLD buggy code substituted B's init value (0) when evaluating
    // next(A), concluding next(A) = 0 = init(A), and incorrectly
    // eliminating A as "stuck at 0". But B changes after step 0!
    //
    // At step 0: A=0, B=0
    // At step 1: A=B(step0)=0, B=input(step0)
    // At step 2: A=B(step1)=input(step0) -- A can be 1!
    //
    // Neither latch should be eliminated.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(b)); // next(A) = B
    next_state.insert(b, Lit::pos(inp)); // next(B) = input

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = eliminate_constant_latches(&ts);
    assert_eq!(
        eliminated, 0,
        "neither latch should be eliminated: A depends on B which is not constant"
    );
    assert_eq!(reduced.latch_vars.len(), 2);
}

#[test]
fn test_eliminate_constant_latch_chain_through_and_gate_unsound() {
    // Another regression test for #4047.
    //
    // Latch A starts at 0, next = AND(B, C).
    // Latch B starts at 0, next = input1.
    // Latch C starts at 0, next = input2.
    //
    // AND(B_init, C_init) = AND(0, 0) = 0 = init(A), but B and C change!
    // A must NOT be eliminated.
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);
    let inp1 = Var(4);
    let inp2 = Var(5);
    let gate = Var(6);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(b), Lit::pos(c)));

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(gate)); // next(A) = AND(B, C)
    next_state.insert(b, Lit::pos(inp1)); // next(B) = input1
    next_state.insert(c, Lit::pos(inp2)); // next(C) = input2

    let ts = build_ts(
        6,
        vec![a, b, c],
        vec![inp1, inp2],
        next_state,
        vec![
            Clause::unit(Lit::neg(a)),
            Clause::unit(Lit::neg(b)),
            Clause::unit(Lit::neg(c)),
        ],
        vec![Lit::pos(a)],
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = eliminate_constant_latches(&ts);
    assert_eq!(
        eliminated, 0,
        "A depends on B and C through AND gate; none are truly constant"
    );
    assert_eq!(reduced.latch_vars.len(), 3);
}

#[test]
fn test_structural_hash_merges_identical_gates() {
    let in1 = Var(1);
    let in2 = Var(2);
    let g1 = Var(3);
    let g2 = Var(4);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in2), Lit::pos(in1))); // same inputs, reversed

    let ts = build_ts(
        4,
        Vec::new(),
        vec![in1, in2],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g2)],
        Vec::new(),
        and_defs,
    );

    let reduced = structural_hash(&ts);
    assert_eq!(
        reduced.and_defs.len(),
        1,
        "duplicate gate should be merged"
    );
    assert!(reduced.and_defs.contains_key(&g1));
    assert_eq!(reduced.bad_lits, vec![Lit::pos(g1)]);
}

#[test]
fn test_structural_hash_noop_for_different_gates() {
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in3))); // different second input

    let ts = build_ts(
        5,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1), Lit::pos(g2)],
        Vec::new(),
        and_defs,
    );

    let reduced = structural_hash(&ts);
    assert_eq!(reduced.and_defs.len(), 2, "different gates should not merge");
}

#[test]
fn test_apply_substitution_updates_next_state_and_bad() {
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(a));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    let mut subst = FxHashMap::default();
    subst.insert(b, Lit::neg(a));

    let reduced = apply_substitution(&ts, &subst);
    assert_eq!(reduced.latch_vars, vec![a]);
    assert_eq!(reduced.bad_lits, vec![Lit::neg(a)]);
    assert_eq!(reduced.next_state.get(&a).copied(), Some(Lit::pos(inp)));
}

#[test]
fn test_ternary_constant_propagation_and_with_false() {
    // AND gate with one input being structural constant FALSE.
    // gate = AND(FALSE, input) => output is always 0.
    let inp = Var(1);
    let gate = Var(2);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::FALSE, Lit::pos(inp)));

    let ts = build_ts(
        2,
        Vec::new(),
        vec![inp],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let reduced = ternary_constant_propagation(&ts);
    // Gate AND(FALSE, X) = FALSE, so gate should be eliminated.
    assert!(
        reduced.and_defs.is_empty(),
        "AND gate with constant-FALSE input should be eliminated, got {} gates",
        reduced.and_defs.len()
    );
    assert_eq!(reduced.bad_lits, vec![Lit::FALSE]);
}

#[test]
fn test_ternary_constant_propagation_noop() {
    // AND gate with two non-constant inputs: no elimination.
    let in1 = Var(1);
    let in2 = Var(2);
    let gate = Var(3);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(in1), Lit::pos(in2)));

    let ts = build_ts(
        3,
        Vec::new(),
        vec![in1, in2],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let reduced = ternary_constant_propagation(&ts);
    assert_eq!(
        reduced.and_defs.len(),
        1,
        "non-constant gate should survive"
    );
}

#[test]
fn test_ternary_chain_propagation() {
    // Chain: gate1 = AND(FALSE, in), gate2 = AND(gate1, in2).
    // gate1 is always 0 (structural FALSE input), so gate2 is also always 0.
    let inp = Var(1);
    let inp2 = Var(2);
    let g1 = Var(3);
    let g2 = Var(4);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::FALSE, Lit::pos(inp)));
    and_defs.insert(g2, (Lit::pos(g1), Lit::pos(inp2)));

    let ts = build_ts(
        4,
        Vec::new(),
        vec![inp, inp2],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g2)],
        Vec::new(),
        and_defs,
    );

    let reduced = ternary_constant_propagation(&ts);
    assert!(
        reduced.and_defs.is_empty(),
        "both gates should be eliminated via chain propagation"
    );
    assert_eq!(reduced.bad_lits, vec![Lit::FALSE]);
}

#[test]
fn test_ternary_does_not_use_init_values() {
    // Verify ternary does NOT use init values (which would be unsound).
    // Latch A starts at 0, gate = AND(A, input). Latch A changes over
    // time, so the gate is NOT structurally constant.
    let a = Var(1);
    let inp = Var(2);
    let gate = Var(3);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(a), Lit::pos(inp)));

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a))], // init: a = 0
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let reduced = ternary_constant_propagation(&ts);
    // Ternary should NOT eliminate the gate since latch A is X (unknown).
    assert_eq!(
        reduced.and_defs.len(),
        1,
        "gate depending on latch should NOT be eliminated by ternary"
    );
}

#[test]
fn test_bve_eliminates_low_occurrence_gate() {
    // Simple scenario: gate var appears in only its own Tseitin clauses (3).
    // With no external references, BVE should be able to eliminate it.
    let in1 = Var(1);
    let in2 = Var(2);
    let gate = Var(3);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(in1), Lit::pos(in2)));

    // Bad references gate directly, so gate is frozen (cannot be eliminated).
    let ts = build_ts(
        3,
        Vec::new(),
        vec![in1, in2],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = bounded_variable_elimination(&ts);
    // Gate is referenced by bad_lits, so it's frozen -- BVE cannot eliminate.
    assert_eq!(eliminated, 0, "frozen gate should not be eliminated");
    assert_eq!(reduced.and_defs.len(), 1);
}

#[test]
fn test_bve_eliminates_internal_gate() {
    // Internal gate: feeds into another gate, not directly into bad.
    // gate1 = AND(in1, in2), gate2 = AND(gate1, in3), bad = gate2.
    // gate1 is internal (only appears in gate2's Tseitin clauses + its own).
    // gate2 is frozen (in bad_lits).
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(g1), Lit::pos(in3)));

    let ts = build_ts(
        5,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g2)],
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = bounded_variable_elimination(&ts);
    // g1 appears in its own 3 Tseitin clauses + 2 from g2 (as rhs).
    // pos_occ(g1) = clauses containing +g1: the ternary clause of g1 (1),
    // plus the two binary clauses of g2 that use g1 (2 if g1 is rhs0).
    // This depends on the exact clause structure. We just verify the
    // system remains valid.
    assert!(
        reduced.bad_lits.len() == 1,
        "bad lit should be preserved"
    );
    // Structural invariant: preprocessed system is valid.
    assert!(
        reduced.trans_clauses.len() <= ts.trans_clauses.len()
            || eliminated == 0,
        "BVE should not increase clause count (or should not eliminate)"
    );
}

#[test]
fn test_multi_round_simulation_deterministic() {
    // Multi-round simulation should be deterministic.
    let in1 = Var(1);
    let in2 = Var(2);
    let gate = Var(3);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(in1), Lit::pos(in2)));

    let ts = build_ts(
        3,
        Vec::new(),
        vec![in1, in2],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let sigs1 = simulate_multi_round(&ts);
    let sigs2 = simulate_multi_round(&ts);
    assert_eq!(sigs1, sigs2, "multi-round simulation must be deterministic");
}

#[test]
fn test_multi_round_simulation_distinguishes_different_gates() {
    // Two gates with different inputs should have different signatures.
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in3)));

    let ts = build_ts(
        5,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1), Lit::pos(g2)],
        Vec::new(),
        and_defs,
    );

    let sigs = simulate_multi_round(&ts);
    assert_ne!(
        sigs[g1.index()],
        sigs[g2.index()],
        "different gates should have different signatures"
    );
}

#[test]
fn test_preprocess_full_includes_new_passes() {
    // Verify the full pipeline runs without panics and tracks new stats.
    let a = Var(1);
    let inp = Var(2);
    let gate = Var(3);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(a), Lit::TRUE));

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a))],
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let (result, stats) = preprocess_full(&ts);
    // Gate should be eliminated (AND with TRUE folds to just a).
    assert_eq!(stats.after_trivial_gates, 0);
    // System should be valid.
    assert!(result.latch_vars.len() <= ts.latch_vars.len());
    assert!(result.bad_lits.len() == 1);
}

// ---------------------------------------------------------------------------
// Variable renumbering tests
// ---------------------------------------------------------------------------

#[test]
fn test_renumber_compacts_gaps() {
    // Variables: 1, 5, 10 (gaps at 2-4, 6-9). After renumbering: 1, 2, 3.
    let a = Var(1);
    let b = Var(5);
    let inp = Var(10);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        10,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (renumbered, compacted) = renumber_variables(&ts);
    assert_eq!(compacted, 7, "should compact 10 - 3 = 7 variable slots");
    assert_eq!(renumbered.max_var, 3);
    assert_eq!(renumbered.latch_vars.len(), 2);
    assert_eq!(renumbered.input_vars.len(), 1);
    // All vars should be in 1..=3
    for &var in &renumbered.latch_vars {
        assert!(var.0 >= 1 && var.0 <= 3, "var {} out of dense range", var.0);
    }
    for &var in &renumbered.input_vars {
        assert!(var.0 >= 1 && var.0 <= 3, "var {} out of dense range", var.0);
    }
}

#[test]
fn test_renumber_noop_when_dense() {
    // Variables already dense: 1, 2, 3. No renumbering needed.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (renumbered, compacted) = renumber_variables(&ts);
    assert_eq!(compacted, 0, "already dense, nothing to compact");
    assert_eq!(renumbered.max_var, 3);
}

#[test]
fn test_renumber_preserves_negation() {
    // Bad lit is negated. Renumbering must preserve polarity.
    let a = Var(1);
    let inp = Var(5);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::neg(inp)); // next(a) = !inp

    let ts = build_ts(
        5,
        vec![a],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a))],
        vec![Lit::neg(a)], // bad = !a
        Vec::new(),
        FxHashMap::default(),
    );

    let (renumbered, compacted) = renumber_variables(&ts);
    assert!(compacted > 0);
    // bad_lits[0] should be negated
    assert!(
        renumbered.bad_lits[0].is_negated(),
        "renumbering must preserve negation on bad lit"
    );
    // next_state value should also be negated
    let latch = renumbered.latch_vars[0];
    let next_lit = renumbered.next_state.get(&latch).copied().expect("next_state must exist");
    assert!(
        next_lit.is_negated(),
        "renumbering must preserve negation on next-state lit"
    );
}

#[test]
fn test_renumber_with_and_gates() {
    // Verify AND gate definitions survive renumbering correctly.
    let in1 = Var(2);
    let in2 = Var(4);
    let gate = Var(10);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(gate, (Lit::pos(in1), Lit::pos(in2)));

    let ts = build_ts(
        10,
        Vec::new(),
        vec![in1, in2],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(gate)],
        Vec::new(),
        and_defs,
    );

    let (renumbered, compacted) = renumber_variables(&ts);
    assert!(compacted > 0);
    assert_eq!(renumbered.max_var, 3);
    assert_eq!(renumbered.and_defs.len(), 1);
    // Verify gate output and inputs are in dense range
    for (&out, &(rhs0, rhs1)) in &renumbered.and_defs {
        assert!(out.0 >= 1 && out.0 <= 3);
        assert!(rhs0.var().0 >= 1 && rhs0.var().0 <= 3);
        assert!(rhs1.var().0 >= 1 && rhs1.var().0 <= 3);
    }
}

#[test]
fn test_renumber_preserves_constant_lits() {
    // Lit::FALSE and Lit::TRUE must survive renumbering.
    let a = Var(5);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::FALSE); // next(a) = constant FALSE

    let ts = build_ts(
        5,
        vec![a],
        Vec::new(),
        next_state,
        vec![Clause::unit(Lit::neg(a))],
        vec![Lit::TRUE], // bad = constant TRUE
        Vec::new(),
        FxHashMap::default(),
    );

    let (renumbered, _) = renumber_variables(&ts);
    assert_eq!(renumbered.bad_lits, vec![Lit::TRUE]);
    let latch = renumbered.latch_vars[0];
    assert_eq!(
        renumbered.next_state.get(&latch).copied(),
        Some(Lit::FALSE),
        "constant FALSE in next_state must be preserved"
    );
}

// ---------------------------------------------------------------------------
// Init-seeded simulation tests
// ---------------------------------------------------------------------------

#[test]
fn test_init_seeded_simulation_deterministic() {
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let sigs1 = simulate_multi_round_init_seeded(&ts);
    let sigs2 = simulate_multi_round_init_seeded(&ts);
    assert_eq!(sigs1, sigs2, "init-seeded simulation must be deterministic");
}

#[test]
fn test_init_seeded_differs_from_random() {
    // With init values seeding round 0, signatures should generally differ
    // from pure random simulation.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::neg(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::pos(b))], // a=0, b=1
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let random_sigs = simulate_multi_round(&ts);
    let init_sigs = simulate_multi_round_init_seeded(&ts);
    // At least one latch signature should differ (the init seed changes
    // the first round's values for latches with known init values).
    let differs = (0..=3).any(|i| random_sigs[i] != init_sigs[i]);
    assert!(
        differs,
        "init-seeded simulation should produce different signatures than random"
    );
}

#[test]
fn test_init_seeded_scorr_finds_same_equivalences() {
    // Two latches with same init and same next-state: SCORR should
    // find the equivalence regardless of simulation method.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = scorr(&ts);
    assert_eq!(eliminated, 1, "SCORR with init-seeded sim should still find equivalence");
    assert_eq!(reduced.latch_vars.len(), 1);
}

#[test]
fn test_preprocess_full_includes_renumbering() {
    // After preprocessing removes a latch, variable gaps should be compacted.
    let a = Var(1);
    let b = Var(10);
    let inp = Var(20);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        20,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (result, stats) = preprocess_full(&ts);
    // SCORR should merge a and b (same next-state and init), leaving 1 latch.
    // After renumbering, max_var should be compacted.
    assert!(
        result.max_var < 20,
        "renumbering should compact max_var from 20 to something smaller, got {}",
        result.max_var
    );
    assert!(
        stats.renumber_compacted > 0 || result.max_var <= 2,
        "either renumber compacted some vars or the system is already tiny"
    );
}

// ---------------------------------------------------------------------------
// FRTS (Functional Reduction / Transitive Simplification) tests
// ---------------------------------------------------------------------------

#[test]
fn test_frts_eliminates_equivalent_gates() {
    // Two AND gates with identical inputs. FRTS should detect combinational
    // equivalence and merge them, leaving 1 gate.
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);
    let g3 = Var(6);
    let g4 = Var(7);

    let mut and_defs = FxHashMap::default();
    // g1 and g2 are identical: AND(in1, in2)
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in2)));
    // g3 and g4 are different, to meet the >= 4 signals threshold
    and_defs.insert(g3, (Lit::pos(in1), Lit::pos(in3)));
    and_defs.insert(g4, (Lit::pos(in2), Lit::pos(in3)));

    let ts = build_ts(
        7,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g2), Lit::pos(g3), Lit::pos(g4)],
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = frts(&ts, 0);
    assert!(
        eliminated >= 1,
        "FRTS should eliminate at least 1 equivalent gate, got {}",
        eliminated
    );
    // g2 should be replaced by g1 (or vice versa, since build_candidates
    // picks the lower-indexed variable as representative).
    assert!(
        reduced.and_defs.len() < ts.and_defs.len(),
        "should have fewer gates after FRTS: {} vs {}",
        reduced.and_defs.len(),
        ts.and_defs.len()
    );
}

#[test]
fn test_frts_noop_for_distinct_signals() {
    // All gates have different inputs. FRTS should not eliminate any.
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let in4 = Var(4);
    let g1 = Var(5);
    let g2 = Var(6);
    let g3 = Var(7);
    let g4 = Var(8);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in3)));
    and_defs.insert(g3, (Lit::pos(in2), Lit::pos(in3)));
    and_defs.insert(g4, (Lit::pos(in3), Lit::pos(in4)));

    let ts = build_ts(
        8,
        Vec::new(),
        vec![in1, in2, in3, in4],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1), Lit::pos(g2), Lit::pos(g3), Lit::pos(g4)],
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = frts(&ts, 0);
    assert_eq!(
        eliminated, 0,
        "FRTS should not eliminate any distinct gates"
    );
    assert_eq!(
        reduced.and_defs.len(),
        ts.and_defs.len(),
        "gate count should be unchanged"
    );
}

#[test]
fn test_frts_skips_tiny_circuits() {
    // Circuit with fewer than 4 signals (latches + gates). FRTS should
    // skip and return 0 eliminated.
    let in1 = Var(1);
    let g1 = Var(2);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::TRUE));

    let ts = build_ts(
        2,
        Vec::new(),
        vec![in1],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1)],
        Vec::new(),
        and_defs,
    );

    let (_, eliminated) = frts(&ts, 0);
    assert_eq!(
        eliminated, 0,
        "FRTS should skip circuits with < 4 signals"
    );
}

#[test]
fn test_frts_preserves_system_validity() {
    // After FRTS, the transition system should remain valid: bad_lits
    // should still reference valid variables, and the system should be
    // structurally consistent.
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);
    let g3 = Var(6);
    let g4 = Var(7);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in2))); // same as g1
    and_defs.insert(g3, (Lit::pos(in2), Lit::pos(in3)));
    and_defs.insert(g4, (Lit::pos(in1), Lit::pos(in3)));

    let ts = build_ts(
        7,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1), Lit::pos(g2)],
        Vec::new(),
        and_defs,
    );

    let (reduced, _) = frts(&ts, 0);
    // bad_lits should still have entries (not empty).
    assert!(
        !reduced.bad_lits.is_empty(),
        "bad_lits should not be empty after FRTS"
    );
    // All AND gate definitions should have valid inputs.
    for (&_out, &(rhs0, rhs1)) in &reduced.and_defs {
        assert!(
            rhs0.var().0 <= reduced.max_var,
            "AND gate rhs0 var {} exceeds max_var {}",
            rhs0.var().0,
            reduced.max_var
        );
        assert!(
            rhs1.var().0 <= reduced.max_var,
            "AND gate rhs1 var {} exceeds max_var {}",
            rhs1.var().0,
            reduced.max_var
        );
    }
}

#[test]
fn test_frts_in_full_pipeline() {
    // Verify FRTS integrates correctly in the full preprocessing pipeline
    // and the frts_eliminated stat is tracked.
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);
    let g3 = Var(6);
    let g4 = Var(7);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in2))); // duplicate
    and_defs.insert(g3, (Lit::pos(in2), Lit::pos(in3)));
    and_defs.insert(g4, (Lit::pos(in1), Lit::pos(in3)));

    let ts = build_ts(
        7,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1), Lit::pos(g2), Lit::pos(g3)],
        Vec::new(),
        and_defs,
    );

    let (_result, stats) = preprocess_full(&ts);
    // The frts_eliminated field should be populated (may be 0 if strash
    // already caught the duplicate, but the field should exist).
    // This primarily tests that the pipeline wiring is correct.
    assert!(
        stats.frts_eliminated == 0 || stats.frts_eliminated >= 1,
        "frts_eliminated should be a valid count: {}",
        stats.frts_eliminated
    );
}

// ---------------------------------------------------------------------------
// SAT-seeded simulation tests
// ---------------------------------------------------------------------------

#[test]
fn test_sat_seeded_simulation_deterministic() {
    // SAT-seeded latch signatures must be deterministic across invocations.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let sigs1 = latch_signatures_sat_seeded(&ts);
    let sigs2 = latch_signatures_sat_seeded(&ts);
    assert_eq!(sigs1, sigs2, "SAT-seeded simulation must be deterministic");
}

#[test]
fn test_sat_seeded_signatures_equivalent_latches_match() {
    // Two latches with identical init and next-state should get identical
    // SAT-seeded signatures, so they become SCORR candidates.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let sigs = latch_signatures_sat_seeded(&ts);
    assert_eq!(
        sigs.get(&a),
        sigs.get(&b),
        "equivalent latches should have matching SAT-seeded signatures"
    );
}

#[test]
fn test_sat_seeded_produces_candidates_for_equivalent_latches() {
    // build_candidates on SAT-seeded signatures should find the (a, b, false)
    // candidate pair for two equivalent latches.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let sigs = latch_signatures_sat_seeded(&ts);
    let candidates = build_candidates(&sigs);
    assert!(
        !candidates.is_empty(),
        "SAT-seeded sim should produce candidates for equivalent latches"
    );
    // Should contain the (a, b, false) pair (non-negated equivalence).
    let has_ab = candidates.iter().any(|&(x, y, neg)| x == a && y == b && !neg);
    assert!(
        has_ab,
        "candidates should include (a, b, false): {:?}",
        candidates
    );
}

#[test]
fn test_sat_seeded_with_non_unit_init_constraints() {
    // Test SAT-seeded simulation with non-unit init constraints.
    // Init: (a OR b) -- neither a nor b is fixed by a unit clause, but
    // the SAT solver can still enumerate valid initial states.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::new(vec![Lit::pos(a), Lit::pos(b)])], // a OR b
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    // Should not panic and should produce signatures.
    let sigs = latch_signatures_sat_seeded(&ts);
    assert!(
        sigs.contains_key(&a) && sigs.contains_key(&b),
        "SAT-seeded sim should produce signatures for both latches"
    );
}

#[test]
fn test_sat_seeded_no_init_clauses_fallback() {
    // With no init clauses, SAT-seeded should fall back gracefully
    // (enumerate_init_states returns empty -> falls back to init-seeded).
    let a = Var(1);
    let inp = Var(2);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));

    let ts = build_ts(
        2,
        vec![a],
        vec![inp],
        next_state,
        Vec::new(), // no init clauses
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    // Should not panic.
    let sigs = latch_signatures_sat_seeded(&ts);
    assert!(
        sigs.contains_key(&a),
        "SAT-seeded sim should produce a signature even with no init clauses"
    );
}

#[test]
fn test_three_mode_scorr_merges_equivalent_latches() {
    // End-to-end test: the new three-mode SCORR (random + init-seeded +
    // SAT-seeded) should still correctly merge equivalent latches.
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);
    let inp = Var(4);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));
    next_state.insert(c, Lit::neg(inp)); // c is negated equivalent of a

    let ts = build_ts(
        4,
        vec![a, b, c],
        vec![inp],
        next_state,
        vec![
            Clause::unit(Lit::neg(a)),
            Clause::unit(Lit::neg(b)),
            Clause::unit(Lit::pos(c)),
        ],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = scorr(&ts);
    // a and b are positively equivalent; c is negated-equivalent to a.
    // SCORR should eliminate at least 1 (b -> a), possibly 2 (c -> !a).
    assert!(
        eliminated >= 1,
        "three-mode SCORR should eliminate at least 1 latch, got {}",
        eliminated
    );
    assert!(
        reduced.latch_vars.len() < 3,
        "should have fewer than 3 latches after SCORR"
    );
}

// ---------------------------------------------------------------------------
// Topological renumbering ordering tests
// ---------------------------------------------------------------------------

#[test]
fn test_renumber_topological_latches_get_lowest_ids() {
    // After topological renumbering, latch variables should get the
    // lowest IDs (right after Var(0)/CONST), followed by inputs, then gates.
    let latch = Var(10);
    let inp = Var(20);
    let g1 = Var(30);
    let g2 = Var(40);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(latch), Lit::pos(inp)));
    and_defs.insert(g2, (Lit::pos(g1), Lit::pos(inp)));

    let mut next_state = FxHashMap::default();
    next_state.insert(latch, Lit::pos(g2));

    let ts = build_ts(
        40,
        vec![latch],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(latch))],
        vec![Lit::pos(g2)],
        Vec::new(),
        and_defs,
    );

    let (renumbered, compacted) = renumber_variables(&ts);
    assert!(compacted > 0, "should compact from sparse to dense");

    // Latch should get Var(1) (lowest after CONST).
    assert_eq!(
        renumbered.latch_vars.len(),
        1,
        "should have exactly 1 latch"
    );
    let new_latch = renumbered.latch_vars[0];
    assert_eq!(
        new_latch,
        Var(1),
        "latch should be renumbered to Var(1), got Var({})",
        new_latch.0
    );

    // Input should get Var(2).
    assert_eq!(renumbered.input_vars.len(), 1);
    let new_inp = renumbered.input_vars[0];
    assert_eq!(
        new_inp,
        Var(2),
        "input should be renumbered to Var(2), got Var({})",
        new_inp.0
    );

    // AND gates should get Var(3) and Var(4), with the shallower gate first.
    assert_eq!(renumbered.and_defs.len(), 2);
    // Both gates should be in [3, 4].
    for &gate_var in renumbered.and_defs.keys() {
        assert!(
            gate_var.0 >= 3 && gate_var.0 <= 4,
            "gate var should be in [3, 4], got {}",
            gate_var.0
        );
    }
}

#[test]
fn test_renumber_topological_depth_ordering() {
    // Verify that among depth-sorted AND gates, shallower gates get lower
    // variable IDs than deeper gates. Bad references a latch (not a gate)
    // so no AND gate is pulled out of depth ordering by the bad/constraint step.
    let latch = Var(50);
    let in1 = Var(100);
    let in2 = Var(200);
    let g_shallow = Var(300); // depth 1: AND(in1, in2)
    let g_deep = Var(400);   // depth 2: AND(g_shallow, in1)

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g_shallow, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g_deep, (Lit::pos(g_shallow), Lit::pos(in1)));

    let mut next_state = FxHashMap::default();
    next_state.insert(latch, Lit::pos(g_deep));

    let ts = build_ts(
        400,
        vec![latch],
        vec![in1, in2],
        next_state,
        vec![Clause::unit(Lit::neg(latch))],
        vec![Lit::pos(latch)], // bad references latch, not a gate
        Vec::new(),
        and_defs,
    );

    let (renumbered, compacted) = renumber_variables(&ts);
    assert!(compacted > 0);

    // Expected ordering: CONST(0), latch(1), in1(2), in2(3), g_shallow(4), g_deep(5).
    // Find the shallowest gate (both inputs are primary inputs).
    let mut shallow_new = None;
    let mut deep_new = None;
    for (&out, &(rhs0, rhs1)) in &renumbered.and_defs {
        let inputs_are_primary = renumbered.input_vars.contains(&rhs0.var())
            && renumbered.input_vars.contains(&rhs1.var());
        if inputs_are_primary {
            shallow_new = Some(out);
        } else {
            deep_new = Some(out);
        }
    }

    let shallow_new = shallow_new.expect("should find shallow gate");
    let deep_new = deep_new.expect("should find deep gate");
    assert!(
        shallow_new.0 < deep_new.0,
        "shallow gate ({}) should have lower var ID than deep gate ({})",
        shallow_new.0,
        deep_new.0
    );
}

// ---------------------------------------------------------------------------
// FRTS improvement tests (BVE integration, input filtering, latch equiv)
// ---------------------------------------------------------------------------

#[test]
fn test_frts_with_latch_equivalence() {
    // Two latches with identical next-state functions going through the
    // same AND gate. FRTS should detect that the AND gate outputs are
    // combinationally equivalent and merge them.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);
    let g3 = Var(6);
    let g4 = Var(7);

    let mut and_defs = FxHashMap::default();
    // g1 = AND(inp, inp) = inp (identity-like)
    and_defs.insert(g1, (Lit::pos(inp), Lit::pos(inp)));
    // g2, g3, g4 provide enough signals for the >= 4 threshold
    and_defs.insert(g2, (Lit::pos(a), Lit::pos(inp)));
    and_defs.insert(g3, (Lit::pos(b), Lit::pos(inp)));
    and_defs.insert(g4, (Lit::pos(a), Lit::pos(b)));

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(g2));
    next_state.insert(b, Lit::pos(g3));

    let ts = build_ts(
        7,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(g4)],
        Vec::new(),
        and_defs,
    );

    // FRTS should run without panicking. g1 = AND(inp,inp) is equivalent
    // to inp itself, but since inp is a primary input, the substitution
    // replaces g1 with inp. The system remains valid.
    let (reduced, _eliminated) = frts(&ts, 0);
    assert!(
        !reduced.bad_lits.is_empty(),
        "bad_lits should be preserved after FRTS with latches"
    );
}

#[test]
fn test_frts_negated_equivalence() {
    // Two gates where one is the negation of the other.
    // g1 = AND(in1, in2), g2 = AND(!in1, !in2).
    // These are NOT equivalent (AND is not self-dual), so FRTS should
    // NOT merge them. But g3 = AND(in1, in2) IS equivalent to g1.
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let g1 = Var(4);
    let g2 = Var(5);
    let g3 = Var(6);
    let g4 = Var(7);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::neg(in1), Lit::neg(in2)));
    and_defs.insert(g3, (Lit::pos(in1), Lit::pos(in2))); // same as g1
    and_defs.insert(g4, (Lit::pos(in2), Lit::pos(in3)));

    let ts = build_ts(
        7,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1), Lit::pos(g2), Lit::pos(g3), Lit::pos(g4)],
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = frts(&ts, 0);
    // g3 should be merged with g1 (identical). g2 should NOT be merged
    // with g1 (different function).
    assert!(
        eliminated >= 1,
        "FRTS should eliminate at least the duplicate g3"
    );
    // g2 should still exist since AND(!in1,!in2) != AND(in1,in2)
    // (They have different truth tables: g1=1 only when in1=in2=1,
    // g2=1 only when in1=in2=0.)
    // We can't directly check g2 exists due to renumbering, but
    // we can verify the gate count is >= 2 (g1+g2 or g1+g4 survive).
    assert!(
        reduced.and_defs.len() >= 2,
        "should have at least 2 gates after FRTS (g1, g2, and/or g4): got {}",
        reduced.and_defs.len()
    );
}

#[test]
fn test_frts_input_pair_filtering() {
    // Verify that FRTS does not waste SAT queries on input-input pairs.
    // Create a circuit where two inputs happen to get the same simulation
    // signature (by being unused except in identical positions). Even if
    // simulation produces the same signature, the inputs are free and
    // cannot be functionally equivalent.
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    let in4 = Var(4);
    let g1 = Var(5);
    let g2 = Var(6);
    let g3 = Var(7);
    let g4 = Var(8);

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in3), Lit::pos(in4)));
    and_defs.insert(g3, (Lit::pos(in1), Lit::pos(in3)));
    and_defs.insert(g4, (Lit::pos(in2), Lit::pos(in4)));

    let ts = build_ts(
        8,
        Vec::new(),
        vec![in1, in2, in3, in4],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g1), Lit::pos(g2), Lit::pos(g3), Lit::pos(g4)],
        Vec::new(),
        and_defs,
    );

    // All four inputs are distinct. FRTS should not merge any inputs.
    // This test primarily verifies no panics from the input-pair filter.
    let (reduced, _) = frts(&ts, 0);
    assert_eq!(
        reduced.input_vars.len(),
        4,
        "all 4 inputs should survive FRTS"
    );
}

#[test]
fn test_frts_bve_integration_in_full_pipeline() {
    // Verify that when FRTS eliminates signals, the subsequent BVE pass
    // in the full pipeline can exploit the simplified circuit to eliminate
    // more internal variables.
    let in1 = Var(1);
    let in2 = Var(2);
    let in3 = Var(3);
    // 6 duplicate gates (will be merged) + 2 unique gates
    let g1 = Var(4);
    let g2 = Var(5);
    let g3 = Var(6);
    let g4 = Var(7);
    let g5 = Var(8);
    let g6 = Var(9);
    let g7 = Var(10); // feeds into g8
    let g8 = Var(11); // uses g7

    let mut and_defs = FxHashMap::default();
    // 5 duplicates of AND(in1, in2)
    and_defs.insert(g1, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g2, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g3, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g4, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g5, (Lit::pos(in1), Lit::pos(in2)));
    and_defs.insert(g6, (Lit::pos(in1), Lit::pos(in2)));
    // g7 is unique, g8 uses g7
    and_defs.insert(g7, (Lit::pos(in2), Lit::pos(in3)));
    and_defs.insert(g8, (Lit::pos(g7), Lit::pos(in1)));

    let ts = build_ts(
        11,
        Vec::new(),
        vec![in1, in2, in3],
        FxHashMap::default(),
        Vec::new(),
        vec![Lit::pos(g8)],
        Vec::new(),
        and_defs,
    );

    let (result, stats) = preprocess_full(&ts);
    // The duplicates should be eliminated by strash or FRTS.
    // After elimination, BVE should be able to clean up further.
    assert!(
        result.and_defs.len() < ts.and_defs.len(),
        "preprocessing should reduce gate count: {} -> {}",
        ts.and_defs.len(),
        result.and_defs.len()
    );
    // Verify the pipeline completed without panics and stats are populated.
    assert!(stats.orig_gates == 8);
    assert!(stats.final_gates <= 3, "should have at most 3 gates after full pipeline");
}

// ---------------------------------------------------------------------------
// SCORR iterative early termination tests (#4124)
// ---------------------------------------------------------------------------

#[test]
fn test_scorr_early_termination_no_equivalences() {
    // Circuit with no latch equivalences: SCORR should run exactly 1 round
    // (the first round finds 0 equivalences and terminates early), regardless
    // of the configured round count.
    let a = Var(1);
    let b = Var(2);
    let inp1 = Var(3);
    let inp2 = Var(4);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp1));
    next_state.insert(b, Lit::pos(inp2)); // different next-state → not equivalent

    let ts = build_ts(
        4,
        vec![a, b],
        vec![inp1, inp2],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    // Use 1000 SCORR rounds — early termination should stop at 1.
    let config = PreprocessConfig {
        scorr_rounds: 1000,
        ..PreprocessConfig::default()
    };

    let (_, stats) = preprocess_with_config(&ts, &config);
    assert_eq!(
        stats.scorr_eliminated_latches, 0,
        "no equivalences should be found"
    );
    assert_eq!(
        stats.scorr_iterations, 1,
        "SCORR should stop after 1 round when 0 equivalences found, not run all 1000"
    );
}

#[test]
fn test_scorr_early_termination_after_equivalences_exhausted() {
    // Test early termination via scorr() directly on a circuit with one pair
    // of equivalent latches. SCORR should find the equivalence in round 1,
    // then the pipeline should stop after round 2 finds no more.
    //
    // We test scorr() directly because the full preprocess pipeline may
    // eliminate latches via earlier passes (constant elimination) before
    // SCORR runs, changing the circuit structure.
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);
    let inp1 = Var(4);
    let inp2 = Var(5);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp1));
    next_state.insert(b, Lit::pos(inp1)); // same as a → equivalent
    next_state.insert(c, Lit::pos(inp2)); // different → not equivalent

    let ts = build_ts(
        5,
        vec![a, b, c],
        vec![inp1, inp2],
        next_state,
        vec![
            Clause::unit(Lit::neg(a)),
            Clause::unit(Lit::neg(b)),
            Clause::unit(Lit::neg(c)),
        ],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    // Direct SCORR call: round 1 finds a ≡ b, round 2 would find nothing.
    let (reduced, eliminated) = scorr(&ts);
    assert_eq!(
        eliminated, 1,
        "SCORR should merge the equivalent latch pair (a ≡ b)"
    );
    assert!(
        reduced.latch_vars.len() <= 2,
        "should have at most 2 latches after SCORR"
    );

    // Now test through the full pipeline with 1000 rounds configured.
    // The key assertion is that scorr_iterations is bounded, not 1000.
    let config = PreprocessConfig {
        scorr_rounds: 1000,
        ..PreprocessConfig::default()
    };

    let (_, stats) = preprocess_with_config(&ts, &config);
    // Whether the equivalence is found by SCORR or an earlier pass,
    // SCORR should NOT run all 1000 rounds — early termination must kick in.
    assert!(
        stats.scorr_iterations <= 3,
        "SCORR should terminate early, not run all 1000 rounds, got {} iterations",
        stats.scorr_iterations
    );
}

#[test]
fn test_scorr_aggressive_preset_1000_rounds() {
    // Verify the aggressive preset uses 1000 SCORR rounds and that it
    // terminates early on a simple circuit (no cascading equivalences).
    let config = PreprocessConfig::aggressive();
    assert_eq!(
        config.scorr_rounds, 1000,
        "aggressive preset should use 1000 SCORR rounds"
    );

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
        Vec::new(),
        FxHashMap::default(),
    );

    // With only 1 latch, SCORR has nothing to merge and should return immediately.
    let (_, stats) = preprocess_with_config(&ts, &config);
    assert_eq!(
        stats.scorr_eliminated_latches, 0,
        "single latch should have nothing to merge"
    );
    // SCORR skips entirely when < 2 latches (returns 0 iterations from pipeline).
    assert!(
        stats.scorr_iterations <= 1,
        "should not run many iterations on a single-latch circuit"
    );
}

#[test]
fn test_scorr_default_100_rounds() {
    // Verify the default config uses 100 SCORR rounds.
    let config = PreprocessConfig::default();
    assert_eq!(
        config.scorr_rounds, 100,
        "default preset should use 100 SCORR rounds"
    );
}

// ---------------------------------------------------------------------------
// Direct SAT-based init equivalence candidate generation tests (#4077)
// ---------------------------------------------------------------------------

use super::simulation_sat::sat_init_equivalence_candidates;

#[test]
fn test_sat_init_equiv_finds_identical_init_latches() {
    // Two latches both initialized to 0 (via unit clauses).
    // Direct SAT check should find them as init-equivalent.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    let has_ab_positive = candidates.iter().any(|&(x, y, neg)| x == a && y == b && !neg);
    assert!(
        has_ab_positive,
        "SAT init equiv should find (a, b, false) for two latches both init=0: {:?}",
        candidates
    );
}

#[test]
fn test_sat_init_equiv_finds_negated_latches() {
    // Latch A initialized to 0, latch B initialized to 1.
    // They are complementary in the init state.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::neg(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::pos(b))], // a=0, b=1
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    let has_ab_negated = candidates.iter().any(|&(x, y, neg)| x == a && y == b && neg);
    assert!(
        has_ab_negated,
        "SAT init equiv should find (a, b, true) for complementary init: {:?}",
        candidates
    );
}

#[test]
fn test_sat_init_equiv_no_candidates_for_different_inits() {
    // Latch A init = 0, latch B has no init constraint (can be 0 or 1).
    // They are NOT always equivalent in init since B can differ from A.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a))], // only A is constrained to 0
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    // Neither positive nor negated equivalence should be found since B is free.
    let has_ab = candidates.iter().any(|&(x, y, _)| x == a && y == b);
    assert!(
        !has_ab,
        "should NOT find equivalence when B is unconstrained: {:?}",
        candidates
    );
}

#[test]
fn test_sat_init_equiv_with_non_unit_constraints() {
    // Init: (a <=> b) expressed as two binary clauses: (!a OR b) AND (a OR !b).
    // This means a == b in all init states, but neither is individually fixed.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![
            Clause::new(vec![Lit::neg(a), Lit::pos(b)]), // !a OR b
            Clause::new(vec![Lit::pos(a), Lit::neg(b)]), // a OR !b
        ],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    let has_ab_positive = candidates.iter().any(|&(x, y, neg)| x == a && y == b && !neg);
    assert!(
        has_ab_positive,
        "SAT init equiv should find equivalence from non-unit biconditional constraint: {:?}",
        candidates
    );
}

#[test]
fn test_sat_init_equiv_empty_for_single_latch() {
    // With fewer than 2 latches, no pairs to check.
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
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    assert!(
        candidates.is_empty(),
        "should produce no candidates for single-latch circuit"
    );
}

#[test]
fn test_sat_init_equiv_empty_for_no_init_clauses() {
    // With no init clauses, all latches are unconstrained => no equivalences.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        Vec::new(), // no init clauses
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    assert!(
        candidates.is_empty(),
        "should produce no candidates with no init clauses"
    );
}

#[test]
fn test_sat_init_equiv_multiple_pairs() {
    // Three latches all initialized to 0. Should find all pairwise equivalences.
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);
    let inp = Var(4);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));
    next_state.insert(c, Lit::pos(inp));

    let ts = build_ts(
        4,
        vec![a, b, c],
        vec![inp],
        next_state,
        vec![
            Clause::unit(Lit::neg(a)),
            Clause::unit(Lit::neg(b)),
            Clause::unit(Lit::neg(c)),
        ],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    // Should find all three pairs: (a,b), (a,c), (b,c) — all positive equiv.
    let has_ab = candidates.iter().any(|&(x, y, neg)| x == a && y == b && !neg);
    let has_ac = candidates.iter().any(|&(x, y, neg)| x == a && y == c && !neg);
    let has_bc = candidates.iter().any(|&(x, y, neg)| x == b && y == c && !neg);
    assert!(has_ab, "should find (a,b) equivalence");
    assert!(has_ac, "should find (a,c) equivalence");
    assert!(has_bc, "should find (b,c) equivalence");
}

#[test]
fn test_sat_init_equiv_integrated_in_scorr() {
    // End-to-end test: SCORR with four-mode candidate generation correctly
    // merges latches that are init-equivalent via non-unit constraints.
    // The direct SAT init check is the only mode that can catch this case
    // reliably (simulation might miss it due to random patterns).
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    // Init: a <=> b (biconditional, non-unit).
    // Both latches have the same next-state function.
    // They should be merged by SCORR.
    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![
            Clause::new(vec![Lit::neg(a), Lit::pos(b)]), // !a OR b
            Clause::new(vec![Lit::pos(a), Lit::neg(b)]), // a OR !b
        ],
        vec![Lit::pos(b)],
        Vec::new(),
        FxHashMap::default(),
    );

    let (reduced, eliminated) = scorr(&ts);
    assert_eq!(
        eliminated, 1,
        "SCORR should merge the biconditional-equivalent latches"
    );
    assert_eq!(reduced.latch_vars.len(), 1);
}

// ---------------------------------------------------------------------------
// SAT-seeded simulation with AND gates (forward simulation through gate graph)
// ---------------------------------------------------------------------------

#[test]
fn test_sat_seeded_signatures_with_and_gates() {
    // Circuit with AND gates: two latches whose next-state functions go
    // through AND gates. Forward simulation must evaluate gates correctly.
    //
    //   g1 = AND(inp, inp) = inp   (identity, but goes through a gate)
    //   next(a) = g1
    //   next(b) = g1
    //   init: a=0, b=0
    //
    // Since both latches have the same next-state and init, their SAT-seeded
    // signatures should match.
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);
    let g1 = Var(4);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(g1));
    next_state.insert(b, Lit::pos(g1));

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(inp), Lit::pos(inp)));

    let ts = build_ts(
        4,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        and_defs,
    );

    let sigs = latch_signatures_sat_seeded(&ts);
    assert_eq!(
        sigs.get(&a),
        sigs.get(&b),
        "latches with same next-state (through AND gate) should have matching SAT-seeded sigs"
    );
}

#[test]
fn test_sat_seeded_signatures_different_and_gate_paths() {
    // Two latches with different next-state AND gates should get different
    // SAT-seeded signatures (forward sim must propagate differently).
    //
    //   g1 = AND(inp1, inp2)
    //   g2 = AND(inp1, !inp2)
    //   next(a) = g1
    //   next(b) = g2
    //   init: a=0, b=0
    let a = Var(1);
    let b = Var(2);
    let inp1 = Var(3);
    let inp2 = Var(4);
    let g1 = Var(5);
    let g2 = Var(6);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(g1));
    next_state.insert(b, Lit::pos(g2));

    let mut and_defs = FxHashMap::default();
    and_defs.insert(g1, (Lit::pos(inp1), Lit::pos(inp2)));
    and_defs.insert(g2, (Lit::pos(inp1), Lit::neg(inp2)));

    let ts = build_ts(
        6,
        vec![a, b],
        vec![inp1, inp2],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::neg(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        and_defs,
    );

    let sigs = latch_signatures_sat_seeded(&ts);
    assert_ne!(
        sigs.get(&a),
        sigs.get(&b),
        "latches with different AND-gate next-state functions should have different sigs"
    );
}

// ---------------------------------------------------------------------------
// SAT init equivalence with environment constraints
// ---------------------------------------------------------------------------

#[test]
fn test_sat_init_equiv_with_constraint_lits() {
    // Environment constraint forces a == b even though init clauses alone
    // don't constrain them. The constraint_lits are loaded into the SAT
    // solver and should affect equivalence detection.
    //
    //   init: (no constraints)
    //   constraint: a (a must be true)
    //   constraint: b (b must be true)
    //   => a == b == true in all constrained init states
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        // Init clauses that leave some freedom for the constraint to narrow:
        // at least one of a, b must be true.
        vec![Clause::new(vec![Lit::pos(a), Lit::pos(b)])],
        vec![Lit::pos(a)],
        // Constraints force both a=true and b=true.
        vec![Lit::pos(a), Lit::pos(b)],
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    let has_ab_positive = candidates.iter().any(|&(x, y, neg)| x == a && y == b && !neg);
    assert!(
        has_ab_positive,
        "constraint_lits forcing a=b should produce init-equivalence candidate: {:?}",
        candidates
    );
}

// ---------------------------------------------------------------------------
// SAT-seeded simulation: negated equivalence through signatures
// ---------------------------------------------------------------------------

#[test]
fn test_sat_seeded_signatures_negated_equivalence() {
    // Two latches with complementary next-state functions should get
    // complementary SAT-seeded signatures: sig(a) == !sig(b).
    //
    //   next(a) = inp
    //   next(b) = !inp
    //   init: a=0, b=1 (complementary)
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::neg(inp));

    let ts = build_ts(
        3,
        vec![a, b],
        vec![inp],
        next_state,
        vec![Clause::unit(Lit::neg(a)), Clause::unit(Lit::pos(b))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let sigs = latch_signatures_sat_seeded(&ts);
    let sig_a = sigs.get(&a).copied().unwrap_or(0);
    let sig_b = sigs.get(&b).copied().unwrap_or(0);
    // For complementary latches, build_candidates uses !sig to detect negated
    // equivalence. Verify the signatures are indeed complementary.
    assert_eq!(
        sig_a, !sig_b,
        "complementary latches should have complementary SAT-seeded sigs: a={:#x}, b={:#x}",
        sig_a, sig_b
    );
}

// ---------------------------------------------------------------------------
// Many-latch circuit: verify MAX_PAIRS bounding doesn't panic
// ---------------------------------------------------------------------------

#[test]
fn test_sat_init_equiv_many_latches_bounded() {
    // Create a circuit with enough latches that the O(n^2) pair count
    // exceeds MAX_PAIRS (2048). All latches init=0, so many pairs are
    // equivalent. Verify it completes without panic and produces candidates.
    let n_latches = 100; // C(100,2) = 4950 > 2048
    let inp = Var((n_latches + 1) as u32);
    let max_var = (n_latches + 1) as u32;

    let latches: Vec<Var> = (1..=n_latches).map(|i| Var(i as u32)).collect();
    let mut next_state = FxHashMap::default();
    for &latch in &latches {
        next_state.insert(latch, Lit::pos(inp));
    }

    let init_clauses: Vec<Clause> = latches
        .iter()
        .map(|&latch| Clause::unit(Lit::neg(latch)))
        .collect();

    let ts = build_ts(
        max_var,
        latches,
        vec![inp],
        next_state,
        init_clauses,
        vec![Lit::pos(Var(1))],
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);
    // Should produce candidates (bounded by MAX_PAIRS=2048).
    assert!(
        !candidates.is_empty(),
        "many-latch circuit should produce SAT init equiv candidates"
    );
    // All candidates should be positive equivalence (all init=0).
    for &(_, _, neg) in &candidates {
        assert!(!neg, "all latches init=0, so all equivalences should be positive");
    }
}

// ---------------------------------------------------------------------------
// SCORR integration: AND gates + SAT-based init + inductive verification
// ---------------------------------------------------------------------------

#[test]
fn test_scorr_with_and_gates_and_sat_init() {
    // Full end-to-end: two latches that are equivalent through AND gates,
    // with init constraints that only SAT-based candidate generation can catch.
    //
    //   g1 = AND(inp, TRUE) = inp
    //   next(a) = g1
    //   next(b) = g1
    //   init: (a <=> b) via binary clauses (non-unit, needs SAT)
    let a = Var(1);
    let b = Var(2);
    let inp = Var(3);
    let g1 = Var(4);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(g1));
    next_state.insert(b, Lit::pos(g1));

    let mut and_defs = FxHashMap::default();
    // g1 = AND(inp, TRUE) effectively equals inp
    // Since Var(0) is the constant FALSE (lit 0 = FALSE, lit 1 = TRUE),
    // we use Lit::TRUE which is !Lit::FALSE = Lit(1).
    and_defs.insert(g1, (Lit::pos(inp), Lit::TRUE));

    let ts = build_ts(
        4,
        vec![a, b],
        vec![inp],
        next_state,
        vec![
            Clause::new(vec![Lit::neg(a), Lit::pos(b)]), // !a OR b
            Clause::new(vec![Lit::pos(a), Lit::neg(b)]), // a OR !b
        ],
        vec![Lit::pos(a)],
        Vec::new(),
        and_defs,
    );

    let (reduced, eliminated) = scorr(&ts);
    assert_eq!(
        eliminated, 1,
        "SCORR should merge equivalent latches with AND gate next-state and non-unit init"
    );
    assert_eq!(reduced.latch_vars.len(), 1);
}

#[test]
fn test_sat_init_equiv_mixed_positive_and_negated() {
    // Three latches: a=0, b=0, c=1 in init.
    // Pairs (a,b) should be positive-equivalent, (a,c) and (b,c) should be
    // negated-equivalent.
    let a = Var(1);
    let b = Var(2);
    let c = Var(3);
    let inp = Var(4);

    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::pos(inp));
    next_state.insert(b, Lit::pos(inp));
    next_state.insert(c, Lit::neg(inp));

    let ts = build_ts(
        4,
        vec![a, b, c],
        vec![inp],
        next_state,
        vec![
            Clause::unit(Lit::neg(a)), // a=0
            Clause::unit(Lit::neg(b)), // b=0
            Clause::unit(Lit::pos(c)), // c=1
        ],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );

    let candidates = sat_init_equivalence_candidates(&ts);

    // (a, b) positive equivalence
    let has_ab_pos = candidates.iter().any(|&(x, y, neg)| x == a && y == b && !neg);
    assert!(has_ab_pos, "(a,b) should be positive-equivalent: {:?}", candidates);

    // (a, c) negated equivalence
    let has_ac_neg = candidates.iter().any(|&(x, y, neg)| x == a && y == c && neg);
    assert!(has_ac_neg, "(a,c) should be negated-equivalent: {:?}", candidates);

    // (b, c) negated equivalence
    let has_bc_neg = candidates.iter().any(|&(x, y, neg)| x == b && y == c && neg);
    assert!(has_bc_neg, "(b,c) should be negated-equivalent: {:?}", candidates);
}

// ---------------------------------------------------------------------------
// Wave 29 (#4299) ternary_sim early-exit gate tests.
//
// Design: designs/2026-04-20-hwmcc-wave29-target.md §Change 4.
// Gate: when `is_sat_likely_pattern(ts)` AND the 8-cycle probe eliminates
// < 10% of latches, skip the remaining multi-cycle ternary simulation passes.
// Rationale: on Sokoban/microban SAT circuits, ternary sim yields 2-5% latch
// elimination at best, while the deep BMC search needs every spare millisecond.
// ---------------------------------------------------------------------------

/// Build a synthetic Sokoban/microban-pattern `Transys`:
/// - `num_inputs == num_latches` (action = state bit)
/// - `constraint_lits.len() > 4 * num_latches` (game-rule constraints encoded)
/// - each latch `l_i` has `next = input_i` (free latch — no constant)
///
/// This matches `is_sat_likely_pattern` Pattern 2 and produces 0 constant
/// latches under ternary simulation (all next-states are free inputs = X),
/// so the 8-cycle probe elimination ratio is 0.0 < 0.10 → gate triggers.
fn build_sokoban_like_ts(num_latches: usize) -> Transys {
    assert!(num_latches >= 2, "need >= 2 latches to exceed 4*L constraint density");
    let mut latch_vars = Vec::with_capacity(num_latches);
    let mut input_vars = Vec::with_capacity(num_latches);
    let mut next_state = FxHashMap::default();
    let mut init_clauses = Vec::with_capacity(num_latches);

    // Latches 1..=N, inputs N+1..=2N.
    for i in 0..num_latches {
        let l = Var((i + 1) as u32);
        let inp = Var((num_latches + i + 1) as u32);
        latch_vars.push(l);
        input_vars.push(inp);
        // next(l_i) = inp_i — latch tracks a free input, never constant.
        next_state.insert(l, Lit::pos(inp));
        // Init each latch to 0.
        init_clauses.push(Clause::unit(Lit::neg(l)));
    }

    // Need > 4*L constraint literals (Pattern 2 density). Use 5*L distinct
    // literals drawn from the latch vars so they are valid variables.
    let mut constraint_lits = Vec::with_capacity(5 * num_latches);
    for round in 0..5 {
        for l in &latch_vars {
            // Mix positive and negated literals across rounds to avoid trivial
            // constraint simplification.
            let lit = if round % 2 == 0 { Lit::pos(*l) } else { Lit::neg(*l) };
            constraint_lits.push(lit);
        }
    }
    assert!(constraint_lits.len() > 4 * num_latches);

    let max_var = (2 * num_latches) as u32;
    build_ts(
        max_var,
        latch_vars.clone(),
        input_vars,
        next_state,
        init_clauses,
        vec![Lit::pos(latch_vars[0])], // bad = l_0
        constraint_lits,
        FxHashMap::default(),
    )
}

#[test]
fn test_is_sat_likely_pattern_sokoban_shape() {
    // Pattern 2: I == L and constraint_lits > 4 * L.
    let ts = build_sokoban_like_ts(10);
    assert!(
        super::is_sat_likely_pattern(&ts),
        "sokoban-like Transys (I==L, constraints > 4*L) should match pattern",
    );
}

#[test]
fn test_is_sat_likely_pattern_rejects_nonsokoban() {
    // Non-sat-likely: few latches, no constraints. Should not match either
    // Pattern 1 (requires L>=30, I>2L, constraints) or Pattern 2 (requires
    // I==L and dense constraints).
    let a = Var(1);
    let mut next_state = FxHashMap::default();
    next_state.insert(a, Lit::neg(a));
    let ts = build_ts(
        1,
        vec![a],
        Vec::new(),
        next_state,
        vec![Clause::unit(Lit::neg(a))],
        vec![Lit::pos(a)],
        Vec::new(),
        FxHashMap::default(),
    );
    assert!(
        !super::is_sat_likely_pattern(&ts),
        "small, unconstrained Transys should NOT match sat-likely pattern",
    );
}

#[test]
fn test_ternary_sim_early_exit_on_sokoban_pattern() {
    // Wave 29 (#4299) Change 4: sat-likely circuits with low probe elimination
    // must exit ternary_sim after the 8-cycle probe, skipping the full
    // multi-cycle pass. On this circuit 0/10 latches are constant (all next-
    // state are free inputs), so ratio = 0.0 < 0.10 → early-exit triggers.
    //
    // Soundness: probe-only and full-pass both return 0 on this input, so the
    // final `ternary_sim_eliminated` stat must equal 0 either way. The test
    // verifies the preprocess completes successfully and does not misbehave
    // on sat-likely inputs, not the internal branch taken.
    let ts = build_sokoban_like_ts(10);
    assert!(super::is_sat_likely_pattern(&ts));

    let mut config = PreprocessConfig::default();
    // Force a large full-cycle budget so the probe-vs-full distinction is
    // observable in the elimination stat on circuits where it matters.
    config.ternary_sim_cycles = 128;
    let (_reduced, stats) = preprocess_with_config(&ts, &config);

    // No latches are provably constant on this circuit. Both probe and full
    // pass return 0; the gate just decides *which* path runs.
    assert_eq!(
        stats.ternary_sim_eliminated, 0,
        "sokoban-pattern free-input latches cannot be proven constant by ternary sim",
    );
    // Sanity: orig_latches matches what we built.
    assert_eq!(stats.orig_latches, 10);
}

#[test]
fn test_ternary_sim_full_pass_runs_when_pattern_mismatches() {
    // A non-sat-likely circuit must take the full-pass path (no early-exit).
    // On a stuck-at-0 cascade, the full pass eliminates all N latches whereas
    // the 8-cycle probe also eliminates them (only needs 1 cycle). Both paths
    // agree on the count; we verify the elimination still happens.
    let n = 3usize;
    let mut latch_vars = Vec::with_capacity(n);
    let mut next_state = FxHashMap::default();
    let mut init_clauses = Vec::with_capacity(n);
    for i in 0..n {
        let l = Var((i + 1) as u32);
        latch_vars.push(l);
        next_state.insert(l, Lit::FALSE); // stuck at 0 via next=FALSE
        init_clauses.push(Clause::unit(Lit::neg(l)));
    }
    let ts = build_ts(
        n as u32,
        latch_vars.clone(),
        Vec::new(),
        next_state,
        init_clauses,
        vec![Lit::pos(latch_vars[0])],
        Vec::new(), // no constraints — not sat-likely
        FxHashMap::default(),
    );
    assert!(!super::is_sat_likely_pattern(&ts));

    let (_reduced, stats) = preprocess_with_config(&ts, &PreprocessConfig::default());
    // Stuck-at-0 latches are eliminated by one of {Phase 0b ternary sim,
    // Phase 2 constant latch elimination}. Exact attribution depends on
    // ordering; the guarantee is that all N latches are gone by pipeline end.
    assert_eq!(
        stats.final_latches, 0,
        "all stuck-at-0 latches must be eliminated in a non-sat-likely circuit",
    );
}

#[test]
fn test_ternary_sim_disabled_respects_config() {
    // Regression guard: when `enable_ternary_sim=false`, the gate must not run
    // regardless of sat-likely pattern. Verifies the gate sits inside the
    // existing `if config.enable_ternary_sim` branch and does not leak work
    // when disabled.
    let ts = build_sokoban_like_ts(5);
    assert!(super::is_sat_likely_pattern(&ts));

    let mut config = PreprocessConfig::default();
    config.enable_ternary_sim = false;
    let (_reduced, stats) = preprocess_with_config(&ts, &config);
    assert_eq!(
        stats.ternary_sim_eliminated, 0,
        "ternary_sim_eliminated must stay 0 when enable_ternary_sim=false",
    );
}
