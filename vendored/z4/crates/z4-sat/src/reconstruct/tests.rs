// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for model reconstruction (BVE, BCE, sweep).

use super::*;
use crate::test_util::lit;

#[test]
fn test_bve_reconstruct_simple() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(
        Variable(0),
        vec![vec![lit(0, true), lit(1, true)]],
        vec![vec![lit(0, false), lit(2, true)]],
    );
    let mut model = vec![false, true, true];
    stack.reconstruct(&mut model);
    assert!(model[0] || model[1], "(x0|x1) satisfied");
    assert!(!model[0] || model[2], "(!x0|x2) satisfied");
}

#[test]
fn test_bve_reconstruct_forced_true() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(Variable(0), vec![vec![lit(0, true), lit(1, false)]], vec![]);
    let mut model = vec![false, true];
    stack.reconstruct(&mut model);
    assert!(model[0], "x0 must be true to satisfy (x0|!x1) with x1=true");
}

#[test]
fn test_bve_reconstruct_forced_false() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(
        Variable(0),
        vec![],
        vec![vec![lit(0, false), lit(1, false)]],
    );
    let mut model = vec![true, true];
    stack.reconstruct(&mut model);
    assert!(
        !model[0],
        "x0 must be false to satisfy (!x0|!x1) with x1=true"
    );
}

#[test]
fn test_bve_multi_round_correctness() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(
        Variable(0),
        vec![vec![lit(0, true), lit(1, true)]],
        vec![vec![lit(0, false), lit(2, true)]],
    );
    stack.push_bve(
        Variable(2),
        vec![vec![lit(2, true), lit(3, true)]],
        vec![vec![lit(2, false), lit(4, true)]],
    );
    let mut model = vec![false, true, false, true, true];
    stack.reconstruct(&mut model);
    assert!(model[2] || model[3], "(x2|x3) satisfied");
    assert!(!model[2] || model[4], "(!x2|x4) satisfied");
    assert!(model[0] || model[1], "(x0|x1) satisfied");
    assert!(!model[0] || model[2], "(!x0|x2) satisfied");
}

#[test]
fn test_sweep_reconstruct_equivalence() {
    let mut model = vec![false, true, false];
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    reconstruct_sweep(&mut model, 3, &lit_map);
    assert_eq!(model[0], model[1]);
    assert!(model[0]);
}

#[test]
fn test_reconstruction_stack_order() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(Variable(2), vec![vec![lit(2, true), lit(1, false)]], vec![]);
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    stack.push_sweep(3, lit_map);
    let mut model = vec![false, true, false];
    stack.reconstruct(&mut model);
    assert!(model[0], "x0 true after sweep");
    assert!(model[2], "x2 true after BVE");
}

#[test]
fn test_bce_reconstruct_simple() {
    let mut model = vec![false, false];
    reconstruct_witness(&mut model, &[lit(0, true)], &[lit(0, true), lit(1, true)]);
    assert!(model[0]);
}

#[test]
fn test_bce_reconstruct_already_satisfied() {
    let mut model = vec![false, true];
    reconstruct_witness(&mut model, &[lit(0, true)], &[lit(0, true), lit(1, true)]);
    assert!(!model[0], "x0 stays false when clause already satisfied");
}

#[test]
fn test_bce_reconstruction_stack() {
    let mut stack = ReconstructionStack::new();
    stack.push_bce(lit(0, true), vec![lit(0, true), lit(1, true)]);
    let mut model = vec![false, false];
    stack.reconstruct(&mut model);
    assert!(model[0]);
}

#[test]
fn test_conditional_autarky_flips_multiple_witness_literals() {
    let mut model = vec![false, false, false];
    reconstruct_witness(
        &mut model,
        &[lit(0, true), lit(1, true)],
        &[lit(0, true), lit(1, true), lit(2, true)],
    );
    assert!(model[0], "first witness literal should be flipped true");
    assert!(model[1], "second witness literal should be flipped true");
}

#[test]
fn test_conditional_autarky_skips_when_clause_already_satisfied() {
    let mut model = vec![false, false, true];
    reconstruct_witness(
        &mut model,
        &[lit(0, true), lit(1, true)],
        &[lit(0, true), lit(1, true), lit(2, true)],
    );
    assert!(
        !model[0],
        "witness remains unchanged when clause already true"
    );
    assert!(
        !model[1],
        "witness remains unchanged when clause already true"
    );
}

#[test]
fn test_iter_removed_clauses_includes_bve_and_bce() {
    let mut stack = ReconstructionStack::new();
    stack.push_bve(Variable(0), vec![vec![lit(0, true), lit(1, true)]], vec![]);
    stack.push_bce(lit(2, true), vec![lit(2, true), lit(3, true)]);
    assert_eq!(stack.iter_removed_clauses().count(), 2);
}

#[test]
fn test_drain_witness_entries_preserves_sweep_steps() {
    let mut stack = ReconstructionStack::new();
    // Add a BVE witness entry.
    stack.push_bve(Variable(0), vec![vec![lit(0, true), lit(1, true)]], vec![]);
    // Add a sweep entry.
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    stack.push_sweep(3, lit_map);
    // Add a BCE witness entry.
    stack.push_bce(lit(2, true), vec![lit(2, true), lit(3, true)]);

    assert_eq!(stack.len(), 3);

    let result = stack.drain_witness_entries();

    // Sweep step preserved.
    assert_eq!(stack.len(), 1);
    matches!(&stack.steps[0], ReconstructionStep::Sweep { .. });

    // reactivate_vars should include variables from drained witness/clause literals.
    // BVE: var 0 (witness), var 0+1 (clause). BCE: var 2 (witness+clause), var 3 (clause).
    assert!(result.reactivate_vars.contains(&0));
    assert!(result.reactivate_vars.contains(&1));
    assert!(result.reactivate_vars.contains(&2));
    assert!(result.reactivate_vars.contains(&3));
    // Variables should be deduplicated and sorted.
    assert_eq!(result.reactivate_vars, vec![0, 1, 2, 3]);
}

#[test]
fn test_drain_witness_entries_empty_stack() {
    let mut stack = ReconstructionStack::new();
    let result = stack.drain_witness_entries();
    assert!(result.reactivate_vars.is_empty());
    assert_eq!(stack.len(), 0);
}

#[test]
fn test_drain_witness_entries_only_sweep() {
    let mut stack = ReconstructionStack::new();
    let mut lit_map = vec![Literal(0); 4];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    stack.push_sweep(2, lit_map);

    let result = stack.drain_witness_entries();
    assert!(result.reactivate_vars.is_empty());
    // Sweep step preserved.
    assert_eq!(stack.len(), 1);
}

#[test]
fn test_drain_witness_entries_reconstruction_still_works() {
    let mut stack = ReconstructionStack::new();
    // Add BVE witness + sweep.
    stack.push_bve(Variable(2), vec![vec![lit(2, true), lit(1, false)]], vec![]);
    let mut lit_map = vec![Literal(0); 6];
    lit_map[lit(0, true).index()] = lit(1, true);
    lit_map[lit(0, false).index()] = lit(1, false);
    lit_map[lit(1, true).index()] = lit(1, true);
    lit_map[lit(1, false).index()] = lit(1, false);
    lit_map[lit(2, true).index()] = lit(2, true);
    lit_map[lit(2, false).index()] = lit(2, false);
    stack.push_sweep(3, lit_map);

    // Drain witnesses — only sweep remains.
    let _result = stack.drain_witness_entries();
    assert_eq!(stack.len(), 1);

    // Reconstruction with remaining sweep still works.
    let mut model = vec![false, true, false];
    stack.reconstruct(&mut model);
    // x0 was mapped to x1 via sweep, so x0 should become true.
    assert!(model[0], "x0 true after sweep reconstruction");
}
