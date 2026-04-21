// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symmetry parity tests for parallel vs sequential checking (#3011).

use super::*;

/// Part of #3011: Verify parallel checker produces the same state counts as
/// sequential checker when SYMMETRY is enabled. This is AC3 of #3011.
///
/// Uses a 3-process leader election spec where symmetry reduces 3 states to 1.
/// Both sequential and parallel checkers must agree on the reduced count.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_symmetry_parity() {
    let _scope = ParityTestScope::begin();
    let src = r#"
---- MODULE SymmetryParity ----
EXTENDS TLC
CONSTANT Procs
VARIABLE active

Init == active \in Procs
Next == active' \in Procs /\ active' /= active

Sym == Permutations(Procs)
====
"#;

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        check_deadlock: false,
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string(), "p3".to_string()]),
    );

    // With symmetry: 3 processes are all equivalent → 1 canonical state
    assert_parallel_sequential_parity("symmetry_basic", src, config, 4, Some((1, 1)));
}

/// Part of #3011: Symmetry parity with multiple variables.
/// Two variables (sender, receiver) from symmetric Procs set.
/// Without symmetry: 4 states. With symmetry: 2 states.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_symmetry_multi_var_parity() {
    let _scope = ParityTestScope::begin();
    let src = r#"
---- MODULE SymmetryMultiVarParity ----
EXTENDS TLC
CONSTANT Procs
VARIABLES sender, receiver

Init == sender \in Procs /\ receiver \in Procs /\ sender /= receiver
Next == UNCHANGED <<sender, receiver>>

Sym == Permutations(Procs)
====
"#;

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        check_deadlock: false,
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    // 2 procs, sender /= receiver: (p1,p2) and (p2,p1) → 1 canonical with symmetry
    assert_parallel_sequential_parity("symmetry_multi_var", src, config, 4, Some((1, 1)));
}

/// Part of #3011: Symmetry parity with function-valued variables.
/// Functions [Procs -> {"yes","no"}] have 2^|Procs| states without symmetry.
/// With symmetry on 3 procs: 8 states → 4 canonical (3C0 + 3C1 + 3C2 + 3C3).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_symmetry_function_parity() {
    let _scope = ParityTestScope::begin();
    let src = r#"
---- MODULE SymmetryFunctionParity ----
EXTENDS TLC
CONSTANT Procs
VARIABLE votes

Init == votes \in [Procs -> {"yes", "no"}]
Next == UNCHANGED votes

Sym == Permutations(Procs)
====
"#;

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        check_deadlock: false,
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string(), "p3".to_string()]),
    );

    // [3 procs -> {yes, no}]: 8 total, 4 canonical (by # of "yes" votes: 0,1,2,3)
    assert_parallel_sequential_parity("symmetry_function", src, config, 4, Some((4, 4)));
}

/// Part of #3011: Symmetry with invariant violation — both checkers must
/// detect the same invariant violation under symmetry.
/// Uses a counter alongside symmetric processes to ensure the violation
/// survives symmetry reduction.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_symmetry_invariant_violation_parity() {
    let _scope = ParityTestScope::begin();
    let src = r#"
---- MODULE SymmetryViolationParity ----
EXTENDS TLC, Naturals
CONSTANT Procs
VARIABLES active, count

Init == active \in Procs /\ count = 0
Next == active' \in Procs /\ count' = count + 1

\* Fails: count exceeds 1
Safe == count <= 1

Sym == Permutations(Procs)
====
"#;

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safe".to_string()],
        symmetry: Some("Sym".to_string()),
        check_deadlock: false,
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string(), "p3".to_string()]),
    );

    // Both checkers should detect invariant violation (count reaches 2)
    let module = common::parse_module(src);

    let mut seq_checker = ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_result = seq_checker.check();
    assert!(
        matches!(&seq_result, CheckResult::InvariantViolation { .. }),
        "sequential should find invariant violation, got: {seq_result:?}"
    );

    for use_handle_state in [false, true] {
        let _guard = set_use_handle_state_override(use_handle_state);
        let mut par_checker = ParallelChecker::new(&module, &config, 4);
        par_checker.set_deadlock_check(false);
        let par_result = par_checker.check();
        assert_result_kind_parity(
            "symmetry_violation",
            use_handle_state,
            &seq_result,
            &par_result,
        );
    }
}
