// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_reduction_state_count() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // A spec with symmetric processes - without symmetry, each permutation
    // of process assignment would be a different state. With symmetry,
    // we identify symmetric states as equivalent.
    //
    // With 3 processes and one process being "active", without symmetry:
    // - Init: active = p1, active = p2, active = p3 = 3 initial states
    // With symmetry:
    // - Init: active = p1 (canonical representative) = 1 state
    let src = r#"
---- MODULE SymmetryTest ----
EXTENDS TLC
CONSTANT Procs
VARIABLE active

\* Each process can become active one at a time
Init == active \in Procs
Next == active' \in Procs /\ active' /= active

\* Symmetry: all permutations of Procs are equivalent
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config WITHOUT symmetry
    let mut config_no_sym = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    config_no_sym.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
            "p3".to_string(),
        ]),
    );

    // Config WITH symmetry
    let mut config_sym = config_no_sym.clone();
    config_sym.symmetry = Some("Sym".to_string());

    // Check WITHOUT symmetry
    let mut checker_no_sym = ModelChecker::new(&module, &config_no_sym);
    checker_no_sym.set_deadlock_check(false);
    let result_no_sym = checker_no_sym.check();

    let states_no_sym = match result_no_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success without symmetry, got {:?}", other),
    };

    // Check WITH symmetry
    let mut checker_sym = ModelChecker::new(&module, &config_sym);
    checker_sym.set_deadlock_check(false);
    let result_sym = checker_sym.check();

    let states_sym = match result_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success with symmetry, got {:?}", other),
    };

    // Verify symmetry reduces state count
    // Without symmetry: 3 states (active = p1, p2, or p3)
    // With symmetry: 1 state (all symmetric)
    assert_eq!(states_no_sym, 3, "Without symmetry should have 3 states");
    assert_eq!(states_sym, 1, "With symmetry should have 1 state");
    assert!(
        states_sym < states_no_sym,
        "Symmetry should reduce state count"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_with_pairs() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // A spec where pairs of processes can be selected
    // Without symmetry: 3 choose 2 = 3 pairs, each pair assigned to one variable
    // With symmetry: only 1 canonical pair
    let src = r#"
---- MODULE SymmetryPairs ----
EXTENDS TLC, FiniteSets
CONSTANT Procs
VARIABLE selected

\* Select a subset of exactly 2 processes
Init == selected \in {S \in SUBSET Procs : Cardinality(S) = 2}
Next == UNCHANGED selected

\* Symmetry
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config WITHOUT symmetry
    let mut config_no_sym = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    config_no_sym.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
            "p3".to_string(),
        ]),
    );

    // Config WITH symmetry
    let mut config_sym = config_no_sym.clone();
    config_sym.symmetry = Some("Sym".to_string());

    // Check WITHOUT symmetry
    let mut checker_no_sym = ModelChecker::new(&module, &config_no_sym);
    checker_no_sym.set_deadlock_check(false);
    let result_no_sym = checker_no_sym.check();

    let states_no_sym = match result_no_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success without symmetry, got {:?}", other),
    };

    // Check WITH symmetry
    let mut checker_sym = ModelChecker::new(&module, &config_sym);
    checker_sym.set_deadlock_check(false);
    let result_sym = checker_sym.check();

    let states_sym = match result_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success with symmetry, got {:?}", other),
    };

    // Verify symmetry reduces state count
    // Without symmetry: 3 states ({p1,p2}, {p1,p3}, {p2,p3})
    // With symmetry: 1 state (all pairs are symmetric)
    assert_eq!(states_no_sym, 3, "Without symmetry should have 3 states");
    assert_eq!(states_sym, 1, "With symmetry should have 1 state");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_with_tuples() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test symmetry with model values inside tuples
    // A tuple <<p1, p2>> should be symmetric to <<p2, p1>> etc
    let src = r#"
---- MODULE SymmetryTuples ----
EXTENDS TLC
CONSTANT Procs
VARIABLE pair

\* Select an ordered pair of distinct processes
Init == pair \in {<<a, b>> : a \in Procs, b \in Procs \ {a}}
Next == UNCHANGED pair

\* Symmetry
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config WITHOUT symmetry
    let mut config_no_sym = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    config_no_sym.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
            "p3".to_string(),
        ]),
    );

    // Config WITH symmetry
    let mut config_sym = config_no_sym.clone();
    config_sym.symmetry = Some("Sym".to_string());

    // Check WITHOUT symmetry
    let mut checker_no_sym = ModelChecker::new(&module, &config_no_sym);
    checker_no_sym.set_deadlock_check(false);
    let result_no_sym = checker_no_sym.check();

    let states_no_sym = match result_no_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success without symmetry, got {:?}", other),
    };

    // Check WITH symmetry
    let mut checker_sym = ModelChecker::new(&module, &config_sym);
    checker_sym.set_deadlock_check(false);
    let result_sym = checker_sym.check();

    let states_sym = match result_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success with symmetry, got {:?}", other),
    };

    // Without symmetry: 3*2 = 6 ordered pairs (p1,p2), (p2,p1), (p1,p3), (p3,p1), (p2,p3), (p3,p2)
    // With symmetry: 1 canonical pair (all are symmetric)
    assert_eq!(
        states_no_sym, 6,
        "Without symmetry should have 6 ordered pairs"
    );
    assert_eq!(
        states_sym, 1,
        "With symmetry should have 1 canonical ordered pair"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_with_records() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test symmetry with model values inside records
    let src = r#"
---- MODULE SymmetryRecords ----
EXTENDS TLC
CONSTANT Procs
VARIABLE msg

\* A message with sender and receiver fields
Init == msg \in [sender: Procs, receiver: Procs]
Next == UNCHANGED msg

\* Symmetry
Sym == Permutations(Procs)
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config WITHOUT symmetry
    let mut config_no_sym = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    config_no_sym.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    // Config WITH symmetry
    let mut config_sym = config_no_sym.clone();
    config_sym.symmetry = Some("Sym".to_string());

    // Check WITHOUT symmetry
    let mut checker_no_sym = ModelChecker::new(&module, &config_no_sym);
    checker_no_sym.set_deadlock_check(false);
    let result_no_sym = checker_no_sym.check();

    let states_no_sym = match result_no_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success without symmetry, got {:?}", other),
    };

    // Check WITH symmetry
    let mut checker_sym = ModelChecker::new(&module, &config_sym);
    checker_sym.set_deadlock_check(false);
    let result_sym = checker_sym.check();

    let states_sym = match result_sym {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success with symmetry, got {:?}", other),
    };

    // Without symmetry: 2*2 = 4 records [sender:p1,receiver:p1], [s:p1,r:p2], [s:p2,r:p1], [s:p2,r:p2]
    // With symmetry: 2 canonical records (same/different sender-receiver)
    assert_eq!(
        states_no_sym, 4,
        "Without symmetry should have 4 record states"
    );
    assert_eq!(
        states_sym, 2,
        "With symmetry should have 2 canonical states (same/different)"
    );
}
