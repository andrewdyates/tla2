// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_with_functions() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test symmetry with function values [Procs -> Values]
    let src = r#"
---- MODULE SymmetryFunctions ----
EXTENDS TLC
CONSTANT Procs
VARIABLE votes

\* Each process votes yes or no
Init == votes \in [Procs -> {"yes", "no"}]
Next == UNCHANGED votes

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

    // Without symmetry: 2^2 = 4 functions
    // [p1->yes,p2->yes], [p1->yes,p2->no], [p1->no,p2->yes], [p1->no,p2->no]
    // With symmetry: 3 canonical functions
    // - both yes (or both no by relabeling)
    // - p1->yes, p2->no (symmetric to p1->no, p2->yes)
    // Actually: [yes,yes], [no,no], [yes,no] = 3 states
    assert_eq!(
        states_no_sym, 4,
        "Without symmetry should have 4 function states"
    );
    assert_eq!(
        states_sym, 3,
        "With symmetry should have 3 canonical states"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_with_sequences() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test symmetry with sequences containing model values
    let src = r#"
---- MODULE SymmetrySequences ----
EXTENDS TLC, Sequences
CONSTANT Procs
VARIABLE queue

\* Queue contains a permutation of some processes
Init == queue \in {<<p>> : p \in Procs} \cup {<<p, q>> : p \in Procs, q \in Procs \ {p}}
Next == UNCHANGED queue

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

    // Without symmetry:
    // - Single element: <<p1>>, <<p2>>, <<p3>> = 3
    // - Two elements: <<p1,p2>>, <<p1,p3>>, <<p2,p1>>, <<p2,p3>>, <<p3,p1>>, <<p3,p2>> = 6
    // Total: 9 states
    // With symmetry:
    // - Single element: 1 canonical
    // - Two elements: 1 canonical (all ordered pairs symmetric)
    // Total: 2 canonical states
    assert_eq!(
        states_no_sym, 9,
        "Without symmetry should have 9 sequence states"
    );
    assert_eq!(
        states_sym, 2,
        "With symmetry should have 2 canonical states (length 1 and 2)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_with_nested_structures() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test symmetry with deeply nested model values
    let src = r#"
---- MODULE SymmetryNested ----
EXTENDS TLC
CONSTANT Procs
VARIABLE state

\* Nested structure: set of records containing tuples of processes
Init == state \in {[leader |-> <<p1, p2>>] : p1 \in Procs, p2 \in Procs \ {p1}}
Next == UNCHANGED state

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

    // Without symmetry: 3*2 = 6 ordered pairs in nested structure
    // With symmetry: 1 canonical state
    assert_eq!(
        states_no_sym, 6,
        "Without symmetry should have 6 nested states"
    );
    assert_eq!(
        states_sym, 1,
        "With symmetry should have 1 canonical nested state"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_multiple_variables() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test symmetry with multiple state variables containing model values
    let src = r#"
---- MODULE SymmetryMultiVar ----
EXTENDS TLC
CONSTANT Procs
VARIABLE sender, receiver

Init == sender \in Procs /\ receiver \in Procs
Next == /\ sender' \in Procs
    /\ receiver' \in Procs
    /\ sender' /= sender

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

    // Without symmetry: 2*2 = 4 states for (sender, receiver)
    // With symmetry: 2 canonical states (same or different)
    assert_eq!(
        states_no_sym, 4,
        "Without symmetry should have 4 multi-var states"
    );
    assert_eq!(
        states_sym, 2,
        "With symmetry should have 2 canonical states (same/different)"
    );
}
