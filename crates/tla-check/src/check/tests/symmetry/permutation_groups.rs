// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Part of #3044: Verify group closure correctness through state count verification.
/// Tests S4 symmetry (24 permutations) to ensure the Vec+BTreeSet frontier algorithm
/// generates the full group closure. Incomplete closure (old BTreeSet-only bug) produces
/// over-reduction — more states are collapsed than should be, yielding fewer states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_group_closure_s4() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // S4 (4! = 24 perms): [4 procs -> {yes, no}] = 16 states without symmetry.
    // With S4 symmetry: orbits by count of "yes" = 5 canonical states (0,1,2,3,4).
    let src = r#"
---- MODULE S4Closure ----
EXTENDS TLC
CONSTANT Procs
VARIABLE votes

Init == votes \in [Procs -> {"yes", "no"}]
Next == UNCHANGED votes

Sym == Permutations(Procs)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
            "p3".to_string(),
            "p4".to_string(),
        ]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    let states = match result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success for S4 closure test, got {:?}", other),
    };

    // With 4 procs and binary votes, S4 symmetry gives C(4,k) orbits for k=0..4
    // = 5 canonical states. Incomplete closure would give more (over-counting orbits).
    assert_eq!(
        states, 5,
        "S4 symmetry on [4 -> {{yes,no}}] should give 5 canonical states (TLC verified)"
    );
}

fn multi_group_state_counts() -> (usize, usize) {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE MultiGroupSymmetry ----
EXTENDS TLC
CONSTANTS Acceptors, Values
VARIABLE votes

Init == votes \in [Acceptors -> Values \cup {"none"}]
Next == UNCHANGED votes

Sym == Permutations(Acceptors) \cup Permutations(Values)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config_no_sym = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    config_no_sym.constants.insert(
        "Acceptors".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "a1".to_string(),
            "a2".to_string(),
            "a3".to_string(),
        ]),
    );
    config_no_sym.constants.insert(
        "Values".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["v1".to_string(), "v2".to_string()]),
    );

    let mut config_sym = config_no_sym.clone();
    config_sym.symmetry = Some("Sym".to_string());

    let mut checker_no_sym = ModelChecker::new(&module, &config_no_sym);
    checker_no_sym.set_deadlock_check(false);
    let states_no_sym = match checker_no_sym.check() {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success without symmetry, got {:?}", other),
    };

    let mut checker_sym = ModelChecker::new(&module, &config_sym);
    checker_sym.set_deadlock_check(false);
    let states_sym = match checker_sym.check() {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success with symmetry, got {:?}", other),
    };

    (states_no_sym, states_sym)
}

/// Part of #3044: Verify multi-group symmetry (Permutations(A) ∪ Permutations(B))
/// produces the correct canonical state count. This is the MCVoting scenario
/// where acceptors and values are independently symmetric.
///
/// The permutation group is S_m × S_n (direct product), not just S_m or S_n alone.
/// Incorrect handling of multi-group symmetry could cause over-reduction
/// (too few states) or under-reduction (too many states).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_multi_group_permutations() {
    // Two independent symmetric sets: Acceptors (3 elements) and Values (2 elements).
    // Symmetry group = S3 × S2 = 6 * 2 = 12 permutations.
    // State: a function [Acceptors -> Values ∪ {"none"}]
    //
    // Without symmetry: 3^3 = 27 initial states (each of 3 acceptors maps to one of 3 choices)
    // With symmetry: states are equivalence classes under relabeling of both acceptors and values.
    let (states_no_sym, states_sym) = multi_group_state_counts();

    // Without symmetry: 3^3 = 27 functions [3 acceptors -> {v1, v2, none}]
    assert_eq!(
        states_no_sym, 27,
        "Without symmetry should have 27 function states"
    );
    // With symmetry: verify reduction happens and matches TLC.
    // S3 × S2 acting on [3 -> {v1, v2, none}], orbits by (count_v1, count_v2, count_none):
    // 1. (0,0,3) all none
    // 2. (1,0,2)~(0,1,2) one value, two none
    // 3. (2,0,1)~(0,2,1) two same value, one none
    // 4. (1,1,1) one v1, one v2, one none
    // 5. (3,0,0)~(0,3,0) all same value
    // 6. (2,1,0)~(1,2,0) two of one value, one of other
    // TLC confirms: 6 distinct states.
    assert!(
        states_sym < states_no_sym,
        "Symmetry should reduce state count: {} >= {}",
        states_sym,
        states_no_sym
    );
    assert_eq!(
        states_sym, 6,
        "With multi-group symmetry (S3 × S2) should have 6 canonical states (TLC verified)"
    );
}
