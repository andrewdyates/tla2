// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bug #1558: GameOfLife spec produces error where TLC succeeds
//!
//! Original error: "The first argument of > should be an integer, but instead
//! it is: <<0, 0>>" — caused by tuple destructuring failure where `x` was
//! bound to the entire tuple `<<x, y>>` instead of being destructured into
//! separate integer components.
//!
//! Research (R1068, commit 0163651cc) confirmed both TLC and TLA2 implement
//! `>` as integer-only — the bug was in the destructuring path, not comparison
//! semantics. The error no longer reproduces on current HEAD.

mod common;

use tla_check::{check_module, CheckResult, Config, ConstantValue};

/// Focused test: tuple destructuring in function domain with integer comparison.
///
/// The pattern `f[<<x, y>> \in S]` must properly destructure `x` and `y` as
/// separate values. The body uses `x > N` and `y > N` which requires `x` and
/// `y` to be integers, not tuples.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1558_tuple_destructure_comparison_no_type_error() {
    let spec = r#"
---- MODULE TupleDestructureCompare ----
EXTENDS Integers

CONSTANT N

VARIABLE state

Pos == (1..N) \X (1..N)

f[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
    CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N -> 0
         [] OTHER -> 1

Init == state = [p \in Pos |-> f[p]]

Next == UNCHANGED state

Spec == Init /\ [][Next]_state
====
"#;

    let module = common::parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    config
        .constants
        .insert("N".to_string(), ConstantValue::Value("2".to_string()));

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "Expected 1 state (deterministic Init, UNCHANGED), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Bug #1558 regression: tuple destructure produced error: {}",
                error
            );
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

/// Full GameOfLife spec with N=2.
///
/// TLC baseline (N=2): 32 states generated, 16 distinct states found, no error.
/// This is the actual GameOfLife spec from tlaplus-examples, reduced to N=2 for
/// fast deterministic testing.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_1558_game_of_life_n2_tlc_parity() {
    let spec = r#"
---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

Pos == {<<x, y>> : x, y \in 1..N}
TypeOK == grid \in [Pos -> BOOLEAN]

sc[<<x, y>> \in (0 .. N + 1) \X
                (0 .. N + 1)] == CASE \/ x = 0 \/ y = 0
                                      \/ x > N \/ y > N
                                      \/ ~grid[<<x, y>>] -> 0
                                   [] OTHER -> 1

score(p) == LET nbrs == {x \in {-1, 0, 1} \X
                               {-1, 0, 1} : x /= <<0, 0>>}
                points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
            IN Sum(sc, points)

Init == grid \in [Pos -> BOOLEAN]
Next == grid' = [p \in Pos |-> IF \/  (grid[p] /\ score(p) \in {2, 3})
                                 \/ (~grid[p] /\ score(p) = 3)
                                THEN TRUE
                                ELSE FALSE]

Spec == Init /\ [][Next]_vars
====
"#;

    let module = common::parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };
    config
        .constants
        .insert("N".to_string(), ConstantValue::Value("2".to_string()));

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 16,
                "GameOfLife N=2: TLC produces 16 distinct states, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Bug #1558 regression: GameOfLife N=2 produced error where TLC succeeds: {}",
                error
            );
        }
        other => panic!(
            "Expected success (TLC produces 16 states with no error), got: {:?}",
            other
        ),
    }
}
