// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bug #3155 regressions: full-state streaming must bypass VIEW and SYMMETRY.

mod common;

use common::parse_module;
use std::collections::HashMap;
use tla_check::{CheckResult, Config, ConstantValue, ModelChecker};

fn assert_success_state_count(label: &str, result: CheckResult, expected: usize) {
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expected,
                "{label}: expected {expected} states, got {}",
                stats.states_found
            );
        }
        other => panic!("{label}: expected success, got {other:?}"),
    }
}

/// Bug #3155: full-state streaming fingerprinting must not ignore VIEW.
/// The hidden bit toggles forever, but VIEW projects it away, so the checker
/// must keep only the single visible state in both sequential storage modes.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_3155_view_bypasses_full_state_streaming() {
    let spec = r#"
---- MODULE Bug3155ViewStreaming ----
VARIABLES visible, hidden

Init == /\ visible = 0
        /\ hidden = FALSE

Next == /\ visible' = visible
        /\ hidden' = ~hidden

VisibleView == visible
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        view: Some("VisibleView".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    for store_states in [false, true] {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_store_states(store_states);
        checker.set_auto_create_trace_file(false);

        let label = format!("view bypass (store_states={store_states})");
        assert_success_state_count(&label, checker.check(), 1);
    }
}

/// Bug #3155: full-state streaming fingerprinting must not ignore SYMMETRY.
/// The initial state has one leader in phase 0; phase-1 successors choose a
/// different leader. Without symmetry there are 3 states, but with symmetry
/// the two phase-1 successors are one orbit, so the checker must report 2.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_3155_symmetry_bypasses_full_state_streaming() {
    let spec = r#"
---- MODULE Bug3155SymmetryStreaming ----
EXTENDS TLC
CONSTANT Procs
VARIABLES leader, phase

Init == /\ leader = CHOOSE p \in Procs : TRUE
        /\ phase = 0

Next == /\ phase = 0
        /\ leader' \in Procs
        /\ leader' /= leader
        /\ phase' = 1

Sym == Permutations(Procs)
====
"#;

    let module = parse_module(spec);
    let mut constants = HashMap::new();
    constants.insert(
        "Procs".to_string(),
        ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string(), "p3".to_string()]),
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        constants,
        check_deadlock: false,
        ..Default::default()
    };

    for store_states in [false, true] {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_store_states(store_states);
        checker.set_auto_create_trace_file(false);

        let label = format!("symmetry bypass (store_states={store_states})");
        assert_success_state_count(&label, checker.check(), 2);
    }
}
