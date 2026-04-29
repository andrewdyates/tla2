// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(not(feature = "bumpalo"))]

mod common;

use tla_check::{check_module, CheckResult, Config};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn model_checking_smoke_test_runs_without_default_features() {
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = 0
Inv == x = 0
====
"#;
    let module = common::parse_module(src);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("valid cfg");

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1);
            assert_eq!(stats.states_found, 1);
        }
        other => panic!("expected Success, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn fallback_arena_multi_state_exploration() {
    // Spec with 4 distinct states exercises arena allocation across BFS expansion
    let src = r#"
---- MODULE TwoCounters ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == \/ (x = 0 /\ x' = 1 /\ y' = y)
        \/ (y = 0 /\ y' = 1 /\ x' = x)
        \/ (x = 1 /\ y = 1 /\ x' = 1 /\ y' = 1)
Inv == x \in {0, 1} /\ y \in {0, 1}
====
"#;
    let module = common::parse_module(src);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("valid cfg");

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            // (0,0) -> (1,0), (0,1) -> (1,1): 4 distinct states
            assert_eq!(stats.states_found, 4);
            assert_eq!(stats.initial_states, 1);
        }
        other => panic!("expected Success, got: {other:?}"),
    }
}
