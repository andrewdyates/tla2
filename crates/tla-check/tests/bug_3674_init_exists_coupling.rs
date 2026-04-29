// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::{check_module, CheckResult, Config};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_3674_exists_bound_init_branch_values_stay_coupled() {
    let module = common::parse_module_strict(
        r#"
---- MODULE InitExistsCoupling3674 ----
EXTENDS Integers

VARIABLE incoming, outgoing

Nodes == {1, 2, 3}

Init ==
    \E Nbrs \in {
        {{1, 2}},
        {{1, 3}}
    } :
        /\ incoming = [n \in Nodes |-> {m \in Nodes : {m, n} \in Nbrs /\ m < n}]
        /\ outgoing = [n \in Nodes |-> {m \in Nodes : {m, n} \in Nbrs /\ m > n}]

Next == UNCHANGED <<incoming, outgoing>>

Inv ==
    \A a \in Nodes :
        \A b \in Nodes :
            (a < b) => ((b \in outgoing[a]) = (a \in incoming[b]))
====
"#,
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.initial_states, 2,
                "#3674: the two Nbrs witnesses should produce exactly two initial states"
            );
            assert_eq!(
                stats.states_found, 2,
                "#3674: the stuttering machine should keep exactly those two coupled states"
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "#3674 regression: {invariant} violated because Init mixed values from different EXISTS witnesses"
            );
        }
        other => panic!("expected Success for #3674 regression, got {other:?}"),
    }
}
