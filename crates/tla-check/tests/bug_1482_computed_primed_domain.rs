// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::{check_module, CheckResult, Config};

/// Bug #1482 (MCInnerSerial shape): computed primed domains used inside
/// `SUBSET(... \X ...)` must evaluate against previously assigned primed vars.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1482_computed_primed_domain_cross_product() {
    let spec = r#"
---- MODULE PrimedComputedDomain ----
EXTENDS FiniteSets
VARIABLES q, opId, opOrder

Init == /\ q = {1, 2}
        /\ opId = {}
        /\ opOrder = {}

Next == /\ q' = q \ {1}
        /\ opId' = {i \in q' : TRUE}
        /\ opOrder' \in SUBSET(opId' \X opId')
====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            // Reachable distinct states:
            // (q, opId, opOrder) =
            // ({1,2}, {}, {}) initial
            // ({2}, {2}, {})
            // ({2}, {2}, {<<2,2>>})
            assert_eq!(
                stats.states_found, 3,
                "expected 3 distinct states for computed primed domain cross-product, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("computed primed-domain membership should not raise eval errors: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// SetPred path coverage for #1482: materializing `{v \in S : v = y'}` in
/// `z' \in ...` must still see the bound `y'` in next-state context.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1482_primed_setpred_domain_uses_next_state_context() {
    let spec = r#"
---- MODULE PrimedSetPredDomain ----
VARIABLES y, z

Init == y = 0 /\ z = 0

Next == /\ y' \in {1, 2}
        /\ z' \in {v \in {1, 2} : v = y'}
====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            // Distinct reachable states: (0,0), (1,1), (2,2)
            assert_eq!(
                stats.states_found, 3,
                "expected 3 distinct states for primed SetPred domain, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("primed SetPred domain should not raise eval errors: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Nested SetPred path coverage for #1830/#1827: domain materialization in
/// primed-membership must recurse when a set filter's source is itself SetPred.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1482_nested_setpred_domain_uses_next_state_context() {
    let spec = r#"
---- MODULE PrimedNestedSetPredDomain ----
VARIABLES y, z

Init == y = 0 /\ z = {}

Next == /\ y' \in {1, 2, 3}
        /\ z' \in {w \in {v \in SUBSET {1, 2, 3} : y' \in v} : 3 \in w}
====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            // Distinct reachable states:
            // init: (0, {})
            // next: 8 combinations of y' in {1,2,3} with filtered SUBSET choices.
            assert_eq!(
                stats.states_found, 9,
                "expected 9 distinct states for nested primed SetPred domain, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("nested primed SetPred domain should not raise eval errors: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}
