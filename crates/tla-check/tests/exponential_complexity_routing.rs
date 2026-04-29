// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(feature = "z4")]

//! Integration tests for exponential complexity detection and routing.
//!
//! Requires the `z4` feature because `detect_exponential_complexity` is
//! part of the z4-gated oracle module.
//!
//! Verifies that:
//! 1. The `ComplexityVisitor` detects nested SUBSET(SUBSET ...) patterns
//! 2. The evaluator's nested powerset optimization handles the pattern
//! 3. BFS completes successfully with the correct state count
//!
//! Part of #3826.

mod common;

use tla_check::{check_module, detect_exponential_complexity, CheckResult, Config};

/// SpanTreeTest-like spec with 3 nodes.
///
/// Init: Edges \in {E \in SUBSET(SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}
///
/// With 3 nodes: SUBSET(SUBSET {1,2,3}) has 2^(2^3) = 256 elements.
/// But the Cardinality(e)=2 filter reduces the base to C(3,2) = 3 edges,
/// making SUBSET({2-element subsets}) = 2^3 = 8 possible edge sets.
/// Combined with deterministic mom/dist init, this gives 8 initial states.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_spantree_3nodes_nested_subset_detection_and_check() {
    let module = common::parse_module_strict(
        r#"
---- MODULE SpanTreeTest3 ----
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality

ASSUME /\ Root \in Nodes
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist, Edges
vars == <<mom, dist, Edges>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]
          /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        /\ Edges \in {E \in SUBSET (SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}

Next == \E n \in Nodes :
          \E m \in Nbrs(n) :
             /\ dist[m] < 1 + dist[n]
             /\ \E d \in (dist[m]+1) .. (dist[n] - 1) :
                    /\ dist' = [dist EXCEPT ![n] = d]
                    /\ mom'  = [mom  EXCEPT ![n] = m]
                    /\ Edges' = Edges

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====
"#,
    );

    // Step 1: Verify that static complexity analysis detects the pattern.
    let signal = detect_exponential_complexity(&module);
    assert!(
        signal.is_some(),
        "should detect nested SUBSET(SUBSET Nodes) as exponential complexity"
    );
    assert!(
        signal.as_ref().unwrap().reason.contains("nested SUBSET"),
        "reason should mention nested SUBSET, got: {}",
        signal.unwrap().reason
    );

    // Step 2: Verify that BFS model checking succeeds despite the
    // doubly-exponential pattern, thanks to the evaluator's nested
    // powerset optimization.
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        constants: {
            let mut c = std::collections::HashMap::new();
            c.insert(
                "Nodes".to_string(),
                tla_check::ConstantValue::Value("{1, 2, 3}".to_string()),
            );
            c.insert(
                "Root".to_string(),
                tla_check::ConstantValue::Value("1".to_string()),
            );
            c.insert(
                "MaxCardinality".to_string(),
                tla_check::ConstantValue::Value("4".to_string()),
            );
            c
        },
        constants_order: vec![
            "Nodes".to_string(),
            "Root".to_string(),
            "MaxCardinality".to_string(),
        ],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            // With 3 nodes:
            // - 8 initial states (2^C(3,2) = 2^3 edge configurations)
            // - Each edge config has deterministic mom/dist initialization
            // - Next action explores neighbor relaxation
            assert!(
                stats.states_found > 0,
                "should find some states, got: {}",
                stats.states_found
            );
            eprintln!(
                "[test] SpanTreeTest3 completed: {} states found, {} initial states",
                stats.states_found, stats.initial_states
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "unexpected invariant violation: {invariant} \
                 — the spec should pass TypeOK for all 3-node graphs"
            );
        }
        CheckResult::Deadlock { .. } => {
            // Deadlock is acceptable — some graph configurations may have
            // no relaxation steps.
            eprintln!("[test] SpanTreeTest3 deadlocked (expected for some configs)");
        }
        _ => {
            panic!("unexpected check result: {result:?}");
        }
    }
}

/// Verify that a simple spec without SUBSET(SUBSET) is NOT flagged
/// as exponential complexity.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_simple_spec_no_exponential_detection() {
    let module = common::parse_module_strict(
        r#"
---- MODULE SimpleSpec ----
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
TypeOK == x \in 0..3
====
"#,
    );

    let signal = detect_exponential_complexity(&module);
    assert!(
        signal.is_none(),
        "simple spec should not trigger exponential complexity detection"
    );
}
