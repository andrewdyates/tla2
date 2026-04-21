// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the CausalOrder and IsCausalOrder operators (VectorClocks module).
//!
//! These verify TLC-parity for the causal ordering algorithm from
//! CommunityModules VectorClocks.java, specifically:
//! - global_clock scoped per-host (Bug #1254.1)
//! - own-host time updated before dependency loop (Bug #1254.2)
//! - round-robin per-host-head topological sort (Bug #1254.4)
//! - completeness assertion (Bug #1254.5)

mod common;

use ntest::timeout;
use tla_check::EvalCheckError;
use tla_check::{check_module, CheckError, CheckResult, Config};

/// Test CausalOrder with 2 hosts, cross-host dependencies.
///
/// Scenario: Two hosts A and B each produce 2 events.
/// B's second event depends on A's first event (cross-host causality).
///
/// Expected: CausalOrder produces a sequence where A's event 1 appears
/// before B's event 2 (due to the causal dependency).
#[cfg_attr(test, timeout(10000))]
#[test]
fn test_causal_order_two_hosts_cross_dependency() {
    let spec = r#"
---- MODULE TestCausalOrder2Host ----
EXTENDS VectorClocks, Naturals, Sequences, FiniteSets, TLC

\* Log entries: each is a record with host + vector clock
\* Host A: 2 events, Host B: 2 events
\* B's event 2 has vc["A"] = 1, indicating it causally depends on A's event 1

aE1 == [host |-> "A", vc |-> [A |-> 1, B |-> 0]]
aE2 == [host |-> "A", vc |-> [A |-> 2, B |-> 0]]
bE1 == [host |-> "B", vc |-> [A |-> 0, B |-> 1]]
bE2 == [host |-> "B", vc |-> [A |-> 1, B |-> 2]]

\* Input log in non-causal order: B2 before A1
Log == <<bE2, aE1, bE1, aE2>>

Sorted == CausalOrder(Log,
    LAMBDA entry : entry.vc,
    LAMBDA entry : entry.host,
    LAMBDA clock : DOMAIN clock)

VARIABLE x
Init == x = Sorted
Next == UNCHANGED x

\* A1 must appear before B2 in the sorted output (causal dep)
InvA1BeforeB2 ==
    LET posA1 == CHOOSE i \in 1..Len(Sorted) : Sorted[i] = aE1
        posB2 == CHOOSE i \in 1..Len(Sorted) : Sorted[i] = bE2
    IN posA1 < posB2

\* All 4 events must be present
InvAllPresent == Len(Sorted) = 4

\* Result must be a valid causal ordering
InvIsCausal == IsCausalOrder(Sorted, LAMBDA entry : entry.vc)

====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![
            "InvAllPresent".to_string(),
            "InvA1BeforeB2".to_string(),
            "InvIsCausal".to_string(),
        ],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Expected 1 state");
        }
        other => panic!("Expected Success, got: {:?}", other),
    }
}

/// Test CausalOrder with 3 hosts where independent events can be
/// interleaved differently. Verifies the round-robin topological sort
/// produces a deterministic ordering matching TLC.
///
/// Scenario: 3 hosts (A, B, C), each with 1 event, no cross-host deps.
/// Input: <<cE, bE, aE>> (reverse order).
/// Expected output: <<aE, bE, cE>> (lexicographic host order per round-robin).
/// The round-robin algorithm iterates hosts in BTreeMap order (A, B, C) and
/// emits each host's head when it has no unresolved parents. With no cross-host
/// dependencies, all heads are immediately emittable on the first pass.
///
/// Strengthened per #1299: asserts exact output sequence, not just IsCausalOrder.
#[cfg_attr(test, timeout(10000))]
#[test]
fn test_causal_order_three_hosts_independent() {
    let spec = r#"
---- MODULE TestCausalOrder3Host ----
EXTENDS VectorClocks, Naturals, Sequences, FiniteSets, TLC

aE == [host |-> "A", vc |-> [A |-> 1, B |-> 0, C |-> 0]]
bE == [host |-> "B", vc |-> [A |-> 0, B |-> 1, C |-> 0]]
cE == [host |-> "C", vc |-> [A |-> 0, B |-> 0, C |-> 1]]

\* Input in reverse order
Log == <<cE, bE, aE>>

Sorted == CausalOrder(Log,
    LAMBDA entry : entry.vc,
    LAMBDA entry : entry.host,
    LAMBDA clock : DOMAIN clock)

VARIABLE x
Init == x = Sorted
Next == UNCHANGED x

InvAllPresent == Len(Sorted) = 3
InvIsCausal == IsCausalOrder(Sorted, LAMBDA entry : entry.vc)
\* Assert exact round-robin ordering: hosts visited A, B, C (BTreeMap order).
\* Any permutation passes IsCausalOrder, but only <<aE, bE, cE>> is correct
\* for the deterministic round-robin topological sort.
InvExactOrder == Sorted[1].host = "A" /\ Sorted[2].host = "B" /\ Sorted[3].host = "C"

====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![
            "InvAllPresent".to_string(),
            "InvIsCausal".to_string(),
            "InvExactOrder".to_string(),
        ],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Expected 1 state");
        }
        other => panic!("Expected Success, got: {:?}", other),
    }
}

/// Test CausalOrder with a chain of causal dependencies across 2 hosts.
///
/// A1 -> B1 -> A2 -> B2 (each event depends on the previous host's event)
/// This tests both the global_clock scope fix (Bug 1) and update order (Bug 2).
#[cfg_attr(test, timeout(10000))]
#[test]
fn test_causal_order_chain_dependencies() {
    let spec = r#"
---- MODULE TestCausalOrderChain ----
EXTENDS VectorClocks, Naturals, Sequences, FiniteSets, TLC

\* Causal chain: A1 -> B1 -> A2 -> B2
aE1 == [host |-> "A", vc |-> [A |-> 1, B |-> 0]]
bE1 == [host |-> "B", vc |-> [A |-> 1, B |-> 1]]
aE2 == [host |-> "A", vc |-> [A |-> 2, B |-> 1]]
bE2 == [host |-> "B", vc |-> [A |-> 2, B |-> 2]]

\* Input in scrambled order
Log == <<bE2, aE2, bE1, aE1>>

Sorted == CausalOrder(Log,
    LAMBDA entry : entry.vc,
    LAMBDA entry : entry.host,
    LAMBDA clock : DOMAIN clock)

VARIABLE x
Init == x = Sorted
Next == UNCHANGED x

InvAllPresent == Len(Sorted) = 4

\* The chain must be fully respected
InvChainOrder ==
    LET pos(e) == CHOOSE i \in 1..Len(Sorted) : Sorted[i] = e
    IN pos(aE1) < pos(bE1) /\ pos(bE1) < pos(aE2) /\ pos(aE2) < pos(bE2)

InvIsCausal == IsCausalOrder(Sorted, LAMBDA entry : entry.vc)

====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![
            "InvAllPresent".to_string(),
            "InvChainOrder".to_string(),
            "InvIsCausal".to_string(),
        ],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Expected 1 state");
        }
        other => panic!("Expected Success, got: {:?}", other),
    }
}

/// Negative regression: malformed vector clock dependency should produce a
/// structured evaluation error (not panic or silent success).
#[cfg_attr(test, timeout(10000))]
#[test]
fn test_causal_order_invalid_dependency_index_reports_error() {
    let spec = r#"
---- MODULE TestCausalOrderInvalidDependency ----
EXTENDS VectorClocks, Naturals, Sequences, FiniteSets, TLC

\* Host B has only one event, but A's event claims dependency on B time=2.
\* This must trigger "dependency index ... out of bounds" in CausalOrder.
aE1 == [host |-> "A", vc |-> [A |-> 1, B |-> 2]]
bE1 == [host |-> "B", vc |-> [A |-> 0, B |-> 1]]
Log == <<aE1, bE1>>

Sorted == CausalOrder(Log,
    LAMBDA entry : entry.vc,
    LAMBDA entry : entry.host,
    LAMBDA clock : DOMAIN clock)

VARIABLE x
Init == x = Sorted
Next == UNCHANGED x

====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Eval(EvalCheckError::Eval(tla_check::EvalError::Internal {
                    message, ..
                })),
            ..
        } => {
            assert!(
                message.contains("CausalOrder: dependency index"),
                "unexpected CausalOrder error message: {}",
                message
            );
        }
        other => panic!("Expected CausalOrder internal error, got: {:?}", other),
    }
}
