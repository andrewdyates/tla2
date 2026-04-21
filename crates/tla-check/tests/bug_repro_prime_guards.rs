// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Prime guard in operator body - Bugs #3, #12, #349
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config, ConstantValue};

// ============================================================================
// Bug #3: MCInnerSerial - Prime guard in operator body not enforced
// ============================================================================

/// Bug #3: MCInnerSerial prime guard in operator body
///
/// The MCInnerSerial spec has:
/// - `opOrder' \in SUBSET(opId' \X opId')` which can generate self-loops like <<a, a>>
/// - `UpdateOpOrder` operator containing `Serializable'` prime guard
/// - `Serializable'` checks that opOrder' has no self-loops
///
/// The bug: When the prime guard is inside an operator body (e.g., `UpdateOpOrder`
/// contains `Serializable'`), TLA2 was not validating it because:
/// 1. `needs_next_state_validation(Ident("UpdateOpOrder"))` returned false
/// 2. The operator body containing primed constraints wasn't being evaluated
///
/// This test creates a minimal reproduction where:
/// - Variable `x` is a set of pairs
/// - `NoSelfLoop'` is a prime guard that should filter self-loops
/// - `Update` operator contains the prime guard (not inline in Next)
///
/// Without the fix: TLA2 generates states with self-loops (invariant violated)
/// With the fix: TLA2 correctly filters self-loops (no invariant violation)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_prime_guard_in_operator_body() {
    // Minimal spec that reproduces the bug
    let spec = r#"
---- MODULE PrimeGuardInOperatorBody ----
VARIABLE x

\* Prime guard: no self-loops in x'
NoSelfLoop == \A pair \in x : pair[1] # pair[2]

Init == x = {}

\* The constraint is inside an operator body, not inline
Update ==
    /\ x' \in SUBSET({<<1, 1>>, <<1, 2>>, <<2, 1>>})
    /\ NoSelfLoop'  \* This prime guard must be enforced!

Next == Update

\* Invariant: x should never contain self-loops
\* If bug exists, this invariant will be violated
NoSelfLoopInvariant == \A pair \in x : pair[1] # pair[2]

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["NoSelfLoopInvariant".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    // With the bug fixed, model checking should complete without violations
    match &result {
        CheckResult::Success(stats) => {
            // Expected: 4 distinct states (2^2 subsets of non-self-loop pairs from {1,2}):
            // {}, {<<1,2>>}, {<<2,1>>}, {<<1,2>>, <<2,1>>}
            assert_eq!(
                stats.states_found, 4,
                "Expected exactly 4 states (subsets of non-self-loop pairs), got {}",
                stats.states_found
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug exists! Invariant {} violated - TLA2 is generating states with self-loops",
                invariant
            );
        }
        CheckResult::Deadlock { .. } => {
            panic!("Unexpected deadlock");
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}

/// Bug #1482: primed-variable domains in membership assignments must evaluate
/// against the partially-constructed next state.
///
/// Repro pattern:
/// - `y' \in {1, 2}` binds `y'`
/// - `z' \in SUBSET({y'})` evaluates a domain referencing `y'`
///
/// Without the fix in `enumerate_in_domain`, evaluating `SUBSET({y'})` fails
/// with "Primed variable cannot be evaluated (no next-state context)".
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1482_primed_domain_membership_uses_next_state_context() {
    let spec = r#"
---- MODULE PrimedDomainMembership ----
VARIABLES y, z

Init == y = 0 /\ z = {}

Next == /\ y' \in {1, 2}
        /\ z' \in SUBSET({y'})
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            // Distinct reachable states:
            // (y,z) = (0,{}) initial
            // (1,{}), (1,{1}), (2,{}), (2,{2})
            assert_eq!(
                stats.states_found, 5,
                "expected 5 distinct states for primed-domain membership, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("primed-domain membership should not raise eval errors: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

// ============================================================================
// Bug #12: bosco regression - hidden primed vars in value-op guards (inline EXISTS path)
// ============================================================================

/// Bug #12: Hidden primed variables in value-operator guards must be validated.
///
/// Pattern (from `bosco`):
/// - A value operator references primed state (e.g., `MsgCount(self) == Cardinality(rcvd'[self])`)
/// - The Next relation uses the value operator in a guard position (e.g., `MsgCount(self) >= 1`)
/// - The primed variable is not syntactically visible at the call site, so naive guard evaluation
///   errors (no next-state context) and must be deferred and validated against each successor.
///
/// Regression root cause: the inline EXISTS fast path treated action-level guard eval errors as
/// "guard passed" but did not re-validate them against the computed next-state, allowing bogus
/// transitions (e.g., deciding with `rcvd = {}`).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hidden_prime_in_value_operator_guard_is_validated() {
    let spec = r#"
---- MODULE HiddenPrimeInValueGuard ----
EXTENDS Naturals, FiniteSets

CONSTANT N
VARIABLE pc, rcvd

Corr == 1 .. N
vars == <<pc, rcvd>>

Init ==
  /\ pc = [i \in Corr |-> "S"]
  /\ rcvd = [i \in Corr |-> {}]

\* Nondeterministically "receive" a set for this process (can be empty).
Receive(self) ==
  \E r \in SUBSET {1}:
    /\ rcvd[self] \subseteq r
    /\ rcvd' = [rcvd EXCEPT ![self] = r]

\* Value operator that depends on next-state (hidden prime at call sites).
MsgCount(self) == Cardinality(rcvd'[self])

Step(self) ==
  /\ Receive(self)
  /\ \/
      /\ pc[self] = "S"
      /\ MsgCount(self) >= 1
      /\ pc' = [pc EXCEPT ![self] = "D"]
     \/ pc' = pc

Next == \E self \in Corr: Step(self)

\* Invariant: if a process decides, it must have received at least one message.
DecideHasMsg ==
  \A i \in Corr: (pc[i] = "D") => (Cardinality(rcvd[i]) >= 1)

====
"#;

    let module = parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["DecideHasMsg".to_string()],
        ..Default::default()
    };
    config
        .constants
        .insert("N".to_string(), ConstantValue::Value("1".to_string()));

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(_) => {}
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Invariant {} violated - hidden prime guard was not enforced",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Variant: Nested operator with prime guard (deeper nesting)
///
/// Tests that prime guards are enforced even when nested multiple levels deep.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_operator_prime_guard() {
    let spec = r#"
---- MODULE NestedPrimeGuard ----
VARIABLE x

NoSelfLoop == \A pair \in x : pair[1] # pair[2]

\* Inner operator contains the prime guard
InnerUpdate ==
    /\ x' \in SUBSET({<<1, 1>>, <<1, 2>>})
    /\ NoSelfLoop'

\* Outer operator calls inner
OuterUpdate == InnerUpdate

Init == x = {}
Next == OuterUpdate

NoSelfLoopInvariant == \A pair \in x : pair[1] # pair[2]

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["NoSelfLoopInvariant".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success { .. } => {
            // Good: nested prime guards work
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Nested operator prime guard failed! Invariant {} violated",
                invariant
            );
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}

// ============================================================================
// Bug #12: bosco regression - Cardinality of primed set comprehension in value operator
// ============================================================================

/// Bug #12: Value operators with primed set comprehensions must be validated.
///
/// Pattern (from `bosco`):
/// - A value operator returns Cardinality of a set comprehension over primed state
///   e.g., `MsgCount(self) == Cardinality({m \in rcvd'[self] : ...})`
/// - The Next relation combines an EXISTS that binds primed vars with guards using the value op
///   e.g., `Step(self) == Receive(self) /\ (... MsgCount(self) >= threshold ...)`
/// - The Receive action contains `\E r \in SUBSET ...: ... rcvd' = [rcvd EXCEPT ![self] = r]`
///
/// This is more complex than the simple `MsgCount(self) == Cardinality(rcvd'[self])` pattern
/// because the primed variable is inside a set comprehension filter, not just directly accessed.
///
/// Root cause: When the value operator body contains a set comprehension over primed state,
/// evaluation may fail or produce incorrect results if not properly handled against next-state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bosco_style_cardinality_primed_setcomp() {
    let spec = r#"
---- MODULE BoscoStylePrimedSetComp ----
EXTENDS Naturals, FiniteSets

CONSTANT N
VARIABLE pc, rcvd

Corr == 1 .. N
M == {"ECHO0", "ECHO1"}
vars == <<pc, rcvd>>

\* Value operator: counts messages of a specific type in NEXT state
\* This is the bosco pattern: Cardinality of set comprehension over rcvd'[self]
MsgCount0(self) == Cardinality({m \in rcvd'[self] : m[2] = "ECHO0"})

\* Value operator: counts distinct senders in NEXT state
MsgSenders(self) == Cardinality({p \in Corr : (\E m \in rcvd'[self] : m[1] = p)})

Init ==
  /\ pc = [i \in Corr |-> "S"]
  /\ rcvd = [i \in Corr |-> {}]

\* Receive: nondeterministically receive a subset of possible messages
Receive(self) ==
  \E r \in SUBSET (Corr \X M):
    /\ rcvd[self] \subseteq r
    /\ rcvd' = [rcvd EXCEPT ![self] = r]

\* Decide: can only decide if received enough messages
\* Guard requires at least N-1 messages from distinct senders AND at least 1 ECHO0
UponDecide(self) ==
  /\ pc[self] = "S"
  /\ MsgSenders(self) >= N - 1   \* Need msgs from N-1 senders (hidden primed var)
  /\ MsgCount0(self) >= 1        \* Need at least 1 ECHO0 (hidden primed var)
  /\ pc' = [pc EXCEPT ![self] = "D"]

\* Stay: don't decide, just update rcvd
UponStay(self) ==
  /\ pc' = pc

Step(self) ==
  /\ Receive(self)
  /\ (UponDecide(self) \/ UponStay(self))

Next == \E self \in Corr: Step(self)

\* INVARIANT: If a process decides, it must have received at least 1 message.
\* This checks that the guards were properly enforced.
DecideHasMsg ==
  \A i \in Corr: (pc[i] = "D") => (Cardinality(rcvd[i]) >= 1)

====
"#;

    let module = parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["DecideHasMsg".to_string()],
        ..Default::default()
    };
    config
        .constants
        .insert("N".to_string(), ConstantValue::Value("2".to_string()));

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(_) => {}
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Invariant {} violated - bosco-style primed setcomp guard was not enforced. \
                 Process decided with rcvd=empty, meaning MsgCount0/MsgSenders guards \
                 containing primed set comprehensions were not validated.",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}
