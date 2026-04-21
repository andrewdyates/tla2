// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================
// CONSTANTS binding tests
// ============================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_with_integer_constant() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec with CONSTANT N used in Init and invariant
    let src = r#"
---- MODULE ConstTest ----
CONSTANT N
VARIABLE x
Init == x = N
Next == x' = x + 1
Bounded == x < N + 5
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config with N = 3
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Bounded".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "N".to_string(),
        crate::config::ConstantValue::Value("3".to_string()),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats: _,
        } => {
            assert_eq!(invariant, "Bounded");
            // N=3, starts at x=3, invariant x < 8 (3+5)
            // Violation at x=8
            // Trace: x=3, x=4, x=5, x=6, x=7, x=8
            assert_eq!(trace.len(), 6);
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_with_model_value_set_constant() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec with CONSTANT Procs as model value set
    let src = r#"
---- MODULE SetConstTest ----
CONSTANT Procs
VARIABLE current
Init == current \in Procs
Next == current' \in Procs
AlwaysProc == current \in Procs
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config with Procs = {p1, p2}
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["AlwaysProc".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Should find 2 states: current=p1, current=p2
            assert_eq!(stats.states_found, 2);
            assert_eq!(stats.initial_states, 2);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_value_equality_in_invariant() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test that model value equality works correctly in compiled invariants
    // This tests the fix for the bug where `decision = none` would fail
    // when `none` is a model value constant (like in SimplifiedFastPaxos)
    let src = r#"
---- MODULE ModelValueEqTest ----
CONSTANT none, Values
VARIABLE decision, messages

Init ==
/\ decision = none
/\ messages = {}

Next ==
/\ messages' = messages \union {[value |-> CHOOSE v \in Values : TRUE]}
/\ UNCHANGED decision

\* This invariant should always be true since decision never changes from none
DecisionIsNone == decision = none
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["DecisionIsNone".to_string()],
        ..Default::default()
    };
    // none = none is a model value assignment
    config.constants.insert(
        "none".to_string(),
        crate::config::ConstantValue::Value("none".to_string()),
    );
    // Values = {v1}
    config.constants.insert(
        "Values".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["v1".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Should find 2 states: initial (empty messages) and one with a message
            assert_eq!(stats.states_found, 2);
        }
        other => panic!(
            "Expected success (model value equality should work), got: {:?}",
            other
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_in_invariant() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test function set membership in invariant (like Barrier's TypeOK)
    let src = r#"
---- MODULE FuncTest ----
CONSTANT N
VARIABLE pc
ProcSet == 1..N
Init == pc = [p \in ProcSet |-> "b0"]
Next == UNCHANGED pc
TypeOK == pc \in [ProcSet -> {"b0", "b1"}]
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config with N = 3 (smaller for faster test)
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "N".to_string(),
        crate::config::ConstantValue::Value("3".to_string()),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Should find 1 state with pc = [1 |-> "b0", 2 |-> "b0", 3 |-> "b0"]
            assert_eq!(stats.states_found, 1);
            assert_eq!(stats.initial_states, 1);
        }
        other => panic!("Expected success (TypeOK should pass), got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_guard_evaluation() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test that guards inside LET expressions are properly evaluated.
    // This is a simplified version of the MissionariesAndCannibals spec pattern:
    //   Move(items) == LET newThis == ... IN /\ IsSafe(newThis) /\ x' = ...
    // The IsSafe guard inside the LET body must be checked before generating successors.
    let spec = r#"
---- MODULE LetGuard ----
EXTENDS Integers, FiniteSets

VARIABLES x, y

Init == x = {1, 2} /\ y = {}

IsSafe(S) == Cardinality(S) <= 1

Move(items) ==
/\ items \subseteq x
/\ Cardinality(items) = 1
/\ LET newX == x \ items
       newY == y \cup items
   IN  /\ IsSafe(newX)
       /\ x' = newX
       /\ y' = newY

Next == \E items \in SUBSET x : Move(items)

TypeOK == x \subseteq {1, 2} /\ y \subseteq {1, 2}

====
"#;
    let tree = parse_to_syntax_tree(spec);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // From Init: x={1,2}, y={}
            // Move {1}: newX={2}, IsSafe({2})=TRUE -> x={2}, y={1}
            // Move {2}: newX={1}, IsSafe({1})=TRUE -> x={1}, y={2}
            // From x={2}: Move {2}: newX={}, IsSafe({})=TRUE -> x={}, y={1,2}
            // From x={1}: Move {1}: newX={}, IsSafe({})=TRUE -> x={}, y={1,2}
            // Both paths converge to x={}, y={1,2}
            // Total distinct states: {1,2}/{}; {2}/{1}; {1}/{2}; {}/{1,2} = 4 states
            assert_eq!(stats.states_found, 4);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_selectseq_guard_evaluation() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test that guards using SelectSeq properly limit the state space
    // This uses the exact pattern from ReadersWriters.tla:
    // - SelectSeq filters the waiting queue by type
    // - Guard prevents actors from re-entering the queue
    let src = r#"
---- MODULE SelectSeqGuard ----
EXTENDS Sequences
CONSTANT Actors
VARIABLE waiting

ToSet(s) == { s[i] : i \in DOMAIN s }

\* Predicate to filter by type
is_read(p) == p[1] = "read"

\* Get set of actor IDs with "read" requests (using SelectSeq)
WaitingToRead == { p[2] : p \in ToSet(SelectSeq(waiting, is_read)) }

Init == waiting = <<>>

\* Actor can only request read if not already waiting
TryRead(actor) ==
/\ actor \notin WaitingToRead
/\ waiting' = Append(waiting, <<"read", actor>>)

Next == \E actor \in Actors : TryRead(actor)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config: Actors = {1, 2}
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };
    config.constants.insert(
        "Actors".to_string(),
        crate::config::ConstantValue::Value("{1, 2}".to_string()),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_states(100); // Safety limit

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // From Init: waiting=<<>>
            // 2 actors can request: <<("request", 1)>> or <<("request", 2)>>
            // After one requests, the other can still request
            // Final states: <<>>, <<("read",1)>>, <<("read",2)>>,
            //               <<("read",1),("read",2)>>, <<("read",2),("read",1)>>
            // No actor can request twice because of the guard.
            // Total: 5 distinct states
            // Note: Without the guard, the queue would grow unboundedly.
            assert_eq!(
                stats.states_found, 5,
                "State space should be exactly 5 with guard (found {})",
                stats.states_found
            );
        }
        CheckResult::LimitReached {
            limit_type: _,
            stats,
        } => {
            panic!(
                "Guard failed to limit state space! Found {} states before limit",
                stats.states_found
            );
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inlined_operator_substitution_avoids_variable_capture() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Regression test: compiled inlining substitutes operator parameters into the operator body.
    // This must avoid variable capture when the argument identifier matches a locally-bound name
    // inside the operator body (here: `RemovePending(c)` where `RemovePending` defines `filter(c)`).
    let src = r#"
---- MODULE CaptureAvoidingInline ----
EXTENDS Sequences
VARIABLE pending

RemovePending(cmd) ==
LET filter(c) == c # cmd
IN  SelectSeq(pending, filter)

Init == pending = <<1, 2>>

Next == LET c == 1 IN pending' = RemovePending(c)

NotEmpty == Len(pending) > 0
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["NotEmpty".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_max_states(16);

    let result = checker.check();
    match result {
        CheckResult::Success(stats) => {
            // pending: <<1,2>> -> <<2>> (then stutters on <<2>>)
            assert_eq!(stats.states_found, 2);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_case_expression_in_next_action() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test CASE expression handling in Next actions
    // This pattern appears in ReadersWriters.tla:
    //   CASE pair[1] = "read" -> Read(actor)
    //     [] pair[1] = "write" -> Write(actor)
    let src = r#"
---- MODULE CaseAction ----
VARIABLE state, value

Init == state = "start" /\ value = 0

ProcessRead ==
/\ value' = value + 1
/\ state' = "read"

ProcessWrite ==
/\ value' = value + 10
/\ state' = "write"

\* CASE-based action selection
DoAction(request) ==
CASE request = "read" -> ProcessRead
  [] request = "write" -> ProcessWrite

Next ==
\/ state = "start" /\ DoAction("read")
\/ state = "start" /\ DoAction("write")
\/ state = "read" /\ state' = "done" /\ UNCHANGED value
\/ state = "write" /\ state' = "done" /\ UNCHANGED value

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // States:
            // 1. (start, 0)     -- initial
            // 2. (read, 1)      -- from DoAction("read")
            // 3. (write, 10)    -- from DoAction("write")
            // 4. (done, 1)      -- from read -> done
            // 5. (done, 10)     -- from write -> done
            assert_eq!(
                stats.states_found, 5,
                "Should find 5 states with CASE-based actions (found {})",
                stats.states_found
            );
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_constraints() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test CONSTRAINT directive support
    // Constraint limits state space by filtering states that don't satisfy it
    let src = r#"
---- MODULE ConstraintTest ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = x + 1

\* Without constraint, this would explore infinitely
\* With constraint x <= 5, only states 0-5 are explored
Constraint == x <= 5

TypeOK == x \in Nat
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // With constraint, should find exactly 6 states (x = 0, 1, 2, 3, 4, 5)
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        constraints: vec!["Constraint".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 6,
                "With constraint x <= 5, should find exactly 6 states (x = 0..5), found {}",
                stats.states_found
            );
            assert_eq!(stats.initial_states, 1, "Should have 1 initial state");
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}
