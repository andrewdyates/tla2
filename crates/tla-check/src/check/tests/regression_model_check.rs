// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_operator_replacement() {
    use std::collections::HashMap;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Test operator replacement: Ballot <- MCBallot
    let src = r#"
---- MODULE OpReplace ----
EXTENDS Integers
VARIABLE x

Ballot == Nat
MCBallot == 0..1

Init == x = 0
Next == \E b \in Ballot : x' = b

InRange == x \in MCBallot
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config with operator replacement
    let mut constants = HashMap::new();
    constants.insert(
        "Ballot".to_string(),
        crate::config::ConstantValue::Replacement("MCBallot".to_string()),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        constants,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // With Ballot <- MCBallot, we should have:
            // - 2 states: x=0, x=1
            // - 4 transitions: from x=0 to x=0, x=0 to x=1, x=1 to x=0, x=1 to x=1
            assert_eq!(
                stats.states_found, 2,
                "Should have 2 states with Ballot <- MCBallot"
            );
            assert!(
                stats.transitions > 0,
                "Should have transitions with Ballot <- MCBallot"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("Model check failed with error: {:?}", error);
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Regression test for issue #342: False positive invariant violations due to
/// missing guard validation inside CASE expression bodies.
///
/// Bug: When extract_symbolic_assignments processes a CASE body like Write(actor),
/// it silently ignores non-primed guards (e.g., `readers = {}`) via `_ => Ok(())`.
/// This allows invalid transitions where the guard should have blocked the action.
///
/// This test mirrors the ReadersWriters pattern:
/// - CASE expression selects between Read and Write actions
/// - Write has a guard `resource_free` that must be true
/// - Safety invariant says Read and Write can't happen together
/// - Bug causes Write to execute even when resource_free is false
///
/// Regression test for issue #342: CASE body guards not validated.
/// Fixed in commit d680e2e.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_case_body_guard_validation_issue_342() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Minimal repro of ReadersWriters false positive pattern
    // NOTE: Both DoRead and DoWrite need guards for Safety to hold.
    // The original test was buggy - UNCHANGED <<..., pending>> conflicted
    // with Process's pending' = "none", causing deadlock in TLC.
    let src = r#"
---- MODULE CaseGuardTest ----
VARIABLE active_read, active_write, pending

Init ==
/\ active_read = FALSE
/\ active_write = FALSE
/\ pending = "none"

\* Read action - requires active_write = FALSE
DoRead ==
/\ active_write = FALSE    \* Guard: can't read while writing
/\ active_read' = TRUE
/\ UNCHANGED active_write

\* Write action has a GUARD: requires active_read = FALSE
\* This guard is inside the CASE body and must be checked!
DoWrite ==
/\ active_read = FALSE     \* Guard: can't write while reading
/\ active_write' = TRUE
/\ UNCHANGED active_read

\* Request an action (sets pending)
Request(action) ==
/\ pending = "none"
/\ pending' = action
/\ UNCHANGED <<active_read, active_write>>

\* Process the pending request via CASE
\* DoRead/DoWrite don't touch pending - Process handles it
Process ==
/\ pending /= "none"
/\ CASE pending = "read" -> DoRead
     [] pending = "write" -> DoWrite
/\ pending' = "none"

\* Release active resources
Release ==
/\ active_read \/ active_write
/\ active_read' = FALSE
/\ active_write' = FALSE
/\ UNCHANGED pending

Next ==
\/ Request("read")
\/ Request("write")
\/ Process
\/ Release

\* Safety: read and write should never be active simultaneously
\* TLC: passes (9 states). Bug causes TLA2 false positive.
Safety == ~(active_read /\ active_write)

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    // Should succeed - Safety should hold because DoWrite's guard prevents
    // Write from executing when active_read is TRUE.
    match result {
        CheckResult::Success(stats) => {
            // Correct behavior: model checking passes, Safety holds
            // TLC baseline: 9 states for this spec
            assert_eq!(
                stats.states_found, 9,
                "State count must match TLC baseline (9 states)"
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "BUG #342: False positive - Invariant '{}' reported violated but should hold. \
                 The guard `active_read = FALSE` inside DoWrite (CASE body) is being ignored.",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Regression test for #1483: SetCup/SetDiff with SetPred operands in model-checked invariants.
///
/// Verifies that the compiled guard invariant evaluation path correctly handles
/// set operations (union, difference, intersection) involving SetPred operands
/// that require eval context for membership checks.
///
/// Previously, `set_contains(...).unwrap_or(false)` collapsed indeterminate
/// SetPred membership to `false`, causing false invariant violations.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_set_ops_with_set_pred_invariant_1483() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SetPredInvariant ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = x

\* 2 \in ({1} \cup {n \in Nat : n > 1}) should be TRUE
InvCup == 2 \in ({1} \cup {n \in Nat : n > 1})

\* 2 should NOT be in ({1, 2, 3} \ {n \in Nat : n > 1})
InvDiff == ~(2 \in ({1, 2, 3} \ {n \in Nat : n > 1}))

\* 2 \in ({1, 2, 3} \cap {n \in Nat : n > 1}) should be TRUE
InvCap == 2 \in ({1, 2, 3} \cap {n \in Nat : n > 1})

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();

    // Test all three invariants together
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![
            "InvCup".to_string(),
            "InvDiff".to_string(),
            "InvCap".to_string(),
        ],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Should find exactly 1 state (x=0)");
            assert_eq!(stats.initial_states, 1);
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "BUG #1483: False invariant violation for '{}'. \
                 SetCup/SetDiff/SetCap with SetPred operands must propagate \
                 indeterminate membership to context-aware evaluation, not collapse to false.",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Regression test for #1500: SeqSet/BigUnion with SetPred operands in model-checked invariants.
///
/// Exercises the compiled guard/invariant evaluation path where `set_contains`
/// returns `None` for SeqSet (indeterminate base) and BigUnion (indeterminate inner sets).
/// Previously, only SetCup/SetCap/SetDiff were handled by `set_contains_with_ctx`;
/// SeqSet and BigUnion fell through to TypeError.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_seqset_union_set_pred_invariant_1500() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SeqSetUnionPredInvariant ----
EXTENDS Integers, Sequences
VARIABLE x

Init == x = 0
Next == x' = x

\* Seq(SetPred) membership: <<1, 2>> \in Seq({n \in {1,2,3} : n > 0}) = TRUE
InvSeq == <<1, 2>> \in Seq({n \in {1, 2, 3} : n > 0})

\* UNION with SetPred inner sets: 2 \in UNION {{n \in {1,2,3} : n > 1}, {10}} = TRUE
InvUnion == 2 \in UNION {{n \in {1, 2, 3} : n > 1}, {10}}

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvSeq".to_string(), "InvUnion".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Should find exactly 1 state (x=0)");
            assert_eq!(stats.initial_states, 1);
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "BUG #1500: False invariant violation for '{}'. \
                 SeqSet/BigUnion with SetPred operands must propagate \
                 indeterminate membership to context-aware evaluation, not TypeError.",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Regression test for #1500: PrimeInSet compiled action path with SeqSet/BigUnion + SetPred.
///
/// Exercises the CompiledAction::PrimeInSet bound-variable membership check when the
/// set evaluates to a SeqSet or BigUnion containing SetPred leaves. The bound-check
/// path at action.rs calls `set_contains()` → `None` → `set_contains_with_ctx()`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_prime_in_set_seqset_setpred_1500() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // x' \in Seq({n \in {1,2,3} : n > 0}) acts as a PrimeInSet guard
    // in the compiled action. When x' is already bound to <<1,2>>,
    // the bound-check path fires and needs set_contains_with_ctx for SeqSet.
    let src = r#"
---- MODULE PrimeInSetSeqPred ----
EXTENDS Integers, Sequences
VARIABLE x

Init == x = <<1, 2>>
Next == x' = <<1, 2>> /\ x' \in Seq({n \in {1, 2, 3} : n > 0})

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Should find exactly 1 state");
        }
        other => panic!(
            "BUG #1500: Expected success but got {:?}. \
             PrimeInSet bound-check path must handle SeqSet with SetPred via set_contains_with_ctx.",
            other
        ),
    }
}

/// Regression test for #1500: PrimeInSet compiled action with UNION + SetPred.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_check_prime_in_set_union_setpred_1500() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE PrimeInSetUnionPred ----
EXTENDS Integers
VARIABLE x

Init == x = 2
Next == x' = 2 /\ x' \in UNION {{n \in {1, 2, 3} : n > 1}, {10}}

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Should find exactly 1 state");
        }
        other => panic!(
            "BUG #1500: Expected success but got {:?}. \
             PrimeInSet bound-check path must handle BigUnion with SetPred via set_contains_with_ctx.",
            other
        ),
    }
}
