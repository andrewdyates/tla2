// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unused-binding error deferral regressions: each test verifies that a specific
//! error type from eager LET evaluation is silently deferred when the binding is
//! unused, matching TLC lazy evaluation semantics.

use super::*;

/// Proof coverage: LET lazy binding must skip TypeError from eager evaluation.
///
/// When a zero-arg LET binding body produces a TypeError during eager eval
/// (e.g., DOMAIN applied to a non-function), the error must be silently
/// caught if the binding is unused. This exercises the
/// `matches!(&e, EvalError::TypeError { .. })` path in unified.rs.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_let_unused_type_error_does_not_disable_action() {
    // DOMAIN(1) produces a TypeError because 1 is not a function/record/sequence.
    // Since `bad` is unused, the action should remain enabled.
    let src = r#"
---- MODULE Test ----
VARIABLE x

Action ==
    LET bad == DOMAIN 1
    IN x' = 42

Init == x = 0
Next == Action
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");

    let successors = enumerate_successors(&mut ctx, next_def, &current_state, &vars).unwrap();
    assert_eq!(
        successors.len(),
        1,
        "Unused LET binding with TypeError should not disable the action"
    );
    assert_eq!(successors[0].get("x"), Some(&Value::int(42)));
}

/// Proof coverage: LET lazy binding must skip action-level errors from eager evaluation.
///
/// When a zero-arg LET binding body contains UNCHANGED (which fails with
/// "UNCHANGED cannot be evaluated" outside of action context), the error
/// must be silently caught if the binding is unused. This exercises the
/// `is_action_level_error(&e)` path in unified.rs.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_let_unused_unchanged_does_not_disable_action() {
    // `UNCHANGED x` inside a LET binding body fails with an action-level error
    // during eager evaluation. Since `stutter` is unused, the action should proceed.
    let src = r#"
---- MODULE Test ----
VARIABLE x, y

Action ==
    LET stutter == UNCHANGED x
    IN /\ x' = 42
       /\ y' = y

Init == x = 0 /\ y = 0
Next == Action
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);

    let next_def = find_operator(&module, "Next");

    let successors = enumerate_successors(&mut ctx, next_def, &current_state, &vars).unwrap();
    assert_eq!(
        successors.len(),
        1,
        "Unused LET binding with action-level error should not disable the action"
    );
    assert_eq!(successors[0].get("x"), Some(&Value::int(42)));
}

/// Regression test for #1279: LET lazy binding must catch OneArgumentError.
///
/// `Head(1)` produces a OneArgumentError because 1 is not a sequence.
/// Since `bad` is unused, the action should remain enabled.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_let_unused_one_argument_error_does_not_disable_action() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE x

Action ==
    LET bad == Head(1)
    IN x' = 42

Init == x = 0
Next == Action
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");

    let successors = enumerate_successors(&mut ctx, next_def, &current_state, &vars).unwrap();
    assert_eq!(
        successors.len(),
        1,
        "Unused LET binding with OneArgumentError should not disable the action"
    );
    assert_eq!(successors[0].get("x"), Some(&Value::int(42)));
}

/// Regression test: LET lazy binding catches ApplyEmptySeq (Head(<<>>)).
///
/// `Head(<<>>)` produces ApplyEmptySeq. Since `bad` is unused, the action
/// should remain enabled.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_let_unused_apply_empty_seq_does_not_disable_action() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE x

Action ==
    LET bad == Head(<<>>)
    IN x' = 42

Init == x = 0
Next == Action
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");

    let successors = enumerate_successors(&mut ctx, next_def, &current_state, &vars).unwrap();
    assert_eq!(
        successors.len(),
        1,
        "Unused LET binding with ApplyEmptySeq should not disable the action"
    );
    assert_eq!(successors[0].get("x"), Some(&Value::int(42)));
}

/// Regression test: LET lazy binding catches EvaluatingError (Append(1, 2)).
///
/// `Append(1, 2)` produces EvaluatingError because 1 is not a sequence.
/// Since `bad` is unused, the action should remain enabled.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_let_unused_evaluating_error_does_not_disable_action() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE x

Action ==
    LET bad == Append(1, 2)
    IN x' = 42

Init == x = 0
Next == Action
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");

    let successors = enumerate_successors(&mut ctx, next_def, &current_state, &vars).unwrap();
    assert_eq!(
        successors.len(),
        1,
        "Unused LET binding with EvaluatingError should not disable the action"
    );
    assert_eq!(successors[0].get("x"), Some(&Value::int(42)));
}
