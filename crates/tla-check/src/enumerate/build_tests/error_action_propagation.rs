// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Error handling tests (issue #126: test gaps audit, updated for #1552)
// Fix #1552: TLC propagates ALL errors from getNextStates fatally. There is
// no "disabled action" concept at the action level. These tests verify that
// errors propagate rather than being silently suppressed.
// ========================================================================

// NOTE: test_enumerate_type_error_disables_action removed - verified wrong TLC semantics
// TLC errors on type mismatches like `x' \in 42`, it doesn't silently disable actions
// See: reports/prover/2026-01-27-p196-type-error-analysis.md

/// Fix #1552: DivisionByZero in action body propagates fatally (TLC semantics).
/// TLC: "Error: The second argument of \\div is 0." (terminates model checking)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_division_by_zero_disables_action() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 10 \div 0  \* Division by zero - fatal error
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err =
        result.expect_err("#1552: DivisionByZero must propagate as fatal error (TLC behavior)");
    assert!(
        matches!(err, EvalError::DivisionByZero { .. }),
        "#1634: expected DivisionByZero, got {err:?}"
    );
}

/// Test that UndefinedOp error IS propagated (spec bug, not disabled action).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_undefined_op_propagates_error() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = UndefinedOperator(x)  \* Not defined - spec bug
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    assert!(result.is_err(), "UndefinedOp should propagate as error");
    assert!(matches!(result.unwrap_err(), EvalError::UndefinedOp { .. }));
}

/// Regression test for #1467: plain guard eval errors must propagate.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1467_plain_guard_apply_error_propagates() {
    let src = r#"
---- MODULE Test1467ApplyGuard ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ UndefinedGuardOp(x)
        /\ x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    assert!(
        result.is_err(),
        "#1467 regression: guard eval errors must not be silently treated as guard=false"
    );
    assert!(matches!(result.unwrap_err(), EvalError::UndefinedOp { .. }));
}

/// Regression test for #1467: EXISTS guard eval errors must propagate.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1467_exists_guard_error_propagates() {
    let src = r#"
---- MODULE Test1467ExistsGuard ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ (\E i \in 1..2 : UndefinedGuardOp(i))
        /\ x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    assert!(
        result.is_err(),
        "#1467 regression: EXISTS guard errors must propagate, not disable the action silently"
    );
    assert!(matches!(result.unwrap_err(), EvalError::UndefinedOp { .. }));
}

/// Regression test for #1425: non-boolean CASE guards in actions must be fatal.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1425_case_guard_non_boolean_is_fatal() {
    let src = r#"
---- MODULE Test1425NonBool ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ CASE 42 -> TRUE [] OTHER -> TRUE
        /\ x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err = result.expect_err("#1425: non-boolean CASE guard must be fatal");
    match err {
        EvalError::CaseGuardError { source, .. } => {
            assert!(
                matches!(&*source, EvalError::TypeError { .. }),
                "#1425: expected wrapped TypeError, got {:?}",
                source
            );
        }
        other => panic!("#1425: expected CaseGuardError, got {other:?}"),
    }
}

/// Regression test for #1425: CASE guard eval errors must propagate as fatal.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1425_case_guard_undefined_op_is_fatal() {
    let src = r#"
---- MODULE Test1425UndefinedOp ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ CASE UndefinedGuardOp(1) -> TRUE [] OTHER -> TRUE
        /\ x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err = result.expect_err("#1425: CASE guard eval error must be fatal");
    match err {
        EvalError::CaseGuardError { source, .. } => {
            assert!(
                matches!(&*source, EvalError::UndefinedOp { .. }),
                "#1425: expected wrapped UndefinedOp, got {:?}",
                source
            );
        }
        other => panic!("#1425: expected CaseGuardError, got {other:?}"),
    }
}

/// Regression test for #1425: disabled-action-class errors in CASE guards are fatal.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1425_case_guard_division_by_zero_is_fatal() {
    let src = r#"
---- MODULE Test1425DivZero ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ CASE 1 \div 0 = 0 -> TRUE [] OTHER -> TRUE
        /\ x' = x + 1
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err = result.expect_err("#1425: DivisionByZero in CASE guard must be fatal");
    match err {
        EvalError::CaseGuardError { source, .. } => {
            assert!(
                matches!(&*source, EvalError::DivisionByZero { .. }),
                "#1425: expected wrapped DivisionByZero, got {:?}",
                source
            );
        }
        other => panic!("#1425: expected CaseGuardError, got {other:?}"),
    }
}

/// Test that NotInDomain in action body treats action as disabled (TLC semantics).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_not_in_domain_disables_action() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
f == [n \in {1, 2, 3} |-> n * 10]
Init == x = 0
Next == x' = f[42]  \* 42 not in domain - fatal error
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    // Fix #1552: TLC propagates domain errors fatally.
    // Note: [n \in {1,2,3} |-> n*10] is internally a tuple <<10,20,30>>,
    // so f[42] yields IndexOutOfBounds rather than NotInDomain.
    let err = result.expect_err("#1552: domain error must propagate as fatal error (TLC behavior)");
    assert!(
        matches!(err, EvalError::IndexOutOfBounds { .. }),
        "#1634: expected IndexOutOfBounds, got {err:?}"
    );
}

/// Fix #1552: NotInDomain in action body propagates fatally (TLC semantics).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_index_out_of_bounds_disables_action() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers, Sequences
VARIABLE x
seq == <<1, 2, 3>>
Init == x = 0
Next == x' = seq[10]  \* Index out of bounds - fatal error
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err =
        result.expect_err("#1552: IndexOutOfBounds must propagate as fatal error (TLC behavior)");
    assert!(
        matches!(err, EvalError::IndexOutOfBounds { .. }),
        "#1634: expected IndexOutOfBounds, got {err:?}"
    );
}

/// Fix #1552: NoSuchField in action body propagates fatally (TLC semantics).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_no_such_field_disables_action() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
r == [a |-> 1, b |-> 2]
Init == x = 0
Next == x' = r.nonexistent  \* Field doesn't exist - fatal error
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err = result.expect_err("#1552: NoSuchField must propagate as fatal error (TLC behavior)");
    assert!(
        matches!(err, EvalError::NoSuchField { .. }),
        "#1634: expected NoSuchField, got {err:?}"
    );
}

/// Fix #1552: ChooseFailed in action body propagates fatally (TLC semantics).
/// TLC: "Attempted to compute CHOOSE x \\in S: P, but no element of S satisfied P."
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_choose_failed_disables_action() {
    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = CHOOSE n \in {} : TRUE  \* Empty domain - fatal error
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .unwrap();

    let result = enumerate_action_successors(&mut ctx, &next_def.body, &current_state, &vars);
    let err = result.expect_err("#1552: ChooseFailed must propagate as fatal error (TLC behavior)");
    assert!(
        matches!(err, EvalError::ChooseFailed { .. }),
        "#1634: expected ChooseFailed, got {err:?}"
    );
}
