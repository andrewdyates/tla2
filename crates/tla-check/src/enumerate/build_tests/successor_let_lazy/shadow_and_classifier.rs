// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Guard tests for LET shadowing (#804) and `is_let_lazy_safe_error` coverage (#1892).

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_804_zero_arg_let_shadows_quantifier_binding() {
    // Regression for #804: zero-arg LET definitions must shadow outer quantifier
    // bindings with the same name during successor enumeration.
    //
    // If shadowing fails, this action produces x=1 and x=2; correct behavior is x=3.
    let src = r#"
---- MODULE Test804 ----
VARIABLE x
Init == x = 0
Next ==
  \E h \in {1, 2} :
    LET h == 3 IN
      x' = h
====
"#;

    let (module, mut ctx, vars) = setup_module(src);

    let next_def = find_operator(&module, "Next");

    let current_array = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());

    let succs = enumerate_successors_array(&mut ctx, next_def, &current_array, &vars).unwrap();
    assert!(
        !succs.is_empty(),
        "#804 regression: expected at least one successor from quantified action"
    );
    for succ in &succs {
        assert_eq!(
            succ.get(VarIndex(0)).as_i64(),
            Some(3),
            "#804 regression: LET-bound h must shadow quantifier-bound h"
        );
    }
}

/// Regression guard: verify is_let_lazy_safe_error defers ALL error types that
/// appear in the unused-LET integration tests above.
///
/// TLC evaluates LET bindings lazily — if a binding is unused, its body is
/// NEVER evaluated, so no error of any kind is produced. TLA2 evaluates eagerly
/// as an optimization, but must defer errors for unused bindings to match TLC.
///
/// If this test fails, the `is_let_lazy_safe_error` function has been narrowed
/// in a way that breaks TLC parity. The integration tests above
/// (test_enumerate_successors_let_unused_*) exercise the end-to-end behavior;
/// this test catches the regression at the unit level for faster feedback.
///
/// Part of #1892: prevents re-introduction of narrow allowlist regression.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_let_lazy_safe_error_defers_all_integration_test_error_types() {
    // These error types appear in the unused-LET integration tests above.
    // Each MUST be deferred (return true) to match TLC lazy evaluation semantics.
    let error_types_in_integration_tests: Vec<(&str, EvalError)> = vec![
        (
            "ChooseFailed (test_enumerate_successors_let_unused_choose_does_not_disable_action)",
            EvalError::ChooseFailed { span: None },
        ),
        (
            "TypeError (test_enumerate_successors_let_unused_type_error_does_not_disable_action)",
            EvalError::TypeError {
                expected: "Function",
                got: "Int",
                span: None,
            },
        ),
        (
            "UnchangedNotEvaluable (test_enumerate_successors_let_unused_unchanged_does_not_disable_action)",
            EvalError::UnchangedNotEvaluable { span: None },
        ),
        (
            "DivisionByZero (unused LET body — TLC never evaluates)",
            EvalError::DivisionByZero { span: None },
        ),
        (
            "AssertionFailed (unused LET body — TLC never evaluates)",
            EvalError::AssertionFailed {
                message: "test".to_string(),
                span: None,
            },
        ),
        (
            "ArityMismatch (unused LET body — TLC never evaluates)",
            EvalError::ArityMismatch {
                op: "Foo".to_string(),
                expected: 2,
                got: 1,
                span: None,
            },
        ),
    ];

    // The ONLY error type that must NOT be deferred is ExitRequested (control flow).
    let exit_err = EvalError::ExitRequested { span: None };
    assert!(
        !is_let_lazy_safe_error(&exit_err),
        "ExitRequested must propagate — it's a control flow signal, not a spec error"
    );

    for (label, err) in &error_types_in_integration_tests {
        assert!(
            is_let_lazy_safe_error(err),
            "is_let_lazy_safe_error must defer {} to match TLC lazy LET semantics. \
             Narrowing this function will break the corresponding integration test \
             in the successor_let_lazy test suite. See #1892.",
            label
        );
    }
}
