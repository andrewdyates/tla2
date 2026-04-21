// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::EvalCheckError;
use tla_check::{check_module, Config, EvalError};
use tla_check::{CheckError, CheckResult};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1999_or_guard_left_type_error_is_fatal() {
    let src = r#"
---- MODULE OrGuardTypeErrorFatal ----
VARIABLE x
Init == x = 0
Next == /\ ((1 \in 2) \/ FALSE)
        /\ x' = x + 1
====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let result = check_module(&module, &config);
    assert!(
        matches!(
            result,
            CheckResult::Error {
                error: CheckError::Eval(EvalCheckError::Eval(EvalError::TypeError { .. })),
                ..
            }
        ),
        "#1999 regression: OR guard TypeError must propagate fatally, got: {result:?}"
    );
}

/// #1999: TypeError in the RHS of OR must also propagate fatally.
/// TLC evaluates both branches and propagates all errors — no suppression.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1999_or_guard_right_type_error_is_fatal() {
    let src = r#"
---- MODULE OrGuardRhsTypeError ----
VARIABLE x
Init == x = 0
Next == /\ (FALSE \/ (1 \in 2))
        /\ x' = x + 1
====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let result = check_module(&module, &config);
    assert!(
        matches!(
            result,
            CheckResult::Error {
                error: CheckError::Eval(EvalCheckError::Eval(EvalError::TypeError { .. })),
                ..
            }
        ),
        "#1999 regression: OR guard RHS TypeError must propagate fatally, got: {result:?}"
    );
}

/// #1999: In the checker, both OR branches are explored (TLC's getNextStates
/// for OPCODE_lor iterates ALL disjuncts). Even when LHS is TRUE, the RHS
/// is evaluated as a separate action branch. A TypeError in RHS propagates.
///
/// This differs from eval-level short-circuit (where TRUE \/ X returns TRUE
/// without evaluating X). The checker must explore all branches to find all
/// possible successor states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1999_or_checker_explores_both_branches() {
    let src = r#"
---- MODULE OrCheckerBothBranches ----
VARIABLE x
Init == x = 0
Next == /\ (TRUE \/ (1 \in 2))
        /\ x' = x + 1
====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let result = check_module(&module, &config);
    // The checker explores both OR branches (matching TLC getNextStates behavior).
    // Even though LHS=TRUE, the RHS `1 \in 2` is evaluated and produces TypeError.
    assert!(
        matches!(
            result,
            CheckResult::Error {
                error: CheckError::Eval(EvalCheckError::Eval(EvalError::TypeError { .. })),
                ..
            }
        ),
        "#1999: checker must explore both OR branches — RHS TypeError is fatal, got: {result:?}"
    );
}
