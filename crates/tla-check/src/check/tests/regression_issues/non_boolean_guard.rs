// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn assert_non_boolean_next_guard_fails(src: &str) {
    use crate::EvalCheckError;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Error {
            error: CheckError::Eval(EvalCheckError::NextNotBoolean),
            ..
        } => {}
        CheckResult::Error {
            error:
                CheckError::Eval(EvalCheckError::Eval(crate::error::EvalError::TypeError {
                    expected,
                    got: _,
                    span: _,
                })),
            ..
        } => {
            assert_eq!(
                expected, "BOOLEAN",
                "expected BOOLEAN type error for non-boolean NEXT guard"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("expected non-boolean NEXT guard to fail with type error, got: {error:?}");
        }
        other => {
            panic!("expected non-boolean NEXT guard to fail, got: {other:?}");
        }
    }
}

/// Regression tests for #1479: non-boolean NEXT guard expressions must fail.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_literal_guard_fails() {
    let src = r#"
---- MODULE NonBoolLiteralGuard ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ 1
        /\ x' \in {0, 1}
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_operator_ref_guard_fails() {
    let src = r#"
---- MODULE NonBoolOpRefGuard ----
EXTENDS Integers
VARIABLE x
G == 1
Init == x = 0
Next == /\ G
        /\ x' \in {0, 1}
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_operator_apply_guard_fails() {
    let src = r#"
---- MODULE NonBoolOpApplyGuard ----
EXTENDS Integers
VARIABLE x
G(v) == v
Init == x = 0
Next == /\ G(1)
        /\ x' \in {0, 1}
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_exists_body_guard_fails() {
    let src = r#"
---- MODULE NonBoolExistsGuard ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ (\E n \in {1} : 1)
        /\ x' \in {0, 1}
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_top_level_next_expr_fails() {
    let src = r#"
---- MODULE NonBoolTopLevelNext ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == 1
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_if_condition_fails() {
    let src = r#"
---- MODULE NonBoolIfCondition ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF 1 THEN x' = 1 ELSE x' = 0
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

/// Regression test for #1479: non-boolean guard inside Or branch must fail.
/// Previously, is_or_branch_disabled_error caught TypeError and silently
/// disabled the branch, causing TLA2 to report success where TLC reports
/// a fatal type error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_guard_in_or_branch_fails() {
    let src = r#"
---- MODULE NonBoolOrBranch ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == \/ (/\ 1 /\ x' = 1)
        \/ (/\ x' = 0)
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

/// Regression test for #1479: non-boolean operator guard inside Or branch.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_op_guard_in_or_branch_fails() {
    let src = r#"
---- MODULE NonBoolOrBranchOp ----
EXTENDS Integers
VARIABLE x
G == 1
Init == x = 0
Next == \/ (/\ G /\ x' = 1)
        \/ (/\ x' = 0)
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

/// Regression test for #1479: non-boolean EXISTS inside Or branch.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_exists_in_or_branch_fails() {
    let src = r#"
---- MODULE NonBoolOrBranchExists ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == \/ (/\ (\E n \in {1} : 1) /\ x' = 1)
        \/ (/\ x' = 0)
====
"#;
    assert_non_boolean_next_guard_fails(src);
}

/// Regression test for #1479: non-boolean guard in nested Or (inside conjunction).
/// This exercises conjunct_process_or_branch (unified.rs:875/890), a different
/// code path from the top-level Expr::Or handler (unified.rs:166/187).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1479_non_boolean_guard_in_nested_or_branch_fails() {
    let src = r#"
---- MODULE NonBoolNestedOrBranch ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ x = 0
        /\ (\/ (/\ 1 /\ x' = 1)
            \/ (/\ x' = 0))
====
"#;
    assert_non_boolean_next_guard_fails(src);
}
