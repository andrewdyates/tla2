// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Helper for #1552: assert that a spec with a fatal runtime error produces a
/// CheckResult::Error with specifically a EvalCheckError::Eval variant.
/// TLC propagates all errors from getNextStates fatally — they must not be
/// silently suppressed, and must be runtime eval errors (not setup/config).
fn assert_spec_fails_with_eval_error(src: &str, description: &str) {
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
            error: CheckError::Eval(EvalCheckError::Eval(_)),
            ..
        } => {
            // Correct: the spec failed with an evaluation error, matching TLC behavior.
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "#1552 regression ({description}): expected EvalError but got non-eval \
                 error: {error:?}. This may indicate the spec is failing for the wrong reason."
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "#1552 regression ({description}): spec should fail with a runtime error, \
                 but TLA2 reported success. TLC would report a fatal error."
            );
        }
        other => {
            panic!("#1552 regression ({description}): expected Error, got: {other:?}");
        }
    }
}

/// Regression test for #1552: DivisionByZero in Or branch must be fatal.
/// TLC: "Error: The second argument of \\div is 0." (fatal)
/// Previously TLA2 silently succeeded with 1 state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1552_div_by_zero_in_or_branch_fatal() {
    let src = r#"
---- MODULE DivByZeroOrBranch ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == \/ (/\ x = 0 /\ (1 \div 0) = 1 /\ x' = 1)
        \/ (/\ x' = 0)
====
"#;
    assert_spec_fails_with_eval_error(src, "DivisionByZero in Or branch");
}

/// Regression test for #1552: NotInDomain in Or branch must be fatal.
/// TLC: "Attempted to apply function to argument 3, which is not in the domain."
/// Previously TLA2 silently succeeded with 1 state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1552_not_in_domain_in_or_branch_fatal() {
    let src = r#"
---- MODULE NotInDomainOrBranch ----
EXTENDS Integers
VARIABLE x
f == [i \in {1, 2} |-> i * 10]
Init == x = 0
Next == \/ (/\ x = 0 /\ f[3] = 1 /\ x' = 1)
        \/ (/\ x' = 0)
====
"#;
    assert_spec_fails_with_eval_error(src, "NotInDomain in Or branch");
}

/// Regression test for #1552: IndexOutOfBounds in Or branch must be fatal.
/// TLC reports sequence index errors as fatal.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1552_index_out_of_bounds_in_or_branch_fatal() {
    let src = r#"
---- MODULE IndexOOBOrBranch ----
EXTENDS Integers, Sequences
VARIABLE x
Init == x = 0
Next == \/ (/\ x = 0 /\ <<1, 2>>[5] = 1 /\ x' = 1)
        \/ (/\ x' = 0)
====
"#;
    assert_spec_fails_with_eval_error(src, "IndexOutOfBounds in Or branch");
}

/// Regression test for #1552: DivisionByZero at top-level action must be fatal.
/// Tests the run_unified error handler (enumerate.rs), not the Or-branch handler.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1552_div_by_zero_top_level_action_fatal() {
    let src = r#"
---- MODULE DivByZeroTopLevel ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ (1 \div 0) = 1
        /\ x' = 1
====
"#;
    assert_spec_fails_with_eval_error(src, "DivisionByZero at top-level action");
}

/// Regression test for #1552: NotInDomain at top-level action must be fatal.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1552_not_in_domain_top_level_action_fatal() {
    let src = r#"
---- MODULE NotInDomainTopLevel ----
EXTENDS Integers
VARIABLE x
f == [i \in {1, 2} |-> i * 10]
Init == x = 0
Next == /\ f[3] = 1
        /\ x' = 1
====
"#;
    assert_spec_fails_with_eval_error(src, "NotInDomain at top-level action");
}
