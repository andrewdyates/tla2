// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_check::CheckResult;
use tla_check::{check_module, CheckError, Config, EvalCheckError};
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn assert_spec_fails_with_eval_error(src: &str, description: &str) {
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

    let result = check_module(&module, &config);
    assert!(
        matches!(
            result,
            CheckResult::Error {
                error: CheckError::Eval(EvalCheckError::Eval(_)),
                ..
            }
        ),
        "#1667 regression ({description}): expected EvalError, got: {result:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1667_guard_conjunction_flattened_and_eval_error_fatal() {
    let src = r#"
---- MODULE GuardConjFlattenedAndError ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == /\ x' = x
        /\ (/\ x = 0
            /\ (1 \div 0) = 1)
====
"#;

    assert_spec_fails_with_eval_error(
        src,
        "flattened-AND guard conjunction must propagate DivisionByZero",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1667_guard_conjunction_non_and_eval_error_fatal() {
    let src = r#"
---- MODULE GuardConjNonAndError ----
EXTENDS Integers
VARIABLE x
f == [i \in {1} |-> i]
Init == x = 0
Next == /\ x' = x
        /\ f[2] = 1
====
"#;

    assert_spec_fails_with_eval_error(src, "non-AND guard conjunction must propagate NotInDomain");
}
