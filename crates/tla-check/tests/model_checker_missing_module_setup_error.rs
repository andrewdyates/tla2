// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::ConfigCheckError;
use tla_check::{AdaptiveChecker, CheckError, CheckResult, Config, ModelChecker, ParallelChecker};

fn config_init_next(init: &str, next: &str) -> Config {
    Config {
        init: Some(init.to_string()),
        next: Some(next.to_string()),
        ..Default::default()
    }
}

fn assert_setup_error_via(msg: &str, via: &str) {
    assert!(
        msg.contains(&format!("via {via}")),
        "expected missing module error to indicate {via}, got: {msg}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_missing_non_stdlib_module_is_setup_error() {
    let main_src = r#"
---- MODULE Main ----
EXTENDS Missing
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;

    let main = common::parse_module(main_src);
    let config = config_init_next("Init", "Next");

    let mut checker = ModelChecker::new_with_extends(&main, &[], &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Config(ConfigCheckError::Setup(msg)) => {
                assert_setup_error_via(&msg, "EXTENDS");
            }
            other => panic!("expected SetupError, got {other:?}"),
        },
        other => panic!("expected error, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_missing_non_stdlib_module_via_instance_expr_is_setup_error() {
    let main_src = r#"
---- MODULE Main ----
VARIABLE x
I == INSTANCE Missing
Init == x = 0
Next == x' = x
====
"#;

    let main = common::parse_module(main_src);
    let config = config_init_next("Init", "Next");

    let mut checker = ModelChecker::new_with_extends(&main, &[], &config);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Config(ConfigCheckError::Setup(msg)) => {
                assert_setup_error_via(&msg, "INSTANCE");
            }
            other => panic!("expected SetupError, got {other:?}"),
        },
        other => panic!("expected error, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_missing_non_stdlib_module_is_setup_error() {
    let main_src = r#"
---- MODULE Main ----
EXTENDS Missing
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;

    let main = common::parse_module(main_src);
    let config = config_init_next("Init", "Next");

    let mut checker = ParallelChecker::new_with_extends(&main, &[], &config, 2);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Config(ConfigCheckError::Setup(msg)) => {
                assert_setup_error_via(&msg, "EXTENDS");
            }
            other => panic!("expected SetupError, got {other:?}"),
        },
        other => panic!("expected error, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_missing_non_stdlib_module_via_instance_expr_is_setup_error() {
    let main_src = r#"
---- MODULE Main ----
VARIABLE x
I == INSTANCE Missing
Init == x = 0
Next == x' = x
====
"#;

    let main = common::parse_module(main_src);
    let config = config_init_next("Init", "Next");

    let mut checker = ParallelChecker::new_with_extends(&main, &[], &config, 2);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Config(ConfigCheckError::Setup(msg)) => {
                assert_setup_error_via(&msg, "INSTANCE");
            }
            other => panic!("expected SetupError, got {other:?}"),
        },
        other => panic!("expected error, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_missing_non_stdlib_module_is_setup_error() {
    let main_src = r#"
---- MODULE Main ----
EXTENDS Missing
Init == TRUE
Next == TRUE
====
"#;

    let main = common::parse_module(main_src);
    let config = config_init_next("Init", "Next");

    let mut checker = AdaptiveChecker::new_with_extends(&main, &[], &config);
    checker.set_deadlock_check(false);

    let (result, _analysis) = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Config(ConfigCheckError::Setup(msg)) => {
                assert_setup_error_via(&msg, "EXTENDS");
            }
            other => panic!("expected SetupError, got {other:?}"),
        },
        other => panic!("expected error, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_adaptive_missing_non_stdlib_module_via_instance_expr_is_setup_error() {
    let main_src = r#"
---- MODULE Main ----
I == INSTANCE Missing
Init == TRUE
Next == TRUE
====
"#;

    let main = common::parse_module(main_src);
    let config = config_init_next("Init", "Next");

    let mut checker = AdaptiveChecker::new_with_extends(&main, &[], &config);
    checker.set_deadlock_check(false);

    let (result, _analysis) = checker.check();
    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Config(ConfigCheckError::Setup(msg)) => {
                assert_setup_error_via(&msg, "INSTANCE");
            }
            other => panic!("expected SetupError, got {other:?}"),
        },
        other => panic!("expected error, got {other:?}"),
    }
}
