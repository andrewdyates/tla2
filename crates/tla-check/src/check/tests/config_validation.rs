// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for config-time operator validation (Part of #2573).
//!
//! Validates that the model checker rejects invalid config entries at setup time
//! with clear errors, matching TLC's `SpecProcessor.processConfigInvariants/
//! Properties/Constraints/ActionConstraints` behavior.

use super::*;
use crate::test_support::parse_module;

fn config_init_next(init: &str, next: &str) -> Config {
    Config {
        init: Some(init.to_string()),
        next: Some(next.to_string()),
        ..Default::default()
    }
}

// ============================================================================
// Arity validation tests
// ============================================================================

/// TLC: TLC_CONFIG_ID_REQUIRES_NO_ARG for INVARIANT with parameters.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_with_arity_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Foo(n) == n > 0
====
"#;
    let module = parse_module(src);
    let config = Config {
        invariants: vec!["Foo".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::OpRequiresNoArgs {
                    op_name,
                    kind,
                    arity,
                }),
            ..
        } => {
            assert_eq!(op_name, "Foo");
            assert_eq!(kind, "INVARIANT");
            assert_eq!(*arity, 1);
        }
        other => panic!("Expected ConfigOpRequiresNoArgs, got: {other:?}"),
    }
}

/// TLC: TLC_CONFIG_ID_REQUIRES_NO_ARG for PROPERTY with parameters.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_property_with_arity_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
LiveProp(n) == <>(x = n)
====
"#;
    let module = parse_module(src);
    let config = Config {
        properties: vec!["LiveProp".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::OpRequiresNoArgs {
                    op_name,
                    kind,
                    arity,
                }),
            ..
        } => {
            assert_eq!(op_name, "LiveProp");
            assert_eq!(kind, "PROPERTY");
            assert_eq!(*arity, 1);
        }
        other => panic!("Expected ConfigOpRequiresNoArgs, got: {other:?}"),
    }
}

/// TLC: TLC_CONFIG_ID_REQUIRES_NO_ARG for CONSTRAINT with parameters.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_constraint_with_arity_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Bound(n) == x < n
====
"#;
    let module = parse_module(src);
    let config = Config {
        constraints: vec!["Bound".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::OpRequiresNoArgs {
                    op_name,
                    kind,
                    arity,
                }),
            ..
        } => {
            assert_eq!(op_name, "Bound");
            assert_eq!(kind, "CONSTRAINT");
            assert_eq!(*arity, 1);
        }
        other => panic!("Expected ConfigOpRequiresNoArgs, got: {other:?}"),
    }
}

/// TLC: TLC_CONFIG_ID_REQUIRES_NO_ARG for ACTION_CONSTRAINT with parameters.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_constraint_with_arity_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
ABound(n) == x' < n
====
"#;
    let module = parse_module(src);
    let config = Config {
        action_constraints: vec!["ABound".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::OpRequiresNoArgs {
                    op_name,
                    kind,
                    arity,
                }),
            ..
        } => {
            assert_eq!(op_name, "ABound");
            assert_eq!(kind, "ACTION_CONSTRAINT");
            assert_eq!(*arity, 1);
        }
        other => panic!("Expected ConfigOpRequiresNoArgs, got: {other:?}"),
    }
}

/// TLC: TLC_CONFIG_ID_REQUIRES_NO_ARG for INIT with parameters.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_with_arity_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
MyInit(n) == x = n
Next == x' = x + 1
====
"#;
    let module = parse_module(src);
    let config = config_init_next("MyInit", "Next");

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::OpRequiresNoArgs {
                    op_name,
                    kind,
                    arity,
                }),
            ..
        } => {
            assert_eq!(op_name, "MyInit");
            assert_eq!(kind, "INIT");
            assert_eq!(*arity, 1);
        }
        other => panic!("Expected ConfigOpRequiresNoArgs, got: {other:?}"),
    }
}

/// TLC: TLC_CONFIG_ID_REQUIRES_NO_ARG for NEXT with parameters.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_with_arity_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
MyNext(n) == x' = x + n
====
"#;
    let module = parse_module(src);
    let config = config_init_next("Init", "MyNext");

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::OpRequiresNoArgs {
                    op_name,
                    kind,
                    arity,
                }),
            ..
        } => {
            assert_eq!(op_name, "MyNext");
            assert_eq!(kind, "NEXT");
            assert_eq!(*arity, 1);
        }
        other => panic!("Expected ConfigOpRequiresNoArgs, got: {other:?}"),
    }
}

// ============================================================================
// Invariant level validation tests
// ============================================================================

/// TLC: TLC_INVARIANT_VIOLATED_LEVEL — invariant with primed variables is rejected.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_with_prime_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
InvWithPrime == x' = x + 1
====
"#;
    let module = parse_module(src);
    let config = Config {
        invariants: vec!["InvWithPrime".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::InvariantNotStateLevel {
                    name,
                    has_prime,
                    has_temporal,
                }),
            ..
        } => {
            assert_eq!(name, "InvWithPrime");
            assert!(*has_prime);
            assert!(!*has_temporal);
        }
        other => panic!("Expected InvariantNotStateLevel, got: {other:?}"),
    }
}

/// TLC: TLC_INVARIANT_VIOLATED_LEVEL — invariant with temporal operators is rejected.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_with_temporal_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TemporalInv == <>(x = 5)
====
"#;
    let module = parse_module(src);
    let config = Config {
        invariants: vec!["TemporalInv".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::InvariantNotStateLevel {
                    name,
                    has_prime: _,
                    has_temporal,
                }),
            ..
        } => {
            assert_eq!(name, "TemporalInv");
            assert!(*has_temporal);
        }
        other => panic!("Expected InvariantNotStateLevel, got: {other:?}"),
    }
}

/// TLC: TLC_INVARIANT_VIOLATED_LEVEL — invariant with Always temporal operator rejected.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_with_always_temporal_rejected() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
BoxInv == [](x >= 0)
====
"#;
    let module = parse_module(src);
    let config = Config {
        invariants: vec!["BoxInv".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::InvariantNotStateLevel {
                    name, has_temporal, ..
                }),
            ..
        } => {
            assert_eq!(name, "BoxInv");
            assert!(*has_temporal);
        }
        other => panic!("Expected InvariantNotStateLevel, got: {other:?}"),
    }
}

// ============================================================================
// Positive tests — valid configs should still work
// ============================================================================

/// Zero-arity invariant should pass validation.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_valid_invariant_passes_validation() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = IF x < 3 THEN x + 1 ELSE x
TypeOK == x \in 0..3
====
"#;
    let module = parse_module(src);
    let config = Config {
        invariants: vec!["TypeOK".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    assert!(
        matches!(result, CheckResult::Success(_)),
        "Valid invariant should pass: {result:?}"
    );
}

/// Multiple zero-arity invariants should pass validation.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multiple_valid_invariants_pass_validation() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = IF x < 3 THEN x + 1 ELSE x
TypeOK == x \in 0..3
Positive == x >= 0
====
"#;
    let module = parse_module(src);
    let config = Config {
        invariants: vec!["TypeOK".to_string(), "Positive".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    assert!(
        matches!(result, CheckResult::Success(_)),
        "Valid invariants should pass: {result:?}"
    );
}

// ============================================================================
// Error message format tests (snapshot-style)
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_config_op_requires_no_args_display() {
    let err = ConfigCheckError::OpRequiresNoArgs {
        op_name: "Foo".to_string(),
        kind: "INVARIANT".to_string(),
        arity: 2,
    };
    let msg = err.to_string();
    assert!(msg.contains("INVARIANT"));
    assert!(msg.contains("Foo"));
    assert!(msg.contains('2'));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_not_state_level_display_prime() {
    let err = ConfigCheckError::InvariantNotStateLevel {
        name: "BadInv".to_string(),
        has_prime: true,
        has_temporal: false,
    };
    let msg = err.to_string();
    assert!(msg.contains("BadInv"));
    assert!(msg.contains("primed variables"));
    assert!(!msg.contains("temporal"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_not_state_level_display_temporal() {
    let err = ConfigCheckError::InvariantNotStateLevel {
        name: "BadInv".to_string(),
        has_prime: false,
        has_temporal: true,
    };
    let msg = err.to_string();
    assert!(msg.contains("BadInv"));
    assert!(msg.contains("temporal operators"));
    assert!(!msg.contains("primed"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_not_state_level_display_both() {
    let err = ConfigCheckError::InvariantNotStateLevel {
        name: "BadInv".to_string(),
        has_prime: true,
        has_temporal: true,
    };
    let msg = err.to_string();
    assert!(msg.contains("BadInv"));
    assert!(msg.contains("primed variables and temporal operators"));
}

// ============================================================================
// Multi-arity parameter validation
// ============================================================================

/// SYMMETRY must stay a config error when the operator returns a non-enumerable
/// set-like value. Part of #1918 fixed lazy finite SetPred symmetry support, but
/// malformed configs like `Sym == Nat` must not fall through as eval errors.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_non_enumerable_set_rejected_as_config_error() {
    let src = r#"
---- MODULE Test ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Sym == Nat
====
"#;
    let module = parse_module(src);
    let mut config = config_init_next("Init", "Next");
    config.symmetry = Some("Sym".to_string());

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::Config(message)),
            ..
        } => {
            assert!(
                message.contains("SYMMETRY operator 'Sym' must specify a set of permutations"),
                "unexpected symmetry config message: {message}"
            );
        }
        other => panic!("Expected symmetry ConfigError, got: {other:?}"),
    }
}

/// Operator with 3 parameters should report arity=3.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_multi_param_reports_correct_arity() {
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
ThreeArgs(a, b, c) == a + b + c > 0
====
"#;
    let module = parse_module(src);
    let config = Config {
        invariants: vec!["ThreeArgs".to_string()],
        ..config_init_next("Init", "Next")
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error:
                CheckError::Config(ConfigCheckError::OpRequiresNoArgs {
                    op_name,
                    kind,
                    arity,
                }),
            ..
        } => {
            assert_eq!(op_name, "ThreeArgs");
            assert_eq!(kind, "INVARIANT");
            assert_eq!(*arity, 3);
        }
        other => panic!("Expected ConfigOpRequiresNoArgs with arity 3, got: {other:?}"),
    }
}
