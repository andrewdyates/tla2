// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use tla_check::Config;
use tla_check::EvalCtx;
use tla_check::LivenessCheckError;
use tla_check::{AstToLive, ConvertError};
use tla_check::{CheckError, CheckResult};
use tla_core::ast::{BoundPattern, BoundVar, Expr};
use tla_core::Spanned;

mod common;

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bounded_quantifier_tuple_pattern_errors_on_non_tuple_element() {
    let conv = AstToLive::new();
    let ctx = EvalCtx::new();

    // \E <<a, b>> \in {1} : <>TRUE
    let bounds = vec![BoundVar {
        name: spanned("a".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
            BigInt::from(1),
        ))])))),
        pattern: Some(BoundPattern::Tuple(vec![
            spanned("a".to_string()),
            spanned("b".to_string()),
        ])),
    }];
    let body = spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(true)))));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let err = conv.convert(&ctx, &expr).unwrap_err();
    match err {
        ConvertError::BoundTuplePatternMismatch {
            expected_arity,
            actual_value_variant,
            actual_arity,
            ..
        } => {
            assert_eq!(expected_arity, 2);
            assert!(matches!(actual_value_variant, "SmallInt" | "Int"));
            assert_eq!(actual_arity, None);
        }
        other => panic!("Expected BoundTuplePatternMismatch, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bounded_quantifier_tuple_pattern_errors_on_wrong_arity_tuple() {
    let conv = AstToLive::new();
    let ctx = EvalCtx::new();

    // \E <<a, b>> \in {<<1, 2, 3>>} : <>TRUE
    let bounds = vec![BoundVar {
        name: spanned("a".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(
            Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ]),
        )])))),
        pattern: Some(BoundPattern::Tuple(vec![
            spanned("a".to_string()),
            spanned("b".to_string()),
        ])),
    }];
    let body = spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(true)))));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let err = conv.convert(&ctx, &expr).unwrap_err();
    match err {
        ConvertError::BoundTuplePatternMismatch {
            expected_arity,
            actual_value_variant,
            actual_arity,
            ..
        } => {
            assert_eq!(expected_arity, 2);
            assert_eq!(actual_value_variant, "Tuple");
            assert_eq!(actual_arity, Some(3));
        }
        other => panic!("Expected BoundTuplePatternMismatch, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_module_errors_on_bounded_quantifier_tuple_pattern_non_tuple_element() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessBoundedQuantifierTuplePatternNonTuple ----
VARIABLE x
Init == x = 0
Next == x' = x
Prop == \E <<a, b>> \in {1} : <>(x = 1)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Liveness(LivenessCheckError::Generic(msg)) => {
                assert!(msg.contains("Failed to convert property 'Prop'"));
                assert!(msg.contains("Bounded quantifier tuple pattern expects tuple of length 2"));
                assert!(msg.contains("got SmallInt") || msg.contains("got Int"));
            }
            other => panic!("expected LivenessError, got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_module_errors_on_bounded_quantifier_tuple_pattern_wrong_arity_tuple() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessBoundedQuantifierTuplePatternWrongArity ----
VARIABLE x
Init == x = 0
Next == x' = x
Prop == \E <<a, b>> \in {<<1, 2, 3>>} : <>(x = 1)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Error { error, .. } => match error {
            CheckError::Liveness(LivenessCheckError::Generic(msg)) => {
                assert!(msg.contains("Failed to convert property 'Prop'"));
                assert!(msg.contains("Bounded quantifier tuple pattern expects tuple of length 2"));
                assert!(msg.contains("got Tuple of length 3"));
            }
            other => panic!("expected LivenessError, got: {other:?}"),
        },
        other => panic!("expected Error, got: {other:?}"),
    }
}
