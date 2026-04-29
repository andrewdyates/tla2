// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded quantifier temporal expansion tests: domain enumeration, bindings, tuple patterns
//!
//! Split from liveness/ast_to_live/tests.rs — Part of #2779

use super::helpers::make_ctx;
use super::*;

fn make_parity_filtered_set(inner_domain: &Spanned<Expr>, wanted: i64) -> Spanned<Expr> {
    spanned(Expr::SetFilter(
        BoundVar {
            name: spanned("n".to_string()),
            domain: Some(Box::new(inner_domain.clone())),
            pattern: None,
        },
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Mod(
                Box::new(spanned(Expr::Ident(
                    "n".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(2)))),
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(wanted)))),
        ))),
    ))
}

fn membership_signature(ctx: &EvalCtx, expr: &Spanned<Expr>, value: &Value) -> (bool, bool) {
    let Value::SetPred(spv) = value else {
        panic!("Expected SetPred binding");
    };
    let in_0 =
        crate::eval::check_set_pred_membership(ctx, &Value::SmallInt(0), spv, Some(expr.span))
            .unwrap();
    let in_1 =
        crate::eval::check_set_pred_membership(ctx, &Value::SmallInt(1), spv, Some(expr.span))
            .unwrap();
    (in_0, in_1)
}

fn analyze_temporal_binding_part(ctx: &EvalCtx, part: &LiveExpr) -> (bool, bool) {
    let LiveExpr::Always(inner) = part else {
        panic!("Expected Always");
    };
    let LiveExpr::StatePred {
        expr,
        bindings: Some(bindings),
        ..
    } = inner.as_ref()
    else {
        panic!("Expected StatePred with bindings");
    };
    let Expr::In(_a, b) = &expr.node else {
        panic!("Expected In");
    };
    assert!(matches!(&b.node, Expr::Ident(name, _) if name == "x"));
    let Some(value) = bindings.lookup_by_name("x") else {
        panic!("Expected binding for x");
    };
    membership_signature(ctx, expr, &value)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_temporal_expands() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // \E x \in {1, 2}: <>TRUE
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ])))),
        pattern: None,
    }];
    let body = spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(true)))));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::Or(parts) = live else {
        panic!("Expected Or from temporal bounded quantifier expansion");
    };
    assert_eq!(parts.len(), 2);
    for part in parts {
        let LiveExpr::Eventually(inner) = part else {
            panic!("Expected Eventually");
        };
        assert!(matches!(*inner, LiveExpr::Bool(true)));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_temporal_non_enumerable_domain_errors() {
    let conv = AstToLive::new().with_location_module_name("Test");
    let ctx = make_ctx();

    // \E x \in Seq({1}) : <>TRUE
    //
    // `Seq({1})` is non-enumerable (infinite) and thus cannot be expanded for temporal-level
    // bounded quantifiers. TLC reports this as a "cannot handle formula" liveness error rather
    // than a generic "unsupported temporal expression".
    let seq_domain = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Seq".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::SetEnum(vec![spanned(Expr::Int(
            BigInt::from(1),
        ))]))],
    ));
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(seq_domain)),
        pattern: None,
    }];
    let body = spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(true)))));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    match conv.convert(&ctx, &expr) {
        Err(ref e @ ConvertError::CannotHandleFormula { ref reason, .. }) => {
            let msg = format!("{e}");
            assert!(
                msg.contains("bytes") && msg.contains("of module Test"),
                "expected TLC-shaped location in error, got: {msg}"
            );
            assert!(
                reason
                    .as_ref()
                    .is_some_and(|r| r.contains("iteration failed")),
                "expected reason to mention bounded-quantifier iteration failure, got: {:?}",
                reason
            );
            assert!(
                reason
                    .as_ref()
                    .is_some_and(|r| r.contains("Type error: expected Set")),
                "expected reason to preserve iterator error details, got: {:?}",
                reason
            );
        }
        Ok(_) => panic!("Expected CannotHandleFormula error, got Ok"),
        Err(other) => panic!("Expected CannotHandleFormula error, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_temporal_uses_bindings_not_substitution() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // Domain is a set of SETS where each element is represented lazily as Value::SetPred.
    // This is not reifiable to a pure Expr via value_to_expr (old substitution path).
    //
    // S == { {n \in Nat : n % 2 = 0}, {n \in Nat : n % 2 = 1} }
    //
    // Each element is an infinite set, so it should evaluate to Value::SetPred, which is
    // intentionally *not* supported by `value_to_expr` (the old substitution path).
    let inner_domain = spanned(Expr::Ident(
        "Nat".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let domain = spanned(Expr::SetEnum(vec![
        make_parity_filtered_set(&inner_domain, 0),
        make_parity_filtered_set(&inner_domain, 1),
    ]));

    // \E x \in S : [](y \in x)
    let bounds = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(domain.clone())),
        pattern: None,
    }];
    let body = spanned(Expr::Always(Box::new(spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    )))));
    let expr = spanned(Expr::Exists(bounds, Box::new(body)));

    // Sanity: domain eval yields a Set of SetPred elements.
    let domain_val = eval(&ctx, &domain).unwrap();
    let Some(mut it) = domain_val.iter_set() else {
        panic!("Expected enumerable domain");
    };
    let first = it.next().unwrap();
    assert!(matches!(first, Value::SetPred(_)));

    let live = conv.convert(&ctx, &expr).unwrap();
    let LiveExpr::Or(parts) = live else {
        panic!("Expected Or from temporal bounded quantifier expansion");
    };
    assert_eq!(parts.len(), 2);

    let mut saw_even = false;
    let mut saw_odd = false;

    for part in &parts {
        match analyze_temporal_binding_part(&ctx, part) {
            (true, false) => saw_even = true,
            (false, true) => saw_odd = true,
            other => panic!("Expected even/odd SetPred partition, got {other:?}"),
        }
    }

    assert!(saw_even);
    assert!(saw_odd);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_tuple_pattern_errors_on_non_tuple_element() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

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
            assert_eq!(actual_arity, None);
            assert!(matches!(actual_value_variant, "SmallInt" | "Int"));
        }
        other => panic!("Expected BoundTuplePatternMismatch, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bounded_quantifier_tuple_pattern_errors_on_wrong_arity_tuple() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

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
            assert_eq!(actual_arity, Some(3));
            assert_eq!(actual_value_variant, "Tuple");
        }
        other => panic!("Expected BoundTuplePatternMismatch, got {other:?}"),
    }
}
