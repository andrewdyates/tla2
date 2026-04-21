// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_if_then_else_temporal() {
    // IF TRUE THEN []P ELSE <>Q where P and Q are boolean constants
    // Should produce: (TRUE /\ []P) \/ (~TRUE /\ <>Q)
    let conv = AstToLive::new();
    let ctx = make_ctx();

    let expr = spanned(Expr::If(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Always(Box::new(spanned(Expr::Bool(true)))))),
        Box::new(spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(
            false,
        )))))),
    ));
    let live = conv.convert(&ctx, &expr).unwrap();

    // and([TRUE, []TRUE]) -> []TRUE; and([FALSE, <>FALSE]) -> FALSE;
    // or([[]TRUE, FALSE]) -> []TRUE. Result: Always(Bool(true)).
    match live {
        LiveExpr::Always(inner) => {
            assert!(
                matches!(*inner, LiveExpr::Bool(true)),
                "Expected Always(Bool(true)), got: Always({:?})",
                inner,
            );
        }
        _ => panic!(
            "Expected Always(Bool(true)) for IF TRUE THEN []TRUE ELSE <>FALSE, got: {:?}",
            live
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_case_temporal() {
    // CASE TRUE -> []TRUE [] OTHER -> <>FALSE
    // Should produce: (TRUE /\ []TRUE) \/ <>FALSE
    let conv = AstToLive::new();
    let ctx = make_ctx();

    let expr = spanned(Expr::Case(
        vec![CaseArm {
            guard: spanned(Expr::Bool(true)),
            body: spanned(Expr::Always(Box::new(spanned(Expr::Bool(true))))),
        }],
        Some(Box::new(spanned(Expr::Eventually(Box::new(spanned(
            Expr::Bool(false),
        )))))),
    ));
    let live = conv.convert(&ctx, &expr).unwrap();

    // and([TRUE, []TRUE]) -> []TRUE (no further simplification with <>FALSE).
    match live {
        LiveExpr::Or(parts) => {
            assert_eq!(parts.len(), 2);
            assert!(
                matches!(&parts[0], LiveExpr::Always(inner) if matches!(**inner, LiveExpr::Bool(true))),
                "Expected Always(Bool(true)) for case arm, got: {:?}",
                parts[0],
            );
            assert!(
                matches!(parts[1], LiveExpr::Eventually(_)),
                "Expected Eventually for OTHER clause, got: {:?}",
                parts[1]
            );
        }
        _ => panic!("Expected Or for CASE, got: {:?}", live),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_case_temporal_multiple_arms() {
    // CASE TRUE -> []TRUE [] FALSE -> <>FALSE
    // (no OTHER clause)
    // Should produce: (TRUE /\ []TRUE) \/ (FALSE /\ <>FALSE)
    let conv = AstToLive::new();
    let ctx = make_ctx();

    let expr = spanned(Expr::Case(
        vec![
            CaseArm {
                guard: spanned(Expr::Bool(true)),
                body: spanned(Expr::Always(Box::new(spanned(Expr::Bool(true))))),
            },
            CaseArm {
                guard: spanned(Expr::Bool(false)),
                body: spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(false))))),
            },
        ],
        None,
    ));
    let live = conv.convert(&ctx, &expr).unwrap();

    // and([TRUE, []TRUE]) -> []TRUE; and([FALSE, <>FALSE]) -> FALSE;
    // or([[]TRUE, FALSE]) -> []TRUE. Result: Always(Bool(true)).
    match live {
        LiveExpr::Always(inner) => {
            assert!(
                matches!(*inner, LiveExpr::Bool(true)),
                "Expected Always(Bool(true)), got: Always({:?})",
                inner,
            );
        }
        _ => panic!("Expected Always(Bool(true)) for CASE, got: {:?}", live),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_case_non_temporal_becomes_predicate() {
    // CASE TRUE -> TRUE [] OTHER -> FALSE
    // All constant-level; should fold to a boolean via predicate_by_level,
    // not enter temporal conversion.
    let conv = AstToLive::new();
    let ctx = make_ctx();

    let expr = spanned(Expr::Case(
        vec![CaseArm {
            guard: spanned(Expr::Bool(true)),
            body: spanned(Expr::Bool(true)),
        }],
        Some(Box::new(spanned(Expr::Bool(false)))),
    ));
    let live = conv.convert(&ctx, &expr).unwrap();
    // Constant-level CASE should be evaluated to a boolean
    assert!(
        matches!(live, LiveExpr::Bool(true)),
        "Expected Bool(true) for constant CASE, got: {:?}",
        live
    );
}
