// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_bool_constant() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    let expr = spanned(Expr::Bool(true));
    let live = conv.convert(&ctx, &expr).unwrap();
    assert!(matches!(live, LiveExpr::Bool(true)));

    let expr = spanned(Expr::Bool(false));
    let live = conv.convert(&ctx, &expr).unwrap();
    assert!(matches!(live, LiveExpr::Bool(false)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_always() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // []TRUE
    let expr = spanned(Expr::Always(Box::new(spanned(Expr::Bool(true)))));
    let live = conv.convert(&ctx, &expr).unwrap();

    match live {
        LiveExpr::Always(inner) => {
            assert!(matches!(*inner, LiveExpr::Bool(true)));
        }
        _ => panic!("Expected Always"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_eventually() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // <>TRUE
    let expr = spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(true)))));
    let live = conv.convert(&ctx, &expr).unwrap();

    match live {
        LiveExpr::Eventually(inner) => {
            assert!(matches!(*inner, LiveExpr::Bool(true)));
        }
        _ => panic!("Expected Eventually"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_leads_to() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // P ~> Q expands to [](~P \/ <>Q)
    let expr = spanned(Expr::LeadsTo(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(false))),
    ));
    let live = conv.convert(&ctx, &expr).unwrap();

    // [](~TRUE \/ <>FALSE) = [](FALSE \/ <>FALSE).
    // or() filters Bool(false), yielding [](<>FALSE).
    match live {
        LiveExpr::Always(inner) => match *inner {
            LiveExpr::Eventually(inner_ev) => {
                assert!(
                    matches!(*inner_ev, LiveExpr::Bool(false)),
                    "Expected Eventually(Bool(false)), got: Eventually({:?})",
                    inner_ev,
                );
            }
            _ => panic!("Expected Eventually inside Always, got: {:?}", inner),
        },
        _ => panic!("Expected Always"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_conjunction() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // []P /\ <>Q
    let expr = spanned(Expr::And(
        Box::new(spanned(Expr::Always(Box::new(spanned(Expr::Bool(true)))))),
        Box::new(spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(
            false,
        )))))),
    ));
    let live = conv.convert(&ctx, &expr).unwrap();

    match live {
        LiveExpr::And(parts) => {
            assert_eq!(parts.len(), 2);
            assert!(matches!(parts[0], LiveExpr::Always(_)));
            assert!(matches!(parts[1], LiveExpr::Eventually(_)));
        }
        _ => panic!("Expected And"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_implication() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // []P => <>Q expands to ~[]P \/ <>Q
    let expr = spanned(Expr::Implies(
        Box::new(spanned(Expr::Always(Box::new(spanned(Expr::Bool(true)))))),
        Box::new(spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(
            false,
        )))))),
    ));
    let live = conv.convert(&ctx, &expr).unwrap();

    match live {
        LiveExpr::Or(parts) => {
            assert_eq!(parts.len(), 2);
            // First part is ~[]P
            assert!(matches!(parts[0], LiveExpr::Not(_)));
            // Second part is <>Q
            assert!(matches!(parts[1], LiveExpr::Eventually(_)));
        }
        _ => panic!("Expected Or"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_negation_in_temporal() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // ~<>P
    let expr = spanned(Expr::Not(Box::new(spanned(Expr::Eventually(Box::new(
        spanned(Expr::Bool(true)),
    ))))));
    let live = conv.convert(&ctx, &expr).unwrap();

    match &live {
        LiveExpr::Not(inner) => {
            assert!(matches!(inner.as_ref(), LiveExpr::Eventually(_)));
        }
        _ => panic!("Expected Not"),
    }

    // After push_negation: ~<>P becomes []~P
    let normalized = live.push_negation();
    match normalized {
        LiveExpr::Always(inner) => {
            // ~TRUE = FALSE
            assert!(matches!(*inner, LiveExpr::Bool(false)));
        }
        _ => panic!("Expected Always after push_negation"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_disjunction() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // []P \/ <>Q
    let expr = spanned(Expr::Or(
        Box::new(spanned(Expr::Always(Box::new(spanned(Expr::Bool(true)))))),
        Box::new(spanned(Expr::Eventually(Box::new(spanned(Expr::Bool(
            false,
        )))))),
    ));
    let live = conv.convert(&ctx, &expr).unwrap();

    match live {
        LiveExpr::Or(parts) => {
            assert_eq!(parts.len(), 2);
            assert!(matches!(parts[0], LiveExpr::Always(_)));
            assert!(matches!(parts[1], LiveExpr::Eventually(_)));
        }
        _ => panic!("Expected Or"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_convert_nested_always_eventually() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // []<>P (always eventually P)
    let expr = spanned(Expr::Always(Box::new(spanned(Expr::Eventually(Box::new(
        spanned(Expr::Bool(true)),
    ))))));
    let live = conv.convert(&ctx, &expr).unwrap();

    match live {
        LiveExpr::Always(inner) => match *inner {
            LiveExpr::Eventually(innermost) => {
                assert!(matches!(*innermost, LiveExpr::Bool(true)));
            }
            _ => panic!("Expected Eventually inside Always"),
        },
        _ => panic!("Expected Always"),
    }
}
