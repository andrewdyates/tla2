// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-binding-form shadowing tests for SubstituteExpr: Exists, Choose,
//! SetBuilder, SetFilter, FuncDef. Also tests DummyAll span policy.

use super::*;
use crate::span::FileId;

#[test]
fn test_substitute_expr_exists_shadows_body_but_not_domain() {
    // \E x \in x : x = y with subs {x->1, y->2}
    // Domain x should become 1, body x should stay (shadowed), body y becomes 2.
    let expr = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("x".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        }],
        boxed_expr(Expr::Eq(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
        )),
    ));
    let repl_x = spanned(Expr::Int(BigInt::from(1)));
    let repl_y = spanned(Expr::Int(BigInt::from(2)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl_x), ("y", &repl_y)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Exists(bounds, body)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Int(n)) if n == &BigInt::from(1)
            ) && matches!(
                &body.node,
                Expr::Eq(left, right)
                    if matches!(&left.node, Expr::Ident(name, NameId::INVALID) if name == "x")
                        && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(2))
            )
    ));
}

#[test]
fn test_substitute_expr_choose_shadows_body_but_not_domain() {
    // CHOOSE x \in x : x = y with subs {x->1, y->2}
    let expr = spanned(Expr::Choose(
        BoundVar {
            name: spanned("x".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        },
        boxed_expr(Expr::Eq(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
        )),
    ));
    let repl_x = spanned(Expr::Int(BigInt::from(1)));
    let repl_y = spanned(Expr::Int(BigInt::from(2)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl_x), ("y", &repl_y)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Choose(bound, body)
            if matches!(
                bound.domain.as_ref().map(|d| &d.node),
                Some(Expr::Int(n)) if n == &BigInt::from(1)
            ) && matches!(
                &body.node,
                Expr::Eq(left, right)
                    if matches!(&left.node, Expr::Ident(name, NameId::INVALID) if name == "x")
                        && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(2))
            )
    ));
}

#[test]
fn test_substitute_expr_choose_allows_lambda_without_free_bound_var_capture() {
    // CHOOSE pc \in S : P(pc) with subs {P -> LAMBDA pc : x \in pc}
    let expr = spanned(Expr::Choose(
        BoundVar {
            name: spanned("pc".to_string()),
            domain: Some(boxed_expr(Expr::Ident("S".to_string(), NameId::INVALID))),
            pattern: None,
        },
        boxed_expr(Expr::Apply(
            boxed_expr(Expr::Ident("P".to_string(), NameId::INVALID)),
            vec![spanned(Expr::Ident("pc".to_string(), NameId::INVALID))],
        )),
    ));
    let repl_p = spanned(Expr::Lambda(
        vec![spanned("pc".to_string())],
        boxed_expr(Expr::In(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("pc".to_string(), NameId::INVALID)),
        )),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("P", &repl_p)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Choose(_, body)
            if matches!(
                &body.node,
                Expr::Apply(op, args)
                    if args.len() == 1
                        && matches!(&args[0].node, Expr::Ident(name, NameId::INVALID) if name == "pc")
                        && matches!(&op.node, Expr::Lambda(params, _)
                            if params.len() == 1 && params[0].node == "pc")
            )
    ));
}

#[test]
fn test_substitute_expr_choose_blocks_lambda_with_free_bound_var_capture() {
    // CHOOSE pc \in S : P(pc) with subs {P -> LAMBDA q : pc \in q}
    // Here `pc` is free in the replacement lambda and would be captured.
    let expr = spanned(Expr::Choose(
        BoundVar {
            name: spanned("pc".to_string()),
            domain: Some(boxed_expr(Expr::Ident("S".to_string(), NameId::INVALID))),
            pattern: None,
        },
        boxed_expr(Expr::Apply(
            boxed_expr(Expr::Ident("P".to_string(), NameId::INVALID)),
            vec![spanned(Expr::Ident("pc".to_string(), NameId::INVALID))],
        )),
    ));
    let repl_p = spanned(Expr::Lambda(
        vec![spanned("q".to_string())],
        boxed_expr(Expr::In(
            boxed_expr(Expr::Ident("pc".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("q".to_string(), NameId::INVALID)),
        )),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("P", &repl_p)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Choose(_, body)
            if matches!(
                &body.node,
                Expr::Apply(op, args)
                    if args.len() == 1
                        && matches!(&args[0].node, Expr::Ident(name, NameId::INVALID) if name == "pc")
                        && matches!(&op.node, Expr::Ident(name, NameId::INVALID) if name == "P")
            )
    ));
}

#[test]
fn test_substitute_expr_set_builder_shadows_body_but_not_domain() {
    // {x + y : x \in x} with subs {x->1, y->2}
    let expr = spanned(Expr::SetBuilder(
        boxed_expr(Expr::Add(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
        )),
        vec![BoundVar {
            name: spanned("x".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        }],
    ));
    let repl_x = spanned(Expr::Int(BigInt::from(1)));
    let repl_y = spanned(Expr::Int(BigInt::from(2)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl_x), ("y", &repl_y)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::SetBuilder(body, bounds)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Int(n)) if n == &BigInt::from(1)
            ) && matches!(
                &body.node,
                Expr::Add(left, right)
                    if matches!(&left.node, Expr::Ident(name, NameId::INVALID) if name == "x")
                        && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(2))
            )
    ));
}

#[test]
fn test_substitute_expr_set_filter_shadows_pred_but_not_domain() {
    // {x \in x : x = y} with subs {x->1, y->2}
    let expr = spanned(Expr::SetFilter(
        BoundVar {
            name: spanned("x".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        },
        boxed_expr(Expr::Eq(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
        )),
    ));
    let repl_x = spanned(Expr::Int(BigInt::from(1)));
    let repl_y = spanned(Expr::Int(BigInt::from(2)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl_x), ("y", &repl_y)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::SetFilter(bound, pred)
            if matches!(
                bound.domain.as_ref().map(|d| &d.node),
                Some(Expr::Int(n)) if n == &BigInt::from(1)
            ) && matches!(
                &pred.node,
                Expr::Eq(left, right)
                    if matches!(&left.node, Expr::Ident(name, NameId::INVALID) if name == "x")
                        && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(2))
            )
    ));
}

#[test]
fn test_substitute_expr_func_def_shadows_body_but_not_domain() {
    // [x \in x |-> x + y] with subs {x->1, y->2}
    let expr = spanned(Expr::FuncDef(
        vec![BoundVar {
            name: spanned("x".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        }],
        boxed_expr(Expr::Add(
            boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
            boxed_expr(Expr::Ident("y".to_string(), NameId::INVALID)),
        )),
    ));
    let repl_x = spanned(Expr::Int(BigInt::from(1)));
    let repl_y = spanned(Expr::Int(BigInt::from(2)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl_x), ("y", &repl_y)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::FuncDef(bounds, body)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Int(n)) if n == &BigInt::from(1)
            ) && matches!(
                &body.node,
                Expr::Add(left, right)
                    if matches!(&left.node, Expr::Ident(name, NameId::INVALID) if name == "x")
                        && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(2))
            )
    ));
}

#[test]
fn test_substitute_expr_dummy_all_span_policy() {
    // DummyAll should make ALL output spans dummy, not just substituted nodes.
    let real_span = Span {
        start: 10,
        end: 20,
        file: FileId(1),
    };
    let input = Spanned {
        node: Expr::Add(
            Box::new(Spanned {
                node: Expr::Ident("x".to_string(), NameId::INVALID),
                span: real_span,
            }),
            Box::new(Spanned {
                node: Expr::Int(BigInt::from(1)),
                span: real_span,
            }),
        ),
        span: real_span,
    };
    let repl = spanned(Expr::Int(BigInt::from(42)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::DummyAll,
    };

    let out = sub.fold_expr(input);
    // Outer span should be dummy
    assert_eq!(out.span, Span::dummy());
    // Inner non-substituted node (Int(1)) should also have dummy span
    if let Expr::Add(_, right) = &out.node {
        assert_eq!(right.span, Span::dummy());
    } else {
        panic!("expected Add");
    }
}
