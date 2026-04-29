// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SubstituteExpr tests: span policy, basic quantifier shadowing, and
//! binding form capture avoidance for Forall, Let, and multi-form tests.

use super::*;
use crate::span::FileId;

#[test]
fn test_substitute_expr_preserve_span_policy_uses_replacement_span() {
    let input = Spanned::new(
        Expr::Ident("x".to_string(), NameId::INVALID),
        Span::new(FileId(1), 10, 11),
    );
    let replacement = Spanned::new(Expr::Int(BigInt::from(99)), Span::new(FileId(2), 40, 44));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &replacement)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(input);
    assert_eq!(out.node, Expr::Int(BigInt::from(99)));
    assert_eq!(out.span, replacement.span);
}

#[test]
fn test_substitute_expr_dummy_span_policy_uses_dummy_span() {
    let input = Spanned::new(
        Expr::Ident("x".to_string(), NameId::INVALID),
        Span::new(FileId(1), 10, 11),
    );
    let replacement = Spanned::new(Expr::Int(BigInt::from(99)), Span::new(FileId(2), 40, 44));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &replacement)]),
        span_policy: SpanPolicy::Dummy,
    };

    let out = sub.fold_expr(input);
    assert_eq!(out.node, Expr::Int(BigInt::from(99)));
    assert_eq!(out.span, Span::dummy());
}

#[test]
fn test_substitute_expr_quantifier_shadows_body_but_not_domain() {
    let expr = spanned(Expr::Forall(
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
        Expr::Forall(bounds, body)
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
fn test_substitute_expr_forall_skips_capture_prone_replacement_in_body() {
    // \A y \in x : x with subs {x->y}
    // Domain should substitute (not bound), body should remain x to avoid capture.
    let expr = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("y".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        }],
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let repl = spanned(Expr::Ident("y".to_string(), NameId::INVALID));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Forall(bounds, body)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Ident(name, NameId::INVALID)) if name == "y"
            ) && matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));
}

#[test]
fn test_substitute_expr_forall_avoids_capture_with_unrelated_domain() {
    // \A y \in S : x with subs {x->y}
    // Body substitution must be skipped because replacement y would be captured.
    let expr = spanned(Expr::Forall(
        vec![BoundVar {
            name: spanned("y".to_string()),
            domain: Some(boxed_expr(Expr::Ident("S".to_string(), NameId::INVALID))),
            pattern: None,
        }],
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let repl = spanned(Expr::Ident("y".to_string(), NameId::INVALID));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Forall(bounds, body)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Ident(name, NameId::INVALID)) if name == "S"
            ) && matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));
}

#[test]
fn test_substitute_expr_binding_forms_skip_capture_prone_replacement() {
    let repl = spanned(Expr::Ident("y".to_string(), NameId::INVALID));

    let exists_expr = spanned(Expr::Exists(
        vec![BoundVar {
            name: spanned("y".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        }],
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };
    let exists_out = sub.fold_expr(exists_expr);
    assert!(matches!(
        exists_out.node,
        Expr::Exists(bounds, body)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Ident(name, NameId::INVALID)) if name == "y"
            ) && matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));

    let choose_expr = spanned(Expr::Choose(
        BoundVar {
            name: spanned("y".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        },
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };
    let choose_out = sub.fold_expr(choose_expr);
    assert!(matches!(
        choose_out.node,
        Expr::Choose(bound, body)
            if matches!(
                bound.domain.as_ref().map(|d| &d.node),
                Some(Expr::Ident(name, NameId::INVALID)) if name == "y"
            ) && matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));

    let set_builder_expr = spanned(Expr::SetBuilder(
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
        vec![BoundVar {
            name: spanned("y".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        }],
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };
    let set_builder_out = sub.fold_expr(set_builder_expr);
    assert!(matches!(
        set_builder_out.node,
        Expr::SetBuilder(body, bounds)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Ident(name, NameId::INVALID)) if name == "y"
            ) && matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));

    let set_filter_expr = spanned(Expr::SetFilter(
        BoundVar {
            name: spanned("y".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        },
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };
    let set_filter_out = sub.fold_expr(set_filter_expr);
    assert!(matches!(
        set_filter_out.node,
        Expr::SetFilter(bound, pred)
            if matches!(
                bound.domain.as_ref().map(|d| &d.node),
                Some(Expr::Ident(name, NameId::INVALID)) if name == "y"
            ) && matches!(&pred.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));

    let func_def_expr = spanned(Expr::FuncDef(
        vec![BoundVar {
            name: spanned("y".to_string()),
            domain: Some(boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID))),
            pattern: None,
        }],
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };
    let func_def_out = sub.fold_expr(func_def_expr);
    assert!(matches!(
        func_def_out.node,
        Expr::FuncDef(bounds, body)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Ident(name, NameId::INVALID)) if name == "y"
            ) && matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));

    let lambda_expr = spanned(Expr::Lambda(
        vec![spanned("y".to_string())],
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };
    let lambda_out = sub.fold_expr(lambda_expr);
    assert!(matches!(
        lambda_out.node,
        Expr::Lambda(_, body) if matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "x")
    ));
}

#[test]
fn test_substitute_expr_let_param_filter_preserves_param_capture_avoidance() {
    let expr = spanned(Expr::Let(
        vec![OperatorDef {
            name: spanned("Op".to_string()),
            params: vec![OpParam {
                name: spanned("p".to_string()),
                arity: 0,
            }],
            body: spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
    ));
    let repl = spanned(Expr::Ident("p".to_string(), NameId::INVALID));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    assert!(matches!(
        out.node,
        Expr::Let(defs, body)
            if matches!(&defs[0].body.node, Expr::Ident(name, NameId::INVALID) if name == "x")
                && matches!(&body.node, Expr::Ident(name, NameId::INVALID) if name == "p")
    ));
}

#[test]
fn test_substitute_expr_let_def_name_capture_avoidance_in_body() {
    // LET op == 5 IN x + op  with subs {x -> Ident("op")}
    let expr = spanned(Expr::Let(
        vec![OperatorDef {
            name: spanned("op".to_string()),
            params: vec![],
            body: spanned(Expr::Int(BigInt::from(5))),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::Apply(
            boxed_expr(Expr::Ident("+".to_string(), NameId::INVALID)),
            vec![
                spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
                spanned(Expr::Ident("op".to_string(), NameId::INVALID)),
            ],
        )),
    ));
    let repl = spanned(Expr::Ident("op".to_string(), NameId::INVALID));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    // Body must remain unchanged: x + op (sub dropped due to capture)
    assert!(matches!(
        &out.node,
        Expr::Let(defs, body)
            if matches!(&defs[0].body.node, Expr::Int(n) if n == &BigInt::from(5))
                && matches!(
                    &body.node,
                    Expr::Apply(_, args)
                        if matches!(&args[0].node, Expr::Ident(name, NameId::INVALID) if name == "x")
                            && matches!(&args[1].node, Expr::Ident(name, NameId::INVALID) if name == "op")
                )
    ));
}

#[test]
fn test_substitute_expr_let_def_name_no_capture_allows_substitution() {
    // LET op == 5 IN x + y  with subs {x -> Ident("z")}
    let expr = spanned(Expr::Let(
        vec![OperatorDef {
            name: spanned("op".to_string()),
            params: vec![],
            body: spanned(Expr::Int(BigInt::from(5))),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed_expr(Expr::Apply(
            boxed_expr(Expr::Ident("+".to_string(), NameId::INVALID)),
            vec![
                spanned(Expr::Ident("x".to_string(), NameId::INVALID)),
                spanned(Expr::Ident("y".to_string(), NameId::INVALID)),
            ],
        )),
    ));
    let repl = spanned(Expr::Ident("z".to_string(), NameId::INVALID));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &repl)]),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr);
    // Body should be substituted: z + y
    assert!(matches!(
        &out.node,
        Expr::Let(defs, body)
            if matches!(&defs[0].body.node, Expr::Int(n) if n == &BigInt::from(5))
                && matches!(
                    &body.node,
                    Expr::Apply(_, args)
                        if matches!(&args[0].node, Expr::Ident(name, NameId::INVALID) if name == "z")
                            && matches!(&args[1].node, Expr::Ident(name, NameId::INVALID) if name == "y")
                )
    ));
}

#[test]
fn test_substitute_expr_empty_subs_is_identity() {
    let expr = spanned(Expr::Add(
        boxed_expr(Expr::Ident("x".to_string(), NameId::INVALID)),
        boxed_expr(Expr::Int(BigInt::from(1))),
    ));
    let mut sub = SubstituteExpr {
        subs: HashMap::new(),
        span_policy: SpanPolicy::Preserve,
    };

    let out = sub.fold_expr(expr.clone());
    assert_eq!(out.node, expr.node);
}
