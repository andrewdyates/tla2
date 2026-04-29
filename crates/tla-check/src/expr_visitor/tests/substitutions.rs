// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Dropbox Apache-2.0.

//! Tests for collect_conjuncts_v and apply_substitutions_v.

use super::*;

#[test]
fn test_collect_conjuncts_v_flattens_and_preserves_order() {
    let expr = sp(Expr::And(
        boxed(Expr::And(
            boxed(Expr::Ident(
                "a".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
            boxed(Expr::Ident(
                "b".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
        )),
        boxed(Expr::And(
            boxed(Expr::Ident(
                "c".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
            boxed(Expr::Bool(true)),
        )),
    ));

    let conjuncts = collect_conjuncts_v(&expr);
    assert_eq!(conjuncts.len(), 4);
    assert!(matches!(&conjuncts[0].node, Expr::Ident(n, _) if n == "a"));
    assert!(matches!(&conjuncts[1].node, Expr::Ident(n, _) if n == "b"));
    assert!(matches!(&conjuncts[2].node, Expr::Ident(n, _) if n == "c"));
    assert!(matches!(&conjuncts[3].node, Expr::Bool(true)));
}

#[test]
fn test_collect_conjuncts_v_keeps_non_and_subtrees_intact() {
    let expr = sp(Expr::And(
        boxed(Expr::Ident(
            "lhs".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Or(
            boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
            boxed(Expr::Ident(
                "y".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
        )),
    ));

    let conjuncts = collect_conjuncts_v(&expr);
    assert_eq!(conjuncts.len(), 2);
    assert!(matches!(&conjuncts[0].node, Expr::Ident(n, _) if n == "lhs"));
    assert!(matches!(
        &conjuncts[1].node,
        Expr::Or(left, right)
            if matches!(&left.node, Expr::Ident(n, _) if n == "x")
                && matches!(&right.node, Expr::Ident(n, _) if n == "y")
    ));
}

#[test]
fn test_apply_substitutions_v_replaces_free_identifiers() {
    let expr = sp(Expr::And(
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    ));
    let subs = vec![Substitution {
        from: sp_str("x"),
        to: sp(Expr::Int(BigInt::from(1))),
    }];

    let out = apply_substitutions_v(&expr, &subs);
    assert!(matches!(
        &out.node,
        Expr::And(left, right)
            if matches!(&left.node, Expr::Int(n) if n == &BigInt::from(1))
                && matches!(&right.node, Expr::Ident(n, _) if n == "y")
    ));
}

#[test]
fn test_apply_substitutions_v_preserves_bound_names_in_quantifier_body() {
    let expr = sp(Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            pattern: None,
            domain: None,
        }],
        boxed(Expr::Eq(
            boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
            boxed(Expr::Ident(
                "y".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
        )),
    ));
    let subs = vec![
        Substitution {
            from: sp_str("x"),
            to: sp(Expr::Int(BigInt::from(1))),
        },
        Substitution {
            from: sp_str("y"),
            to: sp(Expr::Int(BigInt::from(2))),
        },
    ];

    let out = apply_substitutions_v(&expr, &subs);
    assert!(matches!(
        &out.node,
        Expr::Forall(_, body)
            if matches!(
                &body.node,
                Expr::Eq(left, right)
                    if matches!(&left.node, Expr::Ident(n, _) if n == "x")
                        && matches!(&right.node, Expr::Int(n) if n == &BigInt::from(2))
            )
    ));
}

#[test]
fn test_apply_substitutions_v_substitutes_quantifier_domains_with_unfiltered_subs() {
    let expr = sp(Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            pattern: None,
            domain: Some(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        }],
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    ));
    let subs = vec![Substitution {
        from: sp_str("x"),
        to: sp(Expr::Int(BigInt::from(7))),
    }];

    let out = apply_substitutions_v(&expr, &subs);
    assert!(matches!(
        &out.node,
        Expr::Forall(bounds, body)
            if matches!(
                bounds[0].domain.as_ref().map(|d| &d.node),
                Some(Expr::Int(n)) if n == &BigInt::from(7)
            ) && matches!(&body.node, Expr::Ident(name, _) if name == "x")
    ));
}

#[test]
fn test_apply_substitutions_v_let_param_filter_avoids_capture() {
    let expr = sp(Expr::Let(
        vec![OperatorDef {
            name: sp_str("Op"),
            params: vec![tla_core::ast::OpParam {
                name: sp_str("p"),
                arity: 0,
            }],
            body: sp(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    ));
    let subs = vec![Substitution {
        from: sp_str("x"),
        to: sp(Expr::Ident(
            "p".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }];

    let out = apply_substitutions_v(&expr, &subs);
    assert!(matches!(
        &out.node,
        Expr::Let(defs, body)
            if matches!(&defs[0].body.node, Expr::Ident(name, _) if name == "x")
                && matches!(&body.node, Expr::Ident(name, _) if name == "p")
    ));
}

#[test]
fn test_apply_substitutions_v_preserves_replacement_span() {
    let expr = Spanned::new(
        Expr::Ident("x".into(), tla_core::name_intern::NameId::INVALID),
        tla_core::span::Span::new(tla_core::span::FileId(1), 1, 2),
    );
    let replacement = Spanned::new(
        Expr::Int(BigInt::from(17)),
        tla_core::span::Span::new(tla_core::span::FileId(2), 20, 22),
    );
    let subs = vec![Substitution {
        from: sp_str("x"),
        to: replacement.clone(),
    }];

    let out = apply_substitutions_v(&expr, &subs);
    assert_eq!(out.node, Expr::Int(BigInt::from(17)));
    assert_eq!(out.span, replacement.span);
}
