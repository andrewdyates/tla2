// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.

//! Tests for instance substitution handling, primed parameter shadowing,
//! free variable detection, and guard expression classification.

use super::*;

#[test]
fn test_expr_has_any_prime_legacy_ignores_instance_substitutions() {
    let expr = Expr::InstanceExpr(
        "M".to_string(),
        vec![Substitution {
            from: sp_str("x"),
            to: sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )))),
        }],
    );
    assert!(!expr_has_any_prime_legacy_v(&expr));
}

#[test]
fn test_expr_contains_primed_param_shadowed_forall_body() {
    let expr = Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            domain: None,
            pattern: None,
        }],
        boxed(Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    );
    assert!(!expr_contains_primed_param_v(&expr, "x"));
}

#[test]
fn test_expr_contains_primed_param_shadowed_forall_domain_is_still_checked() {
    let expr = Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            ))))),
            pattern: None,
        }],
        boxed(Expr::Bool(true)),
    );
    assert!(expr_contains_primed_param_v(&expr, "x"));
}

#[test]
fn test_expr_contains_primed_param_ignores_instance_substitutions() {
    let expr = Expr::InstanceExpr(
        "M".to_string(),
        vec![Substitution {
            from: sp_str("x"),
            to: sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )))),
        }],
    );
    assert!(!expr_contains_primed_param_v(&expr, "x"));
}

#[test]
fn test_expr_contains_primed_param_detects_statevar() {
    let expr = Expr::Prime(boxed(Expr::StateVar(
        "x".into(),
        0,
        tla_core::name_intern::NameId::INVALID,
    )));
    assert!(expr_contains_primed_param_v(&expr, "x"));
}

#[test]
fn test_expr_contains_primed_param_shadowed_forall_domain_detects_statevar() {
    let expr = Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Prime(boxed(Expr::StateVar(
                "x".into(),
                0,
                tla_core::name_intern::NameId::INVALID,
            ))))),
            pattern: None,
        }],
        boxed(Expr::Bool(true)),
    );
    assert!(expr_contains_primed_param_v(&expr, "x"));
}

#[test]
fn test_expr_has_free_var_in_set_preserves_conservative_binding_behavior() {
    let vars: HashSet<&str> = HashSet::new();
    let expr = Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            domain: None,
            pattern: None,
        }],
        boxed(Expr::Bool(true)),
    );
    assert!(expr_has_free_var_in_set_v(&expr, &vars));
}

#[test]
fn test_expr_has_free_var_in_set_ignores_instance_substitutions() {
    let vars: HashSet<&str> = HashSet::from(["x"]);
    let expr = Expr::InstanceExpr(
        "M".to_string(),
        vec![Substitution {
            from: sp_str("x"),
            to: sp(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
        }],
    );
    assert!(!expr_has_free_var_in_set_v(&expr, &vars));
}

#[test]
fn test_expr_contains_prime_not_assignment_ignores_instance_substitutions() {
    let expr = Expr::InstanceExpr(
        "M".to_string(),
        vec![Substitution {
            from: sp_str("x"),
            to: sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )))),
        }],
    );
    assert!(!expr_contains_prime_not_assignment_v(&expr));
}

#[test]
fn test_is_guard_expression_let_checks_only_body() {
    let expr = Expr::Let(
        vec![OperatorDef {
            name: sp_str("Def"),
            params: vec![],
            body: sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )))),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed(Expr::Bool(true)),
    );
    assert!(is_guard_expression_v(&expr));
}
