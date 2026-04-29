// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Dropbox Apache-2.0.

//! Tests for basic containment visitors: expr_contains_prime_v, expr_contains_any_prime_v,
//! expr_contains_ident_v, expr_contains_exists_v, and ModuleRef traversal.

use super::*;

#[test]
fn test_contains_prime_basic() {
    let expr = Expr::Prime(boxed(Expr::Ident(
        "x".into(),
        tla_core::name_intern::NameId::INVALID,
    )));
    assert!(expr_contains_prime_v(&expr));
    assert!(expr_contains_any_prime_v(&expr));
}

#[test]
fn test_contains_prime_unchanged() {
    let expr = Expr::Unchanged(boxed(Expr::Ident(
        "x".into(),
        tla_core::name_intern::NameId::INVALID,
    )));
    assert!(expr_contains_prime_v(&expr));
    assert!(!expr_contains_any_prime_v(&expr));
}

#[test]
fn test_contains_prime_nested() {
    let expr = Expr::And(
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Prime(boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_contains_prime_none() {
    let expr = Expr::And(
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    assert!(!expr_contains_prime_v(&expr));
}

#[test]
fn test_contains_ident() {
    let expr = Expr::And(
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    assert!(expr_contains_ident_v(&expr, "x"));
    assert!(expr_contains_ident_v(&expr, "y"));
    assert!(!expr_contains_ident_v(&expr, "z"));
}

#[test]
fn test_contains_ident_in_bound_var() {
    let expr = Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            domain: None,
            pattern: None,
        }],
        boxed(Expr::Bool(true)),
    );
    assert!(expr_contains_ident_v(&expr, "x"));
    assert!(!expr_contains_ident_v(&expr, "z"));
}

#[test]
fn test_contains_prime_in_parameterized_module_target() {
    let expr = Expr::ModuleRef(
        ModuleTarget::Parameterized(
            "IS".to_string(),
            vec![sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            ))))],
        ),
        "Op".to_string(),
        vec![],
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_contains_prime_in_chained_module_target() {
    let inner_module_ref = Expr::ModuleRef(
        ModuleTarget::Named("A".to_string()),
        "B".to_string(),
        vec![sp(Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        ))))],
    );
    let expr = Expr::ModuleRef(
        ModuleTarget::Chained(Box::new(sp(inner_module_ref))),
        "C".to_string(),
        vec![],
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_contains_ident_in_parameterized_module_target() {
    let expr = Expr::ModuleRef(
        ModuleTarget::Parameterized(
            "IS".to_string(),
            vec![sp(Expr::Ident(
                "y".into(),
                tla_core::name_intern::NameId::INVALID,
            ))],
        ),
        "Op".to_string(),
        vec![],
    );
    assert!(expr_contains_ident_v(&expr, "y"));
    assert!(!expr_contains_ident_v(&expr, "z"));
}

#[test]
fn test_contains_ident_in_chained_module_target() {
    let inner_module_ref = Expr::ModuleRef(
        ModuleTarget::Named("A".to_string()),
        "B".to_string(),
        vec![sp(Expr::Ident(
            "target_var".into(),
            tla_core::name_intern::NameId::INVALID,
        ))],
    );
    let expr = Expr::ModuleRef(
        ModuleTarget::Chained(Box::new(sp(inner_module_ref))),
        "C".to_string(),
        vec![],
    );
    assert!(expr_contains_ident_v(&expr, "target_var"));
    assert!(!expr_contains_ident_v(&expr, "other"));
}

#[test]
fn test_module_ref_named_target_no_false_positive() {
    let expr = Expr::ModuleRef(
        ModuleTarget::Named("M".to_string()),
        "Op".to_string(),
        vec![sp(Expr::Ident(
            "arg".into(),
            tla_core::name_intern::NameId::INVALID,
        ))],
    );
    assert!(expr_contains_ident_v(&expr, "arg"));
    assert!(!expr_contains_ident_v(&expr, "M"));
    assert!(!expr_contains_prime_v(&expr));
}

#[test]
fn test_contains_prime_in_parameterized_args_and_target() {
    let expr = Expr::ModuleRef(
        ModuleTarget::Parameterized(
            "IS".to_string(),
            vec![sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            ))))],
        ),
        "Op".to_string(),
        vec![sp(Expr::Prime(boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        ))))],
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_contains_exists() {
    let expr = Expr::And(
        boxed(Expr::Exists(
            vec![BoundVar {
                name: sp_str("x"),
                domain: None,
                pattern: None,
            }],
            boxed(Expr::Bool(true)),
        )),
        boxed(Expr::Bool(false)),
    );
    assert!(expr_contains_exists_v(&expr));
}

#[test]
fn test_contains_exists_none() {
    let expr = Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            domain: None,
            pattern: None,
        }],
        boxed(Expr::Bool(true)),
    );
    assert!(!expr_contains_exists_v(&expr));
}
