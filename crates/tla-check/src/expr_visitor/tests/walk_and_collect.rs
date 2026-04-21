// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache-2.0.

//! Tests for AST walk coverage (If/Case/Record/Except/SetBuilder/Lambda),
//! collect_bound_names_v, and single_bound_var_names.

use super::*;

#[test]
fn test_collect_bound_names() {
    let expr = Expr::Let(
        vec![OperatorDef {
            name: sp_str("op1"),
            params: vec![],
            body: sp(Expr::Forall(
                vec![BoundVar {
                    name: sp_str("x"),
                    domain: None,
                    pattern: None,
                }],
                boxed(Expr::Bool(true)),
            )),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed(Expr::Exists(
            vec![BoundVar {
                name: sp_str("y"),
                domain: None,
                pattern: None,
            }],
            boxed(Expr::Bool(true)),
        )),
    );
    let names = collect_bound_names_v(&expr);
    assert!(names.contains("op1"));
    assert!(names.contains("x"));
    assert!(names.contains("y"));
}

#[test]
fn test_walk_if_then_else() {
    let expr = Expr::If(
        boxed(Expr::Bool(true)),
        boxed(Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_walk_case() {
    let expr = Expr::Case(
        vec![CaseArm {
            guard: sp(Expr::Bool(true)),
            body: sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )))),
        }],
        Some(boxed(Expr::Ident(
            "default".into(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_walk_record() {
    let expr = Expr::Record(vec![(
        sp_str("field"),
        sp(Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    )]);
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_walk_except() {
    let expr = Expr::Except(
        boxed(Expr::Ident(
            "f".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        vec![tla_core::ast::ExceptSpec {
            path: vec![ExceptPathElement::Index(sp(Expr::Int(BigInt::from(1))))],
            value: sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )))),
        }],
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_walk_set_builder() {
    let expr = Expr::SetBuilder(
        boxed(Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        vec![BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "S".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        }],
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_walk_lambda() {
    let expr = Expr::Lambda(
        vec![sp_str("x")],
        boxed(Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    );
    assert!(expr_contains_prime_v(&expr));
}

#[test]
fn test_bound_var_names_with_pattern() {
    let bv = BoundVar {
        name: sp_str("_tuple"),
        domain: None,
        pattern: Some(BoundPattern::Tuple(vec![sp_str("a"), sp_str("b")])),
    };
    let names = single_bound_var_names(&bv);
    assert_eq!(names, vec!["a".to_string(), "b".to_string()]);
}

#[test]
fn test_bound_var_names_simple() {
    let bv = BoundVar {
        name: sp_str("x"),
        domain: None,
        pattern: None,
    };
    let names = single_bound_var_names(&bv);
    assert_eq!(names, vec!["x".to_string()]);
}
