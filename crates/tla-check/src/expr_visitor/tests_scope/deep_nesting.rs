// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.

//! F4: Deeply nested multi-binding structure tests (#1213).

use super::*;

#[test]
fn test_deeply_nested_multi_binding_scope_tracking_let() {
    let let_expr = build_deeply_nested_let();

    let mut visitor = ScopeTrackingVisitor::new();
    walk_expr(&mut visitor, &let_expr);

    assert_eq!(visitor.depth, 0, "scope depth not balanced after walk");
    assert_eq!(visitor.max_depth, 4, "expected 4 nested scopes");
    assert_eq!(visitor.events.len(), 8, "expected 8 scope events");
}

#[test]
fn test_deeply_nested_multi_binding_scope_tracking_events() {
    let let_expr = build_deeply_nested_let();

    let mut visitor = ScopeTrackingVisitor::new();
    walk_expr(&mut visitor, &let_expr);

    assert_eq!(
        visitor.events[0],
        (
            "enter".to_string(),
            vec!["op_a".to_string(), "op_b".to_string()]
        )
    );
    assert_eq!(
        visitor.events[1],
        ("enter".to_string(), vec!["x".to_string(), "y".to_string()])
    );
    assert_eq!(
        visitor.events[2],
        ("enter".to_string(), vec!["z".to_string()])
    );
    assert_eq!(
        visitor.events[3],
        ("enter".to_string(), vec!["w".to_string()])
    );
    assert_eq!(
        visitor.events[4],
        ("exit".to_string(), vec!["w".to_string()])
    );
    assert_eq!(
        visitor.events[5],
        ("exit".to_string(), vec!["z".to_string()])
    );
    assert_eq!(
        visitor.events[6],
        ("exit".to_string(), vec!["x".to_string(), "y".to_string()])
    );
    assert_eq!(
        visitor.events[7],
        (
            "exit".to_string(),
            vec!["op_a".to_string(), "op_b".to_string()]
        )
    );
}

/// Build the deeply nested Let > Forall > SetBuilder > Lambda expression
/// used by the F4 scope tracking tests.
fn build_deeply_nested_let() -> Expr {
    let lambda_body = Expr::Lambda(vec![sp_str("w")], boxed(Expr::Bool(true)));
    let set_builder = Expr::SetBuilder(
        boxed(lambda_body),
        vec![BoundVar {
            name: sp_str("z"),
            domain: Some(boxed(Expr::Ident(
                "T".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        }],
    );
    let forall = Expr::Forall(
        vec![
            BoundVar {
                name: sp_str("x"),
                domain: Some(boxed(Expr::Ident(
                    "S".into(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                pattern: None,
            },
            BoundVar {
                name: sp_str("y"),
                domain: Some(boxed(Expr::Ident(
                    "S".into(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                pattern: None,
            },
        ],
        boxed(set_builder),
    );
    Expr::Let(
        vec![
            OperatorDef {
                name: sp_str("op_a"),
                params: vec![],
                body: sp(Expr::Int(BigInt::from(1))),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            },
            OperatorDef {
                name: sp_str("op_b"),
                params: vec![],
                body: sp(Expr::Int(BigInt::from(2))),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            },
        ],
        boxed(forall),
    )
}
