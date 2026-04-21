// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache-2.0.

//! F1: Scope enter/exit ordering tests (#1213).

use super::*;

#[test]
fn test_scope_enter_exit_ordering_nested_let_forall() {
    let inner_exists = Expr::Exists(
        vec![BoundVar {
            name: sp_str("y"),
            domain: Some(boxed(Expr::Ident(
                "T".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        }],
        boxed(Expr::Bool(true)),
    );
    let forall = Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "S".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        }],
        boxed(inner_exists),
    );
    let let_expr = Expr::Let(
        vec![OperatorDef {
            name: sp_str("op_a"),
            params: vec![],
            body: sp(Expr::Int(BigInt::from(1))),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        }],
        boxed(forall),
    );

    let mut visitor = ScopeTrackingVisitor::new();
    walk_expr(&mut visitor, &let_expr);

    assert_eq!(visitor.depth, 0, "scope depth not balanced after walk");
    assert_eq!(visitor.max_depth, 3, "expected 3 nested scopes");
    assert_eq!(visitor.events.len(), 6);
    assert_eq!(
        visitor.events[0],
        ("enter".to_string(), vec!["op_a".to_string()])
    );
    assert_eq!(
        visitor.events[1],
        ("enter".to_string(), vec!["x".to_string()])
    );
    assert_eq!(
        visitor.events[2],
        ("enter".to_string(), vec!["y".to_string()])
    );
    assert_eq!(
        visitor.events[3],
        ("exit".to_string(), vec!["y".to_string()])
    );
    assert_eq!(
        visitor.events[4],
        ("exit".to_string(), vec!["x".to_string()])
    );
    assert_eq!(
        visitor.events[5],
        ("exit".to_string(), vec!["op_a".to_string()])
    );
}

#[test]
fn test_scope_enter_exit_all_binding_constructs() {
    let constructs = vec![
        (
            "SetBuilder",
            Expr::SetBuilder(
                boxed(Expr::Bool(true)),
                vec![BoundVar {
                    name: sp_str("sb"),
                    domain: Some(boxed(Expr::Ident(
                        "S".into(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    pattern: None,
                }],
            ),
        ),
        (
            "SetFilter",
            Expr::SetFilter(
                BoundVar {
                    name: sp_str("sf"),
                    domain: Some(boxed(Expr::Ident(
                        "S".into(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    pattern: None,
                },
                boxed(Expr::Bool(true)),
            ),
        ),
        (
            "FuncDef",
            Expr::FuncDef(
                vec![BoundVar {
                    name: sp_str("fd"),
                    domain: Some(boxed(Expr::Ident(
                        "S".into(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    pattern: None,
                }],
                boxed(Expr::Bool(true)),
            ),
        ),
        (
            "Choose",
            Expr::Choose(
                BoundVar {
                    name: sp_str("ch"),
                    domain: Some(boxed(Expr::Ident(
                        "S".into(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    pattern: None,
                },
                boxed(Expr::Bool(true)),
            ),
        ),
        (
            "Lambda",
            Expr::Lambda(vec![sp_str("lm")], boxed(Expr::Bool(true))),
        ),
    ];

    for (label, expr) in constructs {
        let mut visitor = ScopeTrackingVisitor::new();
        walk_expr(&mut visitor, &expr);
        assert_eq!(visitor.depth, 0, "{}: scope depth not balanced", label);
        assert_eq!(
            visitor.events.len(),
            2,
            "{}: expected exactly one enter + one exit",
            label
        );
        assert_eq!(
            visitor.events[0].0, "enter",
            "{}: first event not enter",
            label
        );
        assert_eq!(
            visitor.events[1].0, "exit",
            "{}: second event not exit",
            label
        );
        assert_eq!(
            visitor.events[0].1, visitor.events[1].1,
            "{}: enter/exit name mismatch",
            label
        );
    }
}

#[test]
fn test_scope_exit_on_short_circuit_in_let_body() {
    let let_expr = Expr::Let(
        vec![OperatorDef {
            name: sp_str("op"),
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

    struct ScopeAndPrimeVisitor {
        depth: i32,
    }
    impl ExprVisitor for ScopeAndPrimeVisitor {
        type Output = bool;
        fn visit_node(&mut self, expr: &Expr) -> Option<Self::Output> {
            match expr {
                Expr::Prime(_) => Some(true),
                _ => None,
            }
        }
        fn enter_scope(&mut self, _names: &[String]) {
            self.depth += 1;
        }
        fn exit_scope(&mut self, _names: &[String]) {
            self.depth -= 1;
        }
    }

    let mut visitor = ScopeAndPrimeVisitor { depth: 0 };
    let result = walk_expr(&mut visitor, &let_expr);
    assert!(result, "should detect Prime in Let def body");
    assert_eq!(
        visitor.depth, 0,
        "scope must be balanced even on short-circuit"
    );
}
