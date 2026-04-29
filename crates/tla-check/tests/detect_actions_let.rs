// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::detect_actions;
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::name_intern::NameId;

fn find_op<'a>(module: &'a Module, name: &str) -> &'a OperatorDef {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(op) if op.name.node == name => Some(op),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing operator {name:?}"))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_actions_treats_let_as_transparent_wrapper() {
    let src = r#"
---- MODULE LetActions ----
VARIABLE x
Init == x = 0
B == x' = 2

Next ==
  LET C == x' = 1
  IN C \/ B
====
"#;

    let module = common::parse_module_strict(src);
    let next = find_op(&module, "Next");

    let actions = detect_actions(next);
    assert_eq!(
        actions.len(),
        2,
        "expected LET-wrapped disjunction to split into two actions; got: {actions:?}"
    );

    let names: std::collections::HashSet<_> = actions.iter().map(|a| a.name.as_str()).collect();
    assert!(
        names.contains("C"),
        "expected local LET operator action name"
    );
    assert!(names.contains("B"), "expected global operator action name");

    for action in actions {
        assert!(
            matches!(action.expr.node, Expr::Let(_, _)),
            "expected each detected action expr to preserve the LET wrapper; got: {:?}",
            action.expr.node
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_actions_let_preserves_guards_inside_wrapper() {
    let src = r#"
---- MODULE LetIfActions ----
VARIABLE x
Init == x = 0

c == TRUE

A == x' = 1
B == x' = 2

Next ==
  LET D == A
  IN IF c THEN D ELSE B
====
"#;

    let module = common::parse_module_strict(src);
    let next = find_op(&module, "Next");

    let actions = detect_actions(next);
    assert_eq!(
        actions.len(),
        2,
        "expected IF under LET to split into 2 actions"
    );

    let mut saw_then = false;
    let mut saw_else = false;

    for action in actions {
        match &action.expr.node {
            Expr::Let(defs, body) => {
                assert_eq!(defs.len(), 1);
                assert_eq!(defs[0].name.node, "D");
                match &body.node {
                    Expr::And(g, inner) => match (action.name.as_str(), &g.node, &inner.node) {
                        ("D", Expr::Ident(c, NameId::INVALID), Expr::Ident(d, NameId::INVALID)) => {
                            assert_eq!(c, "c");
                            assert_eq!(d, "D");
                            saw_then = true;
                        }
                        ("B", Expr::Not(c), Expr::Ident(b, NameId::INVALID)) => {
                            assert!(matches!(&c.node, Expr::Ident(name, _) if name == "c"));
                            assert_eq!(b, "B");
                            saw_else = true;
                        }
                        _ => panic!("unexpected guarded LET action: {action:?}"),
                    },
                    other => panic!("expected LET body to be And guard, got {other:?}"),
                }
            }
            other => panic!("expected LET wrapper, got {other:?}"),
        }
    }

    assert!(saw_then, "missing THEN action");
    assert!(saw_else, "missing ELSE action");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_actions_nested_lets_stack_in_scope_order() {
    let src = r#"
---- MODULE NestedLetActions ----
VARIABLE x
Init == x = 0

Next ==
  LET D == x' = 1
  IN (LET E == x' = 2 IN E) \/ D
====
"#;

    let module = common::parse_module_strict(src);
    let next = find_op(&module, "Next");

    let actions = detect_actions(next);
    assert_eq!(
        actions.len(),
        2,
        "expected disjunction under LET to split into 2 actions"
    );

    let names: std::collections::HashSet<_> = actions.iter().map(|a| a.name.as_str()).collect();
    assert!(
        names.contains("D"),
        "expected outer LET operator action name"
    );
    assert!(
        names.contains("E"),
        "expected inner LET operator action name"
    );

    for action in actions {
        match action.name.as_str() {
            "D" => match &action.expr.node {
                Expr::Let(defs_d, body) => {
                    assert_eq!(defs_d.len(), 1);
                    assert_eq!(defs_d[0].name.node, "D");
                    assert!(matches!(&body.node, Expr::Ident(name, _) if name == "D"));
                }
                other => panic!("expected outer LET wrapper for D, got {other:?}"),
            },
            "E" => match &action.expr.node {
                Expr::Let(defs_d, body) => {
                    assert_eq!(defs_d.len(), 1);
                    assert_eq!(defs_d[0].name.node, "D");
                    match &body.node {
                        Expr::Let(defs_e, inner) => {
                            assert_eq!(defs_e.len(), 1);
                            assert_eq!(defs_e[0].name.node, "E");
                            assert!(matches!(&inner.node, Expr::Ident(name, _) if name == "E"));
                        }
                        other => panic!("expected inner LET wrapper for E, got {other:?}"),
                    }
                }
                other => panic!("expected LET wrapper stack for E, got {other:?}"),
            },
            other => panic!("unexpected action name {other:?}"),
        }
    }
}
