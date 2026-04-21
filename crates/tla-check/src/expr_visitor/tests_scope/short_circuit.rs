// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache-2.0.

//! F2: Short-circuit counting tests (#1213).
//! F3: Except path element traversal test (#1213).

use super::*;

struct NodeCountingVisitor {
    nodes_visited: usize,
}

impl ExprVisitor for NodeCountingVisitor {
    type Output = bool;
    fn visit_node(&mut self, expr: &Expr) -> Option<Self::Output> {
        self.nodes_visited += 1;
        match expr {
            Expr::Prime(_) => Some(true),
            _ => None,
        }
    }
}

#[test]
fn test_short_circuit_stops_traversal_on_first_terminal() {
    let big_tree = Expr::Or(
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
            boxed(Expr::Ident(
                "d".into(),
                tla_core::name_intern::NameId::INVALID,
            )),
        )),
    );
    let expr = Expr::And(
        boxed(Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        boxed(big_tree),
    );

    let mut visitor = NodeCountingVisitor { nodes_visited: 0 };
    let result = walk_expr(&mut visitor, &expr);

    assert!(result, "should detect Prime");
    assert_eq!(
        visitor.nodes_visited, 2,
        "should visit only And and Prime, not the big tree (visited {})",
        visitor.nodes_visited
    );
}

#[test]
fn test_no_short_circuit_visits_all_nodes() {
    let expr = Expr::And(
        boxed(Expr::Ident(
            "a".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Ident(
            "b".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );

    let mut visitor = NodeCountingVisitor { nodes_visited: 0 };
    let result = walk_expr(&mut visitor, &expr);

    assert!(!result, "no Prime to detect");
    assert_eq!(visitor.nodes_visited, 3, "should visit And + 2 Idents");
}

#[test]
fn test_except_path_index_contains_prime() {
    let expr = Expr::Except(
        boxed(Expr::Ident(
            "f".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(sp(Expr::Prime(boxed(
                Expr::Ident("x".into(), tla_core::name_intern::NameId::INVALID),
            ))))],
            value: sp(Expr::Int(BigInt::from(1))),
        }],
    );
    assert!(
        expr_contains_prime_v(&expr),
        "Prime inside ExceptPathElement::Index must be detected"
    );
}
