// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::nodes::{TirNameKind, TirNameRef};
use tla_core::Spanned;

fn bool_const(b: bool) -> Spanned<TirExpr> {
    Spanned::dummy(TirExpr::Const {
        value: Value::Bool(b),
        ty: TirType::Bool,
    })
}

fn name_expr(s: &str) -> Spanned<TirExpr> {
    Spanned::dummy(TirExpr::Name(TirNameRef {
        name: s.to_string(),
        name_id: tla_core::intern_name(s),
        kind: TirNameKind::Ident,
        ty: TirType::Bool,
    }))
}

fn and(left: Spanned<TirExpr>, right: Spanned<TirExpr>) -> Spanned<TirExpr> {
    Spanned::dummy(TirExpr::BoolBinOp {
        left: Box::new(left),
        op: TirBoolOp::And,
        right: Box::new(right),
    })
}

fn or(left: Spanned<TirExpr>, right: Spanned<TirExpr>) -> Spanned<TirExpr> {
    Spanned::dummy(TirExpr::BoolBinOp {
        left: Box::new(left),
        op: TirBoolOp::Or,
        right: Box::new(right),
    })
}

fn implies(left: Spanned<TirExpr>, right: Spanned<TirExpr>) -> Spanned<TirExpr> {
    Spanned::dummy(TirExpr::BoolBinOp {
        left: Box::new(left),
        op: TirBoolOp::Implies,
        right: Box::new(right),
    })
}

fn not(inner: Spanned<TirExpr>) -> Spanned<TirExpr> {
    Spanned::dummy(TirExpr::BoolNot(Box::new(inner)))
}

// --- NNF tests ---

#[test]
fn test_nnf_double_negation_eliminated() {
    let a = name_expr("a");
    let result = nnf_transform(not(not(a.clone())));
    assert_eq!(result.node, a.node);
}

#[test]
fn test_nnf_de_morgan_and() {
    // ~(A /\ B) -> ~A \/ ~B
    let result = nnf_transform(not(and(name_expr("a"), name_expr("b"))));
    match &result.node {
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::Or,
            right,
        } => {
            assert!(matches!(&left.node, TirExpr::BoolNot(_)));
            assert!(matches!(&right.node, TirExpr::BoolNot(_)));
        }
        other => panic!("expected Or, got {other:?}"),
    }
}

#[test]
fn test_nnf_de_morgan_or() {
    // ~(A \/ B) -> ~A /\ ~B
    let result = nnf_transform(not(or(name_expr("a"), name_expr("b"))));
    match &result.node {
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::And,
            right,
        } => {
            assert!(matches!(&left.node, TirExpr::BoolNot(_)));
            assert!(matches!(&right.node, TirExpr::BoolNot(_)));
        }
        other => panic!("expected And, got {other:?}"),
    }
}

#[test]
fn test_nnf_negate_implies() {
    // ~(A => B) -> A /\ ~B
    let a = name_expr("a");
    let result = nnf_transform(not(implies(a.clone(), name_expr("b"))));
    match &result.node {
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::And,
            right,
        } => {
            assert_eq!(left.node, a.node);
            assert!(matches!(&right.node, TirExpr::BoolNot(_)));
        }
        other => panic!("expected And, got {other:?}"),
    }
}

#[test]
fn test_nnf_negate_constant() {
    let result = nnf_transform(not(bool_const(true)));
    assert_eq!(
        result.node,
        TirExpr::Const {
            value: Value::Bool(false),
            ty: TirType::Bool
        }
    );
}

// --- Constant folding tests ---

#[test]
fn test_fold_true_and_a() {
    let a = name_expr("a");
    assert_eq!(constant_fold(and(bool_const(true), a.clone())).node, a.node);
}

#[test]
fn test_fold_false_and_a() {
    assert_eq!(
        is_bool_const(&constant_fold(and(bool_const(false), name_expr("a")))),
        Some(false)
    );
}

#[test]
fn test_fold_false_or_a() {
    let a = name_expr("a");
    assert_eq!(constant_fold(or(bool_const(false), a.clone())).node, a.node);
}

#[test]
fn test_fold_true_or_a() {
    assert_eq!(
        is_bool_const(&constant_fold(or(bool_const(true), name_expr("a")))),
        Some(true)
    );
}

#[test]
fn test_fold_if_true() {
    let a = name_expr("a");
    let expr = Spanned::dummy(TirExpr::If {
        cond: Box::new(bool_const(true)),
        then_: Box::new(a.clone()),
        else_: Box::new(name_expr("b")),
    });
    assert_eq!(constant_fold(expr).node, a.node);
}

#[test]
fn test_fold_if_false() {
    let b = name_expr("b");
    let expr = Spanned::dummy(TirExpr::If {
        cond: Box::new(bool_const(false)),
        then_: Box::new(name_expr("a")),
        else_: Box::new(b.clone()),
    });
    assert_eq!(constant_fold(expr).node, b.node);
}

#[test]
fn test_fold_not_true() {
    assert_eq!(
        is_bool_const(&constant_fold(not(bool_const(true)))),
        Some(false)
    );
}

#[test]
fn test_fold_not_false() {
    assert_eq!(
        is_bool_const(&constant_fold(not(bool_const(false)))),
        Some(true)
    );
}

// --- Keramelization tests ---

#[test]
fn test_keramelize_nested_and() {
    // (A /\ B) /\ C -> A /\ (B /\ C)
    let a = name_expr("a");
    let b = name_expr("b");
    let c = name_expr("c");
    let result = keramelize(and(and(a.clone(), b.clone()), c.clone()));
    match &result.node {
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::And,
            right,
        } => {
            assert_eq!(left.node, a.node);
            match &right.node {
                TirExpr::BoolBinOp {
                    left: inner_left,
                    op: TirBoolOp::And,
                    right: inner_right,
                } => {
                    assert_eq!(inner_left.node, b.node);
                    assert_eq!(inner_right.node, c.node);
                }
                other => panic!("expected nested And, got {other:?}"),
            }
        }
        other => panic!("expected And, got {other:?}"),
    }
}

#[test]
fn test_keramelize_nested_or() {
    // (A \/ B) \/ C -> A \/ (B \/ C)
    let a = name_expr("a");
    let b = name_expr("b");
    let c = name_expr("c");
    let result = keramelize(or(or(a.clone(), b.clone()), c.clone()));
    match &result.node {
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::Or,
            right,
        } => {
            assert_eq!(left.node, a.node);
            match &right.node {
                TirExpr::BoolBinOp {
                    left: inner_left,
                    op: TirBoolOp::Or,
                    right: inner_right,
                } => {
                    assert_eq!(inner_left.node, b.node);
                    assert_eq!(inner_right.node, c.node);
                }
                other => panic!("expected nested Or, got {other:?}"),
            }
        }
        other => panic!("expected Or, got {other:?}"),
    }
}

// --- Pipeline integration test ---

#[test]
fn test_pipeline_full() {
    // ~(TRUE /\ A) -> NNF: FALSE \/ ~A -> constant fold: ~A
    let a = name_expr("a");
    let result = PreprocessPipeline::new().run(not(and(bool_const(true), a.clone())));
    assert!(matches!(&result.node, TirExpr::BoolNot(_)));
}

#[test]
fn test_pipeline_no_passes() {
    let a = name_expr("a");
    let expr = not(not(a.clone()));
    let pipeline = PreprocessPipeline {
        nnf: false,
        keramelize: false,
        constant_fold: false,
    };
    let result = pipeline.run(expr.clone());
    // With all passes disabled, expression should be unchanged.
    assert_eq!(result.node, expr.node);
}
