// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::nodes::{
    TirArithOp, TirBoundVar, TirCaseArm, TirCmpOp, TirLetDef, TirNameKind, TirNameRef,
};
use crate::types::TirType;
use tla_core::Spanned;
use tla_value::Value;

fn bool_const(b: bool) -> Spanned<TirExpr> {
    Spanned::dummy(TirExpr::Const {
        value: Value::Bool(b),
        ty: TirType::Bool,
    })
}

fn int_const(n: i64) -> Spanned<TirExpr> {
    Spanned::dummy(TirExpr::Const {
        value: Value::int(n),
        ty: TirType::Int,
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

fn bounded_var(name: &str, with_domain: bool) -> TirBoundVar {
    TirBoundVar {
        name: name.to_string(),
        name_id: tla_core::intern_name(name),
        domain: with_domain
            .then(|| Box::new(Spanned::dummy(TirExpr::SetEnum(vec![bool_const(true)])))),
        pattern: None,
    }
}

#[test]
fn test_arith_fold_add() {
    let expr = Spanned::dummy(TirExpr::ArithBinOp {
        left: Box::new(int_const(1)),
        op: TirArithOp::Add,
        right: Box::new(int_const(2)),
    });

    assert_eq!(arith_constant_fold(expr).node, int_const(3).node);
}

#[test]
fn test_arith_fold_sub() {
    let expr = Spanned::dummy(TirExpr::ArithBinOp {
        left: Box::new(int_const(5)),
        op: TirArithOp::Sub,
        right: Box::new(int_const(3)),
    });

    assert_eq!(arith_constant_fold(expr).node, int_const(2).node);
}

#[test]
fn test_arith_fold_mul() {
    let expr = Spanned::dummy(TirExpr::ArithBinOp {
        left: Box::new(int_const(3)),
        op: TirArithOp::Mul,
        right: Box::new(int_const(4)),
    });

    assert_eq!(arith_constant_fold(expr).node, int_const(12).node);
}

#[test]
fn test_arith_fold_neg() {
    let expr = Spanned::dummy(TirExpr::ArithNeg(Box::new(int_const(5))));

    assert_eq!(arith_constant_fold(expr).node, int_const(-5).node);
}

#[test]
fn test_arith_fold_nested() {
    let expr = Spanned::dummy(TirExpr::ArithBinOp {
        left: Box::new(Spanned::dummy(TirExpr::ArithBinOp {
            left: Box::new(int_const(1)),
            op: TirArithOp::Add,
            right: Box::new(int_const(2)),
        })),
        op: TirArithOp::Mul,
        right: Box::new(int_const(3)),
    });

    assert_eq!(arith_constant_fold(expr).node, int_const(9).node);
}

#[test]
fn test_arith_fold_cmp_lt() {
    let expr = Spanned::dummy(TirExpr::Cmp {
        left: Box::new(int_const(1)),
        op: TirCmpOp::Lt,
        right: Box::new(int_const(2)),
    });

    assert_eq!(arith_constant_fold(expr).node, bool_const(true).node);
}

#[test]
fn test_arith_fold_cmp_geq() {
    let expr = Spanned::dummy(TirExpr::Cmp {
        left: Box::new(int_const(5)),
        op: TirCmpOp::Geq,
        right: Box::new(int_const(3)),
    });

    assert_eq!(arith_constant_fold(expr).node, bool_const(true).node);
}

#[test]
fn test_skolem_bounded_exists() {
    let expr = Spanned::dummy(TirExpr::Exists {
        vars: vec![bounded_var("x", true)],
        body: Box::new(name_expr("p")),
    });

    let result = skolemize_bounded_exists(expr);

    match &result.node {
        TirExpr::Label { name, body } => {
            assert_eq!(name, "__skolem__");
            assert!(matches!(body.node, TirExpr::Exists { .. }));
        }
        other => panic!("expected labeled skolemized exists, got {other:?}"),
    }
}

#[test]
fn test_skolem_unbounded_exists() {
    let expr = Spanned::dummy(TirExpr::Exists {
        vars: vec![bounded_var("x", false)],
        body: Box::new(name_expr("p")),
    });

    let result = skolemize_bounded_exists(expr);

    assert!(matches!(result.node, TirExpr::Exists { .. }));
}

#[test]
fn test_dead_branch_case_true_guard() {
    let expr = Spanned::dummy(TirExpr::Case {
        arms: vec![
            TirCaseArm {
                guard: bool_const(false),
                body: bool_const(false),
            },
            TirCaseArm {
                guard: bool_const(true),
                body: name_expr("winner"),
            },
        ],
        other: Some(Box::new(bool_const(false))),
    });

    assert_eq!(dead_branch_eliminate(expr).node, name_expr("winner").node);
}

#[test]
fn test_dead_branch_case_all_false_with_other() {
    let expr = Spanned::dummy(TirExpr::Case {
        arms: vec![
            TirCaseArm {
                guard: bool_const(false),
                body: name_expr("a"),
            },
            TirCaseArm {
                guard: bool_const(false),
                body: name_expr("b"),
            },
        ],
        other: Some(Box::new(name_expr("fallback"))),
    });

    assert_eq!(dead_branch_eliminate(expr).node, name_expr("fallback").node);
}

#[test]
fn test_dead_branch_forall_true_body() {
    let expr = Spanned::dummy(TirExpr::Forall {
        vars: vec![bounded_var("x", true)],
        body: Box::new(bool_const(true)),
    });

    assert_eq!(dead_branch_eliminate(expr).node, bool_const(true).node);
}

#[test]
fn test_dead_branch_exists_false_body() {
    let expr = Spanned::dummy(TirExpr::Exists {
        vars: vec![bounded_var("x", true)],
        body: Box::new(bool_const(false)),
    });

    assert_eq!(dead_branch_eliminate(expr).node, bool_const(false).node);
}

#[test]
fn test_dead_branch_let_const_body() {
    let expr = Spanned::dummy(TirExpr::Let {
        defs: vec![TirLetDef {
            name: "X".to_string(),
            name_id: tla_core::intern_name("X"),
            params: Vec::new(),
            body: name_expr("p"),
        }],
        body: Box::new(int_const(42)),
    });

    assert_eq!(dead_branch_eliminate(expr).node, int_const(42).node);
}

#[test]
fn test_pipeline_default() {
    let case_expr = Spanned::dummy(TirExpr::Case {
        arms: vec![TirCaseArm {
            guard: Spanned::dummy(TirExpr::Cmp {
                left: Box::new(Spanned::dummy(TirExpr::ArithBinOp {
                    left: Box::new(int_const(1)),
                    op: TirArithOp::Add,
                    right: Box::new(int_const(2)),
                })),
                op: TirCmpOp::Eq,
                right: Box::new(int_const(3)),
            }),
            body: bool_const(true),
        }],
        other: Some(Box::new(bool_const(false))),
    });
    let expr = Spanned::dummy(TirExpr::BoolNot(Box::new(Spanned::dummy(
        TirExpr::Forall {
            vars: vec![bounded_var("x", true)],
            body: Box::new(Spanned::dummy(TirExpr::BoolNot(Box::new(case_expr)))),
        },
    ))));

    let result = PassPipeline::default_pipeline().run(expr);

    match &result.node {
        TirExpr::Label { name, body } => {
            assert_eq!(name, "__skolem__");
            match &body.node {
                TirExpr::Exists { body, .. } => {
                    assert_eq!(body.node, bool_const(true).node);
                }
                other => panic!("expected exists under skolem label, got {other:?}"),
            }
        }
        other => panic!("expected default pipeline to produce skolem label, got {other:?}"),
    }
}

#[test]
fn test_dead_branch_case_mixed_guards() {
    let expr = Spanned::dummy(TirExpr::Case {
        arms: vec![
            TirCaseArm {
                guard: bool_const(false),
                body: int_const(1),
            },
            TirCaseArm {
                guard: name_expr("x"),
                body: int_const(2),
            },
            TirCaseArm {
                guard: bool_const(false),
                body: int_const(3),
            },
        ],
        other: Some(Box::new(int_const(99))),
    });

    let result = dead_branch_eliminate(expr);

    match &result.node {
        TirExpr::Case { arms, other } => {
            assert_eq!(arms.len(), 1, "only the dynamic-guard arm should survive");
            assert_eq!(arms[0].body.node, int_const(2).node);
            assert!(other.is_some(), "OTHER should be preserved");
            assert_eq!(other.as_ref().unwrap().node, int_const(99).node);
        }
        other => panic!("expected Case with one arm, got {other:?}"),
    }
}

#[test]
fn test_dead_branch_if_true() {
    let expr = Spanned::dummy(TirExpr::If {
        cond: Box::new(bool_const(true)),
        then_: Box::new(int_const(42)),
        else_: Box::new(int_const(99)),
    });

    assert_eq!(dead_branch_eliminate(expr).node, int_const(42).node);
}

#[test]
fn test_dead_branch_if_false() {
    let expr = Spanned::dummy(TirExpr::If {
        cond: Box::new(bool_const(false)),
        then_: Box::new(int_const(42)),
        else_: Box::new(int_const(99)),
    });

    assert_eq!(dead_branch_eliminate(expr).node, int_const(99).node);
}

#[test]
fn test_arith_fold_div_by_zero() {
    let expr = Spanned::dummy(TirExpr::ArithBinOp {
        left: Box::new(int_const(5)),
        op: TirArithOp::IntDiv,
        right: Box::new(int_const(0)),
    });

    let result = arith_constant_fold(expr);

    assert!(
        matches!(result.node, TirExpr::ArithBinOp { .. }),
        "division by zero should leave ArithBinOp unchanged, got {:?}",
        result.node
    );
}

#[test]
fn test_arith_fold_overflow() {
    let expr = Spanned::dummy(TirExpr::ArithBinOp {
        left: Box::new(int_const(i64::MAX)),
        op: TirArithOp::Add,
        right: Box::new(int_const(1)),
    });

    let result = arith_constant_fold(expr);

    assert!(
        matches!(result.node, TirExpr::ArithBinOp { .. }),
        "overflow should leave ArithBinOp unchanged, got {:?}",
        result.node
    );
}

#[test]
fn test_pass_name() {
    assert_eq!(NnfPass.name(), "nnf");
    assert_eq!(ConstantFoldPass.name(), "constant_fold");
    assert_eq!(SkolemizationPass.name(), "skolemization");
    assert_eq!(DeadBranchPass.name(), "dead_branch");
}
