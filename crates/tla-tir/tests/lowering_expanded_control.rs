// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Tests for TIR lowering: control flow, actions, apply, temporal, and type inference.
// Split from lowering_expanded.rs — Part of #3671

mod common;

use common::{expect_ident, expect_int_const, expect_name, lower_named_operator};
use tla_tir::{TirArithOp, TirCmpOp, TirExpr, TirType};

// === Control ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_let_in() {
    let source = r"
---- MODULE Main ----
Result == LET x == 1 + 2 IN x > 0
====
";
    let lowered = lower_named_operator(source, "Result");
    let TirExpr::Let { defs, body } = &lowered.node else {
        panic!("expected Let, got {:?}", lowered.node);
    };
    assert_eq!(defs.len(), 1);
    assert_eq!(defs[0].name, "x");
    assert!(defs[0].params.is_empty());
    let TirExpr::ArithBinOp { op, .. } = &defs[0].body.node else {
        panic!(
            "expected ArithBinOp in def body, got {:?}",
            defs[0].body.node
        );
    };
    assert_eq!(*op, TirArithOp::Add);
    let TirExpr::Cmp { op, .. } = &body.node else {
        panic!("expected Cmp in let body, got {:?}", body.node);
    };
    assert_eq!(*op, TirCmpOp::Gt);
}

// Part of #3262: parameterized LET defs are lowered to LAMBDA + zero-param binding.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_let_parameterized_to_lambda() {
    let source = r"
---- MODULE Main ----
Result == LET Inc(x) == x + 1 IN Inc(4)
====
";
    let lowered = lower_named_operator(source, "Result");
    let TirExpr::Let { defs, body: _ } = &lowered.node else {
        panic!("expected Let, got {:?}", lowered.node);
    };
    assert_eq!(defs.len(), 1);
    assert_eq!(defs[0].name, "Inc");
    // Parameterized def should be lowered to zero-param with Lambda body
    assert!(
        defs[0].params.is_empty(),
        "parameterized LET def should have empty params after lowering, got: {:?}",
        defs[0].params
    );
    let TirExpr::Lambda { params, .. } = &defs[0].body.node else {
        panic!(
            "expected Lambda body for parameterized LET def, got {:?}",
            defs[0].body.node
        );
    };
    assert_eq!(params, &["x".to_string()]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_case_with_other() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Pick == CASE x = 1 -> TRUE
          [] x = 2 -> FALSE
          [] OTHER -> TRUE
====
";
    let lowered = lower_named_operator(source, "Pick");
    let TirExpr::Case { arms, other } = &lowered.node else {
        panic!("expected Case, got {:?}", lowered.node);
    };
    assert_eq!(arms.len(), 2);
    assert!(other.is_some());
}

// === Actions ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_prime() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Assign == x' = x + 1
====
";
    let lowered = lower_named_operator(source, "Assign");
    let TirExpr::Cmp { left, op, .. } = &lowered.node else {
        panic!("expected Cmp, got {:?}", lowered.node);
    };
    assert_eq!(*op, TirCmpOp::Eq);
    let TirExpr::Prime(inner) = &left.node else {
        panic!("expected Prime on lhs, got {:?}", left.node);
    };
    expect_name(inner, "x");
}

// === Generic Apply ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_apply_operator() {
    let source = r"
---- MODULE Main ----
F(x) == x + 1
Result == F(3)
====
";
    let lowered = lower_named_operator(source, "Result");
    let TirExpr::Apply { op, args } = &lowered.node else {
        panic!("expected Apply, got {:?}", lowered.node);
    };
    expect_ident(op, "F");
    assert_eq!(args.len(), 1);
    expect_int_const(&args[0], 3);
}

// === Temporal (extended) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_leads_to() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Prop == (x = 1) ~> (x = 2)
====
";
    let lowered = lower_named_operator(source, "Prop");
    let TirExpr::LeadsTo { left, right } = &lowered.node else {
        panic!("expected LeadsTo, got {:?}", lowered.node);
    };
    let TirExpr::Cmp { .. } = &left.node else {
        panic!("expected Cmp on lhs, got {:?}", left.node);
    };
    let TirExpr::Cmp { .. } = &right.node else {
        panic!("expected Cmp on rhs, got {:?}", right.node);
    };
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_weak_fair() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Fair == WF_x(x' = x + 1)
====
";
    let lowered = lower_named_operator(source, "Fair");
    let TirExpr::WeakFair { vars, action: _ } = &lowered.node else {
        panic!("expected WeakFair, got {:?}", lowered.node);
    };
    expect_name(vars, "x");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_strong_fair() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Fair == SF_x(x' = x + 1)
====
";
    let lowered = lower_named_operator(source, "Fair");
    let TirExpr::StrongFair { vars, action: _ } = &lowered.node else {
        panic!("expected StrongFair, got {:?}", lowered.node);
    };
    expect_name(vars, "x");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_enabled() {
    let source = r"
---- MODULE Main ----
VARIABLE x
IsEnabled == ENABLED (x' = x + 1)
====
";
    let lowered = lower_named_operator(source, "IsEnabled");
    let TirExpr::Enabled(_inner) = &lowered.node else {
        panic!("expected Enabled, got {:?}", lowered.node);
    };
}

// === Type inference ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn set_enum_has_set_type() {
    let source = r"
---- MODULE Main ----
S == {1, 2, 3}
====
";
    let lowered = lower_named_operator(source, "S");
    // With improved type inference, {1, 2, 3} infers element type Int.
    assert_eq!(lowered.node.ty(), TirType::Set(Box::new(TirType::Int)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn empty_set_enum_has_dyn_set_type() {
    let source = r"
---- MODULE Main ----
Empty == {}
====
";
    let lowered = lower_named_operator(source, "Empty");
    let TirExpr::SetEnum(elems) = &lowered.node else {
        panic!("expected SetEnum, got {:?}", lowered.node);
    };
    assert!(
        elems.is_empty(),
        "empty set should lower with zero elements"
    );
    assert_eq!(lowered.node.ty(), TirType::Set(Box::new(TirType::Dyn)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tuple_has_tuple_type() {
    let source = r"
---- MODULE Main ----
T == <<1, TRUE>>
====
";
    let lowered = lower_named_operator(source, "T");
    assert_eq!(
        lowered.node.ty(),
        TirType::Tuple(vec![TirType::Int, TirType::Bool])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn forall_has_bool_type() {
    let source = r"
---- MODULE Main ----
P == \A x \in 1..3 : x > 0
====
";
    let lowered = lower_named_operator(source, "P");
    assert_eq!(lowered.node.ty(), TirType::Bool);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn nested_quantifiers_have_bool_type() {
    let source = r"
---- MODULE Main ----
P == \A x \in 1..3 : \E y \in {x} : y = x
====
";
    let lowered = lower_named_operator(source, "P");
    let TirExpr::Forall { body, .. } = &lowered.node else {
        panic!("expected Forall, got {:?}", lowered.node);
    };
    let TirExpr::Exists {
        body: inner_body, ..
    } = &body.node
    else {
        panic!("expected nested Exists, got {:?}", body.node);
    };
    let TirExpr::Cmp { op, .. } = &inner_body.node else {
        panic!(
            "expected comparison in nested quantifier body, got {:?}",
            inner_body.node
        );
    };
    assert_eq!(*op, TirCmpOp::Eq);
    assert_eq!(lowered.node.ty(), TirType::Bool);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn let_body_type_propagates() {
    let source = r"
---- MODULE Main ----
V == LET x == 1 IN x + 2
====
";
    let lowered = lower_named_operator(source, "V");
    assert_eq!(lowered.node.ty(), TirType::Int);
}
