// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_eq_and_lt_to_first_class_cmp_nodes() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Init == x = 0
Ordered == x < 3
====
";

    let init = lower_named_operator(source, "Init");
    let TirExpr::Cmp { left, op, right } = &init.node else {
        panic!("expected Cmp for Init, got {:?}", init.node);
    };
    assert_eq!(*op, TirCmpOp::Eq);
    expect_name(left, "x");
    expect_int_const(right, 0);

    let ordered = lower_named_operator(source, "Ordered");
    let TirExpr::Cmp { left, op, right } = &ordered.node else {
        panic!("expected Cmp for Ordered, got {:?}", ordered.node);
    };
    assert_eq!(*op, TirCmpOp::Lt);
    expect_name(left, "x");
    expect_int_const(right, 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_arithmetic_and_range_to_first_class_tir_nodes() {
    let source = r"
---- MODULE Main ----
Math == (1 + 2) * 3
Window == 1..3
====
";

    let math = lower_named_operator(source, "Math");
    let TirExpr::ArithBinOp { left, op, right } = &math.node else {
        panic!("expected outer arithmetic op, got {:?}", math.node);
    };
    assert_eq!(*op, TirArithOp::Mul);
    expect_int_const(right, 3);
    let TirExpr::ArithBinOp {
        left: inner_left,
        op: inner_op,
        right: inner_right,
    } = &left.node
    else {
        panic!("expected nested arithmetic op, got {:?}", left.node);
    };
    assert_eq!(*inner_op, TirArithOp::Add);
    expect_int_const(inner_left, 1);
    expect_int_const(inner_right, 2);

    let window = lower_named_operator(source, "Window");
    let TirExpr::Range { lo, hi } = &window.node else {
        panic!("expected Range, got {:?}", window.node);
    };
    expect_int_const(lo, 1);
    expect_int_const(hi, 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_membership_subseteq_and_notin() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Within == x \in 1..3
Outside == x \notin S
Subset == A \subseteq B
====
";

    let within = lower_named_operator(source, "Within");
    let TirExpr::In { elem, set } = &within.node else {
        panic!("expected In, got {:?}", within.node);
    };
    expect_name(elem, "x");
    let TirExpr::Range { lo, hi } = &set.node else {
        panic!("expected range on rhs, got {:?}", set.node);
    };
    expect_int_const(lo, 1);
    expect_int_const(hi, 3);

    let outside = lower_named_operator(source, "Outside");
    let TirExpr::BoolNot(inner) = &outside.node else {
        panic!("expected BoolNot for notin, got {:?}", outside.node);
    };
    let TirExpr::In { elem, set } = &inner.node else {
        panic!("expected lowered In inside BoolNot, got {:?}", inner.node);
    };
    expect_name(elem, "x");
    expect_ident(set, "S");

    let subset = lower_named_operator(source, "Subset");
    let TirExpr::Subseteq { left, right } = &subset.node else {
        panic!("expected Subseteq, got {:?}", subset.node);
    };
    expect_ident(left, "A");
    expect_ident(right, "B");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_if_preserves_condition_and_branch_structure() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Branch == IF x < 3 THEN x + 1 ELSE x - 1
====
";

    let branch = lower_named_operator(source, "Branch");
    let TirExpr::If { cond, then_, else_ } = &branch.node else {
        panic!("expected If, got {:?}", branch.node);
    };

    let TirExpr::Cmp { left, op, right } = &cond.node else {
        panic!("expected Cmp condition, got {:?}", cond.node);
    };
    assert_eq!(*op, TirCmpOp::Lt);
    expect_name(left, "x");
    expect_int_const(right, 3);

    let TirExpr::ArithBinOp { left, op, right } = &then_.node else {
        panic!("expected arithmetic then branch, got {:?}", then_.node);
    };
    assert_eq!(*op, TirArithOp::Add);
    expect_name(left, "x");
    expect_int_const(right, 1);

    let TirExpr::ArithBinOp { left, op, right } = &else_.node else {
        panic!("expected arithmetic else branch, got {:?}", else_.node);
    };
    assert_eq!(*op, TirArithOp::Sub);
    expect_name(left, "x");
    expect_int_const(right, 1);
}
