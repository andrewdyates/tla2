// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Tests for TIR lowering: lambda, quantifiers, sets, functions, records, tuples.
// Control, actions, temporal, type inference moved to lowering_expanded_control.rs — Part of #3671

mod common;

use common::{expect_ident, expect_int_const, expect_name, lower_named_operator};
use tla_tir::{TirArithOp, TirCmpOp, TirExpr, TirSetOp, TirType};

// === Lambda / higher-order ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_lambda_expression() {
    let source = r"
---- MODULE Main ----
F == LAMBDA x : x + 1
====
";
    let lowered = lower_named_operator(source, "F");
    let TirExpr::Lambda { params, body, .. } = &lowered.node else {
        panic!("expected Lambda, got {:?}", lowered.node);
    };
    assert_eq!(params, &["x"]);
    let TirExpr::ArithBinOp { op, .. } = &body.node else {
        panic!("expected ArithBinOp in lambda body, got {:?}", body.node);
    };
    assert_eq!(*op, TirArithOp::Add);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_lambda_with_multiple_params() {
    let source = r"
---- MODULE Main ----
G == LAMBDA x, y : x + y
====
";
    let lowered = lower_named_operator(source, "G");
    let TirExpr::Lambda { params, .. } = &lowered.node else {
        panic!("expected Lambda, got {:?}", lowered.node);
    };
    assert_eq!(params, &["x", "y"]);
    assert_eq!(lowered.node.ty(), TirType::Dyn);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_opref_expression() {
    let source = r"
---- MODULE Main ----
EXTENDS Naturals
Op == +
====
";
    let lowered = lower_named_operator(source, "Op");
    let TirExpr::OpRef(name) = &lowered.node else {
        panic!("expected OpRef, got {:?}", lowered.node);
    };
    assert_eq!(name, "+");
    assert_eq!(lowered.node.ty(), TirType::Dyn);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_label_expression() {
    let source = r"
---- MODULE Main ----
P == lab:: 1 + 2
====
";
    let lowered = lower_named_operator(source, "P");
    let TirExpr::Label { name, body } = &lowered.node else {
        panic!("expected Label, got {:?}", lowered.node);
    };
    assert_eq!(name, "lab");
    let TirExpr::ArithBinOp { op, .. } = &body.node else {
        panic!("expected ArithBinOp in label body, got {:?}", body.node);
    };
    assert_eq!(*op, TirArithOp::Add);
    assert_eq!(lowered.node.ty(), TirType::Int);
}

// === Quantifiers ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_forall_with_domain() {
    let source = r"
---- MODULE Main ----
VARIABLE x
AllPos == \A i \in 1..10 : i > 0
====
";
    let lowered = lower_named_operator(source, "AllPos");
    let TirExpr::Forall { vars, body } = &lowered.node else {
        panic!("expected Forall, got {:?}", lowered.node);
    };
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "i");
    assert!(vars[0].domain.is_some());
    let TirExpr::Cmp { op, .. } = &body.node else {
        panic!("expected Cmp body, got {:?}", body.node);
    };
    assert_eq!(*op, TirCmpOp::Gt);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_exists_with_domain() {
    let source = r"
---- MODULE Main ----
HasZero == \E i \in 1..10 : i = 0
====
";
    let lowered = lower_named_operator(source, "HasZero");
    let TirExpr::Exists { vars, body } = &lowered.node else {
        panic!("expected Exists, got {:?}", lowered.node);
    };
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "i");
    let TirExpr::Cmp { op, .. } = &body.node else {
        panic!("expected Cmp body, got {:?}", body.node);
    };
    assert_eq!(*op, TirCmpOp::Eq);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_multi_var_forall_desugars_to_nested_single_var_and_shadows_outer_binding() {
    let source = r"
---- MODULE Main ----
Check == LET x == 99 IN \A x \in {1, 2}, y \in {x} : x = y
====
";
    let lowered = lower_named_operator(source, "Check");
    let TirExpr::Let { body, .. } = &lowered.node else {
        panic!("expected Let, got {:?}", lowered.node);
    };
    let TirExpr::Forall {
        vars: outer_vars,
        body: outer_body,
    } = &body.node
    else {
        panic!("expected outer Forall, got {:?}", body.node);
    };
    assert_eq!(outer_vars.len(), 1);
    assert_eq!(outer_vars[0].name, "x");

    let TirExpr::Forall {
        vars: inner_vars,
        body: inner_body,
    } = &outer_body.node
    else {
        panic!("expected nested Forall, got {:?}", outer_body.node);
    };
    assert_eq!(inner_vars.len(), 1);
    assert_eq!(inner_vars[0].name, "y");

    let domain = inner_vars[0]
        .domain
        .as_ref()
        .expect("inner quantifier should keep its dependent domain");
    let TirExpr::SetEnum(elems) = &domain.node else {
        panic!("expected SetEnum domain, got {:?}", domain.node);
    };
    assert_eq!(elems.len(), 1);
    expect_ident(&elems[0], "x");

    let TirExpr::Cmp { left, op, right } = &inner_body.node else {
        panic!("expected comparison body, got {:?}", inner_body.node);
    };
    assert_eq!(*op, TirCmpOp::Eq);
    expect_ident(left, "x");
    expect_ident(right, "y");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_multi_var_exists_desugars_to_nested_single_var_and_shadows_outer_binding() {
    let source = r"
---- MODULE Main ----
Check == LET x == 99 IN \E x \in {1, 2}, y \in {x} : x = 1 /\ x = y
====
";
    let lowered = lower_named_operator(source, "Check");
    let TirExpr::Let { body, .. } = &lowered.node else {
        panic!("expected Let, got {:?}", lowered.node);
    };
    let TirExpr::Exists {
        vars: outer_vars,
        body: outer_body,
    } = &body.node
    else {
        panic!("expected outer Exists, got {:?}", body.node);
    };
    assert_eq!(outer_vars.len(), 1);
    assert_eq!(outer_vars[0].name, "x");

    let TirExpr::Exists {
        vars: inner_vars,
        body: inner_body,
    } = &outer_body.node
    else {
        panic!("expected nested Exists, got {:?}", outer_body.node);
    };
    assert_eq!(inner_vars.len(), 1);
    assert_eq!(inner_vars[0].name, "y");

    let domain = inner_vars[0]
        .domain
        .as_ref()
        .expect("inner quantifier should keep its dependent domain");
    let TirExpr::SetEnum(elems) = &domain.node else {
        panic!("expected SetEnum domain, got {:?}", domain.node);
    };
    assert_eq!(elems.len(), 1);
    expect_ident(&elems[0], "x");

    let TirExpr::BoolBinOp { left, op, right } = &inner_body.node else {
        panic!("expected conjunction body, got {:?}", inner_body.node);
    };
    assert_eq!(*op, tla_tir::TirBoolOp::And);

    let TirExpr::Cmp {
        left: left_cmp_left,
        op: left_cmp_op,
        right: left_cmp_right,
    } = &left.node
    else {
        panic!("expected left comparison, got {:?}", left.node);
    };
    assert_eq!(*left_cmp_op, TirCmpOp::Eq);
    expect_ident(left_cmp_left, "x");
    expect_int_const(left_cmp_right, 1);

    let TirExpr::Cmp {
        left: right_cmp_left,
        op: right_cmp_op,
        right: right_cmp_right,
    } = &right.node
    else {
        panic!("expected right comparison, got {:?}", right.node);
    };
    assert_eq!(*right_cmp_op, TirCmpOp::Eq);
    expect_ident(right_cmp_left, "x");
    expect_ident(right_cmp_right, "y");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_choose_with_domain() {
    let source = r"
---- MODULE Main ----
Pick == CHOOSE i \in 1..10 : i > 5
====
";
    let lowered = lower_named_operator(source, "Pick");
    let TirExpr::Choose { var, body } = &lowered.node else {
        panic!("expected Choose, got {:?}", lowered.node);
    };
    assert_eq!(var.name, "i");
    assert!(var.domain.is_some());
    let TirExpr::Cmp { op, .. } = &body.node else {
        panic!("expected Cmp body, got {:?}", body.node);
    };
    assert_eq!(*op, TirCmpOp::Gt);
}

// === Sets ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_set_enum() {
    let source = r"
---- MODULE Main ----
Colors == {1, 2, 3}
====
";
    let lowered = lower_named_operator(source, "Colors");
    let TirExpr::SetEnum(elems) = &lowered.node else {
        panic!("expected SetEnum, got {:?}", lowered.node);
    };
    assert_eq!(elems.len(), 3);
    expect_int_const(&elems[0], 1);
    expect_int_const(&elems[1], 2);
    expect_int_const(&elems[2], 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_set_filter() {
    let source = r"
---- MODULE Main ----
Evens == {x \in 1..10 : x > 5}
====
";
    let lowered = lower_named_operator(source, "Evens");
    let TirExpr::SetFilter { var, body } = &lowered.node else {
        panic!("expected SetFilter, got {:?}", lowered.node);
    };
    assert_eq!(var.name, "x");
    assert!(var.domain.is_some());
    let TirExpr::Cmp { op, .. } = &body.node else {
        panic!("expected Cmp body, got {:?}", body.node);
    };
    assert_eq!(*op, TirCmpOp::Gt);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_set_builder() {
    let source = r"
---- MODULE Main ----
Doubled == {x + x : x \in 1..5}
====
";
    let lowered = lower_named_operator(source, "Doubled");
    let TirExpr::SetBuilder { body, vars } = &lowered.node else {
        panic!("expected SetBuilder, got {:?}", lowered.node);
    };
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "x");
    let TirExpr::ArithBinOp { op, .. } = &body.node else {
        panic!("expected ArithBinOp body, got {:?}", body.node);
    };
    assert_eq!(*op, TirArithOp::Add);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_set_union_intersect_minus() {
    let source = r"
---- MODULE Main ----
U == A \union B
I == A \intersect B
D == A \ B
====
";
    let u = lower_named_operator(source, "U");
    let TirExpr::SetBinOp { op, .. } = &u.node else {
        panic!("expected SetBinOp for union, got {:?}", u.node);
    };
    assert_eq!(*op, TirSetOp::Union);

    let i = lower_named_operator(source, "I");
    let TirExpr::SetBinOp { op, .. } = &i.node else {
        panic!("expected SetBinOp for intersect, got {:?}", i.node);
    };
    assert_eq!(*op, TirSetOp::Intersect);

    let d = lower_named_operator(source, "D");
    let TirExpr::SetBinOp { op, .. } = &d.node else {
        panic!("expected SetBinOp for minus, got {:?}", d.node);
    };
    assert_eq!(*op, TirSetOp::Minus);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_powerset_and_big_union() {
    let source = r"
---- MODULE Main ----
P == SUBSET S
U == UNION S
====
";
    let p = lower_named_operator(source, "P");
    let TirExpr::Powerset(inner) = &p.node else {
        panic!("expected Powerset, got {:?}", p.node);
    };
    expect_ident(inner, "S");

    let u = lower_named_operator(source, "U");
    let TirExpr::BigUnion(inner) = &u.node else {
        panic!("expected BigUnion, got {:?}", u.node);
    };
    expect_ident(inner, "S");
}

// === Functions ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_func_def() {
    let source = r"
---- MODULE Main ----
F == [x \in 1..3 |-> x + 1]
====
";
    let lowered = lower_named_operator(source, "F");
    let TirExpr::FuncDef { vars, body } = &lowered.node else {
        panic!("expected FuncDef, got {:?}", lowered.node);
    };
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "x");
    let TirExpr::ArithBinOp { op, .. } = &body.node else {
        panic!("expected ArithBinOp body, got {:?}", body.node);
    };
    assert_eq!(*op, TirArithOp::Add);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_func_apply() {
    let source = r"
---- MODULE Main ----
VARIABLE f
Val == f[k]
====
";
    let lowered = lower_named_operator(source, "Val");
    let TirExpr::FuncApply { func, arg } = &lowered.node else {
        panic!("expected FuncApply, got {:?}", lowered.node);
    };
    expect_name(func, "f");
    expect_ident(arg, "k");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_func_set_and_domain() {
    let source = r"
---- MODULE Main ----
FS == [S -> T]
D == DOMAIN f
====
";
    let fs = lower_named_operator(source, "FS");
    let TirExpr::FuncSet { domain, range } = &fs.node else {
        panic!("expected FuncSet, got {:?}", fs.node);
    };
    expect_ident(domain, "S");
    expect_ident(range, "T");

    let d = lower_named_operator(source, "D");
    let TirExpr::Domain(inner) = &d.node else {
        panic!("expected Domain, got {:?}", d.node);
    };
    expect_ident(inner, "f");
}

// === Records/Tuples ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_record_constructor() {
    let source = r"
---- MODULE Main ----
R == [a |-> 1, b |-> 2]
====
";
    let lowered = lower_named_operator(source, "R");
    let TirExpr::Record(fields) = &lowered.node else {
        panic!("expected Record, got {:?}", lowered.node);
    };
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].0.name, "a");
    expect_int_const(&fields[0].1, 1);
    assert_eq!(fields[1].0.name, "b");
    expect_int_const(&fields[1].1, 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_record_set() {
    let source = r"
---- MODULE Main ----
RS == [a : 1..3, b : 1..2]
====
";
    let lowered = lower_named_operator(source, "RS");
    let TirExpr::RecordSet(fields) = &lowered.node else {
        panic!("expected RecordSet, got {:?}", lowered.node);
    };
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].0.name, "a");
    assert_eq!(fields[1].0.name, "b");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_tuple() {
    let source = r"
---- MODULE Main ----
T == <<1, 2, 3>>
====
";
    let lowered = lower_named_operator(source, "T");
    let TirExpr::Tuple(elems) = &lowered.node else {
        panic!("expected Tuple, got {:?}", lowered.node);
    };
    assert_eq!(elems.len(), 3);
    expect_int_const(&elems[0], 1);
    expect_int_const(&elems[1], 2);
    expect_int_const(&elems[2], 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_times() {
    let source = r"
---- MODULE Main ----
Cross == S \X T
====
";
    let lowered = lower_named_operator(source, "Cross");
    let TirExpr::Times(factors) = &lowered.node else {
        panic!("expected Times, got {:?}", lowered.node);
    };
    assert_eq!(factors.len(), 2);
    expect_ident(&factors[0], "S");
    expect_ident(&factors[1], "T");
}
