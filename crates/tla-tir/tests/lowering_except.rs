// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use common::{expect_ident, lower_named_operator, lower_named_operator_result};
use tla_tir::{TirExceptPathElement, TirExpr, TirLowerError};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_single_index_except() {
    let source = r"
---- MODULE Main ----
VARIABLE f
Update == [f EXCEPT ![k] = v]
====
";

    let lowered = lower_named_operator(source, "Update");
    let TirExpr::Except { base, specs } = &lowered.node else {
        panic!("expected Except, got {:?}", lowered.node);
    };
    expect_ident(base, "f");
    assert_eq!(specs.len(), 1);
    assert_eq!(specs[0].path.len(), 1);
    match &specs[0].path[0] {
        TirExceptPathElement::Index(idx) => expect_ident(idx, "k"),
        other => panic!("expected index path element, got {other:?}"),
    }
    expect_ident(&specs[0].value, "v");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_record_field_except() {
    let source = r"
---- MODULE Main ----
VARIABLE r
Update == [r EXCEPT !.field = v]
====
";

    let lowered = lower_named_operator(source, "Update");
    let TirExpr::Except { base, specs } = &lowered.node else {
        panic!("expected Except, got {:?}", lowered.node);
    };
    expect_ident(base, "r");
    assert_eq!(specs.len(), 1);
    assert_eq!(specs[0].path.len(), 1);
    match &specs[0].path[0] {
        TirExceptPathElement::Field(field) => {
            assert_eq!(field.name, "field");
        }
        other => panic!("expected field path element, got {other:?}"),
    }
    expect_ident(&specs[0].value, "v");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_multiple_except_specs_preserves_source_order() {
    let source = r"
---- MODULE Main ----
VARIABLE f
Update == [f EXCEPT ![a] = b, ![c] = @]
====
";

    let lowered = lower_named_operator(source, "Update");
    let TirExpr::Except { base, specs } = &lowered.node else {
        panic!("expected Except, got {:?}", lowered.node);
    };
    expect_ident(base, "f");
    assert_eq!(specs.len(), 2, "both specs should be preserved in order");

    match &specs[0].path[0] {
        TirExceptPathElement::Index(idx) => expect_ident(idx, "a"),
        other => panic!("expected index path element, got {other:?}"),
    }
    expect_ident(&specs[0].value, "b");

    match &specs[1].path[0] {
        TirExceptPathElement::Index(idx) => expect_ident(idx, "c"),
        other => panic!("expected index path element, got {other:?}"),
    }
    assert_eq!(
        specs[1].value.node,
        TirExpr::ExceptAt,
        "@ in EXCEPT value should lower to ExceptAt"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_nested_except_with_outer_at_in_inner_base() {
    let source = r"
---- MODULE Main ----
VARIABLE f
Update == [f EXCEPT ![a] = [@ EXCEPT !.field = b]]
====
";

    let lowered = lower_named_operator(source, "Update");
    let TirExpr::Except { base, specs } = &lowered.node else {
        panic!("expected outer Except, got {:?}", lowered.node);
    };
    expect_ident(base, "f");
    assert_eq!(specs.len(), 1);

    let TirExpr::Except {
        base: inner_base,
        specs: inner_specs,
    } = &specs[0].value.node
    else {
        panic!("expected inner Except, got {:?}", specs[0].value.node);
    };

    assert_eq!(
        inner_base.node,
        TirExpr::ExceptAt,
        "inner base @ should be ExceptAt"
    );
    assert_eq!(inner_specs.len(), 1);
    match &inner_specs[0].path[0] {
        TirExceptPathElement::Field(field) => {
            assert_eq!(field.name, "field");
        }
        other => panic!("expected field path element, got {other:?}"),
    }
    expect_ident(&inner_specs[0].value, "b");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_stray_at_outside_except_returns_invalid_except_at() {
    let source = r"
---- MODULE Main ----
Bad == @
====
";

    let err = lower_named_operator_result(source, "Bad").expect_err("@ outside EXCEPT should fail");
    match err {
        TirLowerError::InvalidExceptAt { .. } => {}
        other => panic!("expected InvalidExceptAt, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_record_access_to_first_class_tir_node() {
    let source = r"
---- MODULE Main ----
VARIABLE r
Read == r.field
====
";

    let lowered = lower_named_operator(source, "Read");
    let TirExpr::RecordAccess { record, field } = &lowered.node else {
        panic!("expected RecordAccess, got {:?}", lowered.node);
    };
    expect_ident(record, "r");
    assert_eq!(field.name, "field");
}
