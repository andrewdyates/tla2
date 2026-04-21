// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_real_box_action_subscript_to_first_class_tir_node() {
    let source = r"
---- MODULE Main ----
Sub == [Next]_vars
====
";

    let lowered = lower_named_operator(source, "Sub");
    match &lowered.node {
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => {
            assert_eq!(*kind, TirActionSubscriptKind::Box);
            expect_ident(action, "Next");
            expect_ident(subscript, "vars");
        }
        other => panic!("expected action subscript, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_real_angle_action_subscript_to_first_class_tir_node() {
    let source = r"
---- MODULE Main ----
Angle == <<Next>>_vars
====
";

    let lowered = lower_named_operator(source, "Angle");
    match &lowered.node {
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => {
            assert_eq!(*kind, TirActionSubscriptKind::Angle);
            expect_ident(action, "Next");
            expect_ident(subscript, "vars");
        }
        other => panic!("expected action subscript, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_nested_box_action_subscript_to_first_class_tir_node() {
    let source = r"
---- MODULE Main ----
Nested == TRUE /\ [Next]_vars
====
";

    let lowered = lower_named_operator(source, "Nested");
    let TirExpr::BoolBinOp { left, op, right } = &lowered.node else {
        panic!("expected boolean and, got {:?}", lowered.node);
    };
    assert_eq!(*op, TirBoolOp::And);
    expect_bool_const(left, true);
    match &right.node {
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => {
            assert_eq!(*kind, TirActionSubscriptKind::Box);
            expect_ident(action, "Next");
            expect_ident(subscript, "vars");
        }
        other => panic!("expected nested action subscript, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn keep_explicit_box_expansion_as_plain_boolean_formula() {
    let source = r"
---- MODULE Main ----
Expanded == Next \/ UNCHANGED vars
====
";

    let lowered = lower_named_operator(source, "Expanded");
    let TirExpr::BoolBinOp { left, op, right } = &lowered.node else {
        panic!("expected boolean or, got {:?}", lowered.node);
    };
    assert_eq!(*op, TirBoolOp::Or);
    expect_ident(left, "Next");
    match &right.node {
        TirExpr::Unchanged(inner) => expect_ident(inner, "vars"),
        other => panic!("expected unchanged, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn keep_explicit_angle_expansion_as_plain_boolean_formula() {
    let source = r"
---- MODULE Main ----
Expanded == Next /\ ~UNCHANGED vars
====
";

    let lowered = lower_named_operator(source, "Expanded");
    let TirExpr::BoolBinOp { left, op, right } = &lowered.node else {
        panic!("expected boolean and, got {:?}", lowered.node);
    };
    assert_eq!(*op, TirBoolOp::And);
    expect_ident(left, "Next");
    match &right.node {
        TirExpr::BoolNot(inner) => match &inner.node {
            TirExpr::Unchanged(target) => expect_ident(target, "vars"),
            other => panic!("expected unchanged, got {other:?}"),
        },
        other => panic!("expected bool not, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn wrong_shape_at_action_subscript_span_falls_through_to_normal_lowering() {
    // Expressions with a span in action_subscript_spans but without the
    // canonical Or(_, Unchanged(_)) / And(_, Not(Unchanged(_))) shape should
    // be lowered normally, not rejected. This handles sub-expressions (like
    // the synthesized Unchanged wrapper) that may share a span with the
    // registered action-subscript span.
    let source = r"
---- MODULE Main ----
Broken == [Next]_vars
====
";

    let tree = parse_to_syntax_tree(source);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lower produced no module");
    let def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node.as_str() == "Broken" => Some(def),
            _ => None,
        })
        .expect("missing operator");

    let wrong_shape = Spanned::new(
        Expr::Not(Box::new(Spanned::new(Expr::Bool(true), def.body.span))),
        def.body.span,
    );
    let lowered = lower_expr(&module, &wrong_shape)
        .expect("wrong shape should fall through to normal lowering");
    match &lowered.node {
        TirExpr::BoolNot(inner) => {
            expect_bool_const(inner, true);
        }
        other => panic!("expected BoolNot, got {other:?}"),
    }
}
