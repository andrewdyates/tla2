// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_simple_module() {
    let source = r"---- MODULE Test ----
VARIABLE x
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.name.node, "Test");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Variable(vars) => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].node, "x");
        }
        _ => panic!("Expected Variable unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_operator_def() {
    let source = r"---- MODULE Test ----
Add(a, b) == a + b
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => {
            assert_eq!(def.name.node, "Add");
            // Body should be a + b which is an Add expression
            match &def.body.node {
                Expr::Add(_, _) => {}
                other => panic!("Expected Add expression, got {other:?}"),
            }
        }
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_constant_decl_with_arity() {
    let source = r"---- MODULE Test ----
CONSTANTS F(_, _), G
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Constant(consts) => {
            assert_eq!(consts.len(), 2);
            assert_eq!(consts[0].name.node, "F");
            assert_eq!(consts[0].arity, Some(2));
            assert_eq!(consts[1].name.node, "G");
            assert_eq!(consts[1].arity, None);
        }
        other => panic!("Expected Constant unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_assume_true() {
    let source = r"---- MODULE Test ----
ASSUME TRUE
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Assume(assume) => match &assume.expr.node {
            Expr::Bool(true) => {}
            other => panic!("Expected TRUE, got {other:?}"),
        },
        other => panic!("Expected Assume unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_theorem_true_body() {
    let source = r"---- MODULE Test ----
THEOREM T1 == TRUE
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Theorem(theorem) => match &theorem.body.node {
            Expr::Bool(true) => {}
            other => panic!("Expected TRUE, got {other:?}"),
        },
        other => panic!("Expected Theorem unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_operator_def_with_params() {
    let src = r"
---- MODULE Test ----
add_one(x) == x + 1
====
";
    let tree = crate::parse_to_syntax_tree(src);
    let lower_result = crate::lower(FileId(0), &tree);

    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("Expected module");

    let add_one = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(op) = &u.node {
                if op.name.node == "add_one" {
                    return Some(op);
                }
            }
            None
        })
        .expect("Expected add_one operator");

    assert_eq!(add_one.params.len(), 1, "Expected 1 parameter");
    assert_eq!(add_one.params[0].name.node, "x");
    assert!(
        matches!(&add_one.body.node, Expr::Add(_, _)),
        "Expected Add expression, got {:?}",
        add_one.body.node
    );
}
