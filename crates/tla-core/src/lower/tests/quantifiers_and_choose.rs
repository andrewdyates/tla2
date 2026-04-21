// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_choose_with_literal_body() {
    let source = r"---- MODULE Test ----
Op == CHOOSE x \in {1, 2} : TRUE
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    let body = match &module.units[0].node {
        Unit::Operator(def) => &def.body.node,
        other => panic!("Expected Operator unit, got {other:?}"),
    };

    match body {
        Expr::Choose(bound, choose_body) => {
            assert_eq!(bound.name.node, "x");
            assert!(matches!(choose_body.node, Expr::Bool(true)));
        }
        other => panic!("Expected CHOOSE, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_quantifier() {
    let source = r"---- MODULE Test ----
AllPositive(S) == \A x \in S : x > 0
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::Forall(bounds, _) => {
                assert_eq!(bounds.len(), 1);
                assert_eq!(bounds[0].name.node, "x");
            }
            other => panic!("Expected Forall expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_exists_with_apply() {
    // Test lowering \E p \in S : f(p)
    let source = r"---- MODULE Test ----
CONSTANT N
ProcSet == 1..N
b0(self) == TRUE
Next == \E p \in ProcSet : b0(p)
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    // Find the Next operator
    let next_op = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(op) = &u.node {
                if op.name.node == "Next" {
                    return Some(op);
                }
            }
            None
        })
        .expect("Expected Next operator");

    // Verify Next body is Exists with bound variable p
    match &next_op.body.node {
        Expr::Exists(bounds, _body) => {
            assert_eq!(bounds.len(), 1);
            assert_eq!(bounds[0].name.node, "p");
        }
        other => panic!("Expected Next to be Exists, got {other:?}"),
    }
}
