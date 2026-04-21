// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_local_operator_def() {
    let source = r"---- MODULE Test ----
LOCAL Foo == TRUE
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Operator(def) => {
            assert!(def.local);
            assert_eq!(def.name.node, "Foo");
        }
        other => panic!("Expected Operator unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_local_instance_decl() {
    let source = r"---- MODULE Test ----
LOCAL INSTANCE Foo WITH x <- 1
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Instance(inst) => {
            assert!(inst.local);
            assert_eq!(inst.module.node, "Foo");
            assert_eq!(inst.substitutions.len(), 1);
            assert_eq!(inst.substitutions[0].from.node, "x");
        }
        other => panic!("Expected Instance unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_recursive_simple() {
    let source = r"---- MODULE Test ----
RECURSIVE Factorial(_)
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Recursive(decls) => {
            assert_eq!(decls.len(), 1);
            assert_eq!(decls[0].name.node, "Factorial");
            assert_eq!(decls[0].arity, 1);
        }
        other => panic!("Expected Recursive unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_recursive_multiple() {
    let source = r"---- MODULE Test ----
RECURSIVE F(_), G(_, _)
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Recursive(decls) => {
            assert_eq!(decls.len(), 2);
            assert_eq!(decls[0].name.node, "F");
            assert_eq!(decls[0].arity, 1);
            assert_eq!(decls[1].name.node, "G");
            assert_eq!(decls[1].arity, 2);
        }
        other => panic!("Expected Recursive unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_recursive_no_params() {
    let source = r"---- MODULE Test ----
RECURSIVE Foo
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 1);

    match &module.units[0].node {
        Unit::Recursive(decls) => {
            assert_eq!(decls.len(), 1);
            assert_eq!(decls[0].name.node, "Foo");
            assert_eq!(decls[0].arity, 0);
        }
        other => panic!("Expected Recursive unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_recursive_with_definition() {
    // Test RECURSIVE followed by actual definition
    let source = r"---- MODULE Test ----
RECURSIVE Factorial(_)
Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n - 1)
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");
    assert_eq!(module.units.len(), 2);

    // First unit: RECURSIVE declaration
    match &module.units[0].node {
        Unit::Recursive(decls) => {
            assert_eq!(decls.len(), 1);
            assert_eq!(decls[0].name.node, "Factorial");
            assert_eq!(decls[0].arity, 1);
        }
        other => panic!("Expected Recursive unit, got {other:?}"),
    }

    // Second unit: actual definition
    match &module.units[1].node {
        Unit::Operator(op) => {
            assert_eq!(op.name.node, "Factorial");
            assert_eq!(op.params.len(), 1);
        }
        other => panic!("Expected Operator unit, got {other:?}"),
    }
}
