// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

use crate::name_intern::NameId;
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_case_with_other_literal() {
    let source = r"---- MODULE Test ----
Op(x) == CASE x = 0 -> 0 [] OTHER -> 1
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
        Expr::Case(arms, Some(default)) => {
            assert_eq!(arms.len(), 1);
            match &default.node {
                Expr::Int(n) => assert_eq!(n, &BigInt::from(1)),
                other => panic!("Expected Int default, got {other:?}"),
            }
        }
        other => panic!("Expected CASE with OTHER, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_set_expressions() {
    let source = r"---- MODULE Test ----
S == {1, 2, 3}
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::SetEnum(elements) => {
                assert_eq!(elements.len(), 3);
            }
            other => panic!("Expected SetEnum expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_set_builder() {
    // Test SetBuilder (set map) expressions: { expr : x \in S }
    // Bug #367: These failed to parse when the body expression was a simple token (e.g., Ident)
    let source = r"---- MODULE Test ----
MappedS == { x : x \in S }
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(
        result.errors.is_empty(),
        "Lowering errors: {:?}",
        result.errors
    );
    let module = result.module.expect("Expected module");

    assert_eq!(module.units.len(), 1, "Expected 1 unit (operator)");
    match &module.units[0].node {
        Unit::Operator(def) => {
            assert_eq!(def.name.node, "MappedS");
            match &def.body.node {
                Expr::SetBuilder(body, bounds) => {
                    assert_eq!(bounds.len(), 1);
                    assert_eq!(bounds[0].name.node, "x");
                    assert!(matches!(&body.node, Expr::Ident(s, NameId::INVALID) if s == "x"));
                }
                other => panic!("Expected SetBuilder expression, got {other:?}"),
            }
        }
        other => panic!("Expected Operator unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_function_def() {
    let source = r"---- MODULE Test ----
f == [x \in Nat |-> x * 2]
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::FuncDef(bounds, _) => {
                assert_eq!(bounds.len(), 1);
                assert_eq!(bounds[0].name.node, "x");
            }
            other => panic!("Expected FuncDef expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_function_def_multi_var_domain_propagation() {
    let source = r"---- MODULE Test ----
f == [x, y \in Nat |-> x + y]
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::FuncDef(bounds, _) => {
                assert_eq!(bounds.len(), 2);
                assert_eq!(bounds[0].name.node, "x");
                assert_eq!(bounds[1].name.node, "y");
                let x_domain = bounds[0].domain.as_ref().expect("x domain");
                let y_domain = bounds[1].domain.as_ref().expect("y domain");
                assert!(matches!(&x_domain.node, Expr::Ident(s, NameId::INVALID) if s == "Nat"));
                assert!(matches!(&y_domain.node, Expr::Ident(s, NameId::INVALID) if s == "Nat"));
            }
            other => panic!("Expected FuncDef expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_record() {
    let source = r"---- MODULE Test ----
r == [a |-> 1, b |-> 2]
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::Record(fields) => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0.node, "a");
                assert_eq!(fields[1].0.node, "b");
            }
            other => panic!("Expected Record expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_record_set() {
    // Test lowering of record set expression [field: BOOLEAN]
    // BOOLEAN is a keyword and needs special handling
    let source = r"---- MODULE Test ----
r == [smoking: BOOLEAN]
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::RecordSet(fields) => {
                assert_eq!(fields.len(), 1, "Expected 1 field");
                assert_eq!(fields[0].0.node, "smoking");
                // The value should be Ident("BOOLEAN")
                assert!(
                    matches!(fields[0].1.node, Expr::Ident(ref s, NameId::INVALID) if s == "BOOLEAN")
                );
            }
            other => panic!("Expected RecordSet expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_simple_func_apply() {
    // Test: G == F[1] (no parameters, literal argument)
    // The argument 1 is a Number token that needs special handling
    let source = r"---- MODULE Test ----
S == {1, 2}
F == [r \in S |-> r * 10]
G == F[1]
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    // Find all operators
    let ops: Vec<_> = module
        .units
        .iter()
        .filter_map(|u| {
            if let Unit::Operator(def) = &u.node {
                Some((def.name.node.clone(), def.body.node.clone()))
            } else {
                None
            }
        })
        .collect();

    // Should have S, F, and G
    assert_eq!(ops.len(), 3, "Expected 3 operators");

    let g = ops.iter().find(|(n, _)| n == "G").expect("G should exist");
    match &g.1 {
        Expr::FuncApply(func, arg) => {
            // func should be Ident("F")
            assert!(matches!(&func.node, Expr::Ident(s, NameId::INVALID) if s == "F"));
            // arg should be Int(1)
            assert!(matches!(&arg.node, Expr::Int(n) if *n == BigInt::from(1)));
        }
        other => panic!("G should be FuncApply, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_multi_arg_func_apply_as_tuple() {
    let source = r"---- MODULE Test ----
G == F[1, 2]
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::FuncApply(func, arg) => {
                assert!(matches!(&func.node, Expr::Ident(s, NameId::INVALID) if s == "F"));
                match &arg.node {
                    Expr::Tuple(elements) => {
                        assert_eq!(elements.len(), 2);
                        assert!(matches!(&elements[0].node, Expr::Int(n) if *n == BigInt::from(1)));
                        assert!(matches!(&elements[1].node, Expr::Int(n) if *n == BigInt::from(2)));
                    }
                    other => {
                        panic!("Expected tuple arg for multi-index apply, got {other:?}")
                    }
                }
            }
            other => panic!("Expected FuncApply expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_if_then_else() {
    let source = r"---- MODULE Test ----
Max(a, b) == IF a > b THEN a ELSE b
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::If(_, _, _) => {}
            other => panic!("Expected If expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_tuple() {
    let source = r"---- MODULE Test ----
t == <<1, 2, 3>>
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => match &def.body.node {
            Expr::Tuple(elements) => {
                assert_eq!(elements.len(), 3);
            }
            other => panic!("Expected Tuple expression, got {other:?}"),
        },
        _ => panic!("Expected Operator unit"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_func_constructor_in_equality() {
    // Test: Init == pc = [p \in S |-> "b0"]
    // This pattern is common in specs like Barrier and CigaretteSmokers
    let source = r#"---- MODULE Test ----
VARIABLE pc
Init == pc = [p \in {1,2} |-> "b0"]
===="#;
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    // Find Init operator
    let init_op = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(op) = &u.node {
                if op.name.node == "Init" {
                    return Some(op);
                }
            }
            None
        })
        .expect("Expected Init operator");

    // The body should be Eq(Ident("pc"), FuncDef(...)), not just Ident("pc")
    match &init_op.body.node {
        Expr::Eq(lhs, rhs) => {
            assert!(
                matches!(&lhs.node, Expr::Ident(name, NameId::INVALID) if name == "pc"),
                "Expected lhs to be Ident(pc), got {:?}",
                lhs.node
            );
            assert!(
                matches!(&rhs.node, Expr::FuncDef(_, _)),
                "Expected rhs to be FuncDef, got {:?}",
                rhs.node
            );
        }
        other => panic!("Expected Init body to be Eq(...), got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_func_set_with_ident_domain() {
    // Test: TypeOK == pc \in [ProcSet -> {"b0", "b1"}]
    // The domain is an identifier reference, not a literal set
    let source = r#"---- MODULE Test ----
ProcSet == {1, 2, 3}
TypeOK == pc \in [ProcSet -> {"b0"}]
===="#;
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    // Find TypeOK operator
    let type_ok = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(op) = &u.node {
                if op.name.node == "TypeOK" {
                    return Some(op);
                }
            }
            None
        })
        .expect("Expected TypeOK operator");

    // The body should be In(Ident("pc"), FuncSet(Ident("ProcSet"), {...}))
    match &type_ok.body.node {
        Expr::In(lhs, rhs) => {
            assert!(
                matches!(&lhs.node, Expr::Ident(name, NameId::INVALID) if name == "pc"),
                "Expected lhs to be Ident(pc), got {:?}",
                lhs.node
            );
            match &rhs.node {
                Expr::FuncSet(domain, _range) => {
                    assert!(
                        matches!(&domain.node, Expr::Ident(name, NameId::INVALID) if name == "ProcSet"),
                        "Expected domain to be Ident(ProcSet), got {:?}",
                        domain.node
                    );
                }
                other => panic!("Expected rhs to be FuncSet, got {other:?}"),
            }
        }
        other => panic!("Expected TypeOK body to be In(...), got {other:?}"),
    }
}
