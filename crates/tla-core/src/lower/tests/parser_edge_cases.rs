// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

use crate::name_intern::NameId;
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_bullet_list_then_implies_layout() {
    let source = r"---- MODULE Test ----
A == TRUE
B == TRUE
C == FALSE
Expr ==
  /\ /\ A
 /\ B
 => C
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    let expr_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Expr" => Some(def),
            _ => None,
        })
        .expect("Expected Expr operator");

    match &expr_def.body.node {
        Expr::Implies(lhs, rhs) => {
            assert!(matches!(&rhs.node, Expr::Ident(name, NameId::INVALID) if name == "C"));
            match &lhs.node {
                Expr::And(a, b) => {
                    assert!(matches!(&a.node, Expr::Ident(name, NameId::INVALID) if name == "A"));
                    assert!(matches!(&b.node, Expr::Ident(name, NameId::INVALID) if name == "B"));
                }
                other => panic!("Expected And(A, B) antecedent, got {other:?}"),
            }
        }
        other => panic!("Expected Implies expression, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_multi_char_infix_operator_use() {
    let source = r"---- MODULE Test ----
Op == 2 ++ 3
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
        Expr::Apply(op, args) => {
            assert!(matches!(&op.node, Expr::Ident(name, NameId::INVALID) if name == "++"));
            assert_eq!(args.len(), 2);
        }
        other => panic!("Expected Apply for ++ infix, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_ordering_relation_operator_use() {
    let source = r"---- MODULE Test ----
Op == 1 \prec 2
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
        Expr::Apply(op, args) => {
            assert!(matches!(&op.node, Expr::Ident(name, NameId::INVALID) if name == "\\prec"));
            assert_eq!(args.len(), 2);
        }
        other => panic!("Expected Apply for \\prec, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_infix_operator_def() {
    let source = r"---- MODULE Test ----
a \prec b == a < b
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    match &module.units[0].node {
        Unit::Operator(def) => {
            assert_eq!(def.name.node, "\\prec");
            assert_eq!(def.params.len(), 2);
            assert_eq!(def.params[0].name.node, "a");
            assert_eq!(def.params[1].name.node, "b");
            assert!(matches!(&def.body.node, Expr::Lt(_, _)));
        }
        other => panic!("Expected Operator unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_underscore_prefixed_let_def_and_ref() {
    let source = r"---- MODULE Test ----
Op == LET _msgs == 1 IN _msgs
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
        Expr::Let(defs, inner) => {
            assert_eq!(defs.len(), 1);
            assert_eq!(defs[0].name.node, "_msgs");
            assert!(matches!(&inner.node, Expr::Ident(name, NameId::INVALID) if name == "_msgs"));
        }
        other => panic!("Expected LET expression, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_underscore_ident_as_except_base() {
    let source = r"---- MODULE Test ----
Op == LET _msgs == [msgs EXCEPT ![self] = @ \ {id}]
  IN [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
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
        Expr::Let(_defs, inner) => match &inner.node {
            Expr::Except(base, _specs) => {
                assert!(
                    matches!(&base.node, Expr::Ident(name, NameId::INVALID) if name == "_msgs")
                );
            }
            other => panic!("Expected EXCEPT expression, got {other:?}"),
        },
        other => panic!("Expected LET expression, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_colon_eq_operator() {
    // Regression test for #446: ColonEqOp added but untested
    // The := operator is used by Apalache for assignment
    let source = r"---- MODULE Test ----
Op == x := 1
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    // Should parse and lower without errors
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    // The operator should be lowered as Apply(":=", [x, 1])
    match &module.units[0].node {
        Unit::Operator(def) => {
            assert_eq!(def.name.node, "Op");
            match &def.body.node {
                Expr::Apply(op, args) => {
                    assert!(matches!(&op.node, Expr::Ident(name, NameId::INVALID) if name == ":="));
                    assert_eq!(args.len(), 2);
                }
                other => panic!("Expected Apply for :=, got {other:?}"),
            }
        }
        other => panic!("Expected Operator unit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_double_underscore_subscript() {
    // Regression test for #449: trim_start_matches('_') may over-strip double-underscore identifiers
    // Only the first underscore (subscript marker) should be stripped, preserving Apalache identifiers
    //
    // TLC semantics: [A]_v == A \/ UNCHANGED v
    // So [A]__vars should lower to: A \/ UNCHANGED _vars (not UNCHANGED vars)
    let source = r"---- MODULE Test ----
VARIABLES x
Op == [A]__vars
====";
    let tree = parse_to_syntax_tree(source);
    let result = lower(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let module = result.module.expect("Expected module");

    // Find the Op definition
    let op_def = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(def) = &u.node {
                if def.name.node == "Op" {
                    Some(def)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .expect("Op definition should exist");

    // [A]_v is lowered to A \/ UNCHANGED v
    // So [A]__vars becomes A \/ UNCHANGED _vars
    // The subscript variable _vars should be inside the UNCHANGED expression
    match &op_def.body.node {
        Expr::Or(_, unchanged_side) => {
            match &unchanged_side.node {
                Expr::Unchanged(inner) => {
                    // The subscript should be _vars (one underscore stripped from __vars)
                    match &inner.node {
                        Expr::Ident(name, NameId::INVALID) => {
                            assert_eq!(
                                name, "_vars",
                                "Expected subscript '_vars' but got '{name}'. Only first underscore should be stripped."
                            );
                        }
                        other => panic!("Expected Ident in UNCHANGED, got {other:?}"),
                    }
                }
                other => panic!("Expected UNCHANGED on right side of Or, got {other:?}"),
            }
        }
        other => panic!("Expected Or expression ([A]_v == A \\/ UNCHANGED v), got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_func_operator_with_tuple_pattern() {
    // f[<<a, b>> \in S \X T] == a + b → FuncDef with Tuple pattern, Times domain, Add body
    let src = "---- MODULE Test ----\nEXTENDS Integers\n\nf[<<a, b>> \\in {1, 2} \\X {1, 2}] == a + b\n====";
    let tree = crate::parse_to_syntax_tree(src);
    let lower_result = crate::lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("Module should be present");
    let op_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node == "f" => Some(def),
            _ => None,
        })
        .expect("Should have operator def 'f'");

    let (bound_vars, body) = match &op_def.body.node {
        Expr::FuncDef(bv, b) => (bv, b),
        other => panic!("Expected FuncDef, got {other:?}"),
    };
    assert_eq!(bound_vars.len(), 1, "Should have 1 bound variable");
    assert_tuple_pattern_and_domain(&bound_vars[0]);
    assert_add_body(&body.node);
}

fn assert_tuple_pattern_and_domain(bv: &crate::ast::BoundVar) {
    match &bv.pattern {
        Some(BoundPattern::Tuple(names)) => {
            assert_eq!(names.len(), 2, "Tuple pattern should have 2 names");
            assert_eq!(names[0].node, "a");
            assert_eq!(names[1].node, "b");
        }
        other => panic!("Expected Tuple pattern, got {other:?}"),
    }
    assert!(bv.domain.is_some(), "Bound var should have a domain");
    assert!(
        matches!(&bv.domain.as_ref().unwrap().node, Expr::Times(parts) if parts.len() == 2),
        "Domain should be Times with 2 parts"
    );
}

fn assert_add_body(expr: &Expr) {
    match expr {
        Expr::Add(lhs, rhs) => {
            assert!(
                matches!(&lhs.node, Expr::Ident(n, NameId::INVALID) if n == "a"),
                "LHS should be 'a'"
            );
            assert!(
                matches!(&rhs.node, Expr::Ident(n, NameId::INVALID) if n == "b"),
                "RHS should be 'b'"
            );
        }
        other => panic!("FuncDef body should be Add, got {other:?}"),
    }
}
