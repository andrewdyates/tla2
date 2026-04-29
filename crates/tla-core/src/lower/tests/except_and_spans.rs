// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

use crate::name_intern::NameId;
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_func_apply_body() {
    // Test that p[1] in operator body lowers to FuncApply(Ident("p"), Int(1))
    let src = r"
---- MODULE Test ----
f(p) == p[1]
====
";
    let tree = crate::parse_to_syntax_tree(src);
    let lower_result = crate::lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Expected no lowering errors, got: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("Module should be present");
    let op_def = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(def) = &u.node {
                if def.name.node == "f" {
                    Some(def)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .expect("Should have operator def 'f'");

    // Verify parameter
    assert_eq!(op_def.params.len(), 1, "f should have 1 parameter");
    assert_eq!(op_def.params[0].name.node, "p");

    // Verify body is FuncApply(Ident("p"), Int(1))
    match &op_def.body.node {
        Expr::FuncApply(func, arg) => {
            assert!(
                matches!(&func.node, Expr::Ident(name, NameId::INVALID) if name == "p"),
                "Function should be Ident(\"p\"), got {:?}",
                func.node
            );
            assert!(
                matches!(&arg.node, Expr::Int(n) if n == &num_bigint::BigInt::from(1)),
                "Argument should be Int(1), got {:?}",
                arg.node
            );
        }
        other => panic!("Expected FuncApply for p[1], got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_except_nested_path() {
    // Tests that [smokers EXCEPT ![r].smoking = FALSE] lowers with correct EXCEPT structure:
    // - base should be Ident("smokers")
    // - spec path should contain key [r] and field .smoking
    // - spec value should be Bool(false)
    let src = r"
---- MODULE Test ----
VARIABLE smokers, r
Test == smokers' = [smokers EXCEPT ![r].smoking = FALSE]
====
";
    let tree = crate::parse_to_syntax_tree(src);
    let lower_result = crate::lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Expected no lowering errors, got: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("Module should be present");
    let op_def = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(def) = &u.node {
                if def.name.node == "Test" {
                    Some(def)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .expect("Should have operator def 'Test'");

    // Body should be Eq(Prime(smokers), Except(...))
    match &op_def.body.node {
        Expr::Eq(_, rhs) => {
            match &rhs.node {
                Expr::Except(base, specs) => {
                    assert!(
                        matches!(&base.node, Expr::Ident(name, NameId::INVALID) if name == "smokers"),
                        "EXCEPT base should be Ident(\"smokers\"), got {:?}",
                        base.node
                    );
                    assert_eq!(specs.len(), 1, "Should have exactly 1 EXCEPT spec");
                    // The value should be Bool(false)
                    assert!(
                        matches!(&specs[0].value.node, Expr::Bool(false)),
                        "EXCEPT value should be Bool(false), got {:?}",
                        specs[0].value.node
                    );
                    // Path should have at least 2 components (![r] and .smoking)
                    assert!(
                        specs[0].path.len() >= 2,
                        "EXCEPT path should have >= 2 components for ![r].smoking, got {}",
                        specs[0].path.len()
                    );
                }
                other => panic!("RHS should be EXCEPT expression, got {other:?}"),
            }
        }
        other => panic!("Body should be Eq expression, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_except_at_index() {
    // Tests that @[idx] in EXCEPT expressions is correctly lowered to FuncApply(Ident("@"), idx)
    // This is essential for patterns like: [f EXCEPT ![k] = @[1]] where @ refers to the old value
    let src = r"
---- MODULE Test ----
Test == [[i \in {1} |-> 0] EXCEPT ![1] = @[1]]
====
";
    let tree = crate::parse_to_syntax_tree(src);
    let lower_result = crate::lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Expected no lowering errors"
    );

    let module = lower_result.module.expect("Module should be present");
    let op_def = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(def) = &u.node {
                Some(def)
            } else {
                None
            }
        })
        .expect("Should have operator def");

    // The body should be Except with a spec that has FuncApply(@, 1) as the value
    if let Expr::Except(_, specs) = &op_def.body.node {
        assert_eq!(specs.len(), 1, "Should have 1 except spec");
        // Check that the value is FuncApply(Ident("@"), Int(1))
        if let Expr::FuncApply(func, arg) = &specs[0].value.node {
            assert!(
                matches!(&func.node, Expr::Ident(s, NameId::INVALID) if s == "@"),
                "Function should be @ identifier"
            );
            assert!(
                matches!(&arg.node, Expr::Int(n) if n == &num_bigint::BigInt::from(1)),
                "Argument should be Int(1)"
            );
        } else {
            panic!("Expected FuncApply for @[1], got {:?}", specs[0].value.node);
        }
    } else {
        panic!("Expected Except expression");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_except_if_then_else() {
    // Tests that [y EXCEPT ![0] = IF 1 > 0 THEN "b" ELSE @] lowers with:
    // - base = Ident("y")
    // - 1 EXCEPT spec with value being an If expression
    // - THEN branch = String("b"), ELSE branch = Ident("@")
    let src = r#"
---- MODULE Test ----
VARIABLES y
Next == y' = [y EXCEPT ![0] = IF 1 > 0 THEN "b" ELSE @]
====
"#;
    let tree = crate::parse_to_syntax_tree(src);
    let lower_result = crate::lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Expected no lowering errors, got: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("Module should be present");
    let op_def = module
        .units
        .iter()
        .find_map(|u| {
            if let Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    Some(def)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .expect("Should have operator def 'Next'");

    // Body should be Eq(Prime(y), Except(y, specs))
    match &op_def.body.node {
        Expr::Eq(_, rhs) => {
            match &rhs.node {
                Expr::Except(base, specs) => {
                    assert!(
                        matches!(&base.node, Expr::Ident(name, NameId::INVALID) if name == "y"),
                        "EXCEPT base should be Ident(\"y\"), got {:?}",
                        base.node
                    );
                    assert_eq!(specs.len(), 1, "Expected 1 EXCEPT spec");
                    // The spec value should be an If expression
                    match &specs[0].value.node {
                        Expr::If(_, then_branch, else_branch) => {
                            assert!(
                                matches!(&then_branch.node, Expr::String(s) if s == "b"),
                                "THEN branch should be String(\"b\"), got {:?}",
                                then_branch.node
                            );
                            assert!(
                                matches!(&else_branch.node, Expr::Ident(name, NameId::INVALID) if name == "@"),
                                "ELSE branch should be Ident(\"@\"), got {:?}",
                                else_branch.node
                            );
                        }
                        other => {
                            panic!("EXCEPT spec value should be If expression, got {other:?}")
                        }
                    }
                }
                other => panic!("RHS should be EXCEPT expression, got {other:?}"),
            }
        }
        other => panic!("Body should be Eq expression, got {other:?}"),
    }
}

/// Regression test for span offset correctness after whitespace fix
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_span_offsets_correct() {
    let source = "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 5 /\\ x' = x + 1\nInRange == x >= 0 /\\ x <= 5\n====";

    // Expected positions in source
    let init_body_start = source.find("x = 0").expect("x = 0 not found");
    let next_body_start = source.find("x < 5").expect("x < 5 not found");

    // Parse and lower
    let tree = crate::parse_to_syntax_tree(source);
    let result = crate::lower(FileId(0), &tree);
    let module = result.module.expect("Expected module");

    // Verify spans point to correct source text
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let body_start = def.body.span.start as usize;
            let body_end = def.body.span.end as usize;

            match def.name.node.as_str() {
                "Init" => {
                    assert_eq!(
                        body_start, init_body_start,
                        "Init body span start should match 'x = 0' position"
                    );
                    let text = &source[body_start..body_end];
                    assert!(
                        text.starts_with("x = 0"),
                        "Init body should start with 'x = 0', got: {text:?}"
                    );
                }
                "Next" => {
                    assert_eq!(
                        body_start, next_body_start,
                        "Next body span start should match 'x < 5' position"
                    );
                    let text = &source[body_start..body_end];
                    assert!(
                        text.starts_with("x < 5"),
                        "Next body should start with 'x < 5', got: {text:?}"
                    );
                }
                _ => {}
            }
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_nested_except_with_deep_path() {
    // Tests that nested EXCEPT expressions preserve the full base expression path
    // Bug: [node EXCEPT ![r].insts[1] = [node[r].insts[1] EXCEPT !.status = "x"]]
    // was incorrectly lowering the inner EXCEPT base as node[r] instead of node[r].insts[1]
    //
    // The CST for this pattern has sibling nodes for the postfix operations:
    //   ExceptExpr
    //     FuncApplyExpr: "node[r]"
    //     RecordAccessExpr: ".insts"
    //     FuncApplyExpr: "[1]"
    //     ExceptSpec: "!.status = \"x\""
    //
    // The fix chains these sibling postfix operations onto the base expression.
    let src = r#"
---- MODULE Test ----
VARIABLES node
Op(r) == [node EXCEPT ![r].insts[1] = [node[r].insts[1] EXCEPT !.status = "x"]]
====
"#;
    let tree = crate::parse_to_syntax_tree(src);
    let lower_result = crate::lower(FileId(0), &tree);

    assert!(
        lower_result.errors.is_empty(),
        "Expected no lowering errors, got: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("Module should be present");
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

    let outer_specs = match &op_def.body.node {
        Expr::Except(_, outer_specs) => outer_specs,
        other => panic!("Op body should be EXCEPT expression, got {other:?}"),
    };

    assert_eq!(outer_specs.len(), 1, "Outer EXCEPT should have one spec");
    assert_nested_except_path(&outer_specs[0].value.node);
}

fn assert_nested_except_path(value_expr: &Expr) {
    match value_expr {
        Expr::Except(inner_base, _) => assert_inner_except_base(&inner_base.node),
        other => panic!("Outer EXCEPT value should be inner EXCEPT, got {other:?}"),
    }
}

fn assert_inner_except_base(inner_base: &Expr) {
    match inner_base {
        Expr::FuncApply(inner_func, inner_arg) => {
            assert!(
                matches!(&inner_arg.node, Expr::Int(n) if *n == 1.into()),
                "Expected inner EXCEPT base to end with [1], got arg {:?}",
                inner_arg.node
            );
            assert_inner_except_func(&inner_func.node);
        }
        other => panic!("Inner EXCEPT base should be node[r].insts[1], got {other:?}"),
    }
}

fn assert_inner_except_func(inner_func: &Expr) {
    match inner_func {
        Expr::RecordAccess(rec_base, field) => {
            assert_eq!(
                field.name.node, "insts",
                "Expected .insts field access, got .{}",
                field.name.node
            );
            assert_node_r_path(&rec_base.node);
        }
        other => panic!("Expected node[r].insts as func of [1], got {other:?}"),
    }
}

fn assert_node_r_path(rec_base: &Expr) {
    match rec_base {
        Expr::FuncApply(node_expr, r_expr) => {
            assert!(
                matches!(&node_expr.node, Expr::Ident(name, NameId::INVALID) if name == "node"),
                "Expected 'node', got {:?}",
                node_expr.node
            );
            assert!(
                matches!(&r_expr.node, Expr::Ident(name, NameId::INVALID) if name == "r"),
                "Expected 'r', got {:?}",
                r_expr.node
            );
        }
        other => panic!("Expected node[r] as base of .insts, got {other:?}"),
    }
}
