// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_core::ast::{Expr, Unit};
use tla_core::name_intern::NameId;
use tla_core::{lower, parse_to_syntax_tree, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_lambda_expr_with_leaf_body_is_preserved() {
    let source = r"
---- MODULE Test ----
EXTENDS Integers, Bags

Op == BagOfAll(LAMBDA x : 0, 1)
Lam == LAMBDA x : 0
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

    let mut saw_op = false;
    let mut saw_lam = false;

    for unit in &module.units {
        let Unit::Operator(def) = &unit.node else {
            continue;
        };

        match def.name.node.as_str() {
            "Op" => {
                let Expr::Apply(op, args) = &def.body.node else {
                    panic!("expected Op body to be Apply, got: {:?}", def.body.node);
                };
                let Expr::Ident(op_name, NameId::INVALID) = &op.node else {
                    panic!("expected Op operator to be Ident, got: {:?}", op.node);
                };
                assert_eq!(op_name, "BagOfAll");
                assert_eq!(args.len(), 2);
                assert!(matches!(args[0].node, Expr::Lambda(_, _)));
                assert!(matches!(args[1].node, Expr::Int(_)));
                saw_op = true;
            }
            "Lam" => {
                let Expr::Lambda(params, body) = &def.body.node else {
                    panic!("expected Lam body to be Lambda, got: {:?}", def.body.node);
                };
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].node, "x");
                assert!(matches!(body.node, Expr::Int(_)));
                saw_lam = true;
            }
            _ => {}
        }
    }

    assert!(saw_op, "did not find operator Op");
    assert!(saw_lam, "did not find operator Lam");
}
