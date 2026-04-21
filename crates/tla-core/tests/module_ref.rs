// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_core::ast::{Expr, Unit};
use tla_core::name_intern::NameId;
use tla_core::{lower, parse_to_syntax_tree, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_module_ref_extracts_module_and_operator_name() {
    let source = r"
---- MODULE Main ----
Foo == Bar!Baz
FooArgs == Bar!Baz(1, 2)
AtArgs == BagAdd(@, x)
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

    let mut saw_foo = false;
    let mut saw_foo_args = false;
    let mut saw_at_args = false;

    for unit in &module.units {
        let Unit::Operator(def) = &unit.node else {
            continue;
        };

        match def.name.node.as_str() {
            "Foo" => {
                let Expr::ModuleRef(module_target, op_name, args) = &def.body.node else {
                    panic!(
                        "expected Foo body to be ModuleRef, got: {:?}",
                        def.body.node
                    );
                };
                assert_eq!(module_target.name(), "Bar");
                assert_eq!(op_name, "Baz");
                assert!(args.is_empty());
                saw_foo = true;
            }
            "FooArgs" => {
                let Expr::ModuleRef(module_target, op_name, args) = &def.body.node else {
                    panic!(
                        "expected FooArgs body to be ModuleRef, got: {:?}",
                        def.body.node
                    );
                };
                assert_eq!(module_target.name(), "Bar");
                assert_eq!(op_name, "Baz");
                assert_eq!(args.len(), 2);
                saw_foo_args = true;
            }
            "AtArgs" => {
                let Expr::Apply(op, args) = &def.body.node else {
                    panic!("expected AtArgs body to be Apply, got: {:?}", def.body.node);
                };
                assert_eq!(args.len(), 2);
                let Expr::Ident(op_name, NameId::INVALID) = &op.node else {
                    panic!("expected AtArgs operator to be Ident, got: {:?}", op.node);
                };
                assert_eq!(op_name, "BagAdd");
                let Expr::Ident(arg0, NameId::INVALID) = &args[0].node else {
                    panic!("expected AtArgs arg0 to be Ident, got: {:?}", args[0].node);
                };
                assert_eq!(arg0, "@");
                let Expr::Ident(arg1, NameId::INVALID) = &args[1].node else {
                    panic!("expected AtArgs arg1 to be Ident, got: {:?}", args[1].node);
                };
                assert_eq!(arg1, "x");
                saw_at_args = true;
            }
            _ => {}
        }
    }

    assert!(saw_foo, "did not find operator Foo");
    assert!(saw_foo_args, "did not find operator FooArgs");
    assert!(saw_at_args, "did not find operator AtArgs");
}
