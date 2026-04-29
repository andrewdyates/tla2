// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_core::ast::{Expr, Unit};
use tla_core::{collect_conjuncts_v, lower, parse_to_syntax_tree, FileId};

fn find_operator<'a>(
    module: &'a tla_core::ast::Module,
    name: &str,
) -> &'a tla_core::ast::OperatorDef {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == name => Some(def),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operator {name} not found"))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_labelled_subexpression_preserves_label_wrapper() {
    let source = r"
---- MODULE Main ----
Inv ==
  /\ P0:: counter = 0
  /\ counter <= 1
Pick == Inv!P0
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
    let inv = find_operator(&module, "Inv");
    let conjuncts = collect_conjuncts_v(&inv.body);
    assert_eq!(conjuncts.len(), 2, "expected two top-level conjuncts");

    let Expr::Label(label) = &conjuncts[0].node else {
        panic!(
            "expected first conjunct to preserve Label wrapper, got {:?}",
            conjuncts[0].node
        );
    };
    assert_eq!(label.name.node, "P0");
    assert!(
        matches!(label.body.node, Expr::Eq(_, _)),
        "expected label body to wrap the full equality, got {:?}",
        label.body.node
    );

    let pick = find_operator(&module, "Pick");
    let Expr::ModuleRef(target, op_name, args) = &pick.body.node else {
        panic!(
            "expected Pick body to be ModuleRef, got {:?}",
            pick.body.node
        );
    };
    assert_eq!(target.name(), "Inv");
    assert_eq!(op_name, "P0");
    assert!(args.is_empty(), "label selectors should stay zero-arg");
}

/// Regression test for #3125: labeled disjunction with simple identifier body.
///
/// When a label body is a bare identifier (e.g., `RealInv:: Inv`), the lowering
/// code dropped the entire label because it only looked for child *nodes*, not
/// tokens. This caused `\/ RealInv:: Inv \/ Export:: ...` to lose the first
/// disjunct entirely.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn lower_labeled_disjunction_with_ident_body_preserves_or() {
    let source = r"
---- MODULE Main ----
VARIABLE x
Inv == x >= 0
JsonInv ==
    \/ RealInv:: Inv
    \/ Export:: x = 42
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
    let json_inv = find_operator(&module, "JsonInv");

    // The body should be Or(Label("RealInv", Ident("Inv")), Label("Export", Eq(x, 42)))
    let Expr::Or(left, right) = &json_inv.body.node else {
        panic!(
            "expected JsonInv body to be Or, got {:?}",
            json_inv.body.node
        );
    };

    // First disjunct: RealInv:: Inv
    let Expr::Label(real_inv_label) = &left.node else {
        panic!("expected first disjunct to be Label, got {:?}", left.node);
    };
    assert_eq!(real_inv_label.name.node, "RealInv");
    assert!(
        matches!(real_inv_label.body.node, Expr::Ident(ref name, _) if name == "Inv"),
        "expected RealInv label body to be Ident(\"Inv\"), got {:?}",
        real_inv_label.body.node
    );

    // Second disjunct: Export:: x = 42
    let Expr::Label(export_label) = &right.node else {
        panic!("expected second disjunct to be Label, got {:?}", right.node);
    };
    assert_eq!(export_label.name.node, "Export");
    assert!(
        matches!(export_label.body.node, Expr::Eq(_, _)),
        "expected Export label body to be Eq, got {:?}",
        export_label.body.node
    );
}
