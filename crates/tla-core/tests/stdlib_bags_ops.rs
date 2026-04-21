// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Andrew Yates

use tla_core::{lower, parse_to_syntax_tree, resolve, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn bags_parenthesized_ops_resolve_via_stdlib_aliases() {
    let source = r"
        ---- MODULE M ----
        EXTENDS Bags
        CONSTANTS B1, B2

        ASSUME B1 (+) B2 = B1
        ASSUME B1 (-) B2 = B1
        ASSUME B1 \sqsubseteq B2

        ASSUME BagCup(B1, B2) = B1
        ASSUME BagDiff(B1, B2) = B1
        ASSUME SqSubseteq(B1, B2)
        ====
    ";

    let tree = parse_to_syntax_tree(source);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );

    let module = lowered.module.expect("expected lowered module");
    assert_eq!(
        module
            .extends
            .iter()
            .map(|m| m.node.as_str())
            .collect::<Vec<_>>(),
        vec!["Bags"],
        "expected EXTENDS Bags to be lowered into module.extends"
    );

    let bags_ops = tla_core::get_module_operators("Bags");
    assert!(
        bags_ops
            .iter()
            .any(|(name, arity)| *name == "\\oplus" && *arity == 2),
        "expected stdlib Bags operators to include \\\\oplus; got: {bags_ops:?}"
    );
    assert!(
        bags_ops
            .iter()
            .any(|(name, arity)| *name == "\\ominus" && *arity == 2),
        "expected stdlib Bags operators to include \\\\ominus; got: {bags_ops:?}"
    );
    assert!(
        bags_ops
            .iter()
            .any(|(name, arity)| *name == "\\sqsubseteq" && *arity == 2),
        "expected stdlib Bags operators to include \\\\sqsubseteq; got: {bags_ops:?}"
    );

    let resolved = resolve(&module);
    assert!(
        resolved.errors.is_empty(),
        "expected Bags operators to resolve via stdlib injection, got: {:?}",
        resolved.errors
    );
}
