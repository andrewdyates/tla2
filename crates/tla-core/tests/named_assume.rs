// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_core::{
    lower, parse_to_syntax_tree, resolve, resolve_with_extends, resolve_with_extends_and_instances,
    FileId,
};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn named_assume_introduces_resolvable_symbol() {
    let src = r"
---- MODULE Test ----
ASSUME Foo == TRUE
Op == Foo
====
";

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("lower produced no module");

    let result = resolve(&module);
    assert!(result.is_ok(), "resolve errors: {:?}", result.errors);

    let foo_symbols: Vec<_> = result
        .symbols
        .iter()
        .filter(|s| s.name == "Foo" && s.kind == tla_core::SymbolKind::Operator && s.arity == 0)
        .collect();
    assert_eq!(foo_symbols.len(), 1, "Foo symbols: {foo_symbols:?}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn named_assume_conflicts_with_operator_definition() {
    let src = r"
---- MODULE Test ----
ASSUME Foo == TRUE
Foo == TRUE
====
";

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("lower produced no module");

    let result = resolve(&module);
    assert!(!result.is_ok(), "expected resolve error(s)");
    assert!(
        result.errors.iter().any(|e| matches!(
            &e.kind,
            tla_core::ResolveErrorKind::Duplicate { name, .. } if name == "Foo"
        )),
        "resolve errors: {:?}",
        result.errors
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn named_assume_is_visible_via_extends_in_resolve_with_extends() {
    let a_src = r"
---- MODULE A ----
ASSUME Foo == TRUE
====
";
    let b_src = r"
---- MODULE B ----
EXTENDS A
Op == Foo
====
";

    let a_tree = parse_to_syntax_tree(a_src);
    let a_lower = lower(FileId(0), &a_tree);
    assert!(
        a_lower.errors.is_empty(),
        "lower errors: {:?}",
        a_lower.errors
    );
    let a = a_lower.module.expect("lower produced no module");

    let b_tree = parse_to_syntax_tree(b_src);
    let b_lower = lower(FileId(1), &b_tree);
    assert!(
        b_lower.errors.is_empty(),
        "lower errors: {:?}",
        b_lower.errors
    );
    let b = b_lower.module.expect("lower produced no module");

    let result = resolve_with_extends(&b, &[&a]);
    assert!(result.is_ok(), "resolve errors: {:?}", result.errors);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn standalone_instance_imports_public_operators_into_unqualified_scope() {
    let a_src = r"
---- MODULE A ----
CONSTANT C
VARIABLE v
Foo == v
====
";
    let b_src = r"
---- MODULE B ----
CONSTANT C
VARIABLE v
INSTANCE A
Op == Foo
====
";

    let a_tree = parse_to_syntax_tree(a_src);
    let a_lower = lower(FileId(0), &a_tree);
    assert!(
        a_lower.errors.is_empty(),
        "lower errors: {:?}",
        a_lower.errors
    );
    let a = a_lower.module.expect("lower produced no module");

    let b_tree = parse_to_syntax_tree(b_src);
    let b_lower = lower(FileId(1), &b_tree);
    assert!(
        b_lower.errors.is_empty(),
        "lower errors: {:?}",
        b_lower.errors
    );
    let b = b_lower.module.expect("lower produced no module");

    let result = resolve_with_extends_and_instances(&b, &[], &[&a]);
    assert!(result.is_ok(), "resolve errors: {:?}", result.errors);
}
