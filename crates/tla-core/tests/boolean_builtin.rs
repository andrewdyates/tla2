// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_core::{lower, parse_to_syntax_tree, resolve, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn boolean_is_resolvable_without_extends() {
    // BOOLEAN is a core TLA+/TLC builtin, and the parser lowers it to an identifier.
    // It must be resolvable even when a module doesn't EXTEND any stdlib modules.
    let src = r"
---- MODULE Test ----
S == {1}
BoolSet == BOOLEAN
TypeOK == [x: BOOLEAN]
FuncSet == [S -> BOOLEAN]
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

    let boolean_symbols: Vec<_> = result
        .symbols
        .iter()
        .filter(|s| s.name == "BOOLEAN" && s.kind == tla_core::SymbolKind::Constant)
        .collect();
    assert_eq!(
        boolean_symbols.len(),
        1,
        "BOOLEAN symbols: {boolean_symbols:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn boolean_is_not_duplicated_when_extending_stdlib() {
    let src = r"
---- MODULE Test ----
EXTENDS TLC
S == {1}
BoolSet == BOOLEAN
TypeOK == [x: BOOLEAN]
FuncSet == [S -> BOOLEAN]
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

    let boolean_symbols: Vec<_> = result
        .symbols
        .iter()
        .filter(|s| s.name == "BOOLEAN" && s.kind == tla_core::SymbolKind::Constant)
        .collect();
    assert_eq!(
        boolean_symbols.len(),
        1,
        "BOOLEAN symbols: {boolean_symbols:?}"
    );
}
