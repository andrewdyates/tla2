// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ast::{Module, OperatorDef};
use crate::lower::{compute_contains_prime, compute_guards_depend_on_prime, lower_all_modules};
use crate::span::FileId;
use crate::syntax::parse_to_syntax_tree;

fn lower_named_test_module(source: &str, name: &str) -> Module {
    let tree = parse_to_syntax_tree(source);
    let result = lower_all_modules(FileId(0), &tree);

    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    result
        .modules
        .into_iter()
        .find(|module| module.name.node == name)
        .unwrap_or_else(|| panic!("Expected module {name}"))
}

fn find_operator<'a>(module: &'a Module, name: &str) -> &'a OperatorDef {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == name => Some(def),
            _ => None,
        })
        .unwrap_or_else(|| panic!("Expected operator {name}"))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parameterized_module_ref_target_primes_flow_into_metadata() {
    let source = r"
---- MODULE Test ----
VARIABLE x

---- MODULE Inner ----
VARIABLE y
Safe == y \in {0, 1}
====

P(value) == INSTANCE Inner WITH y <- value
Guarded == P(x')!Safe /\ TRUE
====
";

    let mut module = lower_named_test_module(source, "Test");
    compute_contains_prime(&mut module);
    compute_guards_depend_on_prime(&mut module);

    let guarded = find_operator(&module, "Guarded");
    // `x'` appears in the ModuleTarget (`P(x')!Safe`), not as a call arg.
    assert!(
        guarded.contains_prime,
        "primes in parameterized module-ref targets must mark contains_prime"
    );
    assert!(
        guarded.guards_depend_on_prime,
        "primes in parameterized module-ref targets must mark guards_depend_on_prime"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_chained_module_ref_target_primes_flow_into_metadata() {
    let source = r"
---- MODULE Test ----
VARIABLE x

---- MODULE Inner ----
VARIABLE y
Safe == P0:: (y \in {0, 1})
====

P(value) == INSTANCE Inner WITH y <- value
Guarded == P(x')!Safe!P0 /\ TRUE
====
";

    let mut module = lower_named_test_module(source, "Test");
    compute_contains_prime(&mut module);
    compute_guards_depend_on_prime(&mut module);

    let guarded = find_operator(&module, "Guarded");
    assert!(
        guarded.contains_prime,
        "primes in chained module-ref bases must mark contains_prime"
    );
    assert!(
        guarded.guards_depend_on_prime,
        "primes in chained module-ref bases must mark guards_depend_on_prime"
    );
}
