// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ast::{Module, OperatorDef};
use crate::lower::{compute_contains_prime, compute_guards_depend_on_prime, lower_all_modules};

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
fn test_contains_prime_does_not_mark_opaque_module_ref() {
    // ModuleRef is opaque to intra-module analysis. The referenced operator
    // (I!Step) transitively contains primes, but the static analysis cannot
    // see inside ModuleRef nodes without cross-module resolution.
    // This is intentionally non-conservative: falsely marking external refs
    // as containing primes rejects valid INVARIANT operators (5 medium-spec
    // false positives in #2834/#1653). The evaluator catches actual primes
    // at runtime with better error context.
    let source = r"
---- MODULE Test ----
VARIABLE x

---- MODULE Inner ----
VARIABLE y
Step == y' = y
====

I == INSTANCE Inner
UsesInner == I!Step
====";

    let mut module = lower_named_test_module(source, "Test");
    compute_contains_prime(&mut module);

    assert!(!find_operator(&module, "UsesInner").contains_prime);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_guards_depend_on_prime_marks_module_ref_in_guard() {
    let source = r"
---- MODULE Test ----
VARIABLE x

---- MODULE Inner ----
VARIABLE y
Step == y' = y
====

I == INSTANCE Inner
Guarded == I!Step /\ x' = x
====";

    let mut module = lower_named_test_module(source, "Test");
    compute_contains_prime(&mut module);
    compute_guards_depend_on_prime(&mut module);

    let guarded = find_operator(&module, "Guarded");
    // contains_prime is true from the direct `x' = x` (not from the ModuleRef).
    assert!(guarded.contains_prime);
    // guards_depend_on_prime is false: `I!Step` is opaque (ModuleRef), and
    // `x' = x` is a primed assignment skipped by the guard analyzer. The
    // guards_depend_on_prime flag is perf-only (over-conservative = slower).
    assert!(!guarded.guards_depend_on_prime);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_guards_depend_on_prime_ignores_value_position_module_ref() {
    let source = r"
---- MODULE Test ----
VARIABLE x

---- MODULE Inner ----
VARIABLE y
Step == y' = y
====

I == INSTANCE Inner
ValueOnly == IF TRUE THEN I!Step ELSE FALSE
====";

    let mut module = lower_named_test_module(source, "Test");
    compute_contains_prime(&mut module);
    compute_guards_depend_on_prime(&mut module);

    let value_only = find_operator(&module, "ValueOnly");
    // ModuleRef is opaque: no local primes detected (see first test).
    assert!(!value_only.contains_prime);
    assert!(!value_only.guards_depend_on_prime);
}
