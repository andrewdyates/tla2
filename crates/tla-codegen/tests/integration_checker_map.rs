// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Checker-map integration tests: CheckerMapConfig, CheckerMapImpl,
//! checker module generation, ToState trait, and is_next validation.

mod common;

use std::collections::BTreeMap;

use common::parse_and_generate;
use tla_codegen::{CheckerMapConfig, CheckerMapImpl, CodeGenOptions};

/// Assert that the generated checker module uses the expected internal implementation patterns.
fn assert_checker_implementation_patterns(code: &str) {
    assert!(
        code.contains("fn is_next(&self, old: &Self::State, new: &Self::State) -> Option<bool>"),
        "Missing transition predicate (is_next)"
    );
    assert!(
        code.contains("if let Some(ok) = machine.is_next(&old_state, &new_state)"),
        "check_transition should prefer is_next before enumerating successors"
    );
    assert!(
        code.contains("let mut successor_count: usize = 0;")
            && code.contains("machine.for_each_next(&old_state, |s| {"),
        "check_transition should fall back to for_each_next when is_next unavailable"
    );
    assert!(
        code.contains("let mut init_count: usize = 0;")
            && code.contains("machine.for_each_init(|s| {"),
        "check_init should use for_each_init to avoid allocating init()"
    );
    assert!(
        !code.contains("machine.init()"),
        "checkers should avoid materializing init state lists via machine.init()"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checker_module_generation() {
    let source = r#"
---- MODULE Counter ----
VARIABLE count

Init == count = 0

Next == count' = count + 1

InvNonNegative == count >= 0
====
"#;

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: false,
        generate_checker: true,
        checker_map: None,
    };
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(code.contains("pub mod checker"), "Missing checker module");
    assert!(
        code.contains("pub trait ToCounterState"),
        "Missing ToCounterState trait"
    );
    assert!(
        code.contains("fn to_counter_state(&self) -> CounterState;"),
        "Missing to_counter_state method"
    );
    assert!(
        code.contains(
            "pub fn check_transition<T: ToCounterState>(old: &T, new: &T) -> Result<(), String>"
        ),
        "Missing transition checker"
    );
    assert!(
        code.contains("pub fn check_init<T: ToCounterState>(value: &T) -> Result<(), String>"),
        "Missing init checker"
    );
    assert!(
        code.contains(
            "pub fn check_transition_or_stutter<T: ToCounterState>(old: &T, new: &T) -> Result<(), String>"
        ),
        "Missing stuttering-aware transition checker"
    );
    assert_checker_implementation_patterns(&code);
    assert!(
        code.contains("pub fn check_inv_non_negative<T: ToCounterState>(value: &T) -> bool"),
        "Missing invariant wrapper"
    );
    assert!(
        code.contains(
            "pub fn violated_invariants<T: ToCounterState>(value: &T) -> Vec<&'static str>"
        ),
        "Missing violated invariants helper"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checker_map_emits_to_state_impl() {
    let source = r#"
---- MODULE Counter ----
VARIABLE count

Init == count = 0

Next == count' = count + 1
====
"#;

    let mut fields = BTreeMap::new();
    fields.insert("count".to_string(), "self.count".to_string());

    let checker_map = CheckerMapConfig {
        spec_module: Some("Counter".to_string()),
        impls: vec![CheckerMapImpl {
            rust_type: "crate::ProdCounter".to_string(),
            fields,
        }],
    };

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: false,
        generate_checker: true,
        checker_map: Some(checker_map),
    };
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("impl checker::ToCounterState for crate::ProdCounter"),
        "Missing generated impl block"
    );
    assert!(
        code.contains("count: self.count, // TLA+ VARIABLE: count"),
        "Missing generated field mapping"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checker_map_accepts_tla_variable_keys_when_snake_case_differs() {
    let source = r#"
---- MODULE WeirdVars ----
VARIABLE FooBar

Init == FooBar = 0

Next == FooBar' = FooBar
====
"#;

    let mut fields = BTreeMap::new();
    fields.insert("FooBar".to_string(), "self.foo_bar".to_string());

    let checker_map = CheckerMapConfig {
        spec_module: Some("WeirdVars".to_string()),
        impls: vec![CheckerMapImpl {
            rust_type: "crate::ProdWeird".to_string(),
            fields,
        }],
    };

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: false,
        generate_checker: true,
        checker_map: Some(checker_map),
    };
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("foo_bar: self.foo_bar, // TLA+ VARIABLE: FooBar"),
        "Missing normalized field mapping"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checker_map_rejects_unknown_keys_with_expected_list() {
    let source = r#"
---- MODULE Counter ----
VARIABLE count

Init == count = 0

Next == count' = count + 1
====
"#;

    let mut fields = BTreeMap::new();
    fields.insert("count".to_string(), "self.count".to_string());
    fields.insert("typo".to_string(), "self.count".to_string());

    let checker_map = CheckerMapConfig {
        spec_module: Some("Counter".to_string()),
        impls: vec![CheckerMapImpl {
            rust_type: "crate::ProdCounter".to_string(),
            fields,
        }],
    };

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: false,
        generate_checker: true,
        checker_map: Some(checker_map),
    };
    let err = parse_and_generate(source, &options).unwrap_err();
    assert!(
        err.contains("unknown state field(s)")
            && err.contains("typo")
            && err.contains("expected keys"),
        "Unexpected error: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checker_map_requires_total_mapping() {
    let source = r#"
---- MODULE Counter ----
VARIABLE count

Init == count = 0

Next == count' = count + 1
====
"#;

    let checker_map = CheckerMapConfig {
        spec_module: Some("Counter".to_string()),
        impls: vec![CheckerMapImpl {
            rust_type: "crate::ProdCounter".to_string(),
            fields: BTreeMap::new(),
        }],
    };

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: false,
        generate_checker: true,
        checker_map: Some(checker_map),
    };
    let err = parse_and_generate(source, &options).unwrap_err();
    assert!(
        err.contains("missing mapping for state field"),
        "Unexpected error: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_next_handles_unchanged_assigned_var() {
    let source = r#"
---- MODULE UnchangedOverlap ----
VARIABLE x

Init == x = 0

Next == x' \in 0..1 /\ UNCHANGED x
====
"#;

    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: false,
        generate_checker: true,
        checker_map: None,
    };
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("fn is_next(&self, old: &Self::State, new: &Self::State) -> Option<bool>"),
        "Missing is_next method"
    );
    assert!(
        code.contains("let __elem = new.x"),
        "Expected range membership to cache the candidate value"
    );
    assert!(
        code.contains("__elem >= __start && __elem <= __end"),
        "Expected membership check against new.x"
    );
    assert!(
        code.contains("old.x == new.x"),
        "Expected UNCHANGED constraint for assigned variable"
    );
}
