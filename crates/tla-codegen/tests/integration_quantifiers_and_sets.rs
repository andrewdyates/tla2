// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier and set-operation codegen tests: forall, exists, CHOOSE,
//! set builders, set filters, Cartesian product, UNION, multi-bound quantifiers.

mod common;

use common::parse_and_generate;
use tla_codegen::CodeGenOptions;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_quantifier() {
    let source = r#"
---- MODULE ForallTest ----
VARIABLE s

Init == s = {1, 2, 3}

InvAllPositive == \A x \in s : x > 0
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify forall generates iter().all()
    assert!(
        code.contains(".iter().all("),
        "Forall should generate iter().all()"
    );
    assert!(
        code.contains("|x|"),
        "Forall should bind variable x in closure"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_quantifier() {
    let source = r#"
---- MODULE ExistsTest ----
VARIABLE s

Init == s = {1, 2, 3}

InvExistsEven == \E x \in s : x = 2
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify exists generates iter().any()
    assert!(
        code.contains(".iter().any("),
        "Exists should generate iter().any(): got:\n{}",
        code
    );
    assert!(
        code.contains("|x|"),
        "Exists should bind variable x in closure"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_operator() {
    let source = r#"
---- MODULE ChooseTest ----
VARIABLE x

Values == {1, 2, 3, 4, 5}
Init == x = CHOOSE y \in Values : y > 3
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify CHOOSE generates iter().find()
    assert!(
        code.contains(".iter().find("),
        "CHOOSE should generate iter().find()"
    );
    assert!(
        code.contains("cloned()"),
        "CHOOSE should clone the found value"
    );
    assert!(
        code.contains("expect("),
        "CHOOSE should panic if no element found"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder() {
    let source = r#"
---- MODULE SetBuilderTest ----
VARIABLE squares

Domain == 1..5
Init == squares = {x * x : x \in Domain}
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify SetBuilder generates map + collect
    assert!(
        code.contains("TlaSet::from_iter("),
        "SetBuilder should use TlaSet::from_iter"
    );
    assert!(
        code.contains(".iter().map("),
        "SetBuilder should use iter().map()"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_filter() {
    let source = r#"
---- MODULE SetFilterTest ----
VARIABLE evens

Domain == 1..10
Init == evens = {x \in Domain : x % 2 = 0}
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify SetFilter generates filter + collect
    assert!(
        code.contains("TlaSet::from_iter("),
        "SetFilter should use TlaSet::from_iter"
    );
    assert!(
        code.contains(".iter().filter("),
        "SetFilter should use iter().filter()"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cartesian_product() {
    let source = r#"
---- MODULE TimesTest ----
VARIABLE pairs

A == {1, 2}
B == {"a", "b"}

Init == pairs = A \X B
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify Cartesian product generates flat_map
    assert!(
        code.contains("flat_map"),
        "Times should generate flat_map for Cartesian product"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_big_union() {
    let source = r#"
---- MODULE BigUnionTest ----
VARIABLE flattened

Sets == {{1, 2}, {3, 4}, {5}}

Init == flattened = UNION Sets
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify UNION (BigUnion) generates flat_map
    assert!(
        code.contains("flat_map"),
        "UNION should generate flat_map to flatten sets"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_bound_quantifier() {
    let source = r#"
---- MODULE MultiBoundTest ----
VARIABLE ok

A == {1, 2}
B == {3, 4}

Init == ok = \A x \in A, y \in B : x < y
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Verify nested all() for multiple bounds
    assert!(
        code.contains(".iter().all(|x|"),
        "Multi-bound forall should nest all() calls"
    );
    assert!(
        code.contains(".iter().all(|y|"),
        "Multi-bound forall should nest for second variable"
    );
}
