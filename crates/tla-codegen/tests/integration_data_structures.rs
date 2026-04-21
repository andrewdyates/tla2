// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Data structure codegen tests: records, functions, EXCEPT (single/nested/mixed),
//! multi-arg function definitions, and function set expressions.

mod common;

use common::parse_and_generate;
use tla_codegen::CodeGenOptions;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_function_update() {
    // Tests EXCEPT for function update [f EXCEPT ![a] = b]
    let source = r#"
---- MODULE ExceptTest ----
VARIABLE f

Init == f = [x \in {1, 2, 3} |-> x * 2]

Next == f' = [f EXCEPT ![1] = 10]

InvCheckValue == f[1] # 0
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // EXCEPT should generate clone + update pattern
    assert!(
        code.contains("__tmp"),
        "EXCEPT should use temporary variable: {}",
        code
    );
    assert!(
        code.contains(".clone()"),
        "EXCEPT should clone the function: {}",
        code
    );
    assert!(
        code.contains(".update("),
        "EXCEPT should call update method: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_arg_function_definition() {
    // Tests multi-argument function definition [x, y \in S |-> expr]
    let source = r#"
---- MODULE MultiArgFunc ----
VARIABLE matrix

Init == matrix = [x \in {1, 2}, y \in {1, 2} |-> x + y]

Next == matrix' = matrix
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Multi-arg function should use nested flat_map/map iterators
    assert!(
        code.contains("flat_map"),
        "Multi-arg func should use flat_map: {}",
        code
    );
    assert!(
        code.contains("TlaFunc::from_iter"),
        "Should create TlaFunc: {}",
        code
    );
    // Should generate tuple key
    assert!(
        code.contains("x.clone(), y.clone()"),
        "Should create tuple key: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_except_path() {
    // Tests nested EXCEPT path [f EXCEPT ![a][b] = v]
    let source = r#"
---- MODULE NestedExcept ----
VARIABLE matrix

Init == matrix = [x \in {1, 2} |-> [y \in {1, 2} |-> 0]]

Next == matrix' = [matrix EXCEPT ![1][2] = 99]

InvCheck == matrix[1][1] = matrix[1][1]
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Nested EXCEPT should generate keys and intermediate values
    assert!(
        code.contains("__key_0"),
        "Should generate __key_0: {}",
        code
    );
    assert!(
        code.contains("__key_1"),
        "Should generate __key_1: {}",
        code
    );
    assert!(
        code.contains("__inner_0"),
        "Should generate __inner_0: {}",
        code
    );
    // Should have multiple .update calls (or nested update logic)
    assert!(
        code.contains(".update(__key_0"),
        "Should update outer function: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_three_level_nested_except() {
    // Tests deeply nested EXCEPT path [f EXCEPT ![a][b][c] = v]
    let source = r#"
---- MODULE DeepNested ----
VARIABLE cube

Init == cube = [x \in {1, 2} |-> [y \in {1, 2} |-> [z \in {1, 2} |-> 0]]]

Next == cube' = [cube EXCEPT ![1][1][1] = 42]
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Should generate three keys
    assert!(
        code.contains("__key_2"),
        "Should generate __key_2 for third level: {}",
        code
    );
    // Should have __inner_0 and __inner_1
    assert!(
        code.contains("__inner_1"),
        "Should generate __inner_1 for intermediate: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_literal() {
    // Tests record literal expression [a |-> 1, b |-> 2]
    let source = r#"
---- MODULE RecordTest ----
VARIABLE r

Init == r = [x |-> 1, y |-> 2]

Next == r' = r
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Record literal should use TlaRecord::from_fields
    assert!(
        code.contains("TlaRecord::from_fields"),
        "Record should use TlaRecord::from_fields: {}",
        code
    );
    // Should have field names
    assert!(code.contains("\"x\""), "Should have field 'x': {}", code);
    assert!(code.contains("\"y\""), "Should have field 'y': {}", code);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access() {
    // Tests record field access r.field
    let source = r#"
---- MODULE RecordAccessTest ----
VARIABLE total

Init == total = 0

Next ==
    LET rec == [a |-> 10, b |-> 20]
    IN total' = rec.a + rec.b
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Record access should use .get() for non-state variables
    assert!(
        code.contains(".get("),
        "Record access should use .get(): {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bound_record_access_uses_record_runtime_api() {
    let source = r#"
---- MODULE BoundRecordAccessTest ----
VARIABLE can

Init == can \in {c \in [black : 0..1, white : 0..1] : c.black + c.white = 1}

Next == can' = can
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("c.get(\"black\")"),
        "Bound record access should use TlaRecord::get for black: {}",
        code
    );
    assert!(
        code.contains("c.get(\"white\")"),
        "Bound record access should use TlaRecord::get for white: {}",
        code
    );
    assert!(
        !code.contains("c.black") && !code.contains("c.white"),
        "Bound record access should not use struct field syntax: {}",
        code
    );
    assert!(
        !code.contains("let mut __records = TlaSet::new();"),
        "Init should stream filtered record choices instead of materializing a record set: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_record_except_substitutes_at_and_uses_old_new_in_is_next() {
    let source = r#"
---- MODULE RecordExceptAtTest ----
VARIABLE can

Init == can = [black |-> 2, white |-> 1]

Next == can.black > 0 /\ can' = [can EXCEPT !.black = @ - 1]
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    assert!(
        code.contains("state.can.get(\"black\")"),
        "State record access should use TlaRecord::get: {}",
        code
    );
    assert!(
        code.contains("__tmp.set(\"black\""),
        "EXCEPT field update should use TlaRecord::set: {}",
        code
    );
    assert!(
        code.contains("state.can.get(\"black\").cloned().expect(\"record access requires existing field\") - 1_i64"),
        "EXCEPT @ should lower to the old field value in next(): {}",
        code
    );
    assert!(
        code.contains("old.can.get(\"black\")"),
        "is_next guard/value should read old state: {}",
        code
    );
    assert!(
        code.contains("new.can =="),
        "is_next should compare against the candidate new state: {}",
        code
    );
    assert!(
        !code.contains("state.can.black") && !code.contains("__tmp.black") && !code.contains("@"),
        "Generated code should not contain invalid field syntax or raw @: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mixed_index_field_except() {
    // Tests mixed Index/Field EXCEPT path [f EXCEPT ![i].field = v]
    let source = r#"
---- MODULE MixedExcept ----
VARIABLE data

Init == data = [x \in {1, 2} |-> [a |-> 0, b |-> 0]]

Next == data' = [data EXCEPT ![1].a = 10]
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Should generate key for index
    assert!(
        code.contains("__key_0"),
        "Should generate __key_0 for index: {}",
        code
    );
    // Should have __inner for intermediate
    assert!(
        code.contains("__inner_0"),
        "Should generate __inner_0: {}",
        code
    );
    // Should use .set for field update (on TlaRecord)
    assert!(
        code.contains(".set("),
        "Should use .set() for field update: {}",
        code
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_funcset_expression() {
    // Tests FuncSet expression [S -> T] - the set of all functions from S to T
    let source = r#"
---- MODULE FuncSetTest ----
VARIABLE f

Init == f \in [{1, 2} -> {0, 1}]

Next == f' = f
====
"#;

    let options = CodeGenOptions::default();
    let code = parse_and_generate(source, &options).expect("generation failed");

    // Should enumerate all functions from {1,2} to {0,1}
    // That's 2^2 = 4 functions
    assert!(
        code.contains("__domain"),
        "Should have domain variable: {}",
        code
    );
    assert!(
        code.contains("__range"),
        "Should have range variable: {}",
        code
    );
    assert!(
        code.contains("TlaFunc::from_iter"),
        "Should construct functions: {}",
        code
    );
}
