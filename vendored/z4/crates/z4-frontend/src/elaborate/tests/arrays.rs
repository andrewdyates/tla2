// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_array_select() {
    let input = r#"
            (declare-const a (Array Int Int))
            (assert (= (select a 0) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_array_store() {
    let input = r#"
            (declare-const a (Array Int Int))
            (declare-const b (Array Int Int))
            (assert (= (store a 0 42) b))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_array_select_store_composition() {
    let input = r#"
            (declare-const a (Array Int Int))
            (assert (= (select (store a 0 42) 0) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_const_array() {
    let input = r#"
            (declare-const x Int)
            (assert (= (select ((as const (Array Int Int)) 0) x) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    // The assertion should simplify to (= 0 0) which is true
}

#[test]
fn test_elaborate_const_array_bool() {
    let input = r#"
            (declare-const i Int)
            (assert (select ((as const (Array Int Bool)) true) i))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn test_elaborate_const_array_with_store() {
    let input = r#"
            (assert (= (select (store ((as const (Array Int Int)) 0) 5 100) 5) 100))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

/// Regression test for #6124: const array with BV index sort.
/// Now uses `SExpr::to_raw_string()` (#6125) so `_` and `as` are not quoted.
#[test]
fn test_elaborate_const_array_bv_index_sort_6124() {
    let input = r#"
            (set-logic QF_AUFBV)
            (declare-const P (_ BitVec 32))
            (declare-const V (Array (_ BitVec 32) Bool))
            (assert (and
                (= P (_ bv0 32))
                (= V (store ((as const (Array (_ BitVec 32) Bool)) false) P true))
                (not (select V P))))
            (check-sat)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // Formula should parse without errors; the const array index sort
    // (_ BitVec 32) must be resolved as BitVec(32), not Uninterpreted.
    assert_eq!(ctx.assertions.len(), 1);
}

/// Test nested Array sorts via QualifiedApp: (Array (_ BitVec 32) (_ BitVec 64))
#[test]
fn test_elaborate_const_array_bv_both_sorts() {
    let input = r#"
            (declare-const idx (_ BitVec 32))
            (assert (= (select ((as const (Array (_ BitVec 32) (_ BitVec 64))) (_ bv0 64)) idx) (_ bv0 64)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 1);
}
