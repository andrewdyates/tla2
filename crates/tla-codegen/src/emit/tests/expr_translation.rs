// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for expression-to-Rust translation: name case conversion, literals,
//! arithmetic, logic, sets, state access, stdlib apply.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_pascal_case() {
    assert_eq!(to_pascal_case("hello_world"), "HelloWorld");
    assert_eq!(to_pascal_case("Counter"), "Counter");
    assert_eq!(to_pascal_case("my_spec"), "MySpec");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_snake_case() {
    assert_eq!(to_snake_case("HelloWorld"), "hello_world");
    assert_eq!(to_snake_case("Counter"), "counter");
    assert_eq!(to_snake_case("MySpec"), "my_spec");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_literals() {
    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let op_defs = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    assert_eq!(emitter.expr_to_rust(&Expr::Bool(true)), "true");
    assert_eq!(emitter.expr_to_rust(&Expr::Bool(false)), "false");
    assert_eq!(emitter.expr_to_rust(&Expr::Int(42.into())), "42_i64");
    assert_eq!(
        emitter.expr_to_rust(&Expr::String("hello".to_string())),
        "\"hello\".to_string()"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_arithmetic() {
    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let op_defs = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let add = Expr::Add(
        Box::new(spanned(Expr::Int(1.into()))),
        Box::new(spanned(Expr::Int(2.into()))),
    );
    assert_eq!(emitter.expr_to_rust(&add), "(1_i64 + 2_i64)");

    let mul = Expr::Mul(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(3.into()))),
    );
    assert_eq!(emitter.expr_to_rust(&mul), "(x * 3_i64)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_logic() {
    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let op_defs = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let and = Expr::And(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(false))),
    );
    assert_eq!(emitter.expr_to_rust(&and), "(true && false)");

    let not = Expr::Not(Box::new(spanned(Expr::Bool(true))));
    assert_eq!(emitter.expr_to_rust(&not), "!true");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_sets() {
    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let op_defs = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let set = Expr::SetEnum(vec![
        spanned(Expr::Int(1.into())),
        spanned(Expr::Int(2.into())),
    ]);
    assert_eq!(emitter.expr_to_rust(&set), "tla_set![1_i64, 2_i64]");

    let range = Expr::Range(
        Box::new(spanned(Expr::Int(1.into()))),
        Box::new(spanned(Expr::Int(10.into()))),
    );
    assert_eq!(emitter.expr_to_rust(&range), "range_set(1_i64, 10_i64)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_with_state() {
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("count".to_string(), TlaType::Int);

    let mut out = String::new();
    let op_defs = std::collections::HashMap::new();
    let emitter = build_test_emitter(
        &mut out,
        &var_types,
        &op_defs,
        var_types.keys().cloned().collect(),
    );

    // Without state prefix
    assert_eq!(
        emitter.expr_to_rust(&Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID
        )),
        "count"
    );

    // With state prefix
    assert_eq!(
        emitter.expr_to_rust_with_state(
            &Expr::Ident("count".to_string(), tla_core::name_intern::NameId::INVALID),
            true
        ),
        "state.count"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_apply_translation() {
    let mut out = String::new();
    let var_types = std::collections::HashMap::new();
    let op_defs = std::collections::HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    // Test Cardinality(s) - should translate to s.len() as i64
    let cardinality = Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Cardinality".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::Ident(
            "s".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))],
    );
    let result = emitter.expr_to_rust(&cardinality);
    assert!(result.contains(".len() as i64"), "Cardinality: {}", result);

    // Test Len(s) - should translate to s.len() as i64
    let len = Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Len".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::Ident(
            "seq".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))],
    );
    let result = emitter.expr_to_rust(&len);
    assert!(result.contains(".len() as i64"), "Len: {}", result);

    // Test Max(s) - should translate to .iter().max()
    let max = Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Max".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::Ident(
            "s".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))],
    );
    let result = emitter.expr_to_rust(&max);
    assert!(result.contains(".max()"), "Max: {}", result);

    // Test Head(s) - should translate to .first()
    let head = Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Head".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::Ident(
            "seq".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))],
    );
    let result = emitter.expr_to_rust(&head);
    assert!(result.contains(".first()"), "Head: {}", result);
}
