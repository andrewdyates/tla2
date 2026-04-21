// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Identifier-resolution coverage for z4 init enumeration

use super::*;

/// Part of #522: Test Ident resolution through EvalCtx operator definitions.
/// This is the full integration path: define a constant, reference it by name.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_ident_resolution_via_ctx() {
    use tla_core::ast::OperatorDef;

    // Define MySet == {1, 2, 3} as an operator
    let myset_body = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));
    let myset_def = OperatorDef {
        name: spanned("MySet".to_string()),
        params: vec![],
        body: myset_body,
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    // Create EvalCtx with the operator definition
    let mut ctx = EvalCtx::new();
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("MySet".to_string(), Arc::new(myset_def));

    // Init == x \in MySet (reference by name)
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "MySet".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["x".into()];
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();

    // Should find 3 states: x=1, x=2, x=3
    assert_eq!(
        states.len(),
        3,
        "expected 3 states from MySet = {{1, 2, 3}}"
    );

    let values: std::collections::BTreeSet<i64> =
        states.iter().map(|s| state_int_i64(s, "x")).collect();
    assert_eq!(values, [1, 2, 3].into_iter().collect());
}

/// Regression: constant range referenced via Ident must not be rewritten to a placeholder string.
///
/// N == 1..3
/// Init == x \in N
///
/// Part of #251 / #515.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_ident_resolution_range_constant_via_ctx() {
    use tla_core::ast::OperatorDef;

    // Define N == 1..3 as an operator.
    let n_body = spanned(Expr::Range(
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));
    let n_def = OperatorDef {
        name: spanned("N".to_string()),
        params: vec![],
        body: n_body,
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    // Create EvalCtx with the operator definition.
    let mut ctx = EvalCtx::new();
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("N".to_string(), Arc::new(n_def));

    // Init == x \in N (reference by name)
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "N".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["x".into()];
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();

    assert_eq!(states.len(), 3, "expected 3 states from N = 1..3");
    let values: std::collections::BTreeSet<i64> =
        states.iter().map(|s| state_int_i64(s, "x")).collect();
    assert_eq!(values, [1, 2, 3].into_iter().collect());
}

/// Part of #529: Test heterogeneous detection through Ident reference.
/// When a variable references a heterogeneous set via an Ident,
/// the detection must still work through constant resolution.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_heterogeneous_setenum_via_ident_reference() {
    use tla_core::ast::OperatorDef;

    // Define MixedSet == {1, "a"} (heterogeneous)
    let mixed_set_body = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::String("a".to_string())),
    ]));
    let mixed_set_def = OperatorDef {
        name: spanned("MixedSet".to_string()),
        params: vec![],
        body: mixed_set_body,
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    // Create EvalCtx with the operator definition
    let mut ctx = EvalCtx::new();
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("MixedSet".to_string(), Arc::new(mixed_set_def));

    // Init == x \in MixedSet (reference by name, not direct SetEnum)
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "MixedSet".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["x".into()];
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    // z4 enumeration must either:
    // - refuse (return Err), allowing caller fallback, OR
    // - enumerate BOTH solutions (x=1 and x="a").
    //
    // It must not silently under-enumerate to a strict subtype.
    match enumerate_init_states_z4(&ctx, &init, &vars, None, &config) {
        Err(e) => {
            // Refusing is acceptable - caller will fall back to brute-force
            // Part of #529: Verify the error is specifically about heterogeneous types
            assert!(
                matches!(e, Z4EnumError::UnsupportedVarType { .. }),
                "expected UnsupportedVarType error, got: {:?}",
                e
            );
        }
        Ok(states) => {
            assert_eq!(
                states.len(),
                2,
                "heterogeneous SetEnum via Ident must produce 2 initial states or refuse"
            );

            let mut saw_int = false;
            let mut saw_string = false;
            for state in states {
                match state.get("x") {
                    Some(value) if value_is_i64(value, 1) => saw_int = true,
                    Some(Value::String(s)) if s.as_ref() == "a" => saw_string = true,
                    other => panic!("unexpected x value in model: {:?}", other),
                }
            }
            assert!(saw_int, "missing x=1 solution");
            assert!(saw_string, "missing x=\"a\" solution");
        }
    }
}
