// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constant pre-evaluation and set-filter coverage

use super::*;

/// Part of #515: Test constant pre-evaluation.
/// This tests that constants defined using complex expressions (like SetBuilder)
/// that z4 cannot directly translate are pre-evaluated to SetEnum.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_with_pre_evaluated_setbuilder_constant() {
    use tla_core::ast::{BoundVar, OperatorDef};

    // Define DoubledNumbers == { 2*x : x \in 1..3 }
    // This is a SetBuilder that z4 cannot translate directly.
    // Pre-evaluation should convert it to {2, 4, 6}.
    let setbuilder_body = spanned(Expr::SetBuilder(
        Box::new(spanned(Expr::Mul(
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
        vec![BoundVar {
            name: spanned("x".to_string()),
            pattern: None,
            domain: Some(Box::new(spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(3)))),
            )))),
        }],
    ));
    let doubled_def = OperatorDef {
        name: spanned("DoubledNumbers".to_string()),
        params: vec![],
        body: setbuilder_body,
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
        .insert("DoubledNumbers".to_string(), Arc::new(doubled_def));

    // Init == n \in DoubledNumbers (reference by name)
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "n".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "DoubledNumbers".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["n".into()];
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();

    // Should find 3 states: n=2, n=4, n=6
    assert_eq!(
        states.len(),
        3,
        "expected 3 states from DoubledNumbers = {{2, 4, 6}}"
    );

    let values: std::collections::BTreeSet<i64> =
        states.iter().map(|s| state_int_i64(s, "n")).collect();
    assert_eq!(values, [2, 4, 6].into_iter().collect());
}

/// Part of #515: Test constant pre-evaluation with Permutation-like pattern.
/// This simulates what Permutation would produce - a set of tuples.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_with_pre_evaluated_tuple_set_constant() {
    use tla_core::ast::OperatorDef;

    // Define Arrangements == SetEnum of tuples (simulating what Permutation produces)
    // This represents a pre-computed permutation result.
    let arrangements_body = spanned(Expr::SetEnum(vec![
        spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ])),
        spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(1))),
        ])),
    ]));
    let arrangements_def = OperatorDef {
        name: spanned("Arrangements".to_string()),
        params: vec![],
        body: arrangements_body,
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
        .insert("Arrangements".to_string(), Arc::new(arrangements_def));

    // Init == t \in Arrangements (reference by name)
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "Arrangements".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["t".into()];
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();

    // Should find 2 states: t=<<1,2>> and t=<<2,1>>
    assert_eq!(states.len(), 2, "expected 2 states from Arrangements");

    let tuples: std::collections::BTreeSet<(i64, i64)> = states
        .iter()
        .map(|s| match s.get("t") {
            Some(Value::Tuple(elems)) => {
                let a = value_int_i64(&elems[0]);
                let b = value_int_i64(&elems[1]);
                (a, b)
            }
            other => panic!("expected tuple value for t, got {:?}", other),
        })
        .collect();

    assert_eq!(tuples, [(1, 2), (2, 1)].into_iter().collect());
}

/// Part of #515: Regression test for z4 constant pre-evaluation of TLC-style permutation values.
///
/// `Permutations({1,2,3})` evaluates to a set of functions with domain `1..3`.
/// For z4 translation we encode those functions as tuples `<<f[1], f[2], f[3]>>`,
/// so membership `p \in Perms` can be translated as tuple membership.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_enumerate_with_pre_evaluated_permutations_constant() {
    use tla_core::ast::OperatorDef;

    fn value_int_i64(v: &Value) -> i64 {
        super::value_int_i64(v)
    }

    // Perms == Permutations({1,2,3})
    let perms_body = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            "Permutations".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ]))],
    ));
    let perms_def = OperatorDef {
        name: spanned("Perms".to_string()),
        params: vec![],
        body: perms_body,
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    let mut ctx = EvalCtx::new();
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("Perms".to_string(), Arc::new(perms_def));

    // Init == p \in Perms
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "p".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "Perms".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["p".into()];
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();
    assert_eq!(states.len(), 6, "expected 3! = 6 permutations");

    let perms: std::collections::BTreeSet<(i64, i64, i64)> = states
        .iter()
        .map(|s| match s.get("p") {
            Some(Value::Tuple(elems)) => {
                assert_eq!(elems.len(), 3);
                (
                    value_int_i64(&elems[0]),
                    value_int_i64(&elems[1]),
                    value_int_i64(&elems[2]),
                )
            }
            Some(Value::Seq(seq)) => {
                assert_eq!(seq.len(), 3);
                (
                    value_int_i64(&seq[0]),
                    value_int_i64(&seq[1]),
                    value_int_i64(&seq[2]),
                )
            }
            other => panic!("expected tuple/seq value for p, got {:?}", other),
        })
        .collect();

    assert_eq!(
        perms,
        [
            (1, 2, 3),
            (1, 3, 2),
            (2, 1, 3),
            (2, 3, 1),
            (3, 1, 2),
            (3, 2, 1),
        ]
        .into_iter()
        .collect()
    );
}

/// Part of #515: Test Einstein-like pattern - SetFilter over pre-evaluated tuple constant
/// with tuple indexing in the predicate.
///
/// This is the key pattern from the Einstein riddle:
/// ```tla
/// drinks \in { p \in DRINKS : p[3] = "milk" }
/// ```
/// Where DRINKS is a pre-evaluated set of tuples.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_enumerate_einstein_pattern_setfilter_with_tuple_index() {
    use tla_core::ast::{BoundVar, OperatorDef};

    // Define Drinks == set of 3-element tuples (simulating Permutation result)
    // Each tuple is (name, beverage, type) - we filter on p[3] (the type field)
    let drinks_body = spanned(Expr::SetEnum(vec![
        // Tuple with position 3 = "milk" (should match filter)
        spanned(Expr::Tuple(vec![
            spanned(Expr::String("Alice".to_string())),
            spanned(Expr::String("coffee".to_string())),
            spanned(Expr::String("milk".to_string())),
        ])),
        // Tuple with position 3 = "water" (should NOT match filter)
        spanned(Expr::Tuple(vec![
            spanned(Expr::String("Bob".to_string())),
            spanned(Expr::String("tea".to_string())),
            spanned(Expr::String("water".to_string())),
        ])),
        // Tuple with position 3 = "milk" (should match filter)
        spanned(Expr::Tuple(vec![
            spanned(Expr::String("Charlie".to_string())),
            spanned(Expr::String("soda".to_string())),
            spanned(Expr::String("milk".to_string())),
        ])),
        // Tuple with position 3 = "juice" (should NOT match filter)
        spanned(Expr::Tuple(vec![
            spanned(Expr::String("Diana".to_string())),
            spanned(Expr::String("beer".to_string())),
            spanned(Expr::String("juice".to_string())),
        ])),
    ]));
    let drinks_def = OperatorDef {
        name: spanned("Drinks".to_string()),
        params: vec![],
        body: drinks_body,
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
        .insert("Drinks".to_string(), Arc::new(drinks_def));

    // Init == d \in { p \in Drinks : p[3] = "milk" }
    // This is a SetFilter over a constant reference with tuple indexing in predicate
    let bound = BoundVar {
        name: spanned("p".to_string()),
        pattern: None,
        domain: Some(Box::new(spanned(Expr::Ident(
            "Drinks".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    };
    // p[3] = "milk"
    let predicate = spanned(Expr::Eq(
        Box::new(spanned(Expr::FuncApply(
            Box::new(spanned(Expr::Ident(
                "p".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
        Box::new(spanned(Expr::String("milk".to_string()))),
    ));
    let set_filter = spanned(Expr::SetFilter(bound, Box::new(predicate)));
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "d".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(set_filter),
    ));

    let vars: Vec<Arc<str>> = vec!["d".into()];
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config)
        .expect("Einstein pattern should be supported by z4 enumeration");

    // Should find 2 states: the two tuples where position 3 = "milk"
    assert_eq!(
        states.len(),
        2,
        "Expected 2 states matching p[3] = 'milk', got {}",
        states.len()
    );

    // Verify the correct tuples were found
    let first_elements: std::collections::BTreeSet<String> = states
        .iter()
        .map(|s| match s.get("d") {
            Some(Value::Tuple(elems)) => match &elems[0] {
                Value::String(s) => s.to_string(),
                other => panic!("expected String first element, got {:?}", other),
            },
            other => panic!("expected tuple value for d, got {:?}", other),
        })
        .collect();

    // Alice and Charlie have milk at position 3
    assert!(first_elements.contains("Alice"), "missing Alice tuple");
    assert!(first_elements.contains("Charlie"), "missing Charlie tuple");
    assert!(
        !first_elements.contains("Bob"),
        "Bob should not match (has water)"
    );
    assert!(
        !first_elements.contains("Diana"),
        "Diana should not match (has juice)"
    );
}
