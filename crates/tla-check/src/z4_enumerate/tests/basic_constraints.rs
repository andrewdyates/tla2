// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Basic z4 enumeration constraint coverage

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_conjunct_selection_module_ref_init_1_2() {
    // Regression test for #572: z4 init enumeration must handle conjunct selection
    // syntax like Init!1 and Init!2 (ModuleRef numeric op_name).
    //
    // This exercises the *tla-check → tla-z4* integration path (not just the
    // tla-z4 unit tests), matching the real-world failure mode that originally
    // blocked EWD998ChanTrace Init enumeration.
    let src = r#"---- MODULE ConjunctSelection ----
VARIABLES x, y

Init ==
    /\ x = 1
    /\ y = 2

TraceInit ==
    /\ Init!1
    /\ Init!2
====
"#;

    let tree = parse_to_syntax_tree(src);
    let result = lower(FileId(0), &tree);
    let module = result.module.expect("Failed to parse module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let def = ctx
        .shared()
        .ops
        .get("TraceInit")
        .expect("TraceInit definition missing");

    let vars: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let config = Z4EnumConfig {
        max_solutions: 10,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &def.body, &vars, None, &config).unwrap();
    assert_eq!(states.len(), 1);
    assert_eq!(state_int_i64(&states[0], "x"), 1);
    assert_eq!(state_int_i64(&states[0], "y"), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_simple_int_constraint() {
    // Init == x \in 1..3
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["x".into()];
    let ctx = EvalCtx::new();
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();

    // Should find 3 states: x=1, x=2, x=3 — verify exact values, not just count
    assert_eq!(states.len(), 3);
    let mut values: Vec<i64> = states.iter().map(|s| state_int_i64(s, "x")).collect();
    values.sort();
    assert_eq!(values, vec![1, 2, 3], "expected x \\in 1..3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_zero_timeout_reports_solver_timeout() {
    use std::time::Duration;

    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["x".into()];
    let ctx = EvalCtx::new();
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: Some(Duration::ZERO),
        debug: false,
    };

    let err = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap_err();
    assert!(
        matches!(err, Z4EnumError::SolverTimeout),
        "expected SolverTimeout, got {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_bool_constraint() {
    // Init == b \in BOOLEAN
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "b".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "BOOLEAN".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["b".into()];
    let ctx = EvalCtx::new();
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    // Provide explicit type info since BOOLEAN membership needs it
    let mut var_types = HashMap::new();
    var_types.insert(
        "b".to_string(),
        VarInfo {
            name: "b".into(),
            sort: VarSort::Bool,
            domain_keys: None,
        },
    );

    let states = enumerate_init_states_z4(&ctx, &init, &vars, Some(&var_types), &config).unwrap();

    // Should find 2 states: b=TRUE, b=FALSE — verify exact values, not just count
    assert_eq!(states.len(), 2);
    let mut bools: Vec<bool> = states
        .iter()
        .map(|s| {
            s.get("b")
                .expect("missing var b")
                .as_bool()
                .expect("b should be Bool")
        })
        .collect();
    bools.sort();
    assert_eq!(bools, vec![false, true], "expected b \\in BOOLEAN");
}

// Previously blocked by z4#294/z4#309: fixed in z4 commit 8ea188b6
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_conjunction() {
    // Init == x \in 1..3 /\ y \in 1..2
    let init = spanned(Expr::And(
        Box::new(spanned(Expr::In(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(3)))),
            ))),
        ))),
        Box::new(spanned(Expr::In(
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(2)))),
            ))),
        ))),
    ));

    let vars: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let ctx = EvalCtx::new();
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();

    // Should find 3*2 = 6 states — verify exact (x,y) pairs, not just count
    assert_eq!(states.len(), 6);
    use std::collections::BTreeSet;
    let mut pairs: BTreeSet<(i64, i64)> = BTreeSet::new();
    for state in &states {
        let x = state_int_i64(state, "x");
        let y = state_int_i64(state, "y");
        assert!((1..=3).contains(&x), "x out of range: {x}");
        assert!((1..=2).contains(&y), "y out of range: {y}");
        assert!(pairs.insert((x, y)), "duplicate state: ({x}, {y})");
    }
    let expected: BTreeSet<(i64, i64)> = [(1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)]
        .into_iter()
        .collect();
    assert_eq!(
        pairs, expected,
        "wrong solution set for x \\in 1..3 /\\ y \\in 1..2"
    );
}

// Previously blocked by z4#294/z4#309: fixed in z4 commit 8ea188b6
// Previously blocked by z4#949: fixed in z4 commit ebd6f1ab3db5
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_arithmetic_constraint() {
    // Init == x \in 1..10 /\ y \in 1..10 /\ x + y = 5
    let x_in_range = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(10)))),
        ))),
    ));
    let y_in_range = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(10)))),
        ))),
    ));
    let sum_eq_5 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));

    let init = spanned(Expr::And(
        Box::new(x_in_range),
        Box::new(spanned(Expr::And(Box::new(y_in_range), Box::new(sum_eq_5)))),
    ));

    let vars: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let ctx = EvalCtx::new();
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();

    // Should find 4 states: (1,4), (2,3), (3,2), (4,1)
    // Verify exact solutions, not just count
    use std::collections::BTreeSet;
    let mut solutions: BTreeSet<(i64, i64)> = BTreeSet::new();
    for state in &states {
        let x_val = state_int_i64(state, "x");
        let y_val = state_int_i64(state, "y");
        assert!((1..=10).contains(&x_val), "x out of range: {x_val}");
        assert!((1..=10).contains(&y_val), "y out of range: {y_val}");
        assert_eq!(
            x_val + y_val,
            5,
            "constraint violated: {x_val} + {y_val} != 5"
        );
        assert!(
            solutions.insert((x_val, y_val)),
            "duplicate state: ({x_val}, {y_val})"
        );
    }
    let expected: std::collections::BTreeSet<(i64, i64)> =
        [(1, 4), (2, 3), (3, 2), (4, 1)].into_iter().collect();
    assert_eq!(solutions, expected, "wrong solution set");
}
