// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tuple-membership and heterogeneous set coverage

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_heterogeneous_setenum_does_not_silently_underenumerate() {
    // Init == x \in {1, "a"}.
    //
    // z4 enumeration must either:
    // - refuse (return Err), allowing caller fallback, OR
    // - enumerate BOTH solutions (x=1 and x="a").
    //
    // It must not silently under-enumerate to a strict subtype.
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::String("a".to_string())),
        ]))),
    ));

    let vars: Vec<Arc<str>> = vec!["x".into()];
    let ctx = EvalCtx::new();
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    match enumerate_init_states_z4(&ctx, &init, &vars, None, &config) {
        Err(e) => {
            assert!(
                matches!(
                    e,
                    Z4EnumError::UnsupportedVarType { .. }
                        | Z4EnumError::TranslationFailed(_)
                ),
                "heterogeneous set should produce UnsupportedVarType or TranslationFailed, got: {:?}",
                e
            );
        }
        Ok(states) => {
            assert_eq!(
                states.len(),
                2,
                "heterogeneous SetEnum must produce 2 initial states or refuse"
            );

            let mut saw_one = false;
            let mut saw_a = false;
            for state in states {
                match state.get("x") {
                    Some(value) if value_is_i64(value, 1) => saw_one = true,
                    Some(Value::String(s)) if s.as_ref() == "a" => saw_a = true,
                    other => panic!("unexpected x value in model: {:?}", other),
                }
            }
            assert!(saw_one, "missing x=1 solution");
            assert!(saw_a, "missing x=\"a\" solution");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_tuple_set_membership_constraint() {
    // Init == t \in {<<1,2>>, <<3,4>>}
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
            ])),
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(3))),
                spanned(Expr::Int(BigInt::from(4))),
            ])),
        ]))),
    ));

    let vars: Vec<Arc<str>> = vec!["t".into()];
    let ctx = EvalCtx::new();
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init, &vars, None, &config).unwrap();
    assert_eq!(states.len(), 2);

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

    assert_eq!(tuples, [(1, 2), (3, 4)].into_iter().collect());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_tuple_set_membership_from_parsed_module() {
    // Integration-ish: parse a TLA+ module, then enumerate Init via z4.
    let spec = r#"
---- MODULE TupleSetMembership ----
VARIABLE t

Init == t \in {<<1, 2>>, <<3, 4>>}

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let result = lower(FileId(0), &tree);
    let module = result.module.expect("Failed to parse module");

    let init_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Init" => Some(def),
            _ => None,
        })
        .expect("missing Init operator");

    let vars: Vec<Arc<str>> = vec!["t".into()];
    let ctx = EvalCtx::new();
    let config = Z4EnumConfig {
        max_solutions: 100,
        solve_timeout: None,
        debug: false,
    };

    let states = enumerate_init_states_z4(&ctx, &init_def.body, &vars, None, &config).unwrap();
    assert_eq!(states.len(), 2);

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

    assert_eq!(tuples, [(1, 2), (3, 4)].into_iter().collect());
}
