// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-inference and heterogeneous tuple coverage

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_expr_tuple() {
    // Test tuple with int elements: <<1, 2, 3>>
    let tuple_expr = Expr::Tuple(vec![
        spanned(Expr::Int(1.into())),
        spanned(Expr::Int(2.into())),
        spanned(Expr::Int(3.into())),
    ]);
    let sort = infer_sort_from_expr(&tuple_expr);
    match sort {
        VarSort::Tuple { element_sorts } => {
            assert_eq!(element_sorts.len(), 3);
            assert!(matches!(element_sorts[0], VarSort::Int));
            assert!(matches!(element_sorts[1], VarSort::Int));
            assert!(matches!(element_sorts[2], VarSort::Int));
        }
        other => panic!("expected Tuple sort, got {:?}", other),
    }

    // Test tuple with string element: <<1, "a">>
    let mixed_tuple = Expr::Tuple(vec![
        spanned(Expr::Int(1.into())),
        spanned(Expr::String("a".to_string())),
    ]);
    let sort = infer_sort_from_expr(&mixed_tuple);
    match sort {
        VarSort::Tuple { element_sorts } => {
            assert_eq!(element_sorts.len(), 2);
            assert!(matches!(element_sorts[0], VarSort::Int));
            assert!(matches!(element_sorts[1], VarSort::String { .. }));
        }
        other => panic!("expected Tuple sort, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_set_tuple_enum() {
    // Test SetEnum with tuples: {<<1, 2>>, <<3, 4>>}
    let set_expr = Expr::SetEnum(vec![
        spanned(Expr::Tuple(vec![
            spanned(Expr::Int(1.into())),
            spanned(Expr::Int(2.into())),
        ])),
        spanned(Expr::Tuple(vec![
            spanned(Expr::Int(3.into())),
            spanned(Expr::Int(4.into())),
        ])),
    ]);
    let sort = infer_sort_from_set(&set_expr);
    match sort {
        VarSort::Tuple { element_sorts } => {
            assert_eq!(element_sorts.len(), 2);
            assert!(matches!(element_sorts[0], VarSort::Int));
            assert!(matches!(element_sorts[1], VarSort::Int));
        }
        other => panic!("expected Tuple sort, got {:?}", other),
    }
}

/// Part of #523 audit: test heterogeneous tuple element types
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_heterogeneous_tuple_set_element_types() {
    // t \in {<<1, 2>>, <<1, "a">>}
    // Tuples have same arity but different element types at position 2.
    // z4 enumeration must refuse (heterogeneous tuple elements).
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
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::String("a".to_string())),
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

    // Must refuse (Err) since tuple element types differ at position 2
    match enumerate_init_states_z4(&ctx, &init, &vars, None, &config) {
        Err(e) => {
            assert!(
                matches!(
                    e,
                    Z4EnumError::UnsupportedVarType { .. }
                        | Z4EnumError::TranslationFailed(_)
                ),
                "heterogeneous tuple set should produce UnsupportedVarType or TranslationFailed, got: {:?}",
                e
            );
        }
        Ok(states) => {
            // If it somehow succeeds, it must produce both states
            assert_eq!(
                states.len(),
                2,
                "heterogeneous tuple set must refuse or produce all states"
            );
        }
    }
}

/// Part of #523 audit: test heterogeneous tuple arity
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_heterogeneous_tuple_set_arity() {
    // t \in {<<1>>, <<1, 2>>}
    // Tuples have different arities (1 vs 2).
    // z4 enumeration must refuse (heterogeneous tuple arity).
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Tuple(vec![spanned(Expr::Int(BigInt::from(1)))])),
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
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

    // Must refuse (Err) since tuple arities differ
    match enumerate_init_states_z4(&ctx, &init, &vars, None, &config) {
        Err(e) => {
            assert!(
                matches!(
                    e,
                    Z4EnumError::UnsupportedVarType { .. }
                        | Z4EnumError::TranslationFailed(_)
                ),
                "heterogeneous tuple arity should produce UnsupportedVarType or TranslationFailed, got: {:?}",
                e
            );
        }
        Ok(states) => {
            // If it somehow succeeds, it must produce both states
            assert_eq!(
                states.len(),
                2,
                "heterogeneous tuple arity set must refuse or produce all states"
            );
        }
    }
}
