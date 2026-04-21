// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use num_bigint::BigInt;
use proptest::prelude::*;
use proptest::test_runner::TestCaseError;
use std::collections::HashMap;
use tla_core::ast::{BoundVar, Expr};
use tla_core::name_intern::NameId;
use tla_core::Spanned;
use tla_core::{ExprFold, SpanPolicy, SubstituteExpr};
use tla_z4::{BmcTranslator, BmcValue, SolveResult, TlaSort, Z4Error, Z4Translator};

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn bound_var(name: &str, domain: Spanned<Expr>) -> BoundVar {
    BoundVar {
        name: spanned(name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    }
}

fn int_assignment(assignments: &HashMap<String, BmcValue>, name: &str) -> Option<i64> {
    assignments.get(name).and_then(|value| match value {
        BmcValue::Int(v) => Some(*v),
        _ => None,
    })
}

#[test]
#[timeout(10_000)]
fn test_substitute_expr_reaches_prime_and_unchanged() {
    let replacement = spanned(Expr::Int(BigInt::from(7)));
    let mut sub = SubstituteExpr {
        subs: HashMap::from([("x", &replacement)]),
        span_policy: SpanPolicy::Preserve,
    };

    let expr = spanned(Expr::Tuple(vec![
        spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))))),
        spanned(Expr::Unchanged(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))))),
    ]));

    let substituted = sub.fold_expr(expr);
    let tuple = match substituted.node {
        Expr::Tuple(items) => items,
        _ => Vec::new(),
    };

    assert_eq!(tuple.len(), 2);
    assert!(matches!(
        &tuple[0].node,
        Expr::Prime(inner) if matches!(&inner.node, Expr::Int(v) if v == &BigInt::from(7))
    ));
    assert!(matches!(
        &tuple[1].node,
        Expr::Unchanged(inner) if matches!(&inner.node, Expr::Int(v) if v == &BigInt::from(7))
    ));
}

#[test]
#[timeout(10_000)]
fn test_quantifier_substitutes_statevar_body() -> Result<(), Z4Error> {
    let mut trans = Z4Translator::new();
    let expr = spanned(Expr::Exists(
        vec![bound_var(
            "x",
            spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(1)))])),
        )],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::StateVar("x".to_string(), 0, NameId(7)))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
    ));

    let term = trans.translate_bool(&expr)?;
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    Ok(())
}

#[test]
#[timeout(10_000)]
fn test_multi_bound_quantifier_errors_are_covered() {
    let mut trans = Z4Translator::new();
    let forall_expr = spanned(Expr::Forall(
        vec![
            bound_var(
                "x",
                spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(1)))])),
            ),
            bound_var(
                "y",
                spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(2)))])),
            ),
        ],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));

    let forall_err = trans.translate_bool(&forall_expr);
    assert!(matches!(forall_err, Err(Z4Error::UnsupportedOp(_))));

    let mut trans2 = Z4Translator::new();
    let exists_expr = spanned(Expr::Exists(
        vec![
            bound_var(
                "x",
                spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(1)))])),
            ),
            bound_var(
                "y",
                spanned(Expr::SetEnum(vec![spanned(Expr::Int(BigInt::from(2)))])),
            ),
        ],
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
    ));

    let exists_err = trans2.translate_bool(&exists_expr);
    assert!(matches!(exists_err, Err(Z4Error::UnsupportedOp(_))));
}

#[test]
#[timeout(10_000)]
fn test_bmc_extract_trace_multi_variable_completeness() -> Result<(), Z4Error> {
    let k = 3;
    let mut trans = BmcTranslator::new(k)?;

    trans.declare_var("x", TlaSort::Int)?;
    trans.declare_var("y", TlaSort::Int)?;

    let init = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(10)))),
        ))),
    ));
    let init_term = trans.translate_init(&init)?;
    trans.assert(init_term);

    for step in 0..k {
        let next = spanned(Expr::And(
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                )))))),
                Box::new(spanned(Expr::Add(
                    Box::new(spanned(Expr::Ident(
                        "x".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(BigInt::from(1)))),
                ))),
            ))),
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
                    "y".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                )))))),
                Box::new(spanned(Expr::Sub(
                    Box::new(spanned(Expr::Ident(
                        "y".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(BigInt::from(1)))),
                ))),
            ))),
        ));
        let next_term = trans.translate_next(&next, step)?;
        trans.assert(next_term);
    }

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans
        .get_model()
        .ok_or_else(|| Z4Error::UntranslatableExpr("expected model for SAT result".to_string()))?;
    let trace = trans.extract_trace(&model);

    assert_eq!(trace.len(), k + 1);
    for (step, state) in trace.iter().enumerate() {
        assert_eq!(state.step, step);
        assert_eq!(int_assignment(&state.assignments, "x"), Some(step as i64));
        assert_eq!(
            int_assignment(&state.assignments, "y"),
            Some(10 - step as i64)
        );
        assert_eq!(state.assignments.len(), 2);
    }

    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 24,
        .. ProptestConfig::default()
    })]

    #[test]
    fn proptest_bmc_prime_mapping_consistency(init in -20i64..20, delta in -5i64..5, k in 1usize..4) {
        let mut trans = BmcTranslator::new(k)
            .map_err(|err| TestCaseError::fail(format!("BmcTranslator::new failed: {err}")))?;
        trans
            .declare_var("x", TlaSort::Int)
            .map_err(|err| TestCaseError::fail(format!("declare_var failed: {err}")))?;

        let init_expr = spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID))),
            Box::new(spanned(Expr::Int(BigInt::from(init)))),
        ));
        let init_term = trans
            .translate_init(&init_expr)
            .map_err(|err| TestCaseError::fail(format!("translate_init failed: {err}")))?;
        trans.assert(init_term);

        for step in 0..k {
            let next = spanned(Expr::Eq(
                Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
                    "x".to_string(), tla_core::name_intern::NameId::INVALID)))))),
                Box::new(spanned(Expr::Add(
                    Box::new(spanned(Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID))),
                    Box::new(spanned(Expr::Int(BigInt::from(delta)))),
                ))),
            ));
            let next_term = trans
                .translate_next(&next, step)
                .map_err(|err| TestCaseError::fail(format!("translate_next failed: {err}")))?;
            trans.assert(next_term);
        }

        prop_assert!(matches!(trans.check_sat(), SolveResult::Sat));

        let model = trans
            .get_model()
            .ok_or_else(|| TestCaseError::fail("expected model for SAT result"))?;
        let trace = trans.extract_trace(&model);

        prop_assert_eq!(trace.len(), k + 1);
        prop_assert_eq!(int_assignment(&trace[0].assignments, "x"), Some(init));

        for step in 0..k {
            let curr = int_assignment(&trace[step].assignments, "x");
            let next = int_assignment(&trace[step + 1].assignments, "x");
            prop_assert_eq!(curr.map(|v| v + delta), next);
        }
    }
}
