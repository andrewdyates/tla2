// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test If-then-else (ITE) in boolean context
/// Init == x = 5 /\ flag = TRUE
/// Inv == IF flag THEN x > 0 ELSE x < 0 (should hold since flag is TRUE and x > 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_if_then_else_bool() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("flag", TlaSort::Bool).unwrap();

    // Init: x = 5 /\ flag = TRUE
    let init = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "flag".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Bool(true))),
        ))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: IF flag THEN x > 0 ELSE x < 0
    let safety = spanned(Expr::If(
        Box::new(spanned(Expr::Ident(
            "flag".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
        Box::new(spanned(Expr::Lt(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - flag is TRUE, x = 5 > 0
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (IF-THEN-ELSE holds), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Test If-then-else (ITE) in integer context
/// Init == x = 5 /\ y = IF x > 3 THEN 10 ELSE 0
/// Inv == y = 10 (should hold since x > 3)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_if_then_else_int() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // Init: x = 5 /\ y = IF x > 3 THEN 10 ELSE 0
    let init = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::If(
                Box::new(spanned(Expr::Gt(
                    Box::new(spanned(Expr::Ident(
                        "x".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(BigInt::from(3)))),
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(10)))),
                Box::new(spanned(Expr::Int(BigInt::from(0)))),
            ))),
        ))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: y = 10
    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - x = 5 > 3, so y = 10
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (y = 10 holds), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Test complex primed expressions (Prime wrapping non-Ident)
/// Init == x = 0
/// Next == (x + 1)' = x + 2  (primed addition expression)
/// This tests the code path where Prime wraps a complex expression
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_complex_primed_expr() {
    let k = 2;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 0
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Next: (x + 1)' = x + 2
    // The Prime wraps an Add expression, not just an Ident
    // This means x' + 1 = x + 2, which simplifies to x' = x + 1
    for step in 0..k {
        let next = spanned(Expr::Eq(
            Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Add(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
            )))))),
            Box::new(spanned(Expr::Add(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(2)))),
            ))),
        ));
        let next_term = trans.translate_next(&next, step).unwrap();
        trans.assert(next_term);
    }

    // Safety: x <= 1
    let safety = spanned(Expr::Leq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be SAT - violation at step 2 (x=2)
    match trans.check_sat() {
        SolveResult::Sat => {
            let model = trans.get_model().unwrap();
            let trace = trans.extract_trace(&model);
            // x goes: 0 -> 1 -> 2, violation at step 2
            let violation_step = trace
                .iter()
                .find(|s| {
                    if let Some(BmcValue::Int(v)) = s.assignments.get("x") {
                        *v > 1
                    } else {
                        false
                    }
                })
                .map(|s| s.step);
            assert_eq!(violation_step, Some(2));
        }
        SolveResult::Unsat(_) => panic!("expected SAT (violation at step 2), got UNSAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Test edge case: empty SetEnum membership is always false
/// x \in {} should be UNSAT regardless of x's value
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_empty_set_membership() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 5 (any value)
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: x \in {} (empty set - always false)
    let safety = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![]))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be SAT - safety is "x \in {}" = false, so !safety = true
    match trans.check_sat() {
        SolveResult::Sat => {} // Expected - empty set membership is always false
        SolveResult::Unsat(_) => panic!("expected SAT (empty set membership is false), got UNSAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}
