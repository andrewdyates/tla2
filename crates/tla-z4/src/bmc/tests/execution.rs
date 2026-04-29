// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Simple counter spec test
/// Init == count = 0
/// Next == count' = count + 1
/// Inv == count <= 5
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_simple_counter() {
    // Test k=10, violation should be found at step 6
    let k = 10;
    let mut trans = BmcTranslator::new(k).unwrap();

    // Declare variable
    trans.declare_var("count", TlaSort::Int).unwrap();

    // Init: count = 0
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Next: count' = count + 1
    // For each step 0..k-1
    for step in 0..k {
        let next = spanned(Expr::Eq(
            Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
                "count".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )))))),
            Box::new(spanned(Expr::Add(
                Box::new(spanned(Expr::Ident(
                    "count".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
            ))),
        ));
        let next_term = trans.translate_next(&next, step).unwrap();
        trans.assert(next_term);
    }

    // Safety: count <= 5
    // Check NOT safety at all steps
    let safety = spanned(Expr::Leq(
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Check SAT - should find violation
    match trans.check_sat() {
        SolveResult::Sat => {
            // Extract trace and verify
            let model = trans.get_model().unwrap();
            let trace = trans.extract_trace(&model);

            // Find the first step where count > 5
            let violation_step = trace
                .iter()
                .find(|s| {
                    if let Some(BmcValue::Int(v)) = s.assignments.get("count") {
                        *v > 5
                    } else {
                        false
                    }
                })
                .map(|s| s.step);

            assert_eq!(
                violation_step,
                Some(6),
                "violation should be at step 6 (count=6)"
            );
        }
        SolveResult::Unsat(_) => panic!("expected SAT (violation), got UNSAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_rejects_non_linear_mul() {
    let mut trans = BmcTranslator::new(0).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    let expr = spanned(Expr::Gt(
        Box::new(spanned(Expr::Mul(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    let err = trans.translate_bool(&expr).unwrap_err();
    assert!(
        matches!(err, Z4Error::UnsupportedOp(_)),
        "expected UnsupportedOp, got {err:?}"
    );
}

/// Test where no violation exists within bound
/// Init == x \in {0, 1}
/// Next == x' = x (stuttering)
/// Inv == x >= 0
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_no_violation() {
    let k = 5;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x \in {0, 1}
    let init = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(0))),
            spanned(Expr::Int(BigInt::from(1))),
        ]))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Next: x' = x (stuttering)
    for step in 0..k {
        let next = spanned(Expr::Eq(
            Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )))))),
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ));
        let next_term = trans.translate_next(&next, step).unwrap();
        trans.assert(next_term);
    }

    // Safety: x >= 0
    let safety = spanned(Expr::Geq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - no violation
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (no violation), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Test UNCHANGED handling
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_unchanged() {
    let k = 3;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // Init: x = 5 /\ y = 10
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
            Box::new(spanned(Expr::Int(BigInt::from(10)))),
        ))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Next: UNCHANGED <<x, y>>
    for step in 0..k {
        let next = spanned(Expr::Unchanged(Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        ])))));
        let next_term = trans.translate_next(&next, step).unwrap();
        trans.assert(next_term);
    }

    // Safety: x + y = 15
    let safety = spanned(Expr::Eq(
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
        Box::new(spanned(Expr::Int(BigInt::from(15)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - x + y = 15 is always true
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (UNCHANGED preserves invariant), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Test k=0: Only Init state, no Next transitions
/// This tests the edge case where we only check the initial state.
/// Init == x = 10
/// Inv == x > 5 (should hold)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_k0_init_only() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 10
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // No Next assertions for k=0

    // Safety: x > 5
    let safety = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - x = 10 > 5, so invariant holds at Init
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (Init satisfies invariant), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Test k=0 with Init violation
/// Init == x = 3
/// Inv == x > 5 (should fail at Init)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_k0_init_violation() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 3
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: x > 5
    let safety = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be SAT - x = 3 < 5, so invariant fails at Init
    match trans.check_sat() {
        SolveResult::Sat => {
            // Extract trace and verify
            let model = trans.get_model().unwrap();
            let trace = trans.extract_trace(&model);
            assert_eq!(trace.len(), 1, "k=0 should have exactly 1 state");
            assert_eq!(trace[0].step, 0);
        }
        SolveResult::Unsat(_) => panic!("expected SAT (Init violates invariant), got UNSAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}
