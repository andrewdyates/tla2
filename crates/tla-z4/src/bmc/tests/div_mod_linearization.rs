// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// IntDiv with positive constant divisor uses QF_LIA linearization.
/// Test: x \div 3 with constraint that should find x = 10 → x \div 3 = 3.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_intdiv_linearization() {
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

    // Safety: (x \div 3) = 3  (10 \div 3 = 3, so this should hold)
    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - 10 \div 3 = 3 holds
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (10 div 3 = 3), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// IntDiv linearization with negative dividend: -10 \div 3 = -4 (floor division).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_intdiv_linearization_negative() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = -10
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(-10)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: (x \div 3) = -4  (-10 \div 3 = -4 floor division)
    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(-4)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - -10 \div 3 = -4 holds
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (-10 div 3 = -4), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Mod with positive constant divisor uses QF_LIA linearization.
/// Test: x % 3 with constraint that should find x = 10 → x % 3 = 1.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_mod_linearization() {
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

    // Safety: (x % 3) = 1  (10 % 3 = 1, so this should hold)
    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Mod(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - 10 % 3 = 1 holds
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (10 mod 3 = 1), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Mod linearization with negative dividend: -10 % 3 = 2 (TLC semantics: remainder in [0, k-1]).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_mod_linearization_negative() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = -10
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(-10)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: (x % 3) = 2  (-10 % 3 = 2 with TLC semantics)
    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Mod(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - -10 % 3 = 2 holds
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (-10 mod 3 = 2), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Combined div/mod linearization: verify that x \div k and x % k are consistent.
/// x = 17, k = 5 → x \div 5 = 3, x % 5 = 2, and 5*3 + 2 = 17
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_divmod_linearization_consistency() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 17
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(17)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: 5 * (x \div 5) + (x % 5) = x
    // This should always hold by definition of division and modulo.
    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Mul(
                Box::new(spanned(Expr::Int(BigInt::from(5)))),
                Box::new(spanned(Expr::IntDiv(
                    Box::new(spanned(Expr::Ident(
                        "x".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(BigInt::from(5)))),
                ))),
            ))),
            Box::new(spanned(Expr::Mod(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(5)))),
            ))),
        ))),
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - the identity always holds
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (k*(x div k) + (x mod k) = x), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Edge case: k=1 linearization (x \div 1 = x, x % 1 = 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_divmod_linearization_k1() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = 42
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(42)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: (x \div 1) = x /\ (x % 1) = 0
    let div_eq_x = spanned(Expr::Eq(
        Box::new(spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let mod_eq_0 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Mod(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    let safety = spanned(Expr::And(Box::new(div_eq_x), Box::new(mod_eq_0)));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - x div 1 = x and x % 1 = 0 always hold
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (x div 1 = x, x mod 1 = 0), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Edge case: x=0 (0 \div k = 0, 0 % k = 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_divmod_linearization_x0() {
    let k = 0;
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

    // Safety: (x \div 7) = 0 /\ (x % 7) = 0
    let div_eq_0 = spanned(Expr::Eq(
        Box::new(spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(7)))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    let mod_eq_0 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Mod(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(7)))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    let safety = spanned(Expr::And(Box::new(div_eq_0), Box::new(mod_eq_0)));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - 0 div k = 0 and 0 % k = 0 always hold
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => panic!("expected UNSAT (0 div k = 0, 0 mod k = 0), got SAT"),
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Edge case: negative x consistency (k*(x div k) + (x mod k) = x for x < 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_divmod_linearization_negative_consistency() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // Init: x = -17
    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(-17)))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    // Safety: 5 * (x \div 5) + (x % 5) = x
    // For x = -17, k = 5: -17 = 5*(-4) + 3 = -20 + 3 = -17 ✓
    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Mul(
                Box::new(spanned(Expr::Int(BigInt::from(5)))),
                Box::new(spanned(Expr::IntDiv(
                    Box::new(spanned(Expr::Ident(
                        "x".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(BigInt::from(5)))),
                ))),
            ))),
            Box::new(spanned(Expr::Mod(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(5)))),
            ))),
        ))),
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    // Should be UNSAT - the identity always holds even for negative x
    match trans.check_sat() {
        SolveResult::Unsat(_) => {} // Expected
        SolveResult::Sat => {
            panic!("expected UNSAT (k*(x div k) + (x mod k) = x for negative x), got SAT")
        }
        SolveResult::Unknown => panic!("solver returned unknown"),
        _ => panic!("unexpected SolveResult variant"),
    }
}
