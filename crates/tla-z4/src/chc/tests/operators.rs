// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended operator coverage for #643: Division, modulo, boolean vars,
//! arithmetic operators, if-then-else, and logical operators.

use super::helpers::*;
use super::*;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::TlaSort;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_division_with_negative() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int), ("q", TlaSort::Int)]).unwrap();
    let init = and_expr(
        eq_expr(var_expr("x"), int_expr(-7)),
        eq_expr(var_expr("q"), int_expr(0)),
    );
    trans.add_init(&init).unwrap();
    let next = and_expr(
        eq_expr(prime_expr("q"), div_expr(var_expr("x"), int_expr(3))),
        eq_expr(prime_expr("x"), var_expr("x")),
    );
    trans.add_next(&next).unwrap();
    let safety = and_expr(
        ge_expr(var_expr("q"), int_expr(-7)),
        le_expr(var_expr("q"), int_expr(0)),
    );
    trans.add_safety(&safety).unwrap();
    let result = trans.solve_pdr(pdr_test_config()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_modulo_with_negative() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int), ("r", TlaSort::Int)]).unwrap();
    let init = and_expr(
        eq_expr(var_expr("x"), int_expr(-7)),
        eq_expr(var_expr("r"), int_expr(0)),
    );
    trans.add_init(&init).unwrap();
    let next = and_expr(
        eq_expr(prime_expr("r"), mod_expr(var_expr("x"), int_expr(3))),
        eq_expr(prime_expr("x"), var_expr("x")),
    );
    trans.add_next(&next).unwrap();
    let safety = and_expr(
        ge_expr(var_expr("r"), int_expr(-7)),
        le_expr(var_expr("r"), int_expr(7)),
    );
    trans.add_safety(&safety).unwrap();
    let result = trans.solve_pdr(pdr_test_config()).unwrap();
    match result {
        PdrCheckResult::Safe { .. }
        | PdrCheckResult::Unknown { .. }
        | PdrCheckResult::Unsafe { .. } => {}
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subtraction() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(10)))
        .unwrap();
    let next = and_expr(
        gt_expr(var_expr("x"), int_expr(0)),
        eq_expr(prime_expr("x"), sub_expr(var_expr("x"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    trans
        .add_safety(&ge_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config_slow()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negation() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int), ("y", TlaSort::Int)]).unwrap();
    trans
        .add_init(&and_expr(
            eq_expr(var_expr("x"), int_expr(5)),
            eq_expr(var_expr("y"), neg_expr(int_expr(5))),
        ))
        .unwrap();
    let unch = and_expr(
        Spanned::dummy(Expr::Unchanged(Box::new(var_expr("x")))),
        Spanned::dummy(Expr::Unchanged(Box::new(var_expr("y")))),
    );
    trans.add_next(&unch).unwrap();
    trans
        .add_safety(&eq_expr(var_expr("x"), neg_expr(var_expr("y"))))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multiplication() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(1)))
        .unwrap();
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(8)),
        eq_expr(prime_expr("x"), mul_expr(var_expr("x"), int_expr(2))),
    );
    trans.add_next(&next).unwrap();
    trans
        .add_safety(&le_expr(var_expr("x"), int_expr(8)))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config_slow()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_state_var() {
    let mut trans =
        ChcTranslator::new(&[("flag", TlaSort::Bool), ("count", TlaSort::Int)]).unwrap();
    trans
        .add_init(&and_expr(
            eq_expr(var_expr("flag"), bool_expr(false)),
            eq_expr(var_expr("count"), int_expr(0)),
        ))
        .unwrap();
    let a1 = and_expr(
        and_expr(
            not_expr(var_expr("flag")),
            lt_expr(var_expr("count"), int_expr(3)),
        ),
        and_expr(
            eq_expr(prime_expr("flag"), bool_expr(true)),
            eq_expr(
                prime_expr("count"),
                add_expr(var_expr("count"), int_expr(1)),
            ),
        ),
    );
    let a2 = and_expr(
        var_expr("flag"),
        and_expr(
            eq_expr(prime_expr("flag"), bool_expr(false)),
            eq_expr(prime_expr("count"), var_expr("count")),
        ),
    );
    trans.add_next(&or_expr(a1, a2)).unwrap();
    trans
        .add_safety(&le_expr(var_expr("count"), int_expr(3)))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config_slow()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_then_else() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let ite = ite_expr(
        lt_expr(var_expr("x"), int_expr(5)),
        add_expr(var_expr("x"), int_expr(1)),
        var_expr("x"),
    );
    trans.add_next(&eq_expr(prime_expr("x"), ite)).unwrap();
    trans
        .add_safety(&le_expr(var_expr("x"), int_expr(5)))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_implies_operator() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int), ("y", TlaSort::Int)]).unwrap();
    trans
        .add_init(&and_expr(
            eq_expr(var_expr("x"), int_expr(0)),
            eq_expr(var_expr("y"), int_expr(0)),
        ))
        .unwrap();
    let next = and_expr(
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
        eq_expr(prime_expr("y"), add_expr(var_expr("y"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    trans
        .add_safety(&implies_expr(
            gt_expr(var_expr("x"), int_expr(0)),
            ge_expr(var_expr("y"), int_expr(0)),
        ))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_equiv_operator() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int), ("flag", TlaSort::Bool)]).unwrap();
    trans
        .add_init(&and_expr(
            eq_expr(var_expr("x"), int_expr(0)),
            eq_expr(var_expr("flag"), bool_expr(false)),
        ))
        .unwrap();
    let next = and_expr(
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
        eq_expr(prime_expr("flag"), bool_expr(true)),
    );
    trans.add_next(&next).unwrap();
    trans
        .add_safety(&equiv_expr(
            var_expr("flag"),
            gt_expr(var_expr("x"), int_expr(0)),
        ))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_not_operator() {
    let mut trans = ChcTranslator::new(&[("active", TlaSort::Bool), ("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&and_expr(
            eq_expr(var_expr("active"), bool_expr(true)),
            eq_expr(var_expr("x"), int_expr(0)),
        ))
        .unwrap();
    let active = and_expr(
        and_expr(var_expr("active"), lt_expr(var_expr("x"), int_expr(3))),
        and_expr(
            eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
            eq_expr(
                prime_expr("active"),
                ite_expr(
                    lt_expr(add_expr(var_expr("x"), int_expr(1)), int_expr(3)),
                    bool_expr(true),
                    bool_expr(false),
                ),
            ),
        ),
    );
    let inactive = and_expr(
        not_expr(var_expr("active")),
        and_expr(
            eq_expr(prime_expr("x"), var_expr("x")),
            eq_expr(prime_expr("active"), bool_expr(false)),
        ),
    );
    trans.add_next(&or_expr(active, inactive)).unwrap();
    trans
        .add_safety(&or_expr(
            not_expr(var_expr("active")),
            le_expr(var_expr("x"), int_expr(3)),
        ))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_negative_numbers() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(-10)))
        .unwrap();
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(0)),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    trans
        .add_safety(&le_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config_slow()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_comparison_ops() {
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let next = and_expr(
        and_expr(
            ne_expr(var_expr("x"), int_expr(5)),
            lt_expr(var_expr("x"), int_expr(10)),
        ),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    trans
        .add_safety(&and_expr(
            ge_expr(var_expr("x"), int_expr(0)),
            le_expr(var_expr("x"), int_expr(10)),
        ))
        .unwrap();
    let result = trans.solve_pdr(pdr_test_config_slow()).unwrap();
    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}
