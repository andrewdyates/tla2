// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for #647: In/Range/SetEnum/Let + NotIn operator support in CHC
//! translation. Implies and Equiv are already covered in operators.rs via the
//! shared `dispatch_translate_bool` trait dispatch.

use super::helpers::*;
use super::*;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::TlaSort;

// ---------------------------------------------------------------------------
// \in with SetEnum — translate to disjunction x = a \/ x = b \/ x = c
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_set_enum_safe() {
    // x starts in {1,2,3}, stays in that set
    // Init: x = 1
    // Next: x' \in {1,2,3} /\ x' = IF x < 3 THEN x+1 ELSE 1
    // Safety: x \in {1,2,3}
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(1)))
        .unwrap();
    let next = eq_expr(
        prime_expr("x"),
        ite_expr(
            lt_expr(var_expr("x"), int_expr(3)),
            add_expr(var_expr("x"), int_expr(1)),
            int_expr(1),
        ),
    );
    trans.add_next(&next).unwrap();
    let safety = in_expr(
        var_expr("x"),
        set_enum_expr(vec![int_expr(1), int_expr(2), int_expr(3)]),
    );
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_set_enum_unsafe() {
    // x starts at 1, increments unboundedly, but we claim x \in {1,2,3}
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(1)))
        .unwrap();
    trans
        .add_next(&eq_expr(
            prime_expr("x"),
            add_expr(var_expr("x"), int_expr(1)),
        ))
        .unwrap();
    let safety = in_expr(
        var_expr("x"),
        set_enum_expr(vec![int_expr(1), int_expr(2), int_expr(3)]),
    );
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Unsafe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Safe { .. } => panic!("Expected Unsafe or Unknown"),
    }
}

// ---------------------------------------------------------------------------
// \in with Range — translate to a <= x /\ x <= b
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_safe() {
    // x starts at 0, increments up to 5, stays in 0..5
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(5)),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    let safety = in_expr(var_expr("x"), range_expr(int_expr(0), int_expr(5)));
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_range_unsafe() {
    // x starts at 0, increments unboundedly, claims x \in 0..3
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    trans
        .add_next(&eq_expr(
            prime_expr("x"),
            add_expr(var_expr("x"), int_expr(1)),
        ))
        .unwrap();
    let safety = in_expr(var_expr("x"), range_expr(int_expr(0), int_expr(3)));
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Unsafe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Safe { .. } => panic!("Expected Unsafe or Unknown"),
    }
}

// ---------------------------------------------------------------------------
// NotIn — translate to negation of membership
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notin_set_enum() {
    // x starts at 10, stays at 10 — x \notin {1,2,3} should be safe
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(10)))
        .unwrap();
    let next = Spanned::dummy(Expr::Unchanged(Box::new(var_expr("x"))));
    trans.add_next(&next).unwrap();
    let safety = notin_expr(
        var_expr("x"),
        set_enum_expr(vec![int_expr(1), int_expr(2), int_expr(3)]),
    );
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

// ---------------------------------------------------------------------------
// LET x == e IN body — inline substitution
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_in_bool_context() {
    // LET limit == 5 IN x <= limit
    // x starts at 0, increments up to 5
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(5)),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    // Safety: LET limit == 5 IN x <= limit
    let safety = let_expr(
        vec![("limit", int_expr(5))],
        le_expr(var_expr("x"), ident_expr("limit")),
    );
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_let_in_int_context() {
    // LET step == 1 IN x + step
    // x starts at 0, updates via LET with step=1
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    // Next: x < 5 /\ x' = LET step == 1 IN x + step
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(5)),
        eq_expr(
            prime_expr("x"),
            let_expr(
                vec![("step", int_expr(1))],
                add_expr(var_expr("x"), ident_expr("step")),
            ),
        ),
    );
    trans.add_next(&next).unwrap();
    let safety = le_expr(var_expr("x"), int_expr(5));
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config_slow()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_multiple_defs() {
    // LET lo == 0 IN LET hi == 5 IN x >= lo /\ x <= hi
    // Nested LET with multiple definitions
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(5)),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    // Safety: LET lo == 0, hi == 5 IN x >= lo /\ x <= hi
    let safety = let_expr(
        vec![("lo", int_expr(0)), ("hi", int_expr(5))],
        and_expr(
            ge_expr(var_expr("x"), ident_expr("lo")),
            le_expr(var_expr("x"), ident_expr("hi")),
        ),
    );
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_in_init() {
    // LET start == 0 IN x = start
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    let init = let_expr(
        vec![("start", int_expr(0))],
        eq_expr(var_expr("x"), ident_expr("start")),
    );
    trans.add_init(&init).unwrap();
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(3)),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    trans
        .add_safety(&le_expr(var_expr("x"), int_expr(3)))
        .unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_in_next() {
    // Next uses LET to define increment: LET inc == 1 IN x' = x + inc
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(5)),
        let_expr(
            vec![("inc", int_expr(1))],
            eq_expr(prime_expr("x"), add_expr(var_expr("x"), ident_expr("inc"))),
        ),
    );
    trans.add_next(&next).unwrap();
    trans
        .add_safety(&le_expr(var_expr("x"), int_expr(5)))
        .unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

// ---------------------------------------------------------------------------
// Combined operators — mixing \in, LET, Implies, Equiv in one spec
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_combined_let_in_implies() {
    // LET max == 3 IN (x > 0 => x \in 1..max)
    let mut trans = ChcTranslator::new(&[("x", TlaSort::Int)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("x"), int_expr(0)))
        .unwrap();
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(3)),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );
    trans.add_next(&next).unwrap();
    // Safety: LET max == 3 IN (x > 0 => x \in 1..max)
    let safety = let_expr(
        vec![("max", int_expr(3))],
        implies_expr(
            gt_expr(var_expr("x"), int_expr(0)),
            in_expr(var_expr("x"), range_expr(int_expr(1), ident_expr("max"))),
        ),
    );
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_set_enum_boolean() {
    // flag \in {TRUE, FALSE} is always true for a Bool var
    let mut trans = ChcTranslator::new(&[("flag", TlaSort::Bool)]).unwrap();
    trans
        .add_init(&eq_expr(var_expr("flag"), bool_expr(false)))
        .unwrap();
    let next = eq_expr(prime_expr("flag"), not_expr(var_expr("flag")));
    trans.add_next(&next).unwrap();
    // Safety: flag \in BOOLEAN (using Ident "BOOLEAN" which the translator
    // handles specially — test the SetEnum path instead)
    let safety = in_expr(
        var_expr("flag"),
        set_enum_expr(vec![bool_expr(true), bool_expr(false)]),
    );
    trans.add_safety(&safety).unwrap();
    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => panic!("Expected Safe or Unknown"),
    }
}
