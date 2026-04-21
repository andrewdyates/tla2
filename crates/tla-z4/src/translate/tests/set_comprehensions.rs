// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Phase 2c: SetFilter and SetBuilder tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_filter_basic() {
    // Test: x \in {y \in 1..5 : y > 2}
    // Should find x in {3, 4, 5}
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // {y \in 1..5 : y > 2}
    let bound = BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        )))),
        pattern: None,
    };
    let pred = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let filter_set = spanned(Expr::SetFilter(bound, Box::new(pred)));

    // x \in {y \in 1..5 : y > 2}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(filter_set),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x = model.int_val("x").unwrap();
    assert!(
        (bi(3)..=bi(5)).contains(x),
        "x should be in {{3, 4, 5}}, got {x}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_filter_unsatisfiable() {
    // Test: x \in {y \in 1..3 : y > 10} should be UNSAT
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    let bound = BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        )))),
        pattern: None,
    };
    let pred = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let filter_set = spanned(Expr::SetFilter(bound, Box::new(pred)));

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(filter_set),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    // No element in 1..3 is > 10, so UNSAT
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_filter_enumeration() {
    use std::collections::BTreeSet;

    // Enumerate all x in {y \in 1..5 : y > 2}
    // Should yield exactly {3, 4, 5}
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    let bound = BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        )))),
        pattern: None,
    };
    let pred = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let filter_set = spanned(Expr::SetFilter(bound, Box::new(pred)));

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(filter_set),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    let mut solutions = BTreeSet::new();
    for _ in 0..10 {
        match trans.check_sat() {
            SolveResult::Sat => {
                let model = trans.get_model().unwrap();
                let x = model.int_val("x").unwrap();
                solutions.insert(x.clone());

                // Block this solution
                let blocking = spanned(Expr::Neq(
                    Box::new(spanned(Expr::Ident(
                        "x".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(x.clone()))),
                ));
                let blocking_term = trans.translate_bool(&blocking).unwrap();
                trans.assert(blocking_term);
            }
            SolveResult::Unsat(_) => break,
            SolveResult::Unknown => panic!("Unexpected Unknown"),
            _ => panic!("unexpected SolveResult variant"),
        }
    }

    let expected: BTreeSet<BigInt> = [bi(3), bi(4), bi(5)].into_iter().collect();
    assert_eq!(solutions, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_basic() {
    // Test: x \in {y + 10 : y \in {1, 2, 3}}
    // Should find x in {11, 12, 13}
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // {y + 10 : y \in {1, 2, 3}}
    let body = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let bounds = vec![BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ])))),
        pattern: None,
    }];
    let builder_set = spanned(Expr::SetBuilder(Box::new(body), bounds));

    // x \in {y + 10 : y \in {1, 2, 3}}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(builder_set),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x = model.int_val("x").unwrap();
    assert!(
        (bi(11)..=bi(13)).contains(x),
        "x should be in {{11, 12, 13}}, got {x}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_enumeration() {
    use std::collections::BTreeSet;

    // Enumerate all x in {y * 2 : y \in {1, 2, 3}}
    // Should yield exactly {2, 4, 6}
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    let body = spanned(Expr::Mul(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let bounds = vec![BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ])))),
        pattern: None,
    }];
    let builder_set = spanned(Expr::SetBuilder(Box::new(body), bounds));

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(builder_set),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    let mut solutions = BTreeSet::new();
    for _ in 0..10 {
        match trans.check_sat() {
            SolveResult::Sat => {
                let model = trans.get_model().unwrap();
                let x = model.int_val("x").unwrap();
                solutions.insert(x.clone());

                let blocking = spanned(Expr::Neq(
                    Box::new(spanned(Expr::Ident(
                        "x".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(x.clone()))),
                ));
                let blocking_term = trans.translate_bool(&blocking).unwrap();
                trans.assert(blocking_term);
            }
            SolveResult::Unsat(_) => break,
            SolveResult::Unknown => panic!("Unexpected Unknown"),
            _ => panic!("unexpected SolveResult variant"),
        }
    }

    let expected: BTreeSet<BigInt> = [bi(2), bi(4), bi(6)].into_iter().collect();
    assert_eq!(solutions, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_with_constraint() {
    // Test: x \in {y + 10 : y \in 1..5} /\ x > 13
    // Should find x in {14, 15}
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    let body = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    let bounds = vec![BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        )))),
        pattern: None,
    }];
    let builder_set = spanned(Expr::SetBuilder(Box::new(body), bounds));

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(builder_set),
    ));

    let constraint = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(13)))),
    ));

    let combined = spanned(Expr::And(Box::new(membership), Box::new(constraint)));

    let term = trans.translate_bool(&combined).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x = model.int_val("x").unwrap();
    assert!(
        *x == bi(14) || *x == bi(15),
        "x should be 14 or 15, got {x}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_filter_nested_in_set_builder() {
    use std::collections::BTreeSet;

    // Test: x \in {y * 2 : y \in {z \in 1..5 : z > 2}}
    // Inner set: {3, 4, 5}
    // Outer set: {6, 8, 10}
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Inner SetFilter: {z \in 1..5 : z > 2}
    let inner_bound = BoundVar {
        name: spanned("z".to_string()),
        domain: Some(Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        )))),
        pattern: None,
    };
    let inner_pred = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "z".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let inner_filter = Expr::SetFilter(inner_bound, Box::new(inner_pred));

    // Outer SetBuilder: {y * 2 : y \in <inner>}
    let body = spanned(Expr::Mul(
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let bounds = vec![BoundVar {
        name: spanned("y".to_string()),
        domain: Some(Box::new(spanned(inner_filter))),
        pattern: None,
    }];
    let builder_set = spanned(Expr::SetBuilder(Box::new(body), bounds));

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(builder_set),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    let mut solutions = BTreeSet::new();
    for _ in 0..10 {
        match trans.check_sat() {
            SolveResult::Sat => {
                let model = trans.get_model().unwrap();
                let x = model.int_val("x").unwrap();
                solutions.insert(x.clone());

                let blocking = spanned(Expr::Neq(
                    Box::new(spanned(Expr::Ident(
                        "x".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Box::new(spanned(Expr::Int(x.clone()))),
                ));
                let blocking_term = trans.translate_bool(&blocking).unwrap();
                trans.assert(blocking_term);
            }
            SolveResult::Unsat(_) => break,
            SolveResult::Unknown => panic!("Unexpected Unknown"),
            _ => panic!("unexpected SolveResult variant"),
        }
    }

    let expected: BTreeSet<BigInt> = [bi(6), bi(8), bi(10)].into_iter().collect();
    assert_eq!(solutions, expected);
}
