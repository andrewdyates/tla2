// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::collections::HashMap;

// ============================================================================
// Feature #572: Conjunct selection (Init!1 syntax)
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conjunct_selection_init_1() {
    // Test conjunct selection: Init == (x = 1) /\ (y = 2), Init!1 = (x = 1)
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // Define Init == (x = 1) /\ (y = 2)
    let init_def = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    ));

    let mut defs = HashMap::new();
    defs.insert("Init".to_string(), init_def);
    trans.set_constant_defs(defs);

    // Translate Init!1 (should be x = 1)
    let init_1_expr = spanned(Expr::ModuleRef(
        ModuleTarget::Named("Init".to_string()),
        "1".to_string(),
        vec![],
    ));

    let term = trans.translate_bool(&init_1_expr).unwrap();
    trans.assert(term);

    // Should be satisfiable with x = 1
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("x").cloned(), Some(bi(1)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conjunct_selection_init_2() {
    // Test conjunct selection: Init == (x = 1) /\ (y = 2), Init!2 = (y = 2)
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // Define Init == (x = 1) /\ (y = 2)
    let init_def = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    ));

    let mut defs = HashMap::new();
    defs.insert("Init".to_string(), init_def);
    trans.set_constant_defs(defs);

    // Translate Init!2 (should be y = 2)
    let init_2_expr = spanned(Expr::ModuleRef(
        ModuleTarget::Named("Init".to_string()),
        "2".to_string(),
        vec![],
    ));

    let term = trans.translate_bool(&init_2_expr).unwrap();
    trans.assert(term);

    // Should be satisfiable with y = 2
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("y").cloned(), Some(bi(2)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conjunct_selection_out_of_range() {
    // Test conjunct selection with out-of-range index
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // Define Init == (x = 1) /\ (x = 2) - only 2 conjuncts
    let init_def = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    ));

    let mut defs = HashMap::new();
    defs.insert("Init".to_string(), init_def);
    trans.set_constant_defs(defs);

    // Translate Init!3 (should fail - only 2 conjuncts)
    let init_3_expr = spanned(Expr::ModuleRef(
        ModuleTarget::Named("Init".to_string()),
        "3".to_string(),
        vec![],
    ));

    let result = trans.translate_bool(&init_3_expr);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("out of range"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conjunct_selection_init_0_rejected() {
    // Test conjunct selection: Init!0 should be rejected (1-based indexing)
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let init_def = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        ))),
    ));

    let mut defs = HashMap::new();
    defs.insert("Init".to_string(), init_def);
    trans.set_constant_defs(defs);

    // Init!0 should fail (1-based indexing)
    let init_0_expr = spanned(Expr::ModuleRef(
        ModuleTarget::Named("Init".to_string()),
        "0".to_string(),
        vec![],
    ));

    let result = trans.translate_bool(&init_0_expr);
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("ModuleRef not supported"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conjunct_selection_not_conjunction() {
    // Test conjunct selection on non-conjunction body
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // Define Init == (x = 1) - NOT a conjunction
    let init_def = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));

    let mut defs = HashMap::new();
    defs.insert("Init".to_string(), init_def);
    trans.set_constant_defs(defs);

    // Init!1 on non-conjunction should fail
    let init_1_expr = spanned(Expr::ModuleRef(
        ModuleTarget::Named("Init".to_string()),
        "1".to_string(),
        vec![],
    ));

    let result = trans.translate_bool(&init_1_expr);
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("not a conjunction"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conjunct_selection_nested_three_conjuncts() {
    // Test conjunct selection with 3 conjuncts: Init == (a) /\ (b) /\ (c)
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();
    trans.declare_var("z", TlaSort::Int).unwrap();

    // Define Init == (x = 1) /\ (y = 2) /\ (z = 3)
    let init_def = spanned(Expr::And(
        Box::new(spanned(Expr::And(
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
            ))),
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "y".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(2)))),
            ))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "z".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(3)))),
        ))),
    ));

    let mut defs = HashMap::new();
    defs.insert("Init".to_string(), init_def);
    trans.set_constant_defs(defs);

    // Init!3 should be z = 3
    let init_3_expr = spanned(Expr::ModuleRef(
        ModuleTarget::Named("Init".to_string()),
        "3".to_string(),
        vec![],
    ));

    let term = trans.translate_bool(&init_3_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("z").cloned(), Some(bi(3)));
}
