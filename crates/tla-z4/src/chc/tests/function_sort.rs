// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::helpers::*;
use super::*;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::TlaSort;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_function_sort_expands_predicate_arguments() {
    let trans = ChcTranslator::new(&[
        (
            "votes",
            TlaSort::Function {
                domain_keys: vec!["Alice".to_string(), "Bob".to_string()],
                range: Box::new(TlaSort::Bool),
            },
        ),
        ("turn", TlaSort::Int),
    ])
    .unwrap();

    assert!(trans.func_vars.contains_key("votes"));
    assert_eq!(trans.pred_vars.len(), 3);
    assert_eq!(trans.pred_next_vars.len(), 3);
    assert!(trans.vars.contains_key("turn"));
    assert!(trans.next_vars.contains_key("turn"));

    let info = trans.func_vars.get("votes").unwrap();
    assert_eq!(info.domain_keys, vec!["id:Alice", "id:Bob"]);
    assert!(info.element_vars.contains_key("id:Alice"));
    assert!(info.element_vars.contains_key("id:Bob"));
    assert!(info.element_next_vars.contains_key("id:Alice"));
    assert!(info.element_next_vars.contains_key("id:Bob"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_function_unchanged_and_quantified_membership() {
    let nodes = set_enum_expr(vec![ident_expr("Alice"), ident_expr("Bob")]);

    let mut trans = ChcTranslator::new(&[(
        "votes",
        TlaSort::Function {
            domain_keys: vec!["Alice".to_string(), "Bob".to_string()],
            range: Box::new(TlaSort::Bool),
        },
    )])
    .unwrap();

    let init = eq_expr(
        var_expr("votes"),
        func_def_expr(vec![bound_var("n", nodes.clone())], bool_expr(false)),
    );
    trans.add_init(&init).unwrap();

    let next = Spanned::dummy(Expr::Unchanged(Box::new(var_expr("votes"))));
    trans.add_next(&next).unwrap();

    let safety = forall_expr(
        vec![bound_var("n", nodes)],
        eq_expr(
            func_apply_expr(var_expr("votes"), ident_expr("n")),
            bool_expr(false),
        ),
    );
    trans.add_safety(&safety).unwrap();

    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => {
            panic!("expected Safe or Unknown for unchanged function spec")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symbolic_except_via_exists_quantifier() {
    let domain = set_enum_expr(vec![int_expr(0), int_expr(1)]);

    let mut trans = ChcTranslator::new(&[(
        "cells",
        TlaSort::Function {
            domain_keys: vec!["0".to_string(), "1".to_string()],
            range: Box::new(TlaSort::Int),
        },
    )])
    .unwrap();

    let init = eq_expr(
        var_expr("cells"),
        func_def_expr(vec![bound_var("i", domain.clone())], int_expr(0)),
    );
    trans.add_init(&init).unwrap();

    let next = exists_expr(
        vec![bound_var("i", domain.clone())],
        eq_expr(
            prime_expr("cells"),
            except_expr(var_expr("cells"), ident_expr("i"), int_expr(1)),
        ),
    );
    trans.add_next(&next).unwrap();

    let safety = in_expr(
        var_expr("cells"),
        Spanned::dummy(Expr::FuncSet(
            Box::new(domain),
            Box::new(Spanned::dummy(Expr::Range(
                Box::new(int_expr(0)),
                Box::new(int_expr(1)),
            ))),
        )),
    );
    trans.add_safety(&safety).unwrap();

    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => {
            panic!("expected Safe or Unknown for symbolic EXCEPT spec")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_range_function_values() {
    let nodes = set_enum_expr(vec![ident_expr("Alice"), ident_expr("Bob")]);

    let mut trans = ChcTranslator::new(&[(
        "status",
        TlaSort::Function {
            domain_keys: vec!["Alice".to_string(), "Bob".to_string()],
            range: Box::new(TlaSort::String),
        },
    )])
    .unwrap();

    let init = eq_expr(
        var_expr("status"),
        func_def_expr(vec![bound_var("n", nodes.clone())], string_expr("idle")),
    );
    trans.add_init(&init).unwrap();

    let next = Spanned::dummy(Expr::Unchanged(Box::new(var_expr("status"))));
    trans.add_next(&next).unwrap();

    let safety = and_expr(
        eq_expr(
            func_apply_expr(var_expr("status"), ident_expr("Alice")),
            string_expr("idle"),
        ),
        eq_expr(
            func_apply_expr(var_expr("status"), ident_expr("Bob")),
            string_expr("idle"),
        ),
    );
    trans.add_safety(&safety).unwrap();

    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => {
            panic!("expected Safe or Unknown for string-valued function spec")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_domain_func_def_preserves_string_literals() {
    let domain = set_enum_expr(vec![string_expr("a"), string_expr("b")]);

    let mut trans = ChcTranslator::new(&[(
        "votes",
        TlaSort::Function {
            domain_keys: vec!["str:a".to_string(), "str:b".to_string()],
            range: Box::new(TlaSort::Bool),
        },
    )])
    .unwrap();

    let init = eq_expr(
        var_expr("votes"),
        func_def_expr(
            vec![bound_var("s", domain.clone())],
            eq_expr(ident_expr("s"), string_expr("a")),
        ),
    );
    trans.add_init(&init).unwrap();

    let next = Spanned::dummy(Expr::Unchanged(Box::new(var_expr("votes"))));
    trans.add_next(&next).unwrap();

    let safety = and_expr(
        func_apply_expr(var_expr("votes"), string_expr("a")),
        not_expr(func_apply_expr(var_expr("votes"), string_expr("b"))),
    );
    trans.add_safety(&safety).unwrap();

    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => {
            panic!("expected Safe or Unknown for string-keyed function spec")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_sort_expands_predicate_arguments() {
    let trans = ChcTranslator::new(&[
        (
            "can",
            TlaSort::Record {
                field_sorts: vec![
                    ("white".to_string(), TlaSort::Int),
                    ("black".to_string(), TlaSort::Int),
                ],
            },
        ),
        ("turn", TlaSort::Int),
    ])
    .unwrap();

    assert!(trans.record_vars.contains_key("can"));
    assert_eq!(trans.pred_vars.len(), 3);
    assert_eq!(trans.pred_next_vars.len(), 3);
    assert!(trans.vars.contains_key("turn"));
    assert!(trans.next_vars.contains_key("turn"));

    let info = trans.record_vars.get("can").unwrap();
    assert_eq!(
        info.field_sorts,
        vec![
            ("black".to_string(), TlaSort::Int),
            ("white".to_string(), TlaSort::Int),
        ]
    );
    assert!(info.field_vars.contains_key("black"));
    assert!(info.field_vars.contains_key("white"));
    assert!(info.field_next_vars.contains_key("black"));
    assert!(info.field_next_vars.contains_key("white"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_except_and_recordset_membership() {
    let mut trans = ChcTranslator::new(&[(
        "can",
        TlaSort::Record {
            field_sorts: vec![
                ("black".to_string(), TlaSort::Int),
                ("white".to_string(), TlaSort::Int),
            ],
        },
    )])
    .unwrap();

    let init = eq_expr(
        var_expr("can"),
        record_expr(vec![("black", int_expr(2)), ("white", int_expr(1))]),
    );
    trans.add_init(&init).unwrap();

    let next = and_expr(
        gt_expr(record_access_expr(var_expr("can"), "black"), int_expr(0)),
        eq_expr(
            prime_expr("can"),
            record_except_expr(
                record_except_expr(
                    var_expr("can"),
                    "black",
                    sub_expr(ident_expr("@"), int_expr(1)),
                ),
                "white",
                add_expr(ident_expr("@"), int_expr(1)),
            ),
        ),
    );
    trans.add_next(&next).unwrap();

    let safety = and_expr(
        in_expr(
            var_expr("can"),
            record_set_expr(vec![
                (
                    "black",
                    Spanned::dummy(Expr::Range(Box::new(int_expr(0)), Box::new(int_expr(2)))),
                ),
                (
                    "white",
                    Spanned::dummy(Expr::Range(Box::new(int_expr(0)), Box::new(int_expr(3)))),
                ),
            ]),
        ),
        eq_expr(
            add_expr(
                record_access_expr(var_expr("can"), "black"),
                record_access_expr(var_expr("can"), "white"),
            ),
            int_expr(3),
        ),
    );
    trans.add_safety(&safety).unwrap();

    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => {
            panic!("expected Safe or Unknown for record-valued CoffeeCan-shaped spec")
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_field_order_is_name_based() {
    let mut trans = ChcTranslator::new(&[(
        "can",
        TlaSort::Record {
            field_sorts: vec![
                ("black".to_string(), TlaSort::Int),
                ("white".to_string(), TlaSort::Int),
            ],
        },
    )])
    .unwrap();

    let init = eq_expr(
        var_expr("can"),
        record_expr(vec![("white", int_expr(1)), ("black", int_expr(2))]),
    );
    trans.add_init(&init).unwrap();

    let next = Spanned::dummy(Expr::Unchanged(Box::new(var_expr("can"))));
    trans.add_next(&next).unwrap();

    let safety = eq_expr(
        var_expr("can"),
        record_expr(vec![("black", int_expr(2)), ("white", int_expr(1))]),
    );
    trans.add_safety(&safety).unwrap();

    match trans.solve_pdr(pdr_test_config()).unwrap() {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {}
        PdrCheckResult::Unsafe { .. } => {
            panic!("expected Safe or Unknown when record field order differs")
        }
    }
}
