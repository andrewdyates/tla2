// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort inference tests (check_init_assignment, check_membership_constraint)
//!
//! Split from z4_pdr/tests.rs — Part of #3692

use super::helpers::*;
use super::*;
use crate::z4_shared::{check_init_assignment, check_membership_constraint};
use num_bigint::BigInt;
use tla_core::ast::Expr;
use tla_core::Spanned;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_init_int() {
    let init = eq_expr(var_expr("x"), int_expr(0));
    let sort = check_init_assignment("x", &init);
    assert_eq!(sort, Some(TlaSort::Int));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_init_int_under_let() {
    let init = let1_expr("a", int_expr(1), eq_expr(var_expr("x"), int_expr(0)));
    let sort = check_init_assignment("x", &init);
    assert_eq!(sort, Some(TlaSort::Int));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_init_bool() {
    let init = eq_expr(var_expr("flag"), Spanned::dummy(Expr::Bool(false)));
    let sort = check_init_assignment("flag", &init);
    assert_eq!(sort, Some(TlaSort::Bool));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_init_bool_under_nested_let() {
    let inner = let1_expr(
        "b",
        Spanned::dummy(Expr::Bool(true)),
        eq_expr(var_expr("flag"), Spanned::dummy(Expr::Bool(false))),
    );
    let init = let1_expr("a", int_expr(1), inner);
    let sort = check_init_assignment("flag", &init);
    assert_eq!(sort, Some(TlaSort::Bool));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_boolean_membership() {
    let type_ok = Spanned::dummy(Expr::In(
        Box::new(var_expr("flag")),
        Box::new(Spanned::dummy(Expr::Ident(
            "BOOLEAN".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let sort = check_membership_constraint("flag", &type_ok);
    assert_eq!(sort, Some(TlaSort::Bool));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_boolean_membership_under_let() {
    let type_ok = let1_expr(
        "a",
        int_expr(1),
        Spanned::dummy(Expr::In(
            Box::new(var_expr("flag")),
            Box::new(Spanned::dummy(Expr::Ident(
                "BOOLEAN".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        )),
    );
    let sort = check_membership_constraint("flag", &type_ok);
    assert_eq!(sort, Some(TlaSort::Bool));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_nat_membership() {
    let type_ok = Spanned::dummy(Expr::In(
        Box::new(var_expr("count")),
        Box::new(Spanned::dummy(Expr::Ident(
            "Nat".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let sort = check_membership_constraint("count", &type_ok);
    assert_eq!(sort, Some(TlaSort::Int));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_function_membership() {
    let domain = set_enum_expr(vec![ident_expr("Alice"), ident_expr("Bob")]);
    let type_ok = Spanned::dummy(Expr::In(
        Box::new(var_expr("votes")),
        Box::new(Spanned::dummy(Expr::FuncSet(
            Box::new(domain),
            Box::new(ident_expr("BOOLEAN")),
        ))),
    ));

    let sort = check_membership_constraint("votes", &type_ok);
    assert_eq!(
        sort,
        Some(TlaSort::Function {
            domain_keys: vec!["id:Alice".to_string(), "id:Bob".to_string()],
            range: Box::new(TlaSort::Bool),
        })
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_string_domain_function_membership() {
    let domain = set_enum_expr(vec![string_expr("a"), string_expr("b")]);
    let type_ok = Spanned::dummy(Expr::In(
        Box::new(var_expr("votes")),
        Box::new(Spanned::dummy(Expr::FuncSet(
            Box::new(domain),
            Box::new(ident_expr("BOOLEAN")),
        ))),
    ));

    let sort = check_membership_constraint("votes", &type_ok);
    assert_eq!(
        sort,
        Some(TlaSort::Function {
            domain_keys: vec!["str:a".to_string(), "str:b".to_string()],
            range: Box::new(TlaSort::Bool),
        })
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_record_membership() {
    let type_ok = Spanned::dummy(Expr::In(
        Box::new(var_expr("can")),
        Box::new(record_set_expr(vec![
            (
                "black",
                Spanned::dummy(Expr::Range(Box::new(int_expr(0)), Box::new(int_expr(2)))),
            ),
            (
                "white",
                Spanned::dummy(Expr::Range(Box::new(int_expr(0)), Box::new(int_expr(3)))),
            ),
        ])),
    ));

    let sort = check_membership_constraint("can", &type_ok);
    assert_eq!(
        sort,
        Some(TlaSort::Record {
            field_sorts: vec![
                ("black".to_string(), TlaSort::Int),
                ("white".to_string(), TlaSort::Int),
            ],
        })
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_record_literal_init() {
    let init = eq_expr(
        var_expr("can"),
        record_expr(vec![("black", int_expr(2)), ("white", int_expr(1))]),
    );
    let sort = check_init_assignment("can", &init);
    assert_eq!(
        sort,
        Some(TlaSort::Record {
            field_sorts: vec![
                ("black".to_string(), TlaSort::Int),
                ("white".to_string(), TlaSort::Int),
            ],
        })
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_record_membership_normalizes_field_order() {
    let type_ok = Spanned::dummy(Expr::In(
        Box::new(var_expr("can")),
        Box::new(record_set_expr(vec![
            (
                "white",
                Spanned::dummy(Expr::Range(Box::new(int_expr(0)), Box::new(int_expr(3)))),
            ),
            (
                "black",
                Spanned::dummy(Expr::Range(Box::new(int_expr(0)), Box::new(int_expr(2)))),
            ),
        ])),
    ));

    let sort = check_membership_constraint("can", &type_ok);
    assert_eq!(
        sort,
        Some(TlaSort::Record {
            field_sorts: vec![
                ("black".to_string(), TlaSort::Int),
                ("white".to_string(), TlaSort::Int),
            ],
        })
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infer_sort_from_membership_under_implies_and_equiv() {
    let flag_bool = Spanned::dummy(Expr::In(
        Box::new(var_expr("flag")),
        Box::new(Spanned::dummy(Expr::Ident(
            "BOOLEAN".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    let count_nat = Spanned::dummy(Expr::In(
        Box::new(var_expr("count")),
        Box::new(Spanned::dummy(Expr::Ident(
            "Nat".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let implies = Spanned::dummy(Expr::Implies(
        Box::new(flag_bool.clone()),
        Box::new(count_nat.clone()),
    ));
    assert_eq!(
        check_membership_constraint("flag", &implies),
        Some(TlaSort::Bool)
    );
    assert_eq!(
        check_membership_constraint("count", &implies),
        Some(TlaSort::Int)
    );

    let equiv = Spanned::dummy(Expr::Equiv(Box::new(flag_bool), Box::new(count_nat)));
    assert_eq!(
        check_membership_constraint("flag", &equiv),
        Some(TlaSort::Bool)
    );
    assert_eq!(
        check_membership_constraint("count", &equiv),
        Some(TlaSort::Int)
    );
}
