// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for BMC function encoding via SMT arrays.
//!
//! Part of #3786: Validates function construction, application, DOMAIN,
//! and EXCEPT operations in the BMC translator.

use super::*;
use tla_core::ast::{BoundVar, ExceptPathElement, ExceptSpec};
use z4_dpll::api::SolveResult;

/// Helper: create a BMC translator with array support.
fn bmc_array(k: usize) -> BmcTranslator {
    BmcTranslator::new_with_arrays(k).unwrap()
}

// --- declare_func_var ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_func_var() {
    let mut bmc = bmc_array(2);
    // Should succeed: function with Int range
    bmc.declare_func_var("f", TlaSort::Int).unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_func_var_bool_range() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("g", TlaSort::Bool).unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_func_var_rejects_compound_range() {
    let mut bmc = bmc_array(0);
    let result = bmc.declare_func_var(
        "f",
        TlaSort::Set {
            element_sort: Box::new(TlaSort::Int),
        },
    );
    assert!(result.is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_declare_var_with_function_sort() {
    let mut bmc = bmc_array(1);
    // declare_var should delegate Function sort to declare_func_var
    bmc.declare_var(
        "f",
        TlaSort::Function {
            domain_keys: vec!["1".to_string(), "2".to_string()],
            range: Box::new(TlaSort::Int),
        },
    )
    .unwrap();
    // The function should now be accessible via func_vars
    assert!(bmc.func_vars.contains_key("f"));
}

// --- Function application ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_apply_sat() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // f[1] = 42
    let apply_expr = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
    ));

    let result = bmc.translate_init(&spanned(Expr::Eq(
        Box::new(apply_expr),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(42)))),
    )));
    let term = result.unwrap();
    bmc.assert(term);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_apply_contradicts_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Assert f[1] = 10 AND f[1] = 20 -> UNSAT
    let f1 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
    ));

    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(f1.clone()),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(10)))),
        )))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(f1),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(20)))),
        )))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_apply_different_args_sat() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // f[1] = 10 AND f[2] = 20 -> SAT (different arguments)
    let f1 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
    ));
    let f2 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(2)))),
    ));

    let eq1 = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(f1),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(10)))),
        )))
        .unwrap();
    bmc.assert(eq1);

    let eq2 = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(f2),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(20)))),
        )))
        .unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- DOMAIN ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_domain_membership_sat() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();
    bmc.declare_var("x", TlaSort::Int).unwrap();

    // Build: x \in DOMAIN f
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Domain(Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
    ));

    let term = bmc.translate_init(&membership).unwrap();
    bmc.assert(term);

    // SAT: solver can choose domain to include x
    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_domain_with_concrete_domain() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Constrain the domain to {1, 2}: assert (select dom 1) /\ (select dom 2)
    let dom = bmc.get_func_domain_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let two = bmc.solver.int_const(2);
    let three = bmc.solver.int_const(3);

    let in1 = bmc.solver.try_select(dom, one).unwrap();
    let in2 = bmc.solver.try_select(dom, two).unwrap();
    bmc.assert(in1);
    bmc.assert(in2);

    // Also constrain 3 NOT in domain
    let in3 = bmc.solver.try_select(dom, three).unwrap();
    let not_in3 = bmc.solver.try_not(in3).unwrap();
    bmc.assert(not_in3);

    // Now check: x \in DOMAIN f with x = 3 should be UNSAT
    bmc.declare_var("x", TlaSort::Int).unwrap();
    let x_eq_3 = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(3)))),
        )))
        .unwrap();
    bmc.assert(x_eq_3);

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Domain(Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
    ));

    let dom_term = bmc.translate_init(&membership).unwrap();
    bmc.assert(dom_term);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- EXCEPT ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_updates_value() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Assert f[1] = 10
    let f1 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
    ));
    let eq_init = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(f1),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(10)))),
        )))
        .unwrap();
    bmc.assert(eq_init);

    // Build: [f EXCEPT ![1] = 99] via direct translate_func_except_bmc call
    let new_mapping = bmc
        .translate_func_except_bmc(
            &spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            &[ExceptSpec {
                path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                    num_bigint::BigInt::from(1),
                )))],
                value: spanned(Expr::Int(num_bigint::BigInt::from(99))),
            }],
        )
        .unwrap();

    // (select new_mapping 1) should equal 99
    let one = bmc.solver.int_const(1);
    let ninety_nine = bmc.solver.int_const(99);
    let selected = bmc.solver.try_select(new_mapping, one).unwrap();
    let eq = bmc.solver.try_eq(selected, ninety_nine).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_preserves_other_values() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Assert f[2] = 20
    let mapping = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let two = bmc.solver.int_const(2);
    let twenty = bmc.solver.int_const(20);
    let sel = bmc.solver.try_select(mapping, two).unwrap();
    let eq = bmc.solver.try_eq(sel, twenty).unwrap();
    bmc.assert(eq);

    // Build [f EXCEPT ![1] = 99]: changes f[1] but preserves f[2]
    let new_mapping = bmc
        .translate_func_except_bmc(
            &spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            &[ExceptSpec {
                path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                    num_bigint::BigInt::from(1),
                )))],
                value: spanned(Expr::Int(num_bigint::BigInt::from(99))),
            }],
        )
        .unwrap();

    // (select new_mapping 2) should still be 20
    let selected = bmc.solver.try_select(new_mapping, two).unwrap();
    let eq2 = bmc.solver.try_eq(selected, twenty).unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Function construction ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_construct_set_enum_domain() {
    let mut bmc = bmc_array(0);

    // [x \in {1, 2, 3} |-> x + 1]
    let bound_vars = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(num_bigint::BigInt::from(1))),
            spanned(Expr::Int(num_bigint::BigInt::from(2))),
            spanned(Expr::Int(num_bigint::BigInt::from(3))),
        ])))),
        pattern: None,
    }];
    let body = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
    ));

    let (domain, mapping) = bmc
        .translate_func_construct_bmc(&bound_vars, &body)
        .unwrap();

    // Check: 1 is in domain
    let one = bmc.solver.int_const(1);
    let in_dom = bmc.solver.try_select(domain, one).unwrap();
    bmc.assert(in_dom);

    // Check: mapping[1] = 2 (since body is x+1, for x=1 => 2)
    let two = bmc.solver.int_const(2);
    let map_1 = bmc.solver.try_select(mapping, one).unwrap();
    let eq = bmc.solver.try_eq(map_1, two).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_construct_range_domain() {
    let mut bmc = bmc_array(0);

    // [x \in 1..3 |-> x * 2]
    let bound_vars = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(3)))),
        )))),
        pattern: None,
    }];
    let body = spanned(Expr::Mul(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(2)))),
    ));

    let (domain, mapping) = bmc
        .translate_func_construct_bmc(&bound_vars, &body)
        .unwrap();

    // Check: 4 is NOT in domain (only 1,2,3 are)
    let four = bmc.solver.int_const(4);
    let in_dom = bmc.solver.try_select(domain, four).unwrap();
    let not_in = bmc.solver.try_not(in_dom).unwrap();
    bmc.assert(not_in);

    // Check: mapping[2] = 4 (since body is x*2, for x=2 => 4)
    let two_term = bmc.solver.int_const(2);
    let four_term = bmc.solver.int_const(4);
    let map_2 = bmc.solver.try_select(mapping, two_term).unwrap();
    let eq = bmc.solver.try_eq(map_2, four_term).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_construct_wrong_value_unsat() {
    let mut bmc = bmc_array(0);

    // [x \in {1} |-> x + 1]
    // mapping[1] must be 2, so asserting mapping[1] = 5 should be UNSAT
    let bound_vars = vec![BoundVar {
        name: spanned("x".to_string()),
        domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
            num_bigint::BigInt::from(1),
        ))])))),
        pattern: None,
    }];
    let body = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
    ));

    let (_domain, mapping) = bmc
        .translate_func_construct_bmc(&bound_vars, &body)
        .unwrap();

    // Assert mapping[1] = 5 (should be UNSAT because it must be 2)
    let one = bmc.solver.int_const(1);
    let five = bmc.solver.int_const(5);
    let map_1 = bmc.solver.try_select(mapping, one).unwrap();
    let eq = bmc.solver.try_eq(map_1, five).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Function variable across steps ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_var_across_steps() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // At step 0: f[1] = 10
    let map0 = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel0 = bmc.solver.try_select(map0, one).unwrap();
    let eq0 = bmc.solver.try_eq(sel0, ten).unwrap();
    bmc.assert(eq0);

    // At step 1: f[1] = 20 (different step, different value)
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let twenty = bmc.solver.int_const(20);
    let sel1 = bmc.solver.try_select(map1, one).unwrap();
    let eq1 = bmc.solver.try_eq(sel1, twenty).unwrap();
    bmc.assert(eq1);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_apply_primed() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // f'[1] = 42 (at step 0, prime means step 1)
    bmc.current_step = 0;
    let apply_expr = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
    ));

    let result = bmc.translate_bool(&spanned(Expr::Eq(
        Box::new(apply_expr),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(42)))),
    )));
    let term = result.unwrap();
    bmc.assert(term);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Multi-spec EXCEPT ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_multi_spec() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // [f EXCEPT ![1] = 10, ![2] = 20]
    let new_mapping = bmc
        .translate_func_except_bmc(
            &spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            &[
                ExceptSpec {
                    path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                        num_bigint::BigInt::from(1),
                    )))],
                    value: spanned(Expr::Int(num_bigint::BigInt::from(10))),
                },
                ExceptSpec {
                    path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                        num_bigint::BigInt::from(2),
                    )))],
                    value: spanned(Expr::Int(num_bigint::BigInt::from(20))),
                },
            ],
        )
        .unwrap();

    // (select new_mapping 1) = 10
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel1 = bmc.solver.try_select(new_mapping, one).unwrap();
    let eq1 = bmc.solver.try_eq(sel1, ten).unwrap();
    bmc.assert(eq1);

    // (select new_mapping 2) = 20
    let two = bmc.solver.int_const(2);
    let twenty = bmc.solver.int_const(20);
    let sel2 = bmc.solver.try_select(new_mapping, two).unwrap();
    let eq2 = bmc.solver.try_eq(sel2, twenty).unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_multi_spec_last_wins() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // TLA+ semantics: [f EXCEPT ![1] = 10, ![1] = 20] — last write wins
    let new_mapping = bmc
        .translate_func_except_bmc(
            &spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            &[
                ExceptSpec {
                    path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                        num_bigint::BigInt::from(1),
                    )))],
                    value: spanned(Expr::Int(num_bigint::BigInt::from(10))),
                },
                ExceptSpec {
                    path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                        num_bigint::BigInt::from(1),
                    )))],
                    value: spanned(Expr::Int(num_bigint::BigInt::from(20))),
                },
            ],
        )
        .unwrap();

    // Last store wins: (select new_mapping 1) = 20, NOT 10
    let one = bmc.solver.int_const(1);
    let twenty = bmc.solver.int_const(20);
    let sel = bmc.solver.try_select(new_mapping, one).unwrap();
    let eq = bmc.solver.try_eq(sel, twenty).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));

    // Verify it's NOT 10: create fresh solver to check
    let mut bmc2 = bmc_array(0);
    bmc2.declare_func_var("f", TlaSort::Int).unwrap();
    let new_map2 = bmc2
        .translate_func_except_bmc(
            &spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            &[
                ExceptSpec {
                    path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                        num_bigint::BigInt::from(1),
                    )))],
                    value: spanned(Expr::Int(num_bigint::BigInt::from(10))),
                },
                ExceptSpec {
                    path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                        num_bigint::BigInt::from(1),
                    )))],
                    value: spanned(Expr::Int(num_bigint::BigInt::from(20))),
                },
            ],
        )
        .unwrap();

    let one2 = bmc2.solver.int_const(1);
    let ten2 = bmc2.solver.int_const(10);
    let sel2 = bmc2.solver.try_select(new_map2, one2).unwrap();
    let eq2 = bmc2.solver.try_eq(sel2, ten2).unwrap();
    bmc2.assert(eq2);

    // Last write was 20, so asserting it's 10 should be UNSAT
    assert!(matches!(bmc2.check_sat(), SolveResult::Unsat(_)));
}

// --- Nested EXCEPT ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_nested_path_scalar_range_errors() {
    let mut bmc = bmc_array(0);
    // Function with scalar Int range — nested EXCEPT is not supported
    // because (select f_map key) returns Int, not Array.
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // [f EXCEPT ![1][2] = 42] should error: scalar range can't be nested
    let result = bmc.translate_func_except_bmc(
        &spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
        &[ExceptSpec {
            path: vec![
                ExceptPathElement::Index(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
                ExceptPathElement::Index(spanned(Expr::Int(num_bigint::BigInt::from(2)))),
            ],
            value: spanned(Expr::Int(num_bigint::BigInt::from(42))),
        }],
    );
    assert!(
        result.is_err(),
        "nested EXCEPT on scalar-range function should error"
    );
}

// --- EXCEPT via dispatch (translate_eq) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_via_eq_dispatch() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Step 0: set f[1] = 10
    bmc.current_step = 0;
    let f1 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(1)))),
    ));
    let init_eq = bmc
        .translate_init(&spanned(Expr::Eq(
            Box::new(f1),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(10)))),
        )))
        .unwrap();
    bmc.assert(init_eq);

    // Translate: f' = [f EXCEPT ![1] = 99]
    // This should go through translate_eq -> try_translate_func_except_eq
    let except_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Except(
            Box::new(spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            vec![ExceptSpec {
                path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                    num_bigint::BigInt::from(1),
                )))],
                value: spanned(Expr::Int(num_bigint::BigInt::from(99))),
            }],
        ))),
    ));

    bmc.current_step = 0;
    let next_term = bmc.translate_bool(&except_eq).unwrap();
    bmc.assert(next_term);

    // Now at step 1, f[1] should be 99
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let ninety_nine = bmc.solver.int_const(99);
    let selected = bmc.solver.try_select(map1, one).unwrap();
    let eq = bmc.solver.try_eq(selected, ninety_nine).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_via_eq_preserves_unchanged_keys() {
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Step 0: set f[1] = 10 and f[2] = 20
    bmc.current_step = 0;
    let map0 = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let two = bmc.solver.int_const(2);
    let ten = bmc.solver.int_const(10);
    let twenty = bmc.solver.int_const(20);

    let sel1 = bmc.solver.try_select(map0, one).unwrap();
    let eq1 = bmc.solver.try_eq(sel1, ten).unwrap();
    bmc.assert(eq1);

    let sel2 = bmc.solver.try_select(map0, two).unwrap();
    let eq2 = bmc.solver.try_eq(sel2, twenty).unwrap();
    bmc.assert(eq2);

    // Translate: f' = [f EXCEPT ![1] = 99]
    let except_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Except(
            Box::new(spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            vec![ExceptSpec {
                path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                    num_bigint::BigInt::from(1),
                )))],
                value: spanned(Expr::Int(num_bigint::BigInt::from(99))),
            }],
        ))),
    ));

    bmc.current_step = 0;
    let next_term = bmc.translate_bool(&except_eq).unwrap();
    bmc.assert(next_term);

    // At step 1: f[2] should still be 20 (unchanged)
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let sel2_next = bmc.solver.try_select(map1, two).unwrap();
    let eq_unchanged = bmc.solver.try_eq(sel2_next, twenty).unwrap();
    bmc.assert(eq_unchanged);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_via_eq_reversed_operands() {
    // Test: [f EXCEPT ![1] = 99] = f' (EXCEPT on left, variable on right)
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    let except_eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Except(
            Box::new(spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            vec![ExceptSpec {
                path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                    num_bigint::BigInt::from(1),
                )))],
                value: spanned(Expr::Int(num_bigint::BigInt::from(99))),
            }],
        ))),
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
    ));

    bmc.current_step = 0;
    let term = bmc.translate_bool(&except_eq).unwrap();
    bmc.assert(term);

    // f'[1] should be 99
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let one = bmc.solver.int_const(1);
    let ninety_nine = bmc.solver.int_const(99);
    let sel = bmc.solver.try_select(map1, one).unwrap();
    let eq = bmc.solver.try_eq(sel, ninety_nine).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_with_variable_index() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();
    bmc.declare_var("k", TlaSort::Int).unwrap();

    // [f EXCEPT ![k] = 42] — index is a variable, not a literal
    let new_mapping = bmc
        .translate_func_except_bmc(
            &spanned(Expr::Ident(
                "f".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
            &[ExceptSpec {
                path: vec![ExceptPathElement::Index(spanned(Expr::Ident(
                    "k".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                )))],
                value: spanned(Expr::Int(num_bigint::BigInt::from(42))),
            }],
        )
        .unwrap();

    // Constrain k = 5
    let k_term = bmc.get_var_at_step("k", 0).unwrap();
    let five = bmc.solver.int_const(5);
    let k_eq = bmc.solver.try_eq(k_term, five).unwrap();
    bmc.assert(k_eq);

    // (select new_mapping 5) should be 42
    let forty_two = bmc.solver.int_const(42);
    let sel = bmc.solver.try_select(new_mapping, five).unwrap();
    let eq = bmc.solver.try_eq(sel, forty_two).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Chained EXCEPT ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_chained() {
    // [[f EXCEPT ![1] = 10] EXCEPT ![2] = 20]
    // Outer base is itself an Except expression
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    let inner_except = spanned(Expr::Except(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                num_bigint::BigInt::from(1),
            )))],
            value: spanned(Expr::Int(num_bigint::BigInt::from(10))),
        }],
    ));

    let new_mapping = bmc
        .translate_func_except_bmc(
            &inner_except,
            &[ExceptSpec {
                path: vec![ExceptPathElement::Index(spanned(Expr::Int(
                    num_bigint::BigInt::from(2),
                )))],
                value: spanned(Expr::Int(num_bigint::BigInt::from(20))),
            }],
        )
        .unwrap();

    // (select result 1) = 10
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel1 = bmc.solver.try_select(new_mapping, one).unwrap();
    let eq1 = bmc.solver.try_eq(sel1, ten).unwrap();
    bmc.assert(eq1);

    // (select result 2) = 20
    let two = bmc.solver.int_const(2);
    let twenty = bmc.solver.int_const(20);
    let sel2 = bmc.solver.try_select(new_mapping, two).unwrap();
    let eq2 = bmc.solver.try_eq(sel2, twenty).unwrap();
    bmc.assert(eq2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- Error cases ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_empty_path_error() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    let result = bmc.translate_func_except_bmc(
        &spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
        &[ExceptSpec {
            path: vec![],
            value: spanned(Expr::Int(num_bigint::BigInt::from(1))),
        }],
    );
    assert!(result.is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_except_record_field_error() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    let result = bmc.translate_func_except_bmc(
        &spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
        &[ExceptSpec {
            path: vec![ExceptPathElement::Field(tla_core::ast::RecordFieldName {
                name: spanned("x".to_string()),
                field_id: tla_core::name_intern::NameId::INVALID,
            })],
            value: spanned(Expr::Int(num_bigint::BigInt::from(1))),
        }],
    );
    assert!(result.is_err());
}

// --- Function construction equality (Part of #3786) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_construct_eq_init() {
    // f = [x \in {1, 2} |-> x + 10]
    // After translating, f[1] should be 11 and f[2] should be 12.
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    let func_def = spanned(Expr::FuncDef(
        vec![BoundVar {
            name: spanned("x".to_string()),
            domain: Some(Box::new(spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(num_bigint::BigInt::from(1))),
                spanned(Expr::Int(num_bigint::BigInt::from(2))),
            ])))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(10)))),
        ))),
    ));

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(func_def),
    ));

    let term = bmc.translate_init(&eq).unwrap();
    bmc.assert(term);

    // f[1] should be 11
    let map = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let eleven = bmc.solver.int_const(11);
    let sel = bmc.solver.try_select(map, one).unwrap();
    let eq_check = bmc.solver.try_eq(sel, eleven).unwrap();
    bmc.assert(eq_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_construct_eq_wrong_value_unsat() {
    // f = [x \in {1} |-> x + 10]
    // f[1] should be 11, not 99
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    let func_def = spanned(Expr::FuncDef(
        vec![BoundVar {
            name: spanned("x".to_string()),
            domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
                num_bigint::BigInt::from(1),
            ))])))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(10)))),
        ))),
    ));

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(func_def),
    ));

    let term = bmc.translate_init(&eq).unwrap();
    bmc.assert(term);

    // f[1] should NOT be 99
    let map = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let ninety_nine = bmc.solver.int_const(99);
    let sel = bmc.solver.try_select(map, one).unwrap();
    let eq_check = bmc.solver.try_eq(sel, ninety_nine).unwrap();
    bmc.assert(eq_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_construct_eq_primed() {
    // f' = [x \in {1, 2} |-> x * 2]
    let mut bmc = bmc_array(1);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    let func_def = spanned(Expr::FuncDef(
        vec![BoundVar {
            name: spanned("x".to_string()),
            domain: Some(Box::new(spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(num_bigint::BigInt::from(1))),
                spanned(Expr::Int(num_bigint::BigInt::from(2))),
            ])))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Mul(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(num_bigint::BigInt::from(2)))),
        ))),
    ));

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(func_def),
    ));

    bmc.current_step = 0;
    let term = bmc.translate_bool(&eq).unwrap();
    bmc.assert(term);

    // f'[2] should be 4 (at step 1)
    let map1 = bmc.get_func_mapping_at_step("f", 1).unwrap();
    let two = bmc.solver.int_const(2);
    let four = bmc.solver.int_const(4);
    let sel = bmc.solver.try_select(map1, two).unwrap();
    let eq_check = bmc.solver.try_eq(sel, four).unwrap();
    bmc.assert(eq_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_func_construct_eq_reversed() {
    // [x \in {1} |-> 42] = f (FuncDef on left, variable on right)
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    let func_def = spanned(Expr::FuncDef(
        vec![BoundVar {
            name: spanned("x".to_string()),
            domain: Some(Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
                num_bigint::BigInt::from(1),
            ))])))),
            pattern: None,
        }],
        Box::new(spanned(Expr::Int(num_bigint::BigInt::from(42)))),
    ));

    let eq = spanned(Expr::Eq(
        Box::new(func_def),
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let term = bmc.translate_init(&eq).unwrap();
    bmc.assert(term);

    // f[1] should be 42
    let map = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let forty_two = bmc.solver.int_const(42);
    let sel = bmc.solver.try_select(map, one).unwrap();
    let eq_check = bmc.solver.try_eq(sel, forty_two).unwrap();
    bmc.assert(eq_check);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

// --- BmcValue::Function in assert_concrete_state ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_assert_concrete_func_state() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Assert f = {1 -> 10, 2 -> 20}
    bmc.assert_concrete_state(
        &[(
            "f".to_string(),
            super::super::BmcValue::Function(vec![
                (1, super::super::BmcValue::Int(10)),
                (2, super::super::BmcValue::Int(20)),
            ]),
        )],
        0,
    )
    .unwrap();

    // f[1] should be 10
    let map = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let ten = bmc.solver.int_const(10);
    let sel = bmc.solver.try_select(map, one).unwrap();
    let eq = bmc.solver.try_eq(sel, ten).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_assert_concrete_func_state_wrong_value_unsat() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Assert f = {1 -> 10}
    bmc.assert_concrete_state(
        &[(
            "f".to_string(),
            super::super::BmcValue::Function(vec![(1, super::super::BmcValue::Int(10))]),
        )],
        0,
    )
    .unwrap();

    // f[1] should NOT be 99
    let map = bmc.get_func_mapping_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let ninety_nine = bmc.solver.int_const(99);
    let sel = bmc.solver.try_select(map, one).unwrap();
    let eq = bmc.solver.try_eq(sel, ninety_nine).unwrap();
    bmc.assert(eq);

    assert!(matches!(bmc.check_sat(), SolveResult::Unsat(_)));
}

// --- Domain membership in assert_concrete_state ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_assert_concrete_func_domain_membership() {
    let mut bmc = bmc_array(0);
    bmc.declare_func_var("f", TlaSort::Int).unwrap();

    // Assert f = {1 -> 10, 3 -> 30}
    bmc.assert_concrete_state(
        &[(
            "f".to_string(),
            super::super::BmcValue::Function(vec![
                (1, super::super::BmcValue::Int(10)),
                (3, super::super::BmcValue::Int(30)),
            ]),
        )],
        0,
    )
    .unwrap();

    // 1 should be in domain
    let dom = bmc.get_func_domain_at_step("f", 0).unwrap();
    let one = bmc.solver.int_const(1);
    let in_dom_1 = bmc.solver.try_select(dom, one).unwrap();
    bmc.assert(in_dom_1);

    // 2 should NOT be in domain
    let two = bmc.solver.int_const(2);
    let in_dom_2 = bmc.solver.try_select(dom, two).unwrap();
    let not_in_dom_2 = bmc.solver.try_not(in_dom_2).unwrap();
    bmc.assert(not_in_dom_2);

    assert!(matches!(bmc.check_sat(), SolveResult::Sat));
}
