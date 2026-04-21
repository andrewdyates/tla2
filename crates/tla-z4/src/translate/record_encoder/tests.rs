// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the RecordEncoder module.
//! Part of #3749: record and tuple encoding as SMT product types.

use std::collections::HashMap;

use z4_dpll::api::SolveResult;

use super::{build_conjunction, encode_finite_membership, RecordEncoder};
use crate::translate::{TlaSort, Z4Translator};

/// Helper: create a translator and declare a record variable.
fn setup_record(fields: Vec<(&str, TlaSort)>) -> (Z4Translator, RecordEncoder) {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();
    let field_sorts: Vec<(String, TlaSort)> = fields
        .into_iter()
        .map(|(name, sort)| (name.to_string(), sort))
        .collect();
    trans
        .declare_record_var("r", field_sorts)
        .expect("should declare record var");
    (trans, enc)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_field_access_int() {
    let (trans, enc) = setup_record(vec![("x", TlaSort::Int), ("y", TlaSort::Bool)]);

    // r.x should return a valid term
    let term = enc.translate_field_access(&trans, "r", "x");
    assert!(term.is_ok(), "field access for r.x should succeed");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_field_access_bool() {
    let (trans, enc) = setup_record(vec![("x", TlaSort::Int), ("y", TlaSort::Bool)]);

    let term = enc.translate_field_access(&trans, "r", "y");
    assert!(term.is_ok(), "field access for r.y should succeed");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_field_access_unknown_field_errors() {
    let (trans, enc) = setup_record(vec![("x", TlaSort::Int)]);

    let result = enc.translate_field_access(&trans, "r", "nonexistent");
    assert!(result.is_err(), "accessing unknown field should error");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_field_sort_lookup() {
    let (trans, enc) = setup_record(vec![("x", TlaSort::Int), ("y", TlaSort::Bool)]);

    assert_eq!(enc.field_sort(&trans, "r", "x").unwrap(), TlaSort::Int);
    assert_eq!(enc.field_sort(&trans, "r", "y").unwrap(), TlaSort::Bool);
    assert!(enc.field_sort(&trans, "r", "z").is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_construction_sat() {
    let (mut trans, enc) = setup_record(vec![("a", TlaSort::Int), ("b", TlaSort::Int)]);

    // Construct [a |-> 10, b |-> 20]
    let val_a = trans.solver_mut().int_const(10);
    let val_b = trans.solver_mut().int_const(20);
    let mut field_terms = HashMap::new();
    field_terms.insert("a".to_string(), val_a);
    field_terms.insert("b".to_string(), val_b);

    let constr = enc
        .encode_record_construction(&mut trans, "r", &field_terms)
        .unwrap();
    trans.assert(constr);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let a_val: i64 = model.int_val("r__a").unwrap().try_into().unwrap();
    let b_val: i64 = model.int_val("r__b").unwrap().try_into().unwrap();
    assert_eq!(a_val, 10);
    assert_eq!(b_val, 20);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_construction_arity_mismatch() {
    let (mut trans, enc) = setup_record(vec![("a", TlaSort::Int), ("b", TlaSort::Int)]);

    // Only provide one field (arity mismatch)
    let val_a = trans.solver_mut().int_const(10);
    let mut field_terms = HashMap::new();
    field_terms.insert("a".to_string(), val_a);

    let result = enc.encode_record_construction(&mut trans, "r", &field_terms);
    assert!(result.is_err(), "arity mismatch should return error");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_except_updates_one_field() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    // Declare source record r with fields a=10, b=20
    trans
        .declare_record_var(
            "r",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // Set r.a = 10, r.b = 20
    let ten = trans.solver_mut().int_const(10);
    let twenty = trans.solver_mut().int_const(20);
    let r_a = trans.get_record_field("r", "a").unwrap();
    let r_b = trans.get_record_field("r", "b").unwrap();
    let eq_a = trans.solver_mut().try_eq(r_a, ten).unwrap();
    let eq_b = trans.solver_mut().try_eq(r_b, twenty).unwrap();
    trans.assert(eq_a);
    trans.assert(eq_b);

    // Declare target record s
    trans
        .declare_record_var(
            "s",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // s = [r EXCEPT !.a = 99]
    let ninety_nine = trans.solver_mut().int_const(99);
    let except_constr = enc
        .encode_record_except(&mut trans, "r", "s", "a", ninety_nine)
        .unwrap();
    trans.assert(except_constr);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let s_a: i64 = model.int_val("s__a").unwrap().try_into().unwrap();
    let s_b: i64 = model.int_val("s__b").unwrap().try_into().unwrap();
    assert_eq!(s_a, 99, "updated field should be 99");
    assert_eq!(s_b, 20, "unchanged field should be 20");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_except_unknown_field_errors() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    trans
        .declare_record_var("r", vec![("a".to_string(), TlaSort::Int)])
        .unwrap();
    trans
        .declare_record_var("s", vec![("a".to_string(), TlaSort::Int)])
        .unwrap();

    let val = trans.solver_mut().int_const(1);
    let result = enc.encode_record_except(&mut trans, "r", "s", "nonexistent", val);
    assert!(result.is_err(), "EXCEPT on unknown field should error");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_construction_sat() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    let val1 = trans.solver_mut().int_const(5);
    let val2 = trans.solver_mut().int_const(7);

    let constr = enc
        .encode_tuple_construction(&mut trans, "t", &[val1, val2])
        .unwrap();
    trans.assert(constr);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let t1: i64 = model.int_val("t__1").unwrap().try_into().unwrap();
    let t2: i64 = model.int_val("t__2").unwrap().try_into().unwrap();
    assert_eq!(t1, 5);
    assert_eq!(t2, 7);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_construction_arity_mismatch() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    let val1 = trans.solver_mut().int_const(5);
    let result = enc.encode_tuple_construction(&mut trans, "t", &[val1]);
    assert!(result.is_err(), "arity mismatch should return error");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_index_access() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int, TlaSort::Bool])
        .unwrap();

    // Access element 1 (Int)
    let term1 = enc.translate_tuple_index(&trans, "t", 1);
    assert!(term1.is_ok());

    // Access element 3 (Bool)
    let term3 = enc.translate_tuple_index(&trans, "t", 3);
    assert!(term3.is_ok());

    // Out of bounds
    let term_oob = enc.translate_tuple_index(&trans, "t", 4);
    assert!(term_oob.is_err());

    // Index 0 is invalid (1-based)
    let term_zero = enc.translate_tuple_index(&trans, "t", 0);
    assert!(term_zero.is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_equality_same_values_sat() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    // Declare two records with same shape
    trans
        .declare_record_var(
            "r1",
            vec![
                ("x".to_string(), TlaSort::Int),
                ("y".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();
    trans
        .declare_record_var(
            "r2",
            vec![
                ("x".to_string(), TlaSort::Int),
                ("y".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    // Set both to [x |-> 1, y |-> 2]
    let one = trans.solver_mut().int_const(1);
    let two = trans.solver_mut().int_const(2);

    let r1_x = trans.get_record_field("r1", "x").unwrap();
    let r1_y = trans.get_record_field("r1", "y").unwrap();
    let eq1 = trans.solver_mut().try_eq(r1_x, one).unwrap();
    let eq2 = trans.solver_mut().try_eq(r1_y, two).unwrap();
    trans.assert(eq1);
    trans.assert(eq2);

    let one2 = trans.solver_mut().int_const(1);
    let two2 = trans.solver_mut().int_const(2);
    let r2_x = trans.get_record_field("r2", "x").unwrap();
    let r2_y = trans.get_record_field("r2", "y").unwrap();
    let eq3 = trans.solver_mut().try_eq(r2_x, one2).unwrap();
    let eq4 = trans.solver_mut().try_eq(r2_y, two2).unwrap();
    trans.assert(eq3);
    trans.assert(eq4);

    // Assert r1 = r2
    let equality = enc.encode_record_equality(&mut trans, "r1", "r2").unwrap();
    trans.assert(equality);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_equality_different_values_unsat() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    trans
        .declare_record_var("r1", vec![("x".to_string(), TlaSort::Int)])
        .unwrap();
    trans
        .declare_record_var("r2", vec![("x".to_string(), TlaSort::Int)])
        .unwrap();

    // r1.x = 1, r2.x = 2
    let one = trans.solver_mut().int_const(1);
    let two = trans.solver_mut().int_const(2);
    let r1_x = trans.get_record_field("r1", "x").unwrap();
    let r2_x = trans.get_record_field("r2", "x").unwrap();
    let eq1 = trans.solver_mut().try_eq(r1_x, one).unwrap();
    let eq2 = trans.solver_mut().try_eq(r2_x, two).unwrap();
    trans.assert(eq1);
    trans.assert(eq2);

    // Assert r1 = r2 (should be UNSAT since 1 != 2)
    let equality = enc.encode_record_equality(&mut trans, "r1", "r2").unwrap();
    trans.assert(equality);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_equality_different_shapes_false() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    // Different field sorts => not equal
    trans
        .declare_record_var("r1", vec![("x".to_string(), TlaSort::Int)])
        .unwrap();
    trans
        .declare_record_var("r2", vec![("x".to_string(), TlaSort::Bool)])
        .unwrap();

    let equality = enc.encode_record_equality(&mut trans, "r1", "r2").unwrap();
    // Should be constant false (different field sorts)
    trans.assert(equality);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cartesian_product_enumeration() {
    let enc = RecordEncoder::new();

    let pairs = enc.enumerate_cartesian_product(&[1, 2], &[3, 4]);
    assert_eq!(pairs.len(), 4);
    assert!(pairs.contains(&(1, 3)));
    assert!(pairs.contains(&(1, 4)));
    assert!(pairs.contains(&(2, 3)));
    assert!(pairs.contains(&(2, 4)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cartesian_membership_sat() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    // Declare x, y
    let x = trans.declare_var("x", TlaSort::Int).unwrap();
    let y = trans.declare_var("y", TlaSort::Int).unwrap();

    // S1 = {1, 2}, S2 = {10, 20}
    let s1 = [
        trans.solver_mut().int_const(1),
        trans.solver_mut().int_const(2),
    ];
    let s2 = [
        trans.solver_mut().int_const(10),
        trans.solver_mut().int_const(20),
    ];

    let membership = enc
        .encode_cartesian_membership(&mut trans, x, y, &s1, &s2)
        .unwrap();
    trans.assert(membership);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x_val: i64 = model.int_val("x").unwrap().try_into().unwrap();
    let y_val: i64 = model.int_val("y").unwrap().try_into().unwrap();
    assert!(
        [1, 2].contains(&x_val),
        "x should be in {{1, 2}}, got {x_val}"
    );
    assert!(
        [10, 20].contains(&y_val),
        "y should be in {{10, 20}}, got {y_val}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_set_membership_sat() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    // Declare record r: [a: {1,2}, b: {10,20}]
    trans
        .declare_record_var(
            "r",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    let elem1 = trans.solver_mut().int_const(1);
    let elem2 = trans.solver_mut().int_const(2);
    let elem10 = trans.solver_mut().int_const(10);
    let elem20 = trans.solver_mut().int_const(20);

    let mut field_sets = HashMap::new();
    field_sets.insert("a".to_string(), vec![elem1, elem2]);
    field_sets.insert("b".to_string(), vec![elem10, elem20]);

    let membership = enc
        .encode_record_set_membership(&mut trans, "r", &field_sets)
        .unwrap();
    trans.assert(membership);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let a_val: i64 = model.int_val("r__a").unwrap().try_into().unwrap();
    let b_val: i64 = model.int_val("r__b").unwrap().try_into().unwrap();
    assert!(
        [1, 2].contains(&a_val),
        "r.a should be in {{1, 2}}, got {a_val}"
    );
    assert!(
        [10, 20].contains(&b_val),
        "r.b should be in {{10, 20}}, got {b_val}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fresh_record_declaration() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    trans
        .declare_record_var(
            "r",
            vec![
                ("a".to_string(), TlaSort::Int),
                ("b".to_string(), TlaSort::Bool),
            ],
        )
        .unwrap();

    let fresh_name = enc
        .declare_fresh_record(&mut trans, "except_result", "r")
        .unwrap();

    // Verify the fresh record has the same field structure
    let fresh_info = trans.get_record_var(&fresh_name).unwrap();
    let orig_info = trans.get_record_var("r").unwrap();
    assert_eq!(fresh_info.field_sorts, orig_info.field_sorts);

    // The fresh record should have different SMT variable terms
    assert_ne!(
        fresh_info.field_terms.get("a"),
        orig_info.field_terms.get("a"),
        "fresh record fields should be distinct SMT variables"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_empty_conjunction_is_true() {
    let mut trans = Z4Translator::new();
    let result = build_conjunction(&mut trans, &[]).unwrap();
    trans.assert(result);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finite_membership_empty_set_is_false() {
    let mut trans = Z4Translator::new();
    let x = trans.declare_var("x", TlaSort::Int).unwrap();

    let result = encode_finite_membership(&mut trans, x, &[]).unwrap();
    trans.assert(result);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_with_bool_field_construction() {
    let mut trans = Z4Translator::new();
    let enc = RecordEncoder::new();

    trans
        .declare_record_var(
            "r",
            vec![
                ("flag".to_string(), TlaSort::Bool),
                ("count".to_string(), TlaSort::Int),
            ],
        )
        .unwrap();

    let flag_val = trans.solver_mut().bool_const(true);
    let count_val = trans.solver_mut().int_const(42);
    let mut field_terms = HashMap::new();
    field_terms.insert("flag".to_string(), flag_val);
    field_terms.insert("count".to_string(), count_val);

    let constr = enc
        .encode_record_construction(&mut trans, "r", &field_terms)
        .unwrap();
    trans.assert(constr);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let count: i64 = model.int_val("r__count").unwrap().try_into().unwrap();
    assert_eq!(count, 42);
}

// ============================================================================
// Nested compound type tests: records-containing-sets
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_with_set_field_declares_successfully() {
    use crate::translate::finite_set::FiniteSetEncoder;

    // Record with a set field: [id: Int, msgs: Set(Int)]
    let mut trans = Z4Translator::new_with_arrays();
    trans
        .declare_record_var(
            "r",
            vec![
                ("id".to_string(), TlaSort::Int),
                (
                    "msgs".to_string(),
                    TlaSort::Set {
                        element_sort: Box::new(TlaSort::Int),
                    },
                ),
            ],
        )
        .expect("should declare record with set field");

    // The record should exist in record_vars
    let info = trans.get_record_var("r").unwrap();
    assert_eq!(info.field_sorts.len(), 2);

    // r.id should be an Int term
    let id_term = trans.get_record_field("r", "id").unwrap();
    // r.msgs should be an (Array Int Bool) term
    let msgs_term = trans.get_record_field("r", "msgs").unwrap();

    // Verify the set field works with FiniteSetEncoder: 5 \in r.msgs
    let enc = FiniteSetEncoder::new();
    let five = trans.solver_mut().int_const(5);
    let member = enc.encode_membership(&mut trans, five, msgs_term).unwrap();
    trans.assert(member);

    // Also constrain r.id = 42
    let forty_two = trans.solver_mut().int_const(42);
    let eq = trans.solver_mut().try_eq(id_term, forty_two).unwrap();
    trans.assert(eq);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_with_set_field_construction_and_membership() {
    use crate::translate::finite_set::FiniteSetEncoder;

    let mut trans = Z4Translator::new_with_arrays();
    let enc = RecordEncoder::new();
    let set_enc = FiniteSetEncoder::new();

    // Declare record: [count: Int, items: Set(Int)]
    trans
        .declare_record_var(
            "r",
            vec![
                ("count".to_string(), TlaSort::Int),
                (
                    "items".to_string(),
                    TlaSort::Set {
                        element_sort: Box::new(TlaSort::Int),
                    },
                ),
            ],
        )
        .unwrap();

    // Build a concrete set {10, 20, 30}
    let e10 = trans.solver_mut().int_const(10);
    let e20 = trans.solver_mut().int_const(20);
    let e30 = trans.solver_mut().int_const(30);
    let concrete_set = set_enc.encode_set_enum(&mut trans, &[e10, e20, e30]).unwrap();

    // Construct record [count |-> 3, items |-> {10, 20, 30}]
    let three = trans.solver_mut().int_const(3);
    let mut field_terms = HashMap::new();
    field_terms.insert("count".to_string(), three);
    field_terms.insert("items".to_string(), concrete_set);

    let constr = enc
        .encode_record_construction(&mut trans, "r", &field_terms)
        .unwrap();
    trans.assert(constr);

    // Now verify: 20 \in r.items should be SAT
    let items_term = trans.get_record_field("r", "items").unwrap();
    let twenty = trans.solver_mut().int_const(20);
    let member = set_enc.encode_membership(&mut trans, twenty, items_term).unwrap();
    trans.assert(member);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_with_set_field_non_member_unsat() {
    use crate::translate::finite_set::FiniteSetEncoder;

    let mut trans = Z4Translator::new_with_arrays();
    let enc = RecordEncoder::new();
    let set_enc = FiniteSetEncoder::new();

    trans
        .declare_record_var(
            "r",
            vec![
                ("count".to_string(), TlaSort::Int),
                (
                    "items".to_string(),
                    TlaSort::Set {
                        element_sort: Box::new(TlaSort::Int),
                    },
                ),
            ],
        )
        .unwrap();

    // Build set {10, 20}
    let e10 = trans.solver_mut().int_const(10);
    let e20 = trans.solver_mut().int_const(20);
    let concrete_set = set_enc.encode_set_enum(&mut trans, &[e10, e20]).unwrap();

    // Construct record
    let two = trans.solver_mut().int_const(2);
    let mut field_terms = HashMap::new();
    field_terms.insert("count".to_string(), two);
    field_terms.insert("items".to_string(), concrete_set);

    let constr = enc
        .encode_record_construction(&mut trans, "r", &field_terms)
        .unwrap();
    trans.assert(constr);

    // 99 \in r.items should be UNSAT (99 not in {10, 20})
    let items_term = trans.get_record_field("r", "items").unwrap();
    let ninety_nine = trans.solver_mut().int_const(99);
    let member = set_enc
        .encode_membership(&mut trans, ninety_nine, items_term)
        .unwrap();
    trans.assert(member);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_with_set_field_equality() {
    use crate::translate::finite_set::FiniteSetEncoder;

    let mut trans = Z4Translator::new_with_arrays();
    let enc = RecordEncoder::new();
    let set_enc = FiniteSetEncoder::new();

    let field_sorts = vec![
        ("id".to_string(), TlaSort::Int),
        (
            "vals".to_string(),
            TlaSort::Set {
                element_sort: Box::new(TlaSort::Int),
            },
        ),
    ];

    trans
        .declare_record_var("r1", field_sorts.clone())
        .unwrap();
    trans
        .declare_record_var("r2", field_sorts)
        .unwrap();

    // r1 = [id |-> 1, vals |-> {5, 6}]
    let one = trans.solver_mut().int_const(1);
    let e5 = trans.solver_mut().int_const(5);
    let e6 = trans.solver_mut().int_const(6);
    let set1 = set_enc.encode_set_enum(&mut trans, &[e5, e6]).unwrap();

    let r1_id = trans.get_record_field("r1", "id").unwrap();
    let r1_vals = trans.get_record_field("r1", "vals").unwrap();
    let eq1 = trans.solver_mut().try_eq(r1_id, one).unwrap();
    let eq2 = trans.solver_mut().try_eq(r1_vals, set1).unwrap();
    trans.assert(eq1);
    trans.assert(eq2);

    // r2 = [id |-> 1, vals |-> {5, 6}]
    let one2 = trans.solver_mut().int_const(1);
    let e5b = trans.solver_mut().int_const(5);
    let e6b = trans.solver_mut().int_const(6);
    let set2 = set_enc.encode_set_enum(&mut trans, &[e5b, e6b]).unwrap();

    let r2_id = trans.get_record_field("r2", "id").unwrap();
    let r2_vals = trans.get_record_field("r2", "vals").unwrap();
    let eq3 = trans.solver_mut().try_eq(r2_id, one2).unwrap();
    let eq4 = trans.solver_mut().try_eq(r2_vals, set2).unwrap();
    trans.assert(eq3);
    trans.assert(eq4);

    // Assert r1 = r2 (field-wise)
    let equality = enc.encode_record_equality(&mut trans, "r1", "r2").unwrap();
    trans.assert(equality);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// ============================================================================
// Nested compound type tests: records-containing-records
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_with_nested_record_declares_successfully() {
    // Record with a nested record field: [name: Int, addr: [street: Int, zip: Int]]
    let mut trans = Z4Translator::new();

    trans
        .declare_record_var(
            "r",
            vec![
                ("name".to_string(), TlaSort::Int),
                (
                    "addr".to_string(),
                    TlaSort::Record {
                        field_sorts: vec![
                            ("street".to_string(), TlaSort::Int),
                            ("zip".to_string(), TlaSort::Int),
                        ],
                    },
                ),
            ],
        )
        .expect("should declare record with nested record field");

    // The parent record should exist
    let info = trans.get_record_var("r").unwrap();
    assert_eq!(info.field_sorts.len(), 2);

    // The nested record should be auto-declared as "r__addr"
    let nested_name = trans.get_nested_record_name("r", "addr");
    assert_eq!(nested_name, Some("r__addr".to_string()));

    // The nested record should exist in record_vars
    let nested_info = trans.get_record_var("r__addr").unwrap();
    assert_eq!(nested_info.field_sorts.len(), 2);

    // Access nested fields: r__addr.street, r__addr.zip
    let street_term = trans.get_record_field("r__addr", "street").unwrap();
    let zip_term = trans.get_record_field("r__addr", "zip").unwrap();

    // Constrain nested fields and check SAT
    let val_street = trans.solver_mut().int_const(100);
    let val_zip = trans.solver_mut().int_const(94105);
    let eq1 = trans.solver_mut().try_eq(street_term, val_street).unwrap();
    let eq2 = trans.solver_mut().try_eq(zip_term, val_zip).unwrap();
    trans.assert(eq1);
    trans.assert(eq2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));

    let model = trans.get_model().unwrap();
    let zip_val: i64 = model.int_val("r__addr__zip").unwrap().try_into().unwrap();
    assert_eq!(zip_val, 94105);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_with_nested_record_non_record_field_returns_none() {
    let mut trans = Z4Translator::new();

    trans
        .declare_record_var(
            "r",
            vec![
                ("name".to_string(), TlaSort::Int),
                (
                    "addr".to_string(),
                    TlaSort::Record {
                        field_sorts: vec![("zip".to_string(), TlaSort::Int)],
                    },
                ),
            ],
        )
        .unwrap();

    // "name" is Int, not Record, so get_nested_record_name should return None
    assert_eq!(trans.get_nested_record_name("r", "name"), None);

    // Non-existent record should return None
    assert_eq!(trans.get_nested_record_name("nonexistent", "addr"), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deeply_nested_record() {
    // [a: [b: [c: Int]]]
    let mut trans = Z4Translator::new();

    trans
        .declare_record_var(
            "r",
            vec![(
                "a".to_string(),
                TlaSort::Record {
                    field_sorts: vec![(
                        "b".to_string(),
                        TlaSort::Record {
                            field_sorts: vec![("c".to_string(), TlaSort::Int)],
                        },
                    )],
                },
            )],
        )
        .expect("should declare deeply nested record");

    // r -> r__a -> r__a__b -> r__a__b__c
    let nested_a = trans.get_nested_record_name("r", "a");
    assert_eq!(nested_a, Some("r__a".to_string()));

    let nested_b = trans.get_nested_record_name("r__a", "b");
    assert_eq!(nested_b, Some("r__a__b".to_string()));

    // Access the leaf: r__a__b.c
    let c_term = trans.get_record_field("r__a__b", "c").unwrap();
    let val = trans.solver_mut().int_const(999);
    let eq = trans.solver_mut().try_eq(c_term, val).unwrap();
    trans.assert(eq);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));

    let model = trans.get_model().unwrap();
    let c_val: i64 = model.int_val("r__a__b__c").unwrap().try_into().unwrap();
    assert_eq!(c_val, 999);
}
