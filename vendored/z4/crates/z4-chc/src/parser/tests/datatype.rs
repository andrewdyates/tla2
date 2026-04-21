// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_declare_datatype_tuple_parsing() {
    // #1279: Parser should accept declare-datatype for tuple types from zani
    let input = r#"
            (set-logic HORN)
            (declare-datatype Tuple_bv32_bool ((mk (fld_0 (_ BitVec 32)) (fld_1 Bool))))
            (declare-fun Inv (Tuple_bv32_bool) Bool)
            (check-sat)
        "#;

    let result = ChcParser::parse(input);
    assert!(
        result.is_ok(),
        "declare-datatype should be parsed successfully: {:?}",
        result.err()
    );

    let problem = result.expect("test should succeed");
    // Check that the predicate was registered with the datatype sort
    let predicates = problem.predicates();
    assert!(!predicates.is_empty(), "Should have at least one predicate");
    // #7016: Verify DT definitions are propagated to ChcProblem.datatype_defs
    // so SmtContext receives them via make_smt_context.
    let dt_defs = problem.datatype_defs();
    assert!(
        dt_defs.contains_key("Tuple_bv32_bool"),
        "datatype_defs should contain 'Tuple_bv32_bool', got: {:?}",
        dt_defs.keys().collect::<Vec<_>>()
    );
    let ctors = &dt_defs["Tuple_bv32_bool"];
    assert_eq!(ctors.len(), 1, "Should have exactly one constructor (mk)");
    assert_eq!(ctors[0].0, "mk");
    assert_eq!(
        ctors[0].1.len(),
        2,
        "mk should have 2 selectors (fld_0, fld_1)"
    );
}

#[test]
fn test_declare_datatype_constructor_selector_usage() {
    // Test using constructor and selector in expressions
    let input = r#"
            (set-logic HORN)
            (declare-datatype Pair ((mk (fst Int) (snd Bool))))
            (declare-fun Inv (Pair Int) Bool)
            (declare-var p Pair)
            (declare-var x Int)
            (assert
                (forall ((p Pair) (x Int))
                    (=> (= (fst p) x) (Inv p x))))
            (check-sat)
        "#;

    let result = ChcParser::parse(input);
    assert!(
        result.is_ok(),
        "Should parse constructor/selector usage: {:?}",
        result.err()
    );
}

#[test]
fn test_declare_datatype_overloaded_selectors_resolve_by_argument_sort() {
    let input = r#"
            (set-logic HORN)
            (declare-datatypes ((Inner 0) (Outer 0))
              (((Inner_mk (fld_0 (_ BitVec 8)) (fld_1 Bool)))
               ((Outer_mk (fld_0 Inner) (fld_1 (_ BitVec 8))))))
            (assert (= (concat (fld_0 (fld_0 (Outer_mk (Inner_mk #x2a true) #x07))) #x07) #x2a07))
            (check-sat)
        "#;

    let result = ChcParser::parse(input);
    assert!(
        result.is_ok(),
        "Overloaded datatype selectors should resolve by argument sort: {:?}",
        result.err()
    );
}

#[test]
fn test_declare_datatype_nullary_constructor() {
    // Test nullary constructors (like Nil in a list type)
    let input = r#"
            (set-logic HORN)
            (declare-datatype MyList ((nil) (cons (head Int) (tail MyList))))
            (declare-fun Inv (MyList) Bool)
            (assert
                (forall ((x Int))
                    (Inv nil)))
            (check-sat)
        "#;

    let result = ChcParser::parse(input);
    assert!(
        result.is_ok(),
        "Should parse nullary constructor 'nil': {:?}",
        result.err()
    );
}

#[test]
fn test_declare_datatype_wrong_arg_count_errors() {
    // Test that wrong argument count produces an error
    let input = r#"
            (set-logic HORN)
            (declare-datatype Pair ((mk (fst Int) (snd Bool))))
            (declare-fun Inv (Pair) Bool)
            (assert
                (forall ((x Int))
                    (Inv (mk x))))
            (check-sat)
        "#;

    let result = ChcParser::parse(input);
    assert!(
        result.is_err(),
        "Should error on wrong argument count for constructor 'mk'"
    );
    let err_msg = result.expect_err("test should fail").to_string();
    assert!(
        err_msg.contains("expects 2 arguments"),
        "Error should mention expected arg count: {err_msg}"
    );
}

#[test]
fn test_declare_datatypes_plural_mutual_recursive() {
    // #7016: declare-datatypes (plural form) for mutually recursive Tree/Forest
    let input = r#"
(set-logic HORN)
(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf (val Int)) (node (children Forest)))
   ((nil) (cons (head Tree) (tail Forest)))))
(declare-fun |inv| (Tree) Bool)
(assert (forall ((t Tree)) (=> (= t (leaf 42)) (inv t))))
(assert (forall ((t Tree)) (=> (inv t) (inv t))))
(assert (forall ((t Tree)) (=> (and (inv t) (is-leaf t) (< (val t) 0)) false)))
(check-sat)
        "#;
    let problem = ChcParser::parse(input).expect("declare-datatypes should parse");
    // Verify datatypes are registered
    let dt_defs = problem.datatype_defs();
    assert!(dt_defs.contains_key("Tree"), "Tree DT should be registered");
    assert!(
        dt_defs.contains_key("Forest"),
        "Forest DT should be registered"
    );
    // Verify Tree constructors
    let tree_ctors = &dt_defs["Tree"];
    assert_eq!(tree_ctors.len(), 2, "Tree should have 2 constructors");
    assert_eq!(tree_ctors[0].0, "leaf");
    assert_eq!(tree_ctors[1].0, "node");
    // Verify Forest constructors
    let forest_ctors = &dt_defs["Forest"];
    assert_eq!(forest_ctors.len(), 2, "Forest should have 2 constructors");
    assert_eq!(forest_ctors[0].0, "nil");
    assert_eq!(forest_ctors[1].0, "cons");
}

#[test]
fn test_declare_datatypes_plural_single_type() {
    // declare-datatypes with a single type (non-recursive)
    let input = r#"
(set-logic HORN)
(declare-datatypes ((Pair 0))
  (((mk (fst Int) (snd Int)))))
(declare-fun |inv| (Pair) Bool)
(assert (forall ((p Pair)) (=> (= p (mk 1 2)) (inv p))))
(assert (forall ((p Pair)) (=> (and (inv p) (< (fst p) 0)) false)))
(check-sat)
        "#;
    let problem = ChcParser::parse(input).expect("single declare-datatypes should parse");
    let dt_defs = problem.datatype_defs();
    assert!(dt_defs.contains_key("Pair"));
    let pair_ctors = &dt_defs["Pair"];
    assert_eq!(pair_ctors.len(), 1);
    assert_eq!(pair_ctors[0].0, "mk");
    assert_eq!(pair_ctors[0].1.len(), 2); // fst, snd
}
