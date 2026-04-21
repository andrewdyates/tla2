// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_predicate_application() {
    let input = r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
            (rule (=> (= x 0) (Inv x)))
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
    assert_eq!(problem.clauses().len(), 1);

    // Check that the clause has a predicate head
    let clause = &problem.clauses()[0];
    assert!(matches!(clause.head, ClauseHead::Predicate(_, _)));
}

#[test]
fn test_parse_predicate_in_body() {
    let input = r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
            (rule (=> (= x 0) (Inv x)))
            (rule (=> (and (Inv x) (< x 10)) (Inv (+ x 1))))
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.clauses().len(), 2);

    // Second clause should have a predicate in the body
    let clause = &problem.clauses()[1];
    assert!(
        !clause.body.predicates.is_empty(),
        "Body should contain predicate application"
    );
}

#[test]
fn test_parse_query() {
    let input = r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
            (rule (=> (= x 0) (Inv x)))
            (query Inv)
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    // Should have 2 clauses: 1 rule + 1 query
    assert_eq!(problem.clauses().len(), 2);

    // Query should have False head
    let query_clause = &problem.clauses()[1];
    assert!(query_clause.is_query());
}

#[test]
fn test_parse_primed_variables() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);
    parser.variables.insert("x'".to_string(), ChcSort::Int);

    parser.input = "x'".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");

    match expr {
        ChcExpr::Var(v) => {
            assert!(v.is_primed());
            assert_eq!(v.base_name(), "x");
        }
        _ => panic!("Expected variable expression"),
    }
}

#[test]
fn test_parse_counter_safe_example() {
    let input = r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
            (rule (=> (= x 0) (Inv x)))
            (rule (=> (and (Inv x) (< x 10)) (Inv (+ x 1))))
            (query (and (Inv x) (> x 10)))
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
    assert_eq!(problem.clauses().len(), 3); // 2 rules + 1 query

    // Last clause should be a query
    let query = &problem.clauses()[2];
    assert!(query.is_query());
}

#[test]
fn test_parse_multi_predicate() {
    let input = r#"
            (set-logic HORN)
            (declare-rel P (Int))
            (declare-rel Q (Int Int))
            (declare-var x Int)
            (declare-var y Int)
            (rule (=> (= x 0) (P x)))
            (rule (=> (and (P x) (= y (+ x 1))) (Q x y)))
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 2);
    assert_eq!(problem.clauses().len(), 2);
}

#[test]
fn test_parse_nested_let_expr() {
    let mut parser = ChcParser::new();

    // Test nested let bindings like in three_dots_moving_2
    parser.input = "(let ((a!1 5)) (let ((a!2 (+ a!1 1))) (+ a!2 1)))".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    // After substitution of a!1=5, then a!2=(+ 5 1), should be (+ (+ 5 1) 1)
    // (No constant folding, but substitution works correctly)
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Add, _)));
}

#[test]
fn test_parse_three_dots_clause() {
    // This is the problematic clause from three_dots_moving_2_000.smt2
    let input = r#"(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)
(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int))
    (=>
      (and
        (inv B C F A)
        (let ((a!1 (and (= D (ite (<= B F) (+ 1 B) (+ (- 1) B))) (= E D) (= B C))))
        (let ((a!2 (or (and (= D B) (= E (+ (- 1) C)) (not (= B C))) a!1)))
          (and (= G (+ (- 1) A)) a!2 (not (= C F))))))
      (inv D E F G))))
(check-sat)"#;

    let problem = ChcParser::parse(input).expect("parse failed");

    // Should have 1 clause (the transition rule)
    assert_eq!(problem.clauses().len(), 1);

    let clause = &problem.clauses()[0];

    // Check the constraint doesn't contain raw "a!1" or "a!2" variables
    if let Some(ref constraint) = clause.body.constraint {
        let constraint_str = format!("{constraint}");
        println!("Constraint: {constraint_str}");

        // The let bindings should be expanded - no a!1 or a!2 should appear
        assert!(
            !constraint_str.contains("a!1"),
            "Found unexpanded a!1 in constraint: {constraint_str}"
        );
        assert!(
            !constraint_str.contains("a!2"),
            "Found unexpanded a!2 in constraint: {constraint_str}"
        );
    }
}

#[test]
fn test_relational_encoding_normalization() {
    // Test relational encoding: (Inv i) /\ (< i 10) /\ (= i' (+ i 1)) => Inv(i')
    // Should be normalized to: (Inv i) /\ (< i 10) => Inv((+ i 1))
    let input = r#"
            (set-logic HORN)
            (declare-fun Inv (Int) Bool)
            (assert (forall ((i Int)) (=> (= i 0) (Inv i))))
            (assert (forall ((i Int) (i_prime Int))
              (=> (and (Inv i) (< i 10) (= i_prime (+ i 1))) (Inv i_prime))))
            (check-sat)
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
    assert_eq!(problem.clauses().len(), 2);

    // First clause: fact (= i 0) => Inv(i)
    // This should NOT be transformed (no body predicate)
    let init_clause = &problem.clauses()[0];
    assert!(init_clause.body.predicates.is_empty());
    // The head should still have a variable argument, not a constant
    if let ClauseHead::Predicate(_, args) = &init_clause.head {
        assert_eq!(args.len(), 1);
        // The argument should be a variable (i), not a constant (0)
        assert!(
            matches!(args[0], ChcExpr::Var(_)),
            "Init clause head should have variable arg"
        );
    }

    // Second clause: transition rule should be normalized
    // i_prime should be replaced with (+ i 1) in the head
    let trans_clause = &problem.clauses()[1];
    assert!(!trans_clause.body.predicates.is_empty()); // Has body predicate
    if let ClauseHead::Predicate(_, args) = &trans_clause.head {
        assert_eq!(args.len(), 1);
        // The argument should be an expression (+ i 1), not a variable (i_prime)
        let head_arg = &args[0];
        assert!(
            matches!(head_arg, ChcExpr::Op(ChcOp::Add, _)),
            "Trans clause head should have (+ i 1) expression, got: {head_arg}"
        );
    }

    // The constraint should NOT contain (= i_prime ...) anymore
    if let Some(ref constraint) = trans_clause.body.constraint {
        let constraint_str = format!("{constraint}");
        assert!(
            !constraint_str.contains("i_prime"),
            "i_prime equality should be removed from constraint: {constraint_str}"
        );
    }
}

#[test]
fn test_relational_encoding_preserves_facts() {
    // Fact clauses should NOT be transformed
    // (= x 0) /\ (= y 0) => Inv(x, y) should keep x and y as variables in head
    let input = r#"
            (set-logic HORN)
            (declare-fun Inv (Int Int) Bool)
            (assert (forall ((x Int) (y Int))
              (=> (and (= x 0) (= y 0)) (Inv x y))))
            (check-sat)
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.clauses().len(), 1);

    let clause = &problem.clauses()[0];
    // This is a fact (no body predicates)
    assert!(clause.body.predicates.is_empty());

    // Head should have variables, not constants
    if let ClauseHead::Predicate(_, args) = &clause.head {
        assert_eq!(args.len(), 2);
        assert!(
            matches!(args[0], ChcExpr::Var(_)),
            "First arg should be variable"
        );
        assert!(
            matches!(args[1], ChcExpr::Var(_)),
            "Second arg should be variable"
        );
    }

    // Constraint should still contain the equalities
    if let Some(ref constraint) = clause.body.constraint {
        let constraint_str = format!("{constraint}");
        assert!(
            constraint_str.contains("= x 0") || constraint_str.contains("(= 0 x)"),
            "Constraint should contain x = 0: {constraint_str}"
        );
    }
}
