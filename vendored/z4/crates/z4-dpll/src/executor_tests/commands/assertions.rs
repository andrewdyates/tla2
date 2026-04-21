// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========== get-assertions tests ==========

#[test]
fn test_get_assertions_empty() {
    let input = r#"
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "()");
}

#[test]
fn test_get_assertions_single() {
    let input = r#"
        (declare-const a Bool)
        (assert a)
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains('a'),
        "Expected assertion 'a': {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_multiple() {
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains('a'),
        "Expected assertion 'a': {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains("not"),
        "Expected 'not' in assertions: {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_with_compound() {
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (assert (and x y))
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("and"),
        "Expected 'and' in assertions: {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_with_euf() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains('='),
        "Expected '=' in assertions: {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_requotes_symbols_with_colons() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const |foo::bar| Int)
        (assert (= |foo::bar| 0))
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("|foo::bar|"),
        "Expected quoted symbol in assertions: {}",
        outputs[0]
    );

    let sexp = parse_sexp(&outputs[0]).unwrap();
    let SExpr::List(ref items) = sexp else {
        panic!("Expected assertions list, got: {sexp:?}");
    };
    assert_eq!(items.len(), 1);
    let SExpr::List(assertion) = &items[0] else {
        panic!("Expected assertion term list, got: {items:?}");
    };
    assert_eq!(assertion.len(), 3, "Assertion: {assertion:?}");
    assert!(matches!(&assertion[0], SExpr::Symbol(s) if s == "="));
    assert!(matches!(&assertion[1], SExpr::Symbol(s) if s == "foo::bar"));
}

#[test]
fn test_get_assertions_after_push_pop() {
    let input = r#"
        (declare-const a Bool)
        (assert a)
        (push 1)
        (declare-const b Bool)
        (assert b)
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Both a and b should be in assertions
    assert!(
        outputs[0].contains('a'),
        "Expected assertion 'a': {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains('b'),
        "Expected assertion 'b': {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_after_pop() {
    let input = r#"
        (declare-const a Bool)
        (assert a)
        (push 1)
        (declare-const b Bool)
        (assert b)
        (pop 1)
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Only 'a' should remain after pop
    assert!(
        outputs[0].contains('a'),
        "Expected assertion 'a' to remain: {}",
        outputs[0]
    );
    // Check that the output only contains one assertion
    // (the "(a)" pattern should be the whole content)
    assert!(
        !outputs[0].contains('b'),
        "Did not expect 'b' after pop: {}",
        outputs[0]
    );
}

// ========== get-assignment Tests ==========

#[test]
fn test_get_assignment_not_enabled() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named my_assertion))
        (check-sat)
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("error"),
        "Expected error about produce-assignments: {}",
        outputs[1]
    );
}

#[test]
fn test_get_assignment_enabled_sat() {
    let input = r#"
        (set-option :produce-assignments true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named my_assertion))
        (check-sat)
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Should contain assignment for my_assertion
    assert!(
        outputs[1].contains("my_assertion"),
        "Expected named term in assignment: {}",
        outputs[1]
    );
    // Since 'a' is asserted, my_assertion should be true
    assert!(
        outputs[1].contains("true"),
        "Expected true value: {}",
        outputs[1]
    );
}

#[test]
fn test_get_assignment_multiple_named() {
    let input = r#"
        (set-option :produce-assignments true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (! a :named a_holds))
        (assert (! (not b) :named not_b_holds))
        (check-sat)
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Both named terms should appear
    assert!(
        outputs[1].contains("a_holds"),
        "Expected a_holds: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("not_b_holds"),
        "Expected not_b_holds: {}",
        outputs[1]
    );
}

#[test]
fn test_get_assignment_no_named_terms() {
    let input = r#"
        (set-option :produce-assignments true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Should return empty list since no named terms
    assert_eq!(outputs[1], "()");
}

#[test]
fn test_get_assignment_before_check_sat() {
    let input = r#"
        (set-option :produce-assignments true)
        (declare-const a Bool)
        (assert (! a :named my_a))
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should return error since no check-sat yet
    assert!(
        outputs[0].contains("error"),
        "Expected error about unavailable assignment: {}",
        outputs[0]
    );
}

// ========== get-unsat-core Tests ==========

#[test]
fn test_get_unsat_core_not_enabled() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named pos_a))
        (assert (! (not a) :named neg_a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        outputs[1].contains("error"),
        "Expected error about produce-unsat-cores: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_core_enabled() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named pos_a))
        (assert (! (not a) :named neg_a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Should contain names of assertions that form the core
    assert!(
        outputs[1].contains("pos_a") || outputs[1].contains("neg_a"),
        "Expected named assertions in core: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_core_after_sat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named pos_a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Should return error since last result was not unsat
    assert!(
        outputs[1].contains("error"),
        "Expected error about unsat core not available: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_core_no_named_terms() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Should return empty list since no named terms
    assert_eq!(outputs[1], "()");
}
