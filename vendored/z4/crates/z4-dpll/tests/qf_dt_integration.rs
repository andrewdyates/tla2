// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Integration tests for QF_DT (datatype theory) solver.

use ntest::timeout;
mod common;

/// Basic SAT: x is declared but no constraints
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_unconstrained() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Color ((Red) (Green) (Blue)))
        (declare-fun x () Color)
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Unconstrained datatype variable should be sat"
    );
}

/// UNSAT: Constructor clash - None cannot equal Some(y)
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_constructor_clash() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-fun x () Option)
        (declare-fun y () Int)
        (assert (= x None))
        (assert (= x (Some y)))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "unsat", "Constructor clash should be unsat");
}

/// SAT: Boolean structure should allow escaping a constructor clash.
///
/// This is a regression test for DT conflict explanations: the theory must report
/// conflicts using Boolean atoms present in the SAT layer (equality literals),
/// not datatype terms. Otherwise, the solver can learn an empty clause and
/// incorrectly return UNSAT.
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_with_theory_conflict_learning() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-fun x () Option)
        (declare-fun y () Int)
        (declare-fun c () Bool)

        ;; If c is true, both equalities are forced and the DT theory conflicts.
        ;; The solver should learn a non-empty blocking clause and then find the
        ;; satisfying assignment with c = false.
        (assert (or (not c) (= x None)))
        (assert (or (not c) (= x (Some y))))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "sat");
}

/// UNSAT: Injectivity - if (Some a) = (Some b) then a = b.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_injectivity_single_field() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-fun x () Option)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (= x (Some a)))
        (assert (= x (Some b)))
        (assert (distinct a b))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Constructor injectivity should be unsat"
    );
}

/// UNSAT: Injectivity - if (mk-pair a b) = (mk-pair c d) then a=c and b=d.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_injectivity_multi_field() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun x () Pair)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Int)
        (declare-fun d () Int)
        (assert (= x (mk-pair a b)))
        (assert (= x (mk-pair c d)))
        (assert (distinct a c))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Multi-field constructor injectivity should be unsat"
    );
}

/// UNSAT: Injectivity must compose across multiple equal constructor terms.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_injectivity_transitive_conflict() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-fun x () Option)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Int)
        (assert (= x (Some a)))
        (assert (= x (Some b)))
        (assert (= x (Some c)))
        (assert (distinct b c))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

/// UNSAT: Selector axiom - (fst (mk-pair a b)) must equal a.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_axiom_contradiction() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (not (= (fst (mk-pair a b)) a)))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

/// SAT: Selector axiom - a satisfiable instance.
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_selector_axiom_sanity() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (= (fst (mk-pair a b)) a))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "sat");
}

/// UNSAT: Selector axioms must interact with equality reasoning.
///
/// From selector axioms:
/// - (fst (mk-pair a b)) = a
/// - (fst (mk-pair c d)) = c
///
/// So if (fst (mk-pair a b)) = (fst (mk-pair c d)) and a != c, the problem is unsat.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_axiom_implied_equality_conflict() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Int)
        (declare-fun d () Int)
        (assert (= (fst (mk-pair a b)) (fst (mk-pair c d))))
        (assert (distinct a c))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

/// SAT: Same constructor with different variables (no clash)
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_same_constructor() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun x () Pair)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (= x (mk-pair a b)))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "sat", "Same constructor should be sat");
}

/// UNSAT: Two distinct constructors asserted equal via transitivity
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_transitive_clash() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Color ((Red) (Green) (Blue)))
        (declare-fun x () Color)
        (declare-fun y () Color)
        (assert (= x Red))
        (assert (= y Green))
        (assert (= x y))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Transitive constructor clash should be unsat"
    );
}

/// Push/pop: assertions about datatypes must be scoped correctly across check-sat calls.
#[test]
#[timeout(60_000)]
fn test_qf_dt_push_pop_scopes_assertions() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Color ((Red) (Green)))
        (declare-fun x () Color)
        (check-sat)
        (push 1)
        (assert (= x Red))
        (check-sat)
        (pop 1)
        (assert (= x Green))
        (check-sat)
    "#;
    let result = common::solve(smt);
    let lines: Vec<&str> = result
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, vec!["sat", "sat", "sat"]);
}

/// Push/pop: an UNSAT scope must not poison the outer scope.
#[test]
#[timeout(60_000)]
fn test_qf_dt_push_pop_unsat_then_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Color ((Red) (Green)))
        (declare-fun x () Color)
        (push 1)
        (assert (= x Red))
        (assert (= x Green))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let result = common::solve(smt);
    let lines: Vec<&str> = result
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, vec!["unsat", "sat"]);
}

/// Push/pop: nested scopes must behave as a stack (inner UNSAT doesn't poison outer SAT).
#[test]
#[timeout(60_000)]
fn test_qf_dt_push_pop_nested_stack_behavior() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Color ((Red) (Green)))
        (declare-fun x () Color)
        (check-sat)
        (push 1)
        (assert (= x Red))
        (check-sat)
        (push 1)
        (assert (= x Green))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let result = common::solve(smt);
    let lines: Vec<&str> = result
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, vec!["sat", "sat", "unsat", "sat", "sat"]);
}

/// UNSAT: Selector axioms must be enforced under check-sat-assuming as well.
#[test]
#[timeout(60_000)]
fn test_qf_dt_check_sat_assuming_unsat_selector_axiom_contradiction() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (check-sat-assuming ((not (= (fst (mk-pair a b)) a))))
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "unsat");
}

// ========================== Extended Selector Axiom Tests ==========================
// Issue: #1732, Design: designs/2026-01-31-dt-selector-axioms.md

/// UNSAT: Selector axiom for second field (snd).
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_snd_violation() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (not (= (snd (mk-pair a b)) b)))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Selector axiom: (snd (mk-pair a b)) = b must hold"
    );
}

/// UNSAT: Both selector axioms (disjunction).
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_both_fields() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (or (not (= (fst (mk-pair a b)) a)) (not (= (snd (mk-pair a b)) b))))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "unsat", "Both selector axioms must hold");
}

/// UNSAT: Selector axiom on Option datatype - (value (Some x)) = x.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_option_value() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-fun x () Int)
        (assert (not (= (value (Some x)) x)))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Selector axiom: (value (Some x)) = x must hold"
    );
}

// ========================== Acyclicity Constraint Tests ==========================
// Issue: #1733, Design: designs/2026-01-31-dt-acyclicity.md
//
// Algebraic datatypes require finite (well-founded) interpretations.
// Cycles like `x = cons(1, x)` imply infinite structures and are UNSAT.

/// UNSAT: Direct self-cycle x = cons(1, x) implies infinite list [1, 1, 1, ...].
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_direct_cycle() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (assert (= x (cons 1 x)))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Direct cycle x = cons(1, x) should be unsat"
    );
}

/// UNSAT: Nested cycle x = cons(1, cons(2, x)).
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_nested_cycle() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (assert (= x (cons 1 (cons 2 x))))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Nested cycle x = cons(1, cons(2, x)) should be unsat"
    );
}

/// UNSAT: Indirect two-step cycle x = cons(1, y), y = cons(2, x).
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_indirect_cycle() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const y List)
        (assert (= x (cons 1 y)))
        (assert (= y (cons 2 x)))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Indirect cycle x -> y -> x should be unsat"
    );
}

/// SAT: No cycle - finite list structure.
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_finite_list() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (assert (= x (cons 1 (cons 2 nil))))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "sat", "Finite list should be sat");
}

/// SAT: List ends in nil - no cycle.
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_list_ends_in_nil() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const y List)
        (assert (= x (cons 1 y)))
        (assert (= y nil))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(result.trim(), "sat", "List ending in nil should be sat");
}

/// UNSAT: Longer cycle x -> y -> z -> x.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_three_step_cycle() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const y List)
        (declare-const z List)
        (assert (= x (cons 1 y)))
        (assert (= y (cons 2 z)))
        (assert (= z (cons 3 x)))
        (check-sat)
    "#;
    let result = common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Three-step cycle x -> y -> z -> x should be unsat"
    );
}
