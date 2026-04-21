// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for bound invariant discovery.

#![allow(clippy::unwrap_used)]

use crate::pdr::solver::test_helpers::solver_from_str;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};
use ntest::timeout;

#[test]
#[timeout(10_000)]
fn discover_sum_bounds_emits_tightest_only() {
    let input = r#"(set-logic HORN)

(declare-fun inv ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (= A 0) (= B 0))
      (inv A B)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=>
      (and
        (inv A B)
        (= A1 (- A 1))
        (= B1 (+ B 1))
      )
      (inv A1 B1)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (inv A B)
        (not (>= (+ A B) 0))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    let mut solver = solver_from_str(input);
    solver.discover_sum_bounds();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");
    assert_eq!(vars.len(), 2);
    let var_a = vars[0].clone();
    let var_b = vars[1].clone();

    let expected_tight = ChcExpr::ge(
        ChcExpr::add(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone())),
        ChcExpr::Int(0),
    );
    let expected_weak = ChcExpr::ge(
        ChcExpr::add(ChcExpr::var(var_a), ChcExpr::var(var_b)),
        ChcExpr::Int(-1),
    );

    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(lemmas.iter().any(|l| l.formula == expected_tight));
    assert!(!lemmas.iter().any(|l| l.formula == expected_weak));
    assert_eq!(lemmas.len(), 1);
}

/// Sum upper bound discovery: A + B <= 0 for counter-pair with sum-preserving transition.
/// Models the s_mutants_21 pattern where A increments and B decrements (or vice versa),
/// preserving A + B = 0. The upper bound A + B <= 0 complements the lower bound A + B >= 0
/// to establish the equality.
#[test]
#[timeout(10_000)]
fn discover_sum_upper_bounds_emits_tightest_only() {
    let input = r#"(set-logic HORN)

(declare-fun inv ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (= A 0) (= B 0))
      (inv A B)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=>
      (and
        (inv A B)
        (= A1 (+ A 1))
        (= B1 (- B 1))
      )
      (inv A1 B1)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (inv A B)
        (not (>= (+ A B) 0))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    let mut solver = solver_from_str(input);
    solver.discover_sum_upper_bounds();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");
    assert_eq!(vars.len(), 2);
    let var_a = vars[0].clone();
    let var_b = vars[1].clone();

    let expected_tight = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone())),
        ChcExpr::Int(0),
    );
    let expected_weak = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(var_a), ChcExpr::var(var_b)),
        ChcExpr::Int(1),
    );

    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    assert!(
        lemmas.iter().any(|l| l.formula == expected_tight),
        "Expected tight upper bound A+B<=0 not found. Lemmas: {:?}",
        lemmas
            .iter()
            .map(|l| l.formula.to_string())
            .collect::<Vec<_>>()
    );
    assert!(
        !lemmas.iter().any(|l| l.formula == expected_weak),
        "Weak upper bound A+B<=1 should NOT be present. Lemmas: {:?}",
        lemmas
            .iter()
            .map(|l| l.formula.to_string())
            .collect::<Vec<_>>()
    );
    assert_eq!(lemmas.len(), 1);
}

#[test]
#[timeout(10_000)]
fn discover_scaled_diff_bounds_emits_tightest_only() {
    let input = r#"(set-logic HORN)

(declare-fun inv ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (= A 0) (= B 1))
      (inv A B)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) (A1 Int) (B1 Int) )
    (=>
      (and
        (inv A B)
        (= A1 (+ A 1))
        (= B1 (+ B 2))
      )
      (inv A1 B1)
    )
  )
)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (inv A B)
        (< B 0)
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    let mut solver = solver_from_str(input);
    solver.discover_scaled_difference_bounds();

    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "inv")
        .expect("inv predicate")
        .id;
    let vars = solver.canonical_vars(pred).expect("canonical vars");
    assert_eq!(vars.len(), 2);
    let var_a = vars[0].clone();
    let var_b = vars[1].clone();

    let expected_tight = ChcExpr::ge(
        ChcExpr::sub(
            ChcExpr::var(var_b.clone()),
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(var_a.clone())),
        ),
        ChcExpr::Int(1),
    );
    let expected_weak = ChcExpr::ge(
        ChcExpr::sub(
            ChcExpr::var(var_b),
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(var_a)),
        ),
        ChcExpr::Int(0),
    );

    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == pred)
        .collect();
    // Key assertions: tight bound exists, weak version is NOT present
    // Note: Multiple different scaled diff bounds may be discovered (e.g., B-2A>=1 and B-4A>=-1)
    // The test verifies that for scale=2, we emit B-2A>=1 (tight), not B-2A>=0 (weak).
    assert!(
        lemmas.iter().any(|l| l.formula == expected_tight),
        "Expected tight bound B-2A>=1 not found. Lemmas: {:?}",
        lemmas
            .iter()
            .map(|l| l.formula.to_string())
            .collect::<Vec<_>>()
    );
    assert!(
        !lemmas.iter().any(|l| l.formula == expected_weak),
        "Weak bound B-2A>=0 should NOT be present. Lemmas: {:?}",
        lemmas
            .iter()
            .map(|l| l.formula.to_string())
            .collect::<Vec<_>>()
    );
    // Allow multiple different scaled bounds to be discovered (e.g., scale=2 and scale=4)
    // The test's purpose is to verify tightest-bound selection, not unique bound count.
    assert!(
        !lemmas.is_empty(),
        "Expected at least 1 lemma for scaled diff bounds"
    );
}

#[test]
#[timeout(10_000)]
fn discover_entry_guard_bounds_handles_expression_head_args() {
    let input = r#"(set-logic HORN)

(declare-fun src ( Int ) Bool)
(declare-fun dst ( Int ) Bool)

(assert
  (forall ( (x Int) )
    (=>
      (= x 0)
      (src x)
    )
  )
)

(assert
  (forall ( (x Int) )
    (=>
      (and
        (src x)
        (< x 10)
      )
      (dst (+ x 1))
    )
  )
)

(assert
  (forall ( (y Int) )
    (=>
      (dst y)
      (dst y)
    )
  )
)

(check-sat)
(exit)
"#;

    let mut solver = solver_from_str(input);
    solver.discover_entry_guard_bounds();

    let dst = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "dst")
        .expect("dst predicate")
        .id;
    let dst_var = solver
        .canonical_vars(dst)
        .expect("dst canonical vars")
        .first()
        .expect("dst arg 0")
        .clone();
    let expected = ChcExpr::le(ChcExpr::var(dst_var), ChcExpr::Int(10));

    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == dst)
        .collect();
    assert!(
        lemmas.iter().any(|l| l.formula == expected),
        "Expected expression-head bound dst <= 10, lemmas: {:?}",
        lemmas
            .iter()
            .map(|l| l.formula.to_string())
            .collect::<Vec<_>>()
    );
}

fn blocked_state_seed_solver() -> (PdrSolver, PredicateId, Vec<ChcVar>, ChcVar) {
    let input = r#"(set-logic HORN)

(declare-fun inv ( Bool Bool (_ BitVec 32) ) Bool)

(assert
  (forall ( (a Bool) (b Bool) (h (_ BitVec 32)) )
    (=>
      (and a (not b) (= h #x00000001))
      (inv a b h)
    )
  )
)

(assert
  (forall ( (a Bool) (b Bool) (h (_ BitVec 32))
            (a1 Bool) (b1 Bool) (h1 (_ BitVec 32)) )
    (=>
      (and
        (inv a b h)
        a
        (not b)
        (= a1 a)
        (= b1 b)
        (= h1 h)
        (bvsle #x00000001 h)
      )
      (inv a1 b1 h1)
    )
  )
)

(check-sat)
(exit)
"#;

    let solver = solver_from_str(input);
    let pred = solver
        .problem
        .lookup_predicate("inv")
        .expect("inv predicate");
    let vars = solver
        .canonical_vars(pred)
        .expect("canonical vars")
        .to_vec();
    let h = vars[2].clone();
    (solver, pred, vars, h)
}

fn bv_lower_bound(var: &ChcVar, value: u128) -> ChcExpr {
    ChcExpr::Op(
        ChcOp::BvSLe,
        vec![
            std::sync::Arc::new(ChcExpr::BitVec(value, 32)),
            std::sync::Arc::new(ChcExpr::var(var.clone())),
        ],
    )
}

#[test]
#[timeout(10_000)]
fn extract_bv_candidate_invariants_include_blocked_state_seed_constants() {
    let (mut solver, pred, vars, h) = blocked_state_seed_solver();

    solver.record_blocked_state_for_convex(
        pred,
        &ChcExpr::eq(ChcExpr::var(h.clone()), ChcExpr::BitVec(5, 32)),
    );
    solver.record_blocked_state_for_convex(
        pred,
        &ChcExpr::eq(ChcExpr::var(h.clone()), ChcExpr::BitVec(7, 32)),
    );

    let candidates = solver.extract_bv_candidate_invariants(pred, &vars);
    let expected_five = bv_lower_bound(&h, 5);
    let expected_seven = bv_lower_bound(&h, 7);

    assert!(
        candidates
            .iter()
            .any(|candidate| candidate == &expected_five),
        "blocked-state constant 5 should seed a BV lower bound candidate; candidates: {:?}",
        candidates
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );
    assert!(
        candidates
            .iter()
            .any(|candidate| candidate == &expected_seven),
        "blocked-state constant 7 should seed a BV lower bound candidate; candidates: {:?}",
        candidates
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );
}

#[test]
#[timeout(10_000)]
fn extract_bv_clause_seeds_include_blocked_state_seed_constants() {
    let (mut solver, pred, vars, h) = blocked_state_seed_solver();

    solver.record_blocked_state_for_convex(
        pred,
        &ChcExpr::eq(ChcExpr::var(h.clone()), ChcExpr::BitVec(9, 32)),
    );

    let clause_seeds = solver.extract_bv_clause_seeds(pred, &vars);
    let expected = bv_lower_bound(&h, 9);

    assert!(
        clause_seeds
            .iter()
            .any(|seed| seed.comparison_atoms.iter().any(|atom| atom == &expected)),
        "blocked-state constant should seed clause-local BV comparison atoms; seeds: {:?}",
        clause_seeds
            .iter()
            .map(|seed| {
                seed.comparison_atoms
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    );
}
