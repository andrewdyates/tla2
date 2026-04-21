// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_is_trivial_contradiction_le_and_ge_is_not_contradiction() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::ge(ChcExpr::var(a), ChcExpr::var(b)),
    );

    assert!(!cube::is_trivial_contradiction(&expr));
}

#[test]
fn test_point_values_satisfy_cube_handles_simple_bounds() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    let cube = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10)),
    );

    let mut values: FxHashMap<String, SmtValue> = FxHashMap::default();
    values.insert("x".to_string(), SmtValue::Int(5));
    assert!(solver.point_values_satisfy_cube(&cube, &values));

    values.insert("x".to_string(), SmtValue::Int(11));
    assert!(!solver.point_values_satisfy_cube(&cube, &values));
}

#[test]
fn test_point_values_satisfy_cube_swaps_constant_on_lhs() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    // (<= 10 x)  <=>  (>= x 10)
    let cube = ChcExpr::le(ChcExpr::int(10), ChcExpr::var(x));

    let mut values: FxHashMap<String, SmtValue> = FxHashMap::default();
    values.insert("x".to_string(), SmtValue::Int(11));
    assert!(solver.point_values_satisfy_cube(&cube, &values));

    values.insert("x".to_string(), SmtValue::Int(9));
    assert!(!solver.point_values_satisfy_cube(&cube, &values));
}

#[test]
fn test_is_trivial_contradiction_le_and_gt_is_contradiction() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::gt(ChcExpr::var(a), ChcExpr::var(b)),
    );

    assert!(cube::is_trivial_contradiction(&expr));
}

#[test]
fn test_is_trivial_contradiction_le_ge_and_not_eq_is_contradiction() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
            ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ),
        ChcExpr::not(ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b))),
    );

    assert!(cube::is_trivial_contradiction(&expr));
}

#[test]
fn test_is_trivial_contradiction_reversed_order_is_handled() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let not_contradiction = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::gt(ChcExpr::var(b.clone()), ChcExpr::var(a.clone())),
    );
    assert!(!cube::is_trivial_contradiction(&not_contradiction));

    let contradiction = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::lt(ChcExpr::var(b), ChcExpr::var(a)),
    );
    assert!(cube::is_trivial_contradiction(&contradiction));
}

#[test]
fn pdr_applies_user_hints_as_lemmas() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))

(assert
  (forall ((x Int) (x_next Int))
(=>
  (and (inv x) (= x_next (+ x 1)) (< x 5))
  (inv x_next)
)
  )
)

(assert (forall ((x Int)) (=> (and (inv x) (< x (- 123))) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.predicates()[0].id;
    let canonical_vars = solver.canonical_vars(pred_id).unwrap();
    let x = canonical_vars[0].clone();

    // Use a weak-but-inductive hint that isn't produced by built-in hint providers
    // (init bounds would yield x >= 0, but not x >= -123).
    let hint_formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(-123));
    solver.config.user_hints = vec![LemmaHint::new(pred_id, hint_formula.clone(), 0, "user")];

    assert!(
        !solver.frames[1].contains_lemma(pred_id, &hint_formula),
        "test setup: hint unexpectedly already present"
    );

    solver.apply_lemma_hints(HintStage::Startup);

    assert!(
        solver
            .frames
            .iter()
            .any(|f| f.contains_lemma(pred_id, &hint_formula)),
        "expected user hint to be added as a lemma"
    );
}

#[test]
fn pdr_applies_conjunctive_user_hints_when_individual_hints_fail_self_inductive() {
    // Regression test: some hint sets are jointly self-inductive even when each hint
    // fails `is_self_inductive_blocking` in isolation. In these cases we should
    // retry validation on the conjunction.
    //
    // Construction:
    // - Hint A: x >= 0
    // - Hint B: y = 0
    // - From x>=0 alone: unreachable states with y=1 can decrement x below 0.
    // - From y=0 alone: unreachable states with x<0 can flip y to 1.
    // - From (x>=0 ∧ y=0): both counterexample branches are pruned, making the
    //   conjunction self-inductive.
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))

; y = 0, x >= 0  -> x' = x + 1, y' = 0
(assert
  (forall ((x Int) (y Int) (x2 Int) (y2 Int))
(=>
  (and (inv x y) (= y 0) (>= x 0) (= x2 (+ x 1)) (= y2 0))
  (inv x2 y2)
)
  )
)

; y = 0, x < 0  -> x' = x - 1, y' = 1   (breaks y=0 unless x>=0 is assumed)
(assert
  (forall ((x Int) (y Int) (x2 Int) (y2 Int))
(=>
  (and (inv x y) (= y 0) (< x 0) (= x2 (- x 1)) (= y2 1))
  (inv x2 y2)
)
  )
)

; y = 1, x >= 0 -> x' = x - 1, y' = 0   (breaks x>=0 unless y=0 is assumed)
(assert
  (forall ((x Int) (y Int) (x2 Int) (y2 Int))
(=>
  (and (inv x y) (= y 1) (>= x 0) (= x2 (- x 1)) (= y2 0))
  (inv x2 y2)
)
  )
)

; y = 1, x < 0  -> x' = x + 1, y' = 1
(assert
  (forall ((x Int) (y Int) (x2 Int) (y2 Int))
(=>
  (and (inv x y) (= y 1) (< x 0) (= x2 (+ x 1)) (= y2 1))
  (inv x2 y2)
)
  )
)

; No safety query needed: we only test hint injection.
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let canonical_vars = solver.canonical_vars(pred_id).unwrap();
    let x = canonical_vars[0].clone();
    let y = canonical_vars[1].clone();

    let hint_x_ge_0 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let hint_y_eq_0 = ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(0));
    solver.config.user_hints = vec![
        LemmaHint::new(pred_id, hint_x_ge_0.clone(), 0, "test-conj"),
        LemmaHint::new(pred_id, hint_y_eq_0.clone(), 0, "test-conj"),
    ];

    let mut expected_conjuncts = vec![hint_x_ge_0, hint_y_eq_0];
    expected_conjuncts.sort();
    let expected = ChcExpr::and_vec(expected_conjuncts);

    assert!(
        solver
            .frames
            .iter()
            .all(|f| !f.contains_lemma(pred_id, &expected)),
        "test setup: conjunction unexpectedly already present"
    );

    // Use a stage with no built-in providers for this problem shape, so the test isolates
    // the user-hint logic (bounds-from-init + recurrence only run at Startup).
    solver.apply_lemma_hints(HintStage::Stuck);

    assert!(
        solver
            .frames
            .iter()
            .any(|f| f.contains_lemma(pred_id, &expected)),
        "expected conjunction hint to be added as a lemma"
    );
}

#[test]
fn pdr_solve_applies_user_hints_as_lemmas() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))

(assert
  (forall ((x Int) (x_next Int))
(=>
  (and (inv x) (= x_next (+ x 1)) (< x 5))
  (inv x_next)
)
  )
)

(assert (forall ((x Int)) (=> (and (inv x) (< x (- 123))) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.predicates()[0].id;
    let canonical_vars = solver.canonical_vars(pred_id).unwrap();
    let x = canonical_vars[0].clone();
    let hint_formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(-123));
    solver.config.user_hints = vec![LemmaHint::new(pred_id, hint_formula.clone(), 0, "user")];

    assert!(
        !solver.frames[1].contains_lemma(pred_id, &hint_formula),
        "test setup: hint unexpectedly already present"
    );

    // Call apply_lemma_hints directly because solve() may prove safety via
    // discovery before reaching the hint application code (the problem is
    // trivially safe: x starts at 0, increments to 5, query is x < -123).
    solver.apply_lemma_hints(crate::lemma_hints::HintStage::Startup);

    assert!(
        solver
            .frames
            .iter()
            .any(|f| f.contains_lemma(pred_id, &hint_formula)),
        "expected user hint to be applied as a lemma"
    );

    // Also verify solve() produces Safe
    let result = solver.solve();
    assert!(
        matches!(result, crate::pdr::PdrResult::Safe(_)),
        "expected Safe result"
    );
}
