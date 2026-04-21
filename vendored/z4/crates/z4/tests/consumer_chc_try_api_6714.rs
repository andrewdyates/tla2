// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use z4::chc::{
    engines, CexVerificationResult, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, PdrConfig, PdrResult, PortfolioResult,
};

fn create_safe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn portfolio_try_solve_returns_ok_for_safe_and_unsafe_problems() {
    let safe_solver = engines::new_portfolio_solver(create_safe_problem(), Default::default());
    let safe_result = safe_solver.try_solve();
    assert!(
        matches!(safe_result, Ok(PortfolioResult::Safe(_))),
        "expected safe portfolio result, got {safe_result:?}"
    );

    let unsafe_solver = engines::new_portfolio_solver(create_unsafe_problem(), Default::default());
    let unsafe_result = unsafe_solver.try_solve();
    assert!(
        matches!(unsafe_result, Ok(PortfolioResult::Unsafe(_))),
        "expected unsafe portfolio result, got {unsafe_result:?}"
    );
}

#[test]
fn pdr_try_verify_model_accepts_solver_produced_invariant() {
    let problem = create_safe_problem();
    let mut solver = engines::new_pdr_solver(problem, PdrConfig::default());
    let result = solver.solve();

    let PdrResult::Safe(model) = result else {
        panic!("expected Safe, got {result:?}");
    };

    let verification = solver
        .try_verify_model(&model)
        .expect("verification should not panic");
    assert!(verification, "model should verify successfully");
}

#[test]
fn pdr_try_verify_counterexample_accepts_solver_produced_cex() {
    let problem = create_unsafe_problem();
    let mut solver = engines::new_pdr_solver(problem, PdrConfig::default());
    let result = solver.solve();

    let PdrResult::Unsafe(cex) = result else {
        panic!("expected Unsafe, got {result:?}");
    };

    let verification = solver
        .try_verify_counterexample(&cex)
        .expect("verification should not panic");
    assert_eq!(verification, CexVerificationResult::Valid);
}
