// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_try_solve_trivial_safe_returns_valid_model() {
    // Regression test for #2254: `try_solve_trivial` used to return `Safe` with an empty
    // model even when the problem contains predicates, which later fails model validation.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    let config = PortfolioConfig {
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(model) => {
            assert!(!model.is_empty(), "Safe model should not be empty");
            assert!(matches!(
                solver.validate_safe(&model),
                ValidationResult::Valid
            ));
        }
        _ => panic!("Expected Safe from try_solve_trivial"),
    }
}

#[test]
fn test_try_solve_trivial_unsat_query_safe_returns_valid_model() {
    // Regression coverage for #2254: query-constraint UNSAT path should return a valid model.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    // Query: q = 0 /\ q != 0 => false (UNSAT)
    let q = ChcVar::new("q", ChcSort::Int);
    let unsat = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(q.clone()), ChcExpr::int(0)),
        ChcExpr::ne(ChcExpr::var(q), ChcExpr::int(0)),
    );
    problem.add_clause(HornClause::query(ClauseBody::constraint(unsat)));

    let config = PortfolioConfig {
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(model) => {
            assert!(!model.is_empty(), "Safe model should not be empty");
            assert!(matches!(
                solver.validate_safe(&model),
                ValidationResult::Valid
            ));
        }
        _ => panic!("Expected Safe from try_solve_trivial (unsat query constraints)"),
    }
}

#[test]
fn test_try_solve_trivial_sat_query_returns_unsafe() {
    // Regression coverage for #2254: satisfiable query constraint should return Unsafe.
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::empty()));

    let config = PortfolioConfig {
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        validate: false,
        enable_preprocessing: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unsafe(cex) => {
            assert!(
                cex.steps.is_empty(),
                "Trivial unsafe should return empty-step counterexample"
            );
        }
        _ => panic!("Expected Unsafe from try_solve_trivial (sat query constraint)"),
    }
}
