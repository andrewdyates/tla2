// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test for the `z4::chc` and `z4::executor` facade modules (#4696).
//!
//! Verifies that CHC and executor types are accessible through the root crate,
//! matching the surface that tla2 and zani currently fetch from `z4_chc` and
//! `z4_dpll` directly.

#![allow(deprecated)]

use z4::chc::{
    AdaptiveConfig, ChcExpr, ChcProblem, ChcSort, ClauseBody, ClauseHead, EngineConfig, HornClause,
    InvariantModel, LemmaHint, PdrConfig, PdrResult, PortfolioConfig, PortfolioResult, Predicate,
    PredicateId,
};
use z4::executor::{Executor, ExecutorError};

fn assert_public_type<T>() {}

#[test]
fn test_chc_facade_reexports_consumer_surface() {
    assert_public_type::<ChcProblem>();
    assert_public_type::<ChcExpr>();
    assert_public_type::<ChcSort>();
    assert_public_type::<ClauseBody>();
    assert_public_type::<ClauseHead>();
    assert_public_type::<HornClause>();
    assert_public_type::<Predicate>();
    assert_public_type::<PredicateId>();
    assert_public_type::<AdaptiveConfig>();
    assert_public_type::<PdrConfig>();
    assert_public_type::<PdrResult>();
    assert_public_type::<PortfolioConfig>();
    assert_public_type::<PortfolioResult>();
    assert_public_type::<EngineConfig>();
    assert_public_type::<InvariantModel>();
    assert_public_type::<LemmaHint>();

    // Trivial construction smoke test
    let problem = ChcProblem::new();
    assert!(problem.predicates().is_empty());
    let _config = PdrConfig::default();
    let _adaptive = AdaptiveConfig::default();
}

#[test]
fn test_executor_facade_reexports() {
    assert_public_type::<Executor>();
    assert_public_type::<ExecutorError>();

    // Trivial construction and SAT check
    let commands = z4::parse("(set-logic QF_LIA)\n(check-sat)").expect("valid input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs, vec!["sat"]);
}
