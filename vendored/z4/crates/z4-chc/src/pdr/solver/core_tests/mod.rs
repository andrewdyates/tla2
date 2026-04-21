// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::caches::PdrCacheStore;
use super::PdrSolver;
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::{Frame, Lemma};
use crate::pdr::obligation::ProofObligation;
use crate::{
    ChcDtConstructor, ChcDtSelector, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, HornClause, SmtValue,
};
use rustc_hash::FxHashMap;
use std::sync::Arc;

mod cube_and_mbp;
mod formula_extraction;
mod integer_and_bounds;
mod lemma_propagation;
mod must_reach_and_dt;
mod pdr_construction;

/// Build a minimal single-predicate linear CHC problem: P(x) => P(x).
fn test_linear_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));
    problem
}

fn test_config() -> PdrConfig {
    PdrConfig {
        verbose: false,
        use_negated_equality_splits: false,
        ..PdrConfig::default()
    }
}
