// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

fn create_simple_loop_problem() -> ChcProblem {
    // x = 0 => Inv(x)
    // Inv(x) /\ x < 10 => Inv(x + 1)
    // Inv(x) /\ x >= 10 => false
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
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_trivial_problem() -> ChcProblem {
    // x = 0 => Inv(x)
    // Inv(x) /\ x >= 5 => false
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
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_multi_pred_problem() -> ChcProblem {
    // P(x) /\ x < 10 => Q(x+1)
    // Q(y) /\ y < 20 => P(y+1)
    // P(x) /\ x >= 15 => false
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) /\ x < 10 => Q(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Q(y) /\ y < 20 => P(y+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(20))),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1))]),
    ));

    // P(x) /\ x >= 15 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(15))),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_classify_simple_loop() {
    let problem = create_simple_loop_problem();
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 1);
    assert_eq!(features.num_clauses, 3);
    assert!(features.is_linear);
    assert!(features.is_single_predicate);
    assert!(!features.uses_arrays);
    assert!(!features.uses_real);
    assert_eq!(features.num_transitions, 1);
    assert_eq!(features.num_facts, 1);
    assert_eq!(features.num_queries, 1);
    assert_eq!(features.class, ProblemClass::SimpleLoop);

    // Extended features (#7915)
    assert_eq!(features.scc_count, 1);
    assert_eq!(features.max_scc_size, 1);
    assert_eq!(features.dag_depth, 1);
    assert!(features.max_clause_variables > 0);
    assert!(features.mean_clause_variables > 0.0);
    assert!(!features.has_multiplication);
    assert!(!features.has_mod_div);
    assert!(!features.has_ite);
    assert_eq!(features.self_loop_ratio, 1.0); // single transition is a self-loop
    assert_eq!(features.max_predicate_arity, 1);
}

#[test]
fn test_classify_trivial() {
    let problem = create_trivial_problem();
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 1);
    assert_eq!(features.num_clauses, 2);
    assert!(features.is_single_predicate);
    assert_eq!(features.class, ProblemClass::Trivial);
}

#[test]
fn test_classify_multi_pred() {
    let problem = create_multi_pred_problem();
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 2);
    assert!(!features.is_single_predicate);
    assert!(features.is_linear);
    // Has a cycle: P -> Q -> P
    assert!(features.has_cycles);
    assert_eq!(features.class, ProblemClass::MultiPredLinear);

    // Extended features (#7915) — cycle P->Q->P forms a single cyclic SCC
    assert_eq!(features.scc_count, 1);
    assert_eq!(features.max_scc_size, 2);
    assert_eq!(features.dag_depth, 1);
    assert_eq!(features.max_predicate_arity, 1);
}

/// Create an entry-exit-only problem (Golem's isTrivial pattern)
/// This has no predicates - just queries with constraints
fn create_entry_exit_only_safe() -> ChcProblem {
    // x > 5 /\ x < 3 => false  (UNSAT - safe)
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    // Query with unsatisfiable constraint
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(5)),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(3)),
        )),
        ClauseHead::False,
    ));

    problem
}

fn create_entry_exit_only_unsafe() -> ChcProblem {
    // x > 0 /\ x < 10 => false  (SAT - unsafe)
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    // Query with satisfiable constraint
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        )),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_classify_entry_exit_only() {
    // Safe case
    let problem = create_entry_exit_only_safe();
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 0);
    assert_eq!(features.num_clauses, 1);
    assert!(features.is_entry_exit_only);
    assert_eq!(features.class, ProblemClass::EntryExitOnly);

    // Unsafe case
    let problem = create_entry_exit_only_unsafe();
    let features = ProblemClassifier::classify(&problem);

    assert!(features.is_entry_exit_only);
    assert_eq!(features.class, ProblemClass::EntryExitOnly);
}

#[test]
fn test_entry_exit_only_not_regular_problem() {
    // Regular problems with predicates should NOT be entry-exit-only
    let problem = create_simple_loop_problem();
    let features = ProblemClassifier::classify(&problem);
    assert!(!features.is_entry_exit_only);

    let problem = create_trivial_problem();
    let features = ProblemClassifier::classify(&problem);
    assert!(!features.is_entry_exit_only);
}

#[test]
fn test_constraint_feature_scanning() {
    // Problem with multiplication in constraint: x * y > 10 => false
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::gt(
            ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(10),
        )),
        ClauseHead::False,
    ));

    let features = ProblemClassifier::classify(&problem);
    assert!(features.has_multiplication);
    assert!(!features.has_mod_div);
    assert!(!features.has_ite);
    assert_eq!(features.max_clause_variables, 2);
}

#[test]
fn test_extended_features_dag_depth() {
    // Linear chain: P -> Q -> R (no cycles, DAG depth 3)
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Int]);
    let r = problem.declare_predicate("R", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // P(x) => Q(x, x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(x.clone())]),
    ));
    // Q(x, _) => R(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(x.clone())])],
            None,
        ),
        ClauseHead::Predicate(r, vec![ChcExpr::var(x.clone())]),
    ));
    // R(x) /\ x >= 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(r, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let features = ProblemClassifier::classify(&problem);
    assert_eq!(features.num_predicates, 3);
    assert!(!features.has_cycles);
    assert_eq!(features.scc_count, 3); // 3 singleton SCCs
    assert_eq!(features.max_scc_size, 1);
    assert!(features.dag_depth >= 3); // chain P->Q->R
    assert_eq!(features.max_predicate_arity, 2); // Q has arity 2
    assert_eq!(features.self_loop_ratio, 0.0); // no self-loops
}
