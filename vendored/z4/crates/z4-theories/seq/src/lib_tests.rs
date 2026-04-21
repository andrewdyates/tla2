// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use z4_core::term::Symbol;
use z4_core::Sort;

fn make_terms() -> TermStore {
    TermStore::new()
}

#[test]
fn test_seq_solver_unit_injectivity() {
    let mut terms = make_terms();

    // Create seq.unit(a) and seq.unit(b) where a, b are Int variables
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let unit_a = terms.mk_app(Symbol::named("seq.unit"), vec![a], Sort::seq(Sort::Int));
    let unit_b = terms.mk_app(Symbol::named("seq.unit"), vec![b], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_a, unit_b], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    // Should propagate a = b via Nelson-Oppen
    let eq_result = solver.propagate_equalities();
    assert_eq!(eq_result.equalities.len(), 1);
    assert_eq!(eq_result.equalities[0].lhs, a);
    assert_eq!(eq_result.equalities[0].rhs, b);
}

#[test]
fn test_seq_solver_unit_empty_conflict() {
    let mut terms = make_terms();

    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

#[test]
fn test_seq_solver_push_pop() {
    let mut terms = make_terms();

    let x = terms.mk_var("x", Sort::Int);
    let unit_x = terms.mk_app(Symbol::named("seq.unit"), vec![x], Sort::seq(Sort::Int));
    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![unit_x, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);

    // Push, assert conflict, check, pop
    solver.push();
    solver.assert_literal(eq, true);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    solver.pop();

    // After pop, should be sat again
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_seq_solver_model_extraction() {
    let mut terms = make_terms();

    // s = seq.unit(5)
    let five = terms.mk_int(5.into());
    let unit_5 = terms.mk_app(Symbol::named("seq.unit"), vec![five], Sort::seq(Sort::Int));
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, unit_5], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert_eq!(model.values[&s], vec!["5"]);
}

#[test]
fn test_seq_solver_empty_model() {
    let mut terms = make_terms();

    let empty = terms.mk_app(Symbol::named("seq.empty"), vec![], Sort::seq(Sort::Int));
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let eq = terms.mk_app(Symbol::named("="), vec![s, empty], Sort::Bool);

    let mut solver = SeqSolver::new(&terms);
    solver.register_atom(eq);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    let model = solver.extract_model();
    assert!(model.values.contains_key(&s));
    assert!(model.values[&s].is_empty());
}
