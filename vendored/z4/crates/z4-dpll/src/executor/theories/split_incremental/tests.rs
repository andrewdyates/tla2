// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use super::lemmas::{apply_theory_lemma_incremental, apply_theory_lemma_incremental_persistent};
use super::{
    bias_positive_split_clause_vars, encode_and_add_split_clause, encode_split_pair_incremental,
    ensure_incremental_atom_encoded, replay_incremental_bound_refinements,
    BoundRefinementReplayKey,
};
use crate::incremental_proof_cache::IncrementalNegationCache;
#[cfg(not(kani))]
use hashbrown::HashSet;
use num_bigint::BigInt;
use num_rational::BigRational;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::{BoundRefinementRequest, Sort, TermStore, TheoryLit};
use z4_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver, Variable as SatVariable};

struct DuplicateReplayCheckpoint {
    clauses: usize,
    terms: usize,
    next_var: u32,
    mapping_len: usize,
}

fn assert_duplicate_refinement_replay_state(
    solver: &SatSolver,
    terms: &TermStore,
    local_next_var: u32,
    local_term_to_var_len: usize,
    checkpoint: &DuplicateReplayCheckpoint,
    added_refinement_clauses: &HashSet<BoundRefinementReplayKey>,
) {
    assert_eq!(
        solver.num_clauses(),
        checkpoint.clauses,
        "duplicate refinement replay should not add the same implication twice"
    );
    assert_eq!(
        terms.len(),
        checkpoint.terms,
        "duplicate refinement replay should skip term materialization"
    );
    assert_eq!(
        local_next_var, checkpoint.next_var,
        "duplicate refinement replay should not allocate fresh SAT vars"
    );
    assert_eq!(
        local_term_to_var_len, checkpoint.mapping_len,
        "duplicate refinement replay should not grow atom mappings"
    );
    assert_eq!(
        added_refinement_clauses.len(),
        1,
        "duplicate refinement replay should keep one normalized key"
    );
}

#[test]
fn encode_split_pair_incremental_reuses_existing_split_atoms_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let lt_atom = terms.mk_lt(x, y);
    let gt_atom = terms.mk_gt(x, y);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::new();
    let mut local_var_to_term = super::HashMap::new();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let first = encode_split_pair_incremental(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        (lt_atom, gt_atom),
    )
    .expect("first split encoding should succeed");
    let vars_after_first = solver.user_num_vars();
    let next_var_after_first = local_next_var;
    let term_count_after_first = local_term_to_var.len();
    let reverse_count_after_first = local_var_to_term.len();

    let second = encode_split_pair_incremental(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        (lt_atom, gt_atom),
    )
    .expect("re-encoding the same split should reuse SAT vars");

    assert_eq!(second, first, "split roots should keep stable SAT vars");
    assert_eq!(
        solver.user_num_vars(),
        vars_after_first,
        "reusing split atoms must not allocate fresh SAT vars"
    );
    assert_eq!(
        local_next_var, next_var_after_first,
        "reusing split atoms must not advance the SAT var cursor"
    );
    assert_eq!(
        local_term_to_var.len(),
        term_count_after_first,
        "reusing split atoms must not grow the forward map"
    );
    assert_eq!(
        local_var_to_term.len(),
        reverse_count_after_first,
        "reusing split atoms must not grow the reverse map"
    );
}

#[test]
fn encode_and_add_split_clause_skips_duplicate_clause_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let lt_atom = terms.mk_lt(x, y);
    let gt_atom = terms.mk_gt(x, y);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::new();
    let mut local_var_to_term = super::HashMap::new();
    let mut local_next_var = 0;
    let mut added_split_clauses = HashSet::new();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let first = encode_and_add_split_clause(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        lt_atom,
        gt_atom,
        None,
        &mut added_split_clauses,
    );
    let clauses_after_first = solver.num_clauses();

    let second = encode_and_add_split_clause(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        lt_atom,
        gt_atom,
        None,
        &mut added_split_clauses,
    );

    assert_eq!(second, first, "duplicate split should reuse SAT vars");
    assert_eq!(
        solver.num_clauses(),
        clauses_after_first,
        "duplicate split should not add another identical clause"
    );
    assert_eq!(
        added_split_clauses.len(),
        1,
        "duplicate split should keep only one clause key"
    );
}

#[test]
fn replay_incremental_bound_refinements_skips_duplicate_clause_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let trigger_atom = terms.mk_ge(x, zero);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::new();
    let mut local_var_to_term = super::HashMap::new();
    let mut local_next_var = 0;
    let mut added_refinement_clauses = HashSet::new();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let trigger_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        trigger_atom,
    );
    solver.add_clause(vec![SatLiteral::positive(trigger_var)]);

    let request = BoundRefinementRequest {
        variable: x,
        rhs_term: None,
        bound_value: BigRational::from(BigInt::from(1)),
        is_upper: true,
        is_integer: false,
        reason: vec![TheoryLit::new(trigger_atom, true)],
    };

    assert!(replay_incremental_bound_refinements(
        &mut terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        std::slice::from_ref(&request),
        &mut added_refinement_clauses,
    ));
    let checkpoint = DuplicateReplayCheckpoint {
        clauses: solver.num_clauses(),
        terms: terms.len(),
        next_var: local_next_var,
        mapping_len: local_term_to_var.len(),
    };

    assert!(replay_incremental_bound_refinements(
        &mut terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        &[request],
        &mut added_refinement_clauses,
    ));

    assert_duplicate_refinement_replay_state(
        &solver,
        &terms,
        local_next_var,
        local_term_to_var.len(),
        &checkpoint,
        &added_refinement_clauses,
    );
}

#[test]
fn bound_refinement_replay_key_normalizes_integer_bounds_and_reason_order_issue_6586() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Bool);
    let z = terms.mk_var("z", Sort::Bool);

    let first = BoundRefinementReplayKey::new(&BoundRefinementRequest {
        variable: x,
        rhs_term: None,
        bound_value: BigRational::new(BigInt::from(7), BigInt::from(2)),
        is_upper: true,
        is_integer: true,
        reason: vec![TheoryLit::new(z, false), TheoryLit::new(y, true)],
    });
    let second = BoundRefinementReplayKey::new(&BoundRefinementRequest {
        variable: x,
        rhs_term: None,
        bound_value: BigRational::new(BigInt::from(3), BigInt::from(1)),
        is_upper: true,
        is_integer: true,
        reason: vec![
            TheoryLit::new(y, true),
            TheoryLit::new(z, false),
            TheoryLit::new(y, true),
        ],
    });

    assert_eq!(
        first, second,
        "request-level replay keys should canonicalize integer bounds and reason literals"
    );
}

#[test]
fn bias_positive_split_clause_vars_prefers_both_disjuncts_issue_6586() {
    let mut solver = SatSolver::new(2);
    let left_var = SatVariable::new(0);
    let right_var = SatVariable::new(1);

    bias_positive_split_clause_vars(&mut solver, left_var, right_var);

    assert_eq!(
        solver.var_phase(left_var),
        Some(true),
        "disequality/expression split left branch should be tried as true"
    );
    assert_eq!(
        solver.var_phase(right_var),
        Some(true),
        "disequality/expression split right branch should be tried as true"
    );
}

#[test]
fn apply_theory_lemma_incremental_encodes_fresh_atoms_issue_6662() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);

    let mut solver = SatSolver::new(0);
    let mut local_term_to_var = super::HashMap::new();
    let mut local_var_to_term = super::HashMap::new();
    let mut local_next_var = 0;
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    apply_theory_lemma_incremental(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        &[TheoryLit::new(p, true), TheoryLit::new(q, false)],
    );

    let p_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        p,
    );
    let q_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut local_term_to_var,
        &mut local_var_to_term,
        &mut local_next_var,
        &mut negations,
        q,
    );
    solver.add_clause(vec![SatLiteral::negative(p_var)]);
    solver.add_clause(vec![SatLiteral::positive(q_var)]);

    assert_eq!(
        solver.solve().into_inner(),
        SatResult::Unsat,
        "lemma (p ∨ ¬q) plus ¬p and q should be UNSAT after on-demand encoding"
    );
}

#[test]
fn apply_theory_lemma_incremental_persistent_respects_scope_issue_6719() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);

    let mut solver = SatSolver::new(0);
    solver.enable_clause_trace();
    let mut term_to_var = super::HashMap::new();
    let mut var_to_term = super::HashMap::new();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    solver.push();
    let recorded = apply_theory_lemma_incremental_persistent(
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut negations,
        &[TheoryLit::new(p, true)],
    );
    assert!(
        recorded,
        "unit theory lemma should be retained in the SAT original-clause ledger"
    );
    assert_eq!(
        solver
            .clause_trace()
            .expect("clause trace enabled")
            .original_clauses()
            .count(),
        1,
        "scoped no-split lemma should appear once in the trace"
    );

    let mut local_next_var = 0;
    let p_var = ensure_incremental_atom_encoded(
        &terms,
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut local_next_var,
        &mut negations,
        p,
    );
    solver.add_clause_global(vec![SatLiteral::negative(p_var)]);
    assert_eq!(
        solver.solve().into_inner(),
        SatResult::Unsat,
        "scoped lemma p together with global ¬p should be UNSAT before pop"
    );

    assert!(
        solver.pop(),
        "expected scoped lemma push frame to pop cleanly"
    );
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "no-split theory lemma must be scoped, not global, after pop"
    );
}

#[test]
fn apply_theory_lemma_incremental_persistent_skips_tautology_trace_issue_6719() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Bool);

    let mut solver = SatSolver::new(0);
    solver.enable_clause_trace();
    let mut term_to_var = super::HashMap::new();
    let mut var_to_term = super::HashMap::new();
    let mut negations = IncrementalNegationCache::seed(&mut terms, std::iter::empty(), false);

    let trace_original_count = solver
        .clause_trace()
        .expect("clause trace enabled")
        .original_clauses()
        .count();
    let tautology_recorded = apply_theory_lemma_incremental_persistent(
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut negations,
        &[TheoryLit::new(q, true), TheoryLit::new(q, false)],
    );
    assert!(
        !tautology_recorded,
        "tautological theory lemmas must not claim a SAT original-clause slot"
    );
    assert_eq!(
        solver
            .clause_trace()
            .expect("clause trace enabled")
            .original_clauses()
            .count(),
        trace_original_count,
        "tautological no-split lemma must not grow the clause trace"
    );
}
