// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use z4_core::term::Symbol;
use z4_core::{Sort, TheoryLemma, TheoryLit};

#[test]
fn collect_active_theory_atoms_filters_boolean_structure_but_keeps_bool_equalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    let lt = terms.mk_app(Symbol::named("<"), vec![x, five], Sort::Bool);
    let eq_xy = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);

    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let eq_bool = terms.mk_app(Symbol::named("="), vec![p, q], Sort::Bool);

    let and_term = terms.mk_app(Symbol::named("and"), vec![lt, eq_bool], Sort::Bool);
    let assertions = [and_term, eq_xy];

    let atoms = collect_active_theory_atoms(&terms, &assertions);
    // Bool-Bool equality (= p q) IS now a theory atom (#6869):
    // EUF must see all equalities to propagate alias chains.
    assert_eq!(atoms.len(), 3);
    assert!(atoms.contains(&lt));
    assert!(atoms.contains(&eq_xy));
    assert!(atoms.contains(&eq_bool));
    assert!(!atoms.contains(&and_term));
}

#[test]
fn incremental_bv_state_push_pop_tracks_pending_when_solver_missing() {
    let mut st = IncrementalBvState::new();
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_pushes, 0);

    st.push();
    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_pushes, 1);

    assert!(st.pop());
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_pushes, 0);
    assert!(!st.pop());
}

#[test]
fn incremental_bv_state_pop_invalidates_sat_when_present() {
    let mut st = IncrementalBvState::new();
    st.persistent_sat = Some(SatSolver::new(0));
    st.term_to_bits
        .insert(TermId::new(1), vec![1, 2, 3, 4, 5, 6, 7, 8]);
    st.encoded_assertions.insert(TermId::new(2), 9);

    st.push();
    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_pushes, 0);
    assert_eq!(st.persistent_sat.as_ref().unwrap().scope_depth(), 1);

    assert!(st.pop());
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_pushes, 0);
    assert!(st.persistent_sat.is_none());
    assert!(st.term_to_bits.is_empty());
    assert!(st.encoded_assertions.is_empty());
}

#[test]
fn incremental_bv_state_sync_tseitin_and_bv_vars_include_scope_selectors() {
    let mut st = IncrementalBvState::new();

    let mut sat = SatSolver::new(0);
    sat.push(); // adds an internal scope selector variable

    let total = sat.total_num_vars() as u32;
    st.persistent_sat = Some(sat);
    st.tseitin_state.next_var = 1;
    st.next_bv_var = 1;

    st.sync_tseitin_next_var();
    assert!(
        st.tseitin_state.next_var > total,
        "expected tseitin next_var > total_num_vars"
    );

    st.sync_next_bv_var();
    assert!(
        st.next_bv_var > total,
        "expected bv next_var > total_num_vars"
    );
}

#[test]
fn incremental_theory_state_push_pop_tracks_pending_before_solver_creation() {
    let mut st = IncrementalTheoryState::new();
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_push, 0);
    assert!(!st.needs_activation_reassert);

    st.push();
    st.push();
    assert_eq!(st.scope_depth, 2);
    assert_eq!(st.pending_push, 2);

    assert!(st.pop());
    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_push, 1);
    assert!(st.needs_activation_reassert);
}

#[test]
fn incremental_theory_state_push_pop_delegates_to_sat_when_present() {
    let mut st = IncrementalTheoryState::new();
    st.persistent_sat = Some(SatSolver::new(0));
    st.lia_persistent_sat = Some(SatSolver::new(0));
    assert!(!st.needs_activation_reassert);

    st.push();
    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_push, 0);
    assert_eq!(st.persistent_sat.as_ref().unwrap().scope_depth(), 1);
    assert_eq!(st.lia_persistent_sat.as_ref().unwrap().scope_depth(), 1);

    assert!(st.pop());
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.persistent_sat.as_ref().unwrap().scope_depth(), 0);
    assert_eq!(st.lia_persistent_sat.as_ref().unwrap().scope_depth(), 0);
    assert!(st.needs_activation_reassert);
}

#[test]
fn incremental_theory_state_pop_clears_theory_lemmas() {
    let mut st = IncrementalTheoryState::new();
    st.push();
    st.theory_lemmas
        .push(TheoryLemma::new(vec![TheoryLit::new(TermId::new(1), true)]));
    st.theory_lemmas.push(TheoryLemma::new(vec![TheoryLit::new(
        TermId::new(2),
        false,
    )]));
    st.original_clause_theory_proofs.push(None);
    st.original_clause_theory_proofs.push(None);

    assert!(st.pop());
    assert!(st.theory_lemmas.is_empty());
    assert!(st.original_clause_theory_proofs.is_empty());
}

#[test]
fn incremental_theory_state_retain_encoded_assertions_keeps_only_active() {
    let mut st = IncrementalTheoryState::new();
    st.encoded_assertions.insert(TermId::new(1), 101);
    st.encoded_assertions.insert(TermId::new(2), 102);
    st.encoded_assertions.insert(TermId::new(3), 103);
    st.assertion_activation_scope.insert(TermId::new(1), 1);
    st.assertion_activation_scope.insert(TermId::new(2), 0);
    st.assertion_activation_scope.insert(TermId::new(3), 2);

    st.retain_encoded_assertions(&[TermId::new(2), TermId::new(4)]);

    assert_eq!(st.encoded_assertions.len(), 1);
    assert!(st.encoded_assertions.contains_key(&TermId::new(2)));
    assert_eq!(st.assertion_activation_scope.len(), 1);
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(2)), Some(&0));
}

#[test]
fn incremental_theory_state_sync_tseitin_next_var_uses_total_num_vars() {
    let mut st = IncrementalTheoryState::new();

    let mut sat = SatSolver::new(0);
    sat.push(); // internal selector, total_num_vars increases
    let total = sat.total_num_vars() as u32;
    assert_eq!(sat.user_num_vars(), 0);
    assert_eq!(sat.scope_depth(), 1);

    st.persistent_sat = Some(sat);
    st.tseitin_state.next_var = 1;

    st.sync_tseitin_next_var();
    assert!(
        st.tseitin_state.next_var > total,
        "expected tseitin next_var > total_num_vars"
    );
}

#[test]
fn incremental_bv_state_reset_clears_all_state() {
    let mut st = IncrementalBvState::new();

    // Modify all fields from their defaults
    // BvBits is just Vec<i32> (CnfLit), so use vec!
    st.term_to_bits
        .insert(TermId::new(1), vec![1, 2, 3, 4, 5, 6, 7, 8]);
    st.next_bv_var = 100;
    st.scope_depth = 3;
    st.pending_pushes = 2;
    st.persistent_sat = Some(SatSolver::new(10));
    st.tseitin_state.next_var = 50;
    st.encoded_assertions.insert(TermId::new(1), 5);
    st.sat_num_vars = 20;
    st.bv_var_offset = Some(10);
    st.predicate_to_var.insert(TermId::new(2), 7);
    st.bool_to_var.insert(TermId::new(3), 8);
    st.linked_equivalence_terms.insert(TermId::new(4));
    st.assertion_activation_scope.insert(TermId::new(9), 2);
    st.emitted_bv_eq_congruence_pairs
        .insert((TermId::new(10), TermId::new(11)));

    // Reset
    st.reset();

    // Verify all fields are reset to initial state
    assert!(st.term_to_bits.is_empty());
    assert_eq!(st.next_bv_var, 1);
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_pushes, 0);
    assert!(st.persistent_sat.is_none());
    assert_eq!(st.tseitin_state.next_var, 1);
    assert!(st.encoded_assertions.is_empty());
    assert!(st.assertion_activation_scope.is_empty());
    assert_eq!(st.sat_num_vars, 0);
    assert!(st.bv_var_offset.is_none());
    assert!(st.emitted_bv_eq_congruence_pairs.is_empty());
    assert!(st.predicate_to_var.is_empty());
    assert!(st.bool_to_var.is_empty());
    assert!(st.linked_equivalence_terms.is_empty());
}

#[test]
fn incremental_bv_state_rebuild_reset_preserves_scope_depth() {
    let mut st = IncrementalBvState::new();
    st.scope_depth = 3;
    st.pending_pushes = 1;
    st.term_to_bits
        .insert(TermId::new(1), vec![1, 2, 3, 4, 5, 6, 7, 8]);
    st.persistent_sat = Some(SatSolver::new(10));
    st.tseitin_state.next_var = 12;
    st.encoded_assertions.insert(TermId::new(2), 4);
    st.bv_var_offset = Some(9);
    st.predicate_to_var.insert(TermId::new(3), 11);
    st.bool_to_var.insert(TermId::new(4), 12);
    st.linked_equivalence_terms.insert(TermId::new(5));
    st.assertion_activation_scope.insert(TermId::new(6), 3);
    st.emitted_bv_eq_congruence_pairs
        .insert((TermId::new(7), TermId::new(8)));

    st.reset_sat_encoding_for_rebuild();

    assert_eq!(st.scope_depth, 3);
    assert_eq!(st.pending_pushes, 3);
    assert!(st.term_to_bits.is_empty());
    assert_eq!(st.next_bv_var, 1);
    assert!(st.persistent_sat.is_none());
    assert_eq!(st.tseitin_state.next_var, 1);
    assert!(st.encoded_assertions.is_empty());
    assert!(st.assertion_activation_scope.is_empty());
    assert_eq!(st.sat_num_vars, 0);
    assert!(st.bv_var_offset.is_none());
    assert!(st.emitted_bv_eq_congruence_pairs.is_empty());
    assert!(st.predicate_to_var.is_empty());
    assert!(st.bool_to_var.is_empty());
    assert!(st.linked_equivalence_terms.is_empty());
    assert!(st.bv_ite_conditions.is_empty());
    assert!(st.delayed_ops.is_empty());
}

#[test]
fn incremental_bv_state_pop_drops_stale_solver_but_keeps_remaining_depth() {
    let mut st = IncrementalBvState::new();
    st.scope_depth = 2;
    st.pending_pushes = 0;
    st.term_to_bits
        .insert(TermId::new(1), vec![1, 2, 3, 4, 5, 6, 7, 8]);
    let mut sat = SatSolver::new(10);
    sat.push();
    sat.push();
    st.persistent_sat = Some(sat);
    st.tseitin_state.next_var = 12;
    st.encoded_assertions.insert(TermId::new(2), 4);
    st.bv_var_offset = Some(9);
    st.predicate_to_var.insert(TermId::new(3), 11);
    st.bool_to_var.insert(TermId::new(4), 12);
    st.linked_equivalence_terms.insert(TermId::new(5));
    st.bv_ite_conditions.insert(TermId::new(6));
    st.assertion_activation_scope.insert(TermId::new(7), 2);
    st.emitted_bv_eq_congruence_pairs
        .insert((TermId::new(8), TermId::new(9)));

    assert!(st.pop());

    assert_eq!(st.scope_depth, 1);
    assert_eq!(st.pending_pushes, 1);
    assert!(st.term_to_bits.is_empty());
    assert_eq!(st.next_bv_var, 1);
    assert!(st.persistent_sat.is_none());
    assert_eq!(st.tseitin_state.next_var, 1);
    assert!(st.encoded_assertions.is_empty());
    assert!(st.assertion_activation_scope.is_empty());
    assert_eq!(st.sat_num_vars, 0);
    assert!(st.bv_var_offset.is_none());
    assert!(st.emitted_bv_eq_congruence_pairs.is_empty());
    assert!(st.predicate_to_var.is_empty());
    assert!(st.bool_to_var.is_empty());
    assert!(st.linked_equivalence_terms.is_empty());
    assert!(st.bv_ite_conditions.is_empty());
    assert!(st.delayed_ops.is_empty());
}

/// Regression test for #2822: pop must invalidate activation scope entries
/// for the popped depth so that re-activation correctly re-adds them.
#[test]
fn incremental_theory_state_pop_invalidates_activation_scopes_at_popped_depth() {
    let mut st = IncrementalTheoryState::new();
    // Simulate assertions activated at various scope levels
    st.assertion_activation_scope.insert(TermId::new(1), 0); // global
    st.assertion_activation_scope.insert(TermId::new(2), 1); // scope 1
    st.assertion_activation_scope.insert(TermId::new(3), 2); // scope 2

    st.scope_depth = 2;

    // Pop from scope 2 to scope 1
    assert!(st.pop());
    assert_eq!(st.scope_depth, 1);
    // Scope 0 and scope 1 entries survive; scope 2 entry is invalidated
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(1)), Some(&0));
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(2)), Some(&1));
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(3)), None);

    // Pop from scope 1 to scope 0
    assert!(st.pop());
    assert_eq!(st.scope_depth, 0);
    // Only scope 0 entry survives
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(1)), Some(&0));
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(2)), None);
}

#[test]
fn incremental_theory_state_reset_clears_all_state() {
    let mut st = IncrementalTheoryState::new();

    // Modify all fields from their defaults
    st.persistent_sat = Some(SatSolver::new(10));
    st.lia_persistent_sat = Some(SatSolver::new(5));
    st.encoded_assertions.insert(TermId::new(1), 7);
    st.assertion_activation_scope.insert(TermId::new(1), 2);
    st.tseitin_state.next_var = 50;
    st.scope_depth = 3;
    st.pending_push = 2;
    st.theory_atoms.push(TermId::new(1));
    st.pre_push_assertions.insert(TermId::new(2));
    st.needs_activation_reassert = true;
    st.theory_conflicts = 42;
    st.theory_propagations = 100;
    st.round_trips = 7;
    st.sat_solve_secs = 1.5;
    st.theory_sync_secs = 0.3;
    st.theory_check_secs = 0.8;

    // Reset
    st.reset();

    // Verify all fields are reset to initial state
    assert!(st.persistent_sat.is_none());
    assert!(st.lia_persistent_sat.is_none());
    assert!(st.encoded_assertions.is_empty());
    assert!(st.assertion_activation_scope.is_empty());
    assert_eq!(st.tseitin_state.next_var, 1);
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_push, 0);
    assert!(st.theory_atoms.is_empty());
    assert!(st.pre_push_assertions.is_empty());
    assert!(!st.needs_activation_reassert);
    assert_eq!(st.theory_conflicts, 0);
    assert_eq!(st.theory_propagations, 0);
    assert_eq!(st.round_trips, 0);
    assert_eq!(st.sat_solve_secs, 0.0);
    assert_eq!(st.theory_sync_secs, 0.0);
    assert_eq!(st.theory_check_secs, 0.0);
}
