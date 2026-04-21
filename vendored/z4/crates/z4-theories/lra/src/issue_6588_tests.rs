// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use z4_core::term::TermStore;
use z4_core::Sort;

#[derive(Clone, Copy, Debug)]
enum CompoundDirtyResetKind {
    Pop,
    SoftReset,
}

fn assert_compound_source_keys_reseeded(reset_kind: CompoundDirtyResetKind) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    let slack = *solver
        .atom_index
        .keys()
        .next()
        .expect("compound atom must register a slack-keyed atom_index entry");
    assert_ne!(
        slack, x_var,
        "compound atom slack must differ from direct source vars"
    );
    assert_ne!(
        slack, y_var,
        "compound atom slack must differ from direct source vars"
    );
    for source_var in [x_var, y_var] {
        assert!(
            solver.compound_use_index.contains_key(&source_var),
            "compound wakeups must be keyed by source var {source_var}"
        );
        assert!(
            !solver.atom_index.contains_key(&source_var),
            "compound source var {source_var} must stay out of atom_index so the reseed test exercises compound_use_index"
        );
    }
    assert!(
        solver.compound_use_index.contains_key(&slack),
        "compound wakeups must also be keyed by the shared slack var {slack}"
    );

    match reset_kind {
        CompoundDirtyResetKind::Pop => {
            solver.push();
            solver.assert_literal(sum_le_3, true);
            solver.propagation_dirty_vars.clear();
            assert!(
                solver.propagation_dirty_vars.is_empty(),
                "test setup must clear dirty vars before pop() reseeding"
            );
            solver.pop();
        }
        CompoundDirtyResetKind::SoftReset => {
            solver.assert_literal(sum_le_3, true);
            solver.propagation_dirty_vars.clear();
            assert!(
                solver.propagation_dirty_vars.is_empty(),
                "test setup must clear dirty vars before soft_reset() reseeding"
            );
            solver.soft_reset();
        }
    }
    for source_var in [x_var, y_var] {
        assert!(
            solver.compound_use_index.contains_key(&source_var),
            "{reset_kind:?} must preserve compound wakeups for source var {source_var}"
        );
        assert!(
            solver.propagation_dirty_vars.contains(&source_var),
            "{reset_kind:?} must re-add compound source var {source_var} to propagation_dirty_vars"
        );
    }
    assert!(
        solver.propagation_dirty_vars.contains(&slack),
        "{reset_kind:?} must also re-add the shared slack var {slack} to propagation_dirty_vars"
    );
}

#[test]
fn test_soft_reset_warm_preserves_dirty_vars_and_reseeds_compound_sources_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    let phantom_dirty = x_var.max(y_var) + 1024;
    solver.propagation_dirty_vars.insert(phantom_dirty);

    solver.soft_reset_warm();

    assert!(
        solver.propagation_dirty_vars.contains(&phantom_dirty),
        "soft_reset_warm() must preserve already-dirty vars so warm iterations do not lose pending compound work"
    );
    assert!(
        solver.propagation_dirty_vars.contains(&x_var)
            && solver.propagation_dirty_vars.contains(&y_var),
        "soft_reset_warm() must also reseed compound source vars for wakeups"
    );
}

#[test]
fn test_register_atom_seeds_compound_wake_queue_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    let dirty: Vec<u32> = solver.propagation_dirty_vars.iter().copied().collect();

    assert!(
        dirty.contains(&x_var) && dirty.contains(&y_var),
        "compound registration must seed source vars into propagation_dirty_vars"
    );

    let queued = solver.queue_compound_propagations_for_dirty_vars(&dirty);
    assert!(
        solver.last_compound_wake_dirty_hits > 0,
        "compound wake queue must observe at least one dirty source key"
    );
    assert!(
        solver.last_compound_wake_candidates > 0,
        "compound wake queue must surface at least one compound candidate"
    );
    assert_eq!(
        queued, solver.last_compound_propagations_queued,
        "helper should update the queued count consistently"
    );
}

#[test]
fn test_same_variable_slack_propagation_uses_direct_bound_reason_when_interval_is_empty_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_1);
    solver.register_atom(sum_le_3);

    let slack_vars: Vec<u32> = solver
        .expr_to_slack
        .values()
        .map(|(slack, _)| *slack)
        .collect();
    assert_eq!(
        slack_vars.len(),
        1,
        "same-expression additive atoms should share one slack var"
    );

    solver.assert_literal(sum_le_1, true);
    solver
        .process_check_atoms_bcp(false)
        .expect("processing the stronger asserted atom should succeed");

    let pending = solver
        .pending_propagations
        .iter()
        .find(|pending| pending.propagation.literal == TheoryLit::new(sum_le_3, true))
        .unwrap_or_else(|| {
            panic!(
                "asserting stronger slack atom should eagerly propagate weaker same-expression atom, got {:?}",
                solver.pending_propagations
            )
        });
    assert_eq!(
        pending.propagation.reason,
        vec![TheoryLit::new(sum_le_1, true)],
        "when source-variable interval reconstruction is empty, eager slack propagation must fall back to the asserted direct slack bound reason"
    );

    let propagations = solver.propagate();
    assert!(
        propagations
            .iter()
            .any(|prop| prop.literal == TheoryLit::new(sum_le_3, true)
                && prop.reason == vec![TheoryLit::new(sum_le_1, true)]),
        "propagate() should preserve the direct slack-bound reason for the weaker additive atom, got {propagations:?}"
    );
}

#[test]
fn test_multi_reason_assert_bounds_queue_compound_candidate_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let rx1 = terms.mk_var("rx1", Sort::Bool);
    let rx2 = terms.mk_var("rx2", Sort::Bool);
    let ry1 = terms.mk_var("ry1", Sort::Bool);
    let ry2 = terms.mk_var("ry2", Sort::Bool);
    let one = BigRational::from(BigInt::from(1));
    let two = BigRational::from(BigInt::from(2));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);
    solver.propagation_dirty_vars.clear();
    solver.pending_propagations.clear();

    let x_expr = solver.parse_linear_expr(x);
    let y_expr = solver.parse_linear_expr(y);
    let x_reasons = [(rx1, true), (rx2, false)];
    let y_reasons = [(ry1, true), (ry2, false)];
    solver.assert_bound_with_reasons(x_expr, one, BoundType::Upper, false, &x_reasons, None);
    solver.assert_bound_with_reasons(y_expr, two, BoundType::Upper, false, &y_reasons, None);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    let dirty: Vec<u32> = solver.propagation_dirty_vars.iter().copied().collect();
    assert!(
        dirty.contains(&x_var) && dirty.contains(&y_var),
        "multi-reason bound assertions must still mark the source vars dirty"
    );

    let queued = solver.queue_compound_propagations_for_dirty_vars(&dirty);
    assert!(
        solver.last_compound_wake_dirty_hits > 0,
        "multi-reason bound assertions must still reach the compound wake queue"
    );
    assert!(
        solver.last_compound_wake_candidates > 0,
        "multi-reason bound assertions must still surface compound candidates"
    );
    assert!(
        queued > 0,
        "x <= 1 and y <= 2 should queue the registered compound atom x + y <= 3 even with multi-reason bounds"
    );
    assert!(
        solver
            .pending_propagations
            .iter()
            .any(|pending| pending.propagation.literal == TheoryLit::new(sum_le_3, true)),
        "queued compound propagation should target the registered additive atom"
    );
}

#[test]
fn test_direct_bound_propagation_skips_slack_without_interval_reconstruction_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three_value = BigRational::from(BigInt::from(3));
    let three = terms.mk_rational(three_value.clone());
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let sum_expr = solver.parse_linear_expr(sum);
    solver.assert_bound_with_reasons(
        sum_expr,
        three_value,
        BoundType::Upper,
        false,
        &[(sum_le_3, true)],
        None,
    );

    let slack = *solver
        .expr_to_slack
        .values()
        .next()
        .map(|(slack, _)| slack)
        .expect("compound atom should create exactly one slack variable");
    solver.pending_propagations.clear();
    solver.propagated_atoms.clear();
    solver.atom_cache.clear();

    solver.compute_direct_bound_propagations_for_var(slack);

    assert!(
        solver.pending_propagations.is_empty(),
        "slack propagation must skip eager reasons when interval reconstruction is unavailable"
    );
}

#[test]
fn test_reregister_atom_reseeds_compound_wake_queue_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let atom_index_total_before: usize = solver.atom_index.values().map(Vec::len).sum();
    let compound_use_total_before: usize = solver.compound_use_index.values().map(Vec::len).sum();
    solver.propagation_dirty_vars.clear();

    solver.register_atom(sum_le_3);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    let dirty: Vec<u32> = solver.propagation_dirty_vars.iter().copied().collect();

    assert!(
        dirty.contains(&x_var) && dirty.contains(&y_var),
        "re-registering a compound atom must reseed source vars into propagation_dirty_vars"
    );
    let queued = solver.queue_compound_propagations_for_dirty_vars(&dirty);
    assert!(
        solver.last_compound_wake_dirty_hits > 0,
        "re-registering a compound atom must make the wake queue see dirty compound keys"
    );
    assert!(
        solver.last_compound_wake_candidates > 0,
        "re-registering a compound atom must surface compound wake candidates"
    );
    assert_eq!(
        atom_index_total_before,
        solver.atom_index.values().map(Vec::len).sum(),
        "re-registering a compound atom must not grow atom_index"
    );
    assert_eq!(
        compound_use_total_before,
        solver.compound_use_index.values().map(Vec::len).sum(),
        "re-registering a compound atom must not grow compound_use_index"
    );
    assert_eq!(
        queued, solver.last_compound_propagations_queued,
        "helper should update the queued count consistently"
    );
}

#[test]
fn test_propagate_preserves_compound_dirty_wake_keys_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    let y_var = *solver.term_to_var.get(&y).expect("y must be interned");
    let pre_dirty: Vec<u32> = solver.propagation_dirty_vars.iter().copied().collect();
    assert!(
        pre_dirty.contains(&x_var) && pre_dirty.contains(&y_var),
        "compound registration must seed source vars before propagate()"
    );

    let _ = solver.propagate();

    assert!(
        solver.propagation_dirty_vars.contains(&x_var)
            && solver.propagation_dirty_vars.contains(&y_var),
        "propagate() must preserve compound wake keys for the next post-simplex check"
    );

    let dirty: Vec<u32> = solver.propagation_dirty_vars.iter().copied().collect();
    let queued = solver.queue_compound_propagations_for_dirty_vars(&dirty);
    assert!(
        solver.last_compound_wake_dirty_hits > 0,
        "propagate() must leave compound wake hits visible to the next queue pass"
    );
    assert!(
        solver.last_compound_wake_candidates > 0,
        "propagate() must leave compound wake candidates visible to the next queue pass"
    );
    assert_eq!(
        queued, solver.last_compound_propagations_queued,
        "helper should update the queued count consistently"
    );
}

#[test]
fn test_unsat_check_preserves_last_compound_wake_stats_7965() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_3 = terms.mk_le(sum, three);
    let x_ge_10 = terms.mk_ge(x, ten);
    let x_le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_3);
    solver.assert_literal(sum_le_3, true);

    let sat = solver.check();
    assert!(
        matches!(sat, TheoryResult::Sat),
        "expected a satisfiable warm-up check before the unsat regression, got {sat:?}"
    );

    let wake_hits = solver.last_compound_wake_dirty_hits;
    let wake_candidates = solver.last_compound_wake_candidates;
    assert!(
        wake_hits > 0 || wake_candidates > 0,
        "warm-up check must record compound wake activity before the unsat regression"
    );

    solver.assert_literal(x_ge_10, true);
    solver.assert_literal(x_le_5, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "contradictory direct bounds should still be UNSAT, got {result:?}"
    );
    assert_eq!(
        solver.last_compound_wake_dirty_hits, wake_hits,
        "non-Sat checks must not zero the last observed compound wake hit counter"
    );
    assert_eq!(
        solver.last_compound_wake_candidates, wake_candidates,
        "non-Sat checks must not zero the last observed compound wake candidate counter"
    );
}

#[test]
fn test_pop_reseeds_compound_source_dirty_vars_6588() {
    assert_compound_source_keys_reseeded(CompoundDirtyResetKind::Pop);
}

#[test]
fn test_soft_reset_reseeds_compound_source_dirty_vars_6588() {
    assert_compound_source_keys_reseeded(CompoundDirtyResetKind::SoftReset);
}
