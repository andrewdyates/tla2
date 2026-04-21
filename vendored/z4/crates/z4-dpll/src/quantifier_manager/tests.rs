// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::incremental_state::IncrementalSubsystem;

#[test]
fn test_quantifier_manager_creation() {
    let qm = QuantifierManager::new();
    assert_eq!(qm.round(), 0);
    assert!(!qm.has_deferred());
}

#[test]
fn test_quantifier_manager_round_increments() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    // Empty assertions - just verify round counter
    let _result = qm.run_ematching_round(&mut terms, &[], None);
    assert_eq!(qm.round(), 1);

    let _result = qm.run_ematching_round(&mut terms, &[], None);
    assert_eq!(qm.round(), 2);
}

#[test]
fn test_generation_tracker_persists() {
    use num_bigint::BigInt;
    use z4_core::term::Symbol;
    use z4_core::Sort;

    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    // Create: forall x. P(x)
    // We use a simple pattern: forall x. P(x) which matches P(c) for any ground c
    let x = terms.mk_var("x", Sort::Int);
    let p_sym = Symbol::named("P");
    let px = terms.mk_app(p_sym.clone(), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);

    // Create ground term P(1)
    let c1 = terms.mk_int(BigInt::from(1));
    let p1 = terms.mk_app(p_sym, vec![c1], Sort::Bool);

    // First round
    let assertions = vec![forall, p1];
    let _result1 = qm.run_ematching_round(&mut terms, &assertions, None);

    // E-matching on `forall x. P(x)` with pattern P(x) should instantiate P(1)
    // However, the instantiation is the body P(1), and P(1) is already in assertions
    // The key thing is that the tracker's round counter advances
    assert_eq!(qm.round(), 1);

    // Second round with same assertions
    let _result2 = qm.run_ematching_round(&mut terms, &assertions, None);

    // Generation tracker should persist - round counter should advance
    assert_eq!(qm.round(), 2);

    // Verify the tracker's current_round reflects multiple rounds
    assert_eq!(qm.generation_tracker().current_round(), 2);
}

#[test]
fn test_clear_resets_state() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    let _result = qm.run_ematching_round(&mut terms, &[], None);
    assert_eq!(qm.round(), 1);

    qm.clear();

    assert_eq!(qm.round(), 0);
    assert!(!qm.has_deferred());
}

#[test]
fn test_push_pop_restores_state() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    // Run a round at the base scope
    let _result = qm.run_ematching_round(&mut terms, &[], None);
    assert_eq!(qm.round(), 1);

    // Push and run another round in inner scope
    qm.push();
    let _result = qm.run_ematching_round(&mut terms, &[], None);
    assert_eq!(qm.round(), 2);

    // Pop should restore the round counter and generation tracker
    qm.pop();
    assert_eq!(qm.round(), 1);
}

#[test]
fn test_reset_clears_scope_stack() {
    let mut qm = QuantifierManager::new();

    qm.push();
    qm.push();
    qm.reset();

    assert_eq!(qm.round(), 0);
    assert!(!qm.has_deferred());
    // Pop after reset should be a no-op (empty stack)
    qm.pop();
    assert_eq!(qm.round(), 0);
}
