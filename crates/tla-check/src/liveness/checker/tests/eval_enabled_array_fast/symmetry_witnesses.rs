// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn mv(name: &str) -> Value {
    Value::try_model_value(name).expect("test model value should intern")
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_from_fps_fallback_uses_symmetry_witnesses() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;
    use rustc_hash::FxHashMap;

    // A reduced self-loop can still hide a concrete non-stuttering witness under
    // symmetry. On a subscript cache miss, the fingerprint-only fast path must
    // fall back through successor_states_for_enabled(from_fp), which needs to
    // consult succ_witnesses before the state_successor_* maps.
    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: true,
        subscript: Some(subscript),
        tag: 22,
    };

    let current = State::from_pairs([("x", Value::int(0)), ("y", Value::int(1))]);
    let witness = State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]);
    let canon_fp = current.fingerprint();
    let mut checker = crate::liveness::test_helpers::make_checker_with_vars(
        crate::liveness::LiveExpr::Bool(true),
        &["x", "y"],
    );
    let registry = checker.ctx.var_registry().clone();

    let mut fp_map = FxHashMap::default();
    fp_map.insert(current.fingerprint(), canon_fp);
    fp_map.insert(witness.fingerprint(), canon_fp);

    let mut succ_witnesses = crate::SuccessorWitnessMap::default();
    succ_witnesses.insert(
        canon_fp,
        vec![(
            canon_fp,
            crate::ArrayState::from_state_with_fp(&witness, &registry),
        )],
    );
    checker.set_successor_maps(Arc::new(fp_map), Some(Arc::new(succ_witnesses)));

    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();

    let result =
        checker.eval_enabled_array_fast_from_fps(&info, &current, canon_fp, &[canon_fp], &registry);
    assert!(
        result.unwrap(),
        "cache miss fallback should use symmetry witnesses, not treat the reduced self-loop as stuttering"
    );

    crate::liveness::checker::subscript_cache::clear_subscript_value_cache();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_from_fps_self_loop_uses_symmetry_witnesses_without_subscript() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;
    use rustc_hash::FxHashMap;

    // Without a subscript, the fingerprint-only fast path used to treat a reduced
    // self-loop as stuttering and skip it entirely. Under symmetry, a concrete
    // witness may still change state even when the canonical successor fingerprint
    // equals the source fingerprint.
    let action = Arc::new(spanned(Expr::Bool(true)));
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: true,
        subscript: None,
        tag: 23,
    };

    let current = State::from_pairs([("x", Value::int(0)), ("y", Value::int(1))]);
    let witness = State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]);
    let canon_fp = current.fingerprint();
    let mut checker = crate::liveness::test_helpers::make_checker_with_vars(
        crate::liveness::LiveExpr::Bool(true),
        &["x", "y"],
    );
    let registry = checker.ctx.var_registry().clone();

    let mut fp_map = FxHashMap::default();
    fp_map.insert(current.fingerprint(), canon_fp);
    fp_map.insert(witness.fingerprint(), canon_fp);

    let mut succ_witnesses = crate::SuccessorWitnessMap::default();
    succ_witnesses.insert(
        canon_fp,
        vec![(
            canon_fp,
            crate::ArrayState::from_state_with_fp(&witness, &registry),
        )],
    );
    checker.set_successor_maps(Arc::new(fp_map), Some(Arc::new(succ_witnesses)));

    let result =
        checker.eval_enabled_array_fast_from_fps(&info, &current, canon_fp, &[canon_fp], &registry);
    assert!(
        result.unwrap(),
        "reduced self-loop should fall back to concrete symmetry witnesses instead of assuming stuttering"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_array_fast_from_fps_scans_all_witnesses_on_shared_canonical_edge() {
    use crate::liveness::checker::ea_precompute_enabled::EnabledInfo;
    use rustc_hash::FxHashMap;

    // Regression for #3224 prover audit: multi-group symmetry can yield several
    // concrete witnesses for one reduced self-loop. The fast path must not stop
    // at the first witness when a later witness changes the requested subscript.
    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "owner".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let info = EnabledInfo {
        action,
        bindings: None,
        require_state_change: true,
        subscript: Some(subscript),
        tag: 24,
    };

    let current = State::from_pairs([("owner", mv("a1")), ("value", mv("v1"))]);
    let same_owner = State::from_pairs([("owner", mv("a1")), ("value", mv("v2"))]);
    let changed_owner = State::from_pairs([("owner", mv("a2")), ("value", mv("v1"))]);
    let canon_fp = current.fingerprint();
    let mut checker = crate::liveness::test_helpers::make_checker_with_vars(
        crate::liveness::LiveExpr::Bool(true),
        &["owner", "value"],
    );
    let registry = checker.ctx.var_registry().clone();

    let mut fp_map = FxHashMap::default();
    fp_map.insert(current.fingerprint(), canon_fp);
    fp_map.insert(same_owner.fingerprint(), canon_fp);
    fp_map.insert(changed_owner.fingerprint(), canon_fp);

    let mut succ_witnesses = crate::SuccessorWitnessMap::default();
    succ_witnesses.insert(
        canon_fp,
        vec![
            (
                canon_fp,
                crate::ArrayState::from_state_with_fp(&same_owner, &registry),
            ),
            (
                canon_fp,
                crate::ArrayState::from_state_with_fp(&changed_owner, &registry),
            ),
        ],
    );
    checker.set_successor_maps(Arc::new(fp_map), Some(Arc::new(succ_witnesses)));

    let result =
        checker.eval_enabled_array_fast_from_fps(&info, &current, canon_fp, &[canon_fp], &registry);
    assert!(
        result.unwrap(),
        "fast ENABLED lookup must scan all witnesses on a shared canonical edge"
    );
}
