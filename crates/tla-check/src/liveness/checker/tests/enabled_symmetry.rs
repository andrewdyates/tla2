// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Symmetry-specific ENABLED regression tests.

use super::*;
use crate::liveness::test_helpers::{make_checker_with_vars, spanned};
use crate::liveness::LiveExpr;
use crate::Value;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tla_core::ast::Expr;

fn mv(name: &str) -> Value {
    Value::try_model_value(name).expect("test model value should intern")
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_uses_symmetry_witness_successors_for_state_change() {
    // Regression for #3224: under symmetry, the representative state's raw
    // fingerprint can differ from the canonical graph fingerprint used by the
    // witness cache. ENABLED<<TRUE>>_x still has to inspect the concrete witness.
    let mut checker = make_checker_with_vars(LiveExpr::Bool(true), &["x", "y"]);
    let registry = checker.ctx.var_registry().clone();

    let current = State::from_pairs([("x", Value::int(0)), ("y", Value::int(1))]);
    let witness = State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]);
    let canon_fp = current.fingerprint();

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

    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));

    assert!(
        checker
            .eval_enabled(
                &checker.ctx.clone(),
                &current,
                &action,
                None,
                true,
                Some(&subscript),
            )
            .expect("symmetry witness ENABLED should evaluate"),
        "concrete symmetry witness changes x even though the reduced edge is a self-loop"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_scans_all_symmetry_witnesses_on_shared_canonical_edge() {
    // Multi-group symmetry can collapse several concrete successors onto the same
    // canonical edge. ENABLED must keep scanning the witness list until it finds
    // one that actually changes the requested subscript.
    let mut checker = make_checker_with_vars(LiveExpr::Bool(true), &["owner", "value"]);
    let registry = checker.ctx.var_registry().clone();

    let current = State::from_pairs([("owner", mv("a1")), ("value", mv("v1"))]);
    let same_owner = State::from_pairs([("owner", mv("a1")), ("value", mv("v2"))]);
    let changed_owner = State::from_pairs([("owner", mv("a2")), ("value", mv("v1"))]);
    let canon_fp = current.fingerprint();

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

    let action = Arc::new(spanned(Expr::Bool(true)));
    let subscript = Arc::new(spanned(Expr::Ident(
        "owner".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )));

    assert!(
        checker
            .eval_enabled(
                &checker.ctx.clone(),
                &current,
                &action,
                None,
                true,
                Some(&subscript),
            )
            .expect("symmetry witness ENABLED should evaluate"),
        "ENABLED must consider later witnesses when multiple concrete successors share one reduced edge"
    );
    assert_ne!(
        current.get("owner"),
        changed_owner.get("owner"),
        "sanity check: the satisfying witness changes the requested subscript"
    );
}
