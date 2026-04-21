// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Streaming preadmit and constrained streaming eligibility tests.

use super::helpers::{build_array_transport_via_new, ForceBatchEnvGuard};
use crate::parallel::FxDashMap;
use crate::var_index::VarRegistry;
use std::sync::Arc;
use tla_core::span::Spanned;

#[test]
fn test_streaming_preadmit_enabled_for_fp_only_unbounded_transport() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let transport = build_array_transport_via_new(0, 1, registry);

    assert!(
        transport.can_streaming_preadmit(),
        "fp-only transports without a max-states limit should pre-admit streaming diffs by default"
    );
}

#[test]
fn test_streaming_preadmit_disabled_for_full_state_or_state_limit() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));

    let mut full_state_transport = build_array_transport_via_new(0, 1, Arc::clone(&registry));
    full_state_transport.store_full_states = true;
    assert!(
        !full_state_transport.can_streaming_preadmit(),
        "full-state transports must stay on the deferred reducer path"
    );

    let mut limited_transport = build_array_transport_via_new(0, 1, registry);
    limited_transport.max_states_limit = Some(1);
    assert!(
        !limited_transport.can_streaming_preadmit(),
        "state-limited runs must not pre-admit because insert_checked cannot be rolled back"
    );
}

#[test]
fn test_constrained_streaming_eligible_with_state_constraints() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 1, registry);
    transport.config.constraints.push("Bound".to_string());

    assert!(
        transport.constrained_streaming_eligible(),
        "state-constrained specs without first-slice exclusions should use constrained streaming"
    );
}

#[test]
fn test_constrained_streaming_eligible_with_action_constraints() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 1, registry);
    transport
        .config
        .action_constraints
        .push("StepBound".to_string());

    assert!(
        transport.constrained_streaming_eligible(),
        "action-constrained specs without first-slice exclusions should use constrained streaming"
    );
}

#[test]
fn test_constrained_streaming_disabled_without_constraints() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let transport = build_array_transport_via_new(0, 1, registry);

    assert!(
        !transport.constrained_streaming_eligible(),
        "unconstrained specs should stay on the unconstrained streaming or batch paths"
    );
}

#[test]
fn test_constrained_streaming_disabled_with_view_or_symmetry() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));

    let mut view_transport = build_array_transport_via_new(0, 1, Arc::clone(&registry));
    view_transport.config.constraints.push("Bound".to_string());
    view_transport.config.view = Some("View".to_string());
    assert!(
        !view_transport.constrained_streaming_eligible(),
        "VIEW specs must stay on the constrained full-state path"
    );

    let mut symmetry_transport = build_array_transport_via_new(0, 1, registry);
    symmetry_transport
        .config
        .constraints
        .push("Bound".to_string());
    symmetry_transport.config.symmetry = Some("Sym".to_string());
    assert!(
        !symmetry_transport.constrained_streaming_eligible(),
        "symmetry specs must stay on the constrained full-state path"
    );
}

#[test]
fn test_constrained_streaming_disabled_with_implied_actions() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut eval_transport = build_array_transport_via_new(0, 1, registry);
    eval_transport.config.constraints.push("Bound".to_string());
    eval_transport.eval_implied_actions = Arc::new(vec![(
        "Prop".to_string(),
        Spanned::dummy(tla_core::ast::Expr::Bool(true)),
    )]);

    assert!(
        !eval_transport.constrained_streaming_eligible(),
        "eval implied-action checks must stay on the batch constrained full-state path"
    );
}

#[test]
fn test_constrained_streaming_disabled_with_liveness_caches() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut successor_cache_transport = build_array_transport_via_new(0, 1, Arc::clone(&registry));
    successor_cache_transport
        .config
        .constraints
        .push("Bound".to_string());
    successor_cache_transport.successors_cache = Some(Arc::new(FxDashMap::default()));

    assert!(
        !successor_cache_transport.constrained_streaming_eligible(),
        "liveness successor caching must stay on the batch constrained full-state path"
    );

    let mut witness_cache_transport = build_array_transport_via_new(0, 1, registry);
    witness_cache_transport
        .config
        .constraints
        .push("Bound".to_string());
    witness_cache_transport.successor_witnesses_cache =
        Some(Arc::new(crate::parallel::SuccessorWitnessDashMap::default()));

    assert!(
        !witness_cache_transport.constrained_streaming_eligible(),
        "liveness witness caching must stay on the batch constrained full-state path"
    );
}

#[test]
fn test_constrained_streaming_disabled_with_force_batch_env() {
    let _guard = ForceBatchEnvGuard::set(Some("1"));
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 1, registry);
    transport.config.constraints.push("Bound".to_string());

    assert!(
        !transport.constrained_streaming_eligible(),
        "TLA2_FORCE_BATCH must disable constrained streaming for A/B benchmarking"
    );
}
