// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for shortcut reasoning: cyclic-safe, LP reduction, and agglomeration soundness.

use crate::explorer::ExplorationConfig;
use crate::output::Verdict;

use super::super::super::{deadlock_verdict, liveness_verdict, quasi_liveness_verdict};
use super::super::fixtures::{cyclic_safe_net, default_config, linear_deadlock_net};
use super::support::{agglomerable_chain_net, non_free_choice_cycle_net};

#[test]
fn test_quasi_liveness_structural_live_shortcut_with_tight_budget() {
    let config = ExplorationConfig::new(1);
    assert_eq!(
        quasi_liveness_verdict(&cyclic_safe_net(), &config),
        Verdict::True
    );
}

#[test]
fn test_liveness_structural_live_shortcut_with_tight_budget() {
    let config = ExplorationConfig::new(1);
    assert_eq!(liveness_verdict(&cyclic_safe_net(), &config), Verdict::True);
}

#[test]
fn test_liveness_structural_non_live_shortcut_with_tight_budget() {
    let config = ExplorationConfig::new(1);
    assert_eq!(
        liveness_verdict(&linear_deadlock_net(), &config),
        Verdict::False
    );
}

#[test]
fn test_quasi_liveness_does_not_use_structural_non_live_shortcut() {
    let config = default_config();
    assert_eq!(
        quasi_liveness_verdict(&linear_deadlock_net(), &config),
        Verdict::True
    );
}

#[test]
fn test_quasi_liveness_resolves_non_free_choice_net_after_lp_reduction() {
    // LP reduction removes P1 (never constrains T1), making the reduced net
    // free-choice. The structural siphon/trap liveness check then succeeds.
    let config = ExplorationConfig::new(1);
    assert_eq!(
        quasi_liveness_verdict(&non_free_choice_cycle_net(), &config),
        Verdict::True
    );
}

#[test]
fn test_liveness_resolves_non_free_choice_net_after_lp_reduction() {
    // LP reduction removes P1 (never constrains T1), making the reduced net
    // free-choice. The structural siphon/trap liveness check then succeeds.
    let config = ExplorationConfig::new(1);
    assert_eq!(
        liveness_verdict(&non_free_choice_cycle_net(), &config),
        Verdict::True
    );
}

#[test]
fn test_quasi_liveness_not_false_when_agglomeration_removes_transition() {
    let config = default_config();
    // Both t0 and t1 fire once — the system IS quasi-live.
    // Agglomeration removes t0 but it's not dead.
    assert_eq!(
        quasi_liveness_verdict(&agglomerable_chain_net(), &config),
        Verdict::True
    );
}

#[test]
fn test_deadlock_agglomerable_chain_reaches_deadlock() {
    let config = default_config();
    // The chain fires once then reaches deadlock (p_out has a token, nothing consumes it).
    assert_eq!(
        deadlock_verdict(&agglomerable_chain_net(), &config),
        Verdict::True
    );
}
