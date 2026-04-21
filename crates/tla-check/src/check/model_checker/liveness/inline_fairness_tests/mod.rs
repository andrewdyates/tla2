// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for inline fairness cache: preparation, recording, and provenance matching.

use super::*;
use crate::check::model_checker::CheckResult;
use crate::config::Config;
use crate::liveness::LiveExpr;
use crate::spec_formula::FairnessConstraint;
use crate::state::{ArrayState, State};
use crate::test_support::parse_module;
use crate::Value;
use std::sync::Arc;

mod cache;
mod enabled;
mod provenance;

const INLINE_FAIRNESS_SPEC: &str = r#"
---- MODULE InlineFairness ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Prop == []<>(x = 0)
====
"#;

fn inline_fairness_config() -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Prop".to_string()],
        ..Default::default()
    }
}

fn find_tag(checks: &[LiveExpr], predicate: impl Fn(&LiveExpr) -> Option<u32>) -> u32 {
    checks
        .iter()
        .find_map(predicate)
        .expect("expected inline fairness tag")
}

fn assert_inline_state_result(
    checker: &ModelChecker,
    state_fp: Fingerprint,
    tag: u32,
    expected: bool,
    message: &str,
) {
    let bitmask = checker
        .liveness_cache
        .inline_state_bitmasks
        .get(&state_fp)
        .unwrap_or_else(|| panic!("state bitmask missing for fp={state_fp:?}: {message}"));
    let actual = bitmask & (1u64 << tag) != 0;
    assert_eq!(actual, expected, "{message}");
}

fn assert_inline_action_result(
    checker: &ModelChecker,
    from_fp: Fingerprint,
    to_fp: Fingerprint,
    tag: u32,
    expected: bool,
    message: &str,
) {
    let bitmask = checker
        .liveness_cache
        .inline_action_bitmasks
        .get(&(from_fp, to_fp))
        .unwrap_or_else(|| panic!("action bitmask missing for ({from_fp:?},{to_fp:?}): {message}"));
    let actual = bitmask & (1u64 << tag) != 0;
    assert_eq!(actual, expected, "{message}");
}

fn apply_weak_fairness(checker: &mut ModelChecker) {
    checker.set_fairness(vec![FairnessConstraint::Weak {
        vars: "x".to_string(),
        action: "Next".to_string(),
        action_node: None,
    }]);
}

fn assert_recorded_transition_results(
    checker: &ModelChecker,
    current_fp: Fingerprint,
    next_fp: Fingerprint,
) {
    let enabled_tag = find_tag(
        &checker.liveness_cache.fairness_state_checks,
        |expr| match expr {
            LiveExpr::Enabled { tag, .. } => Some(*tag),
            _ => None,
        },
    );
    let action_tag = find_tag(
        &checker.liveness_cache.fairness_action_checks,
        |expr| match expr {
            LiveExpr::ActionPred { tag, .. } => Some(*tag),
            _ => None,
        },
    );
    let changed_tag = find_tag(
        &checker.liveness_cache.fairness_action_checks,
        |expr| match expr {
            LiveExpr::StateChanged { tag, .. } => Some(*tag),
            _ => None,
        },
    );

    assert_inline_state_result(
        checker,
        current_fp,
        enabled_tag,
        true,
        "ENABLED Next should be true at x=0",
    );
    assert_inline_action_result(
        checker,
        current_fp,
        next_fp,
        action_tag,
        true,
        "Next should satisfy the action predicate on the real successor",
    );
    assert_inline_action_result(
        checker,
        current_fp,
        next_fp,
        changed_tag,
        true,
        "Next should satisfy the state-changed leaf on the real successor",
    );
    assert_inline_action_result(
        checker,
        current_fp,
        current_fp,
        action_tag,
        false,
        "stuttering self-loop should not satisfy Next",
    );
    assert_inline_action_result(
        checker,
        current_fp,
        current_fp,
        changed_tag,
        false,
        "stuttering self-loop should not satisfy state-changed",
    );
}
