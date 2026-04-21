// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for SPECIFICATION + PROPERTY liveness combinations:
//! inline cache activation, state count preservation, disk-backed successors,
//! fairness interaction, and diagnostic paths.

use super::*;
use crate::config::Config;
use crate::storage::SuccessorGraph;
use crate::{
    resolve_spec_from_config, set_liveness_disk_bitmask_flush_threshold_override,
    set_use_disk_bitmasks_override, set_use_disk_successors_override, CheckResult, FingerprintSet,
    FingerprintStorage,
};
use std::sync::Arc;
use tla_core::{lower, parse_to_syntax_tree, FileId};

const SPECIFICATION_PROPERTY_SPEC: &str = r#"
---- MODULE SpecPropMinRepro ----
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Live == <>(x = 2)
SafeProp == [](x >= 0)
====
"#;

fn spec_property_config() -> Config {
    Config {
        specification: Some("Spec".to_string()),
        properties: vec!["Live".to_string()],
        ..Default::default()
    }
}

fn spec_safe_property_config() -> Config {
    Config {
        specification: Some("Spec".to_string()),
        properties: vec!["SafeProp".to_string()],
        ..Default::default()
    }
}

/// Fix #3102: SPECIFICATION + PROPERTY now uses inline liveness.
/// The former guard that disabled inline liveness for this combination was
/// a workaround for a Fingerprint(0) placeholder bug in enumerate_successors_array.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn specification_property_enables_inline_liveness_cache() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        specification: unresolved.specification.clone(),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };
    let stuttering_allowed = resolved.stuttering_allowed;
    let fairness = resolved.fairness;

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);
    checker.prepare_inline_liveness_cache();

    assert!(
        checker.inline_liveness_active(),
        "SPECIFICATION + PROPERTY should enable inline liveness now that #3102 is fixed"
    );
    assert!(
        checker.liveness_cache.inline_property_plans.is_empty(),
        "per-property plans should be elided when all leaves are fairness-derived"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn specification_property_preserves_state_count() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        specification: unresolved.specification.clone(),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };
    let stuttering_allowed = resolved.stuttering_allowed;
    let fairness = resolved.fairness;

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "SPECIFICATION + PROPERTY should preserve the 3 reachable states"
            );
        }
        other => panic!("expected success with 3 reachable states, got {other:?}"),
    }
}

/// Part of #3176: the disk-backed BFS successor cache must preserve liveness
/// results when the checker runs the same SPECIFICATION + PROPERTY workload.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn specification_property_auto_selects_disk_successors_for_disk_fingerprint_storage() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        specification: unresolved.specification.clone(),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };
    let stuttering_allowed = resolved.stuttering_allowed;
    let fairness = resolved.fairness;
    let disk_dir = tempfile::tempdir().expect("temp dir for disk fingerprint storage");
    let storage = FingerprintStorage::disk(16, disk_dir.path())
        .expect("disk fingerprint storage should initialize");

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);
    checker.set_fingerprint_storage(Arc::new(storage) as Arc<dyn FingerprintSet>);
    assert!(
        checker.liveness_cache.successors.is_disk(),
        "disk-backed fingerprint storage should auto-select the disk successor graph",
    );
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "disk-backed fingerprint storage should preserve the 3 reachable states"
            );
        }
        other => panic!("expected success with 3 reachable states, got {other:?}"),
    }
    assert!(
        checker.liveness_cache.successors.is_disk(),
        "disk-backed fingerprint storage should keep the disk successor graph installed",
    );
}

/// Part of #3176: an explicit false override must remain authoritative even
/// when the checker installs disk-backed fingerprint storage.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn specification_property_override_false_keeps_in_memory_successors() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        specification: unresolved.specification.clone(),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };
    let stuttering_allowed = resolved.stuttering_allowed;
    let fairness = resolved.fairness;
    let _disk_successors = set_use_disk_successors_override(false);
    let disk_dir = tempfile::tempdir().expect("temp dir for disk fingerprint storage");
    let storage = FingerprintStorage::disk(16, disk_dir.path())
        .expect("disk fingerprint storage should initialize");

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);
    checker.set_fingerprint_storage(Arc::new(storage) as Arc<dyn FingerprintSet>);
    assert!(
        !checker.liveness_cache.successors.is_disk(),
        "explicit false override should keep the in-memory successor graph",
    );
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "explicit false override should still preserve the 3 reachable states"
            );
        }
        other => panic!("expected success with 3 reachable states, got {other:?}"),
    }
}

/// Part of #3176: the disk-backed BFS successor cache must preserve liveness
/// results when the checker runs the same SPECIFICATION + PROPERTY workload.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn specification_property_preserves_state_count_with_disk_successors() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        specification: unresolved.specification.clone(),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };
    let stuttering_allowed = resolved.stuttering_allowed;
    let fairness = resolved.fairness;

    let mut checker = ModelChecker::new(&module, &config);
    checker.liveness_cache.successors =
        SuccessorGraph::disk().expect("disk successor graph should initialize");
    assert!(
        checker.liveness_cache.successors.is_disk(),
        "test setup should install the disk-backed successor graph",
    );
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "disk-backed successor cache should preserve the 3 reachable states"
            );
        }
        other => panic!("expected success with 3 reachable states, got {other:?}"),
    }
    assert!(
        checker.liveness_cache.successors.is_disk(),
        "disk-backed successor cache should remain installed after check() restores the cache",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn specification_state_property_preserves_state_count() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_safe_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        specification: unresolved.specification.clone(),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };
    let stuttering_allowed = resolved.stuttering_allowed;
    let fairness = resolved.fairness;

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "SPECIFICATION + state-level PROPERTY should preserve the 3 reachable states"
            );
        }
        other => panic!("expected success with 3 reachable states, got {other:?}"),
    }
}

/// Test inline liveness WITH fairness + PROPERTY enabled (no SPECIFICATION guard).
///
/// Uses INIT/NEXT config with explicit fairness and PROPERTY. This exercises the
/// inline liveness code path (record_inline_liveness_results, ENABLED evaluation,
/// cache clearing) that the #3102 guard blocks for SPECIFICATION+PROPERTY configs.
/// If this test passes, the cache isolation improvements
/// (`clear_for_eval_scope_boundary()` + `invalidate_state_identity_tracking()`)
/// are sufficient and the guard can be removed.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn inline_liveness_with_fairness_preserves_state_count() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };
    let stuttering_allowed = resolved.stuttering_allowed;
    let fairness = resolved.fairness;

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(fairness);
    checker.set_stuttering_allowed(stuttering_allowed);

    checker.prepare_inline_liveness_cache();
    assert!(
        checker.inline_liveness_active(),
        "INIT/NEXT + PROPERTY + fairness should enable inline liveness"
    );

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "inline liveness with fairness should preserve the 3 reachable states"
            );
        }
        other => panic!("expected success with 3 reachable states, got {other:?}"),
    }
}

/// Diagnostic test: full-state path WITHOUT inline liveness -> should produce 3 states.
/// If this fails, the full-state path itself is broken (not an inline liveness issue).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn full_state_path_without_liveness_preserves_state_count() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);

    checker.prepare_inline_liveness_cache();
    assert!(
        !checker.inline_liveness_active(),
        "no properties -> inline liveness should be inactive"
    );

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "full-state path without liveness should find all 3 reachable states"
            );
        }
        other => panic!("expected success with 3 states, got {other:?}"),
    }
}

/// Diagnostic test: inline property plan without fairness.
/// If this fails, the inline property evaluation (not ENABLED) causes corruption.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn inline_property_without_fairness_preserves_state_count() {
    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "inline property without fairness should find all 3 states"
            );
        }
        CheckResult::LivenessViolation { stats, .. } => {
            assert_eq!(
                stats.states_found, 3,
                "liveness violation is expected without fairness, but state count must be 3"
            );
        }
        other => panic!("expected success or liveness violation with 3 states, got {other:?}"),
    }
}

/// Part of #3177: property-scoped inline plans must use the disk-backed bitmask
/// backend too, otherwise no-fairness PROPERTY runs can still accumulate
/// O(states/transitions) in RAM even when disk bitmasks are enabled.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn inline_property_without_fairness_uses_disk_bitmasks_and_preserves_state_count() {
    let _disk_bitmasks = set_use_disk_bitmasks_override(true);
    let _flush_threshold = set_liveness_disk_bitmask_flush_threshold_override(Some(1));

    let tree = parse_to_syntax_tree(SPECIFICATION_PROPERTY_SPEC);
    let module = lower(FileId(0), &tree).module.expect("lowered module");
    let unresolved = spec_property_config();
    let resolved =
        resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: unresolved.properties.clone(),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.prepare_inline_liveness_cache();

    let plan = checker
        .liveness_cache
        .inline_property_plans
        .first()
        .expect("no-fairness PROPERTY should build an inline property plan");
    assert!(
        plan.state_bitmasks.is_disk(),
        "state bitmasks should use the disk backend for inline property plans",
    );
    assert!(
        plan.action_bitmasks.is_disk(),
        "action bitmasks should use the disk backend for inline property plans",
    );

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "disk-backed inline property recording should find all 3 states"
            );
        }
        CheckResult::LivenessViolation { stats, .. } => {
            assert_eq!(
                stats.states_found, 3,
                "disk-backed inline property recording may still report a liveness violation, but state count must be 3"
            );
        }
        other => panic!("expected success or liveness violation with 3 states, got {other:?}"),
    }
}
