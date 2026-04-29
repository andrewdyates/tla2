// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for automatic symmetry detection from model value sets.

use super::*;
use std::ffi::OsString;
use std::sync::Mutex;

static AUTO_SYMMETRY_ENV_LOCK: Mutex<()> = Mutex::new(());

struct AutoSymmetryEnvGuard {
    previous: Option<OsString>,
}

impl AutoSymmetryEnvGuard {
    fn set(value: Option<&str>) -> Self {
        let previous = std::env::var_os("TLA2_AUTO_SYMMETRY");
        match value {
            Some(value) => std::env::set_var("TLA2_AUTO_SYMMETRY", value),
            None => std::env::remove_var("TLA2_AUTO_SYMMETRY"),
        }
        Self { previous }
    }
}

impl Drop for AutoSymmetryEnvGuard {
    fn drop(&mut self) {
        match self.previous.as_ref() {
            Some(value) => std::env::set_var("TLA2_AUTO_SYMMETRY", value),
            None => std::env::remove_var("TLA2_AUTO_SYMMETRY"),
        }
    }
}

/// Verify that auto-detection produces the same state count as explicit SYMMETRY.
///
/// This test runs twice: once with explicit SYMMETRY config, once with
/// TLA2_AUTO_SYMMETRY=1 and no SYMMETRY config. Both should produce the
/// same canonical state count.
#[cfg_attr(test, ntest::timeout(15000))]
#[test]
fn test_auto_detect_matches_explicit_symmetry() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let _env_lock = AUTO_SYMMETRY_ENV_LOCK
        .lock()
        .expect("auto symmetry env lock must not be poisoned");

    let src = r#"
---- MODULE AutoDetectTest ----
EXTENDS TLC
CONSTANT Procs
VARIABLE active

Init == active \in Procs
Next == active' \in Procs /\ active' /= active

Sym == Permutations(Procs)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config WITH explicit symmetry.
    let mut config_explicit = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config_explicit.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
            "p3".to_string(),
        ]),
    );

    let mut checker_explicit = ModelChecker::new(&module, &config_explicit);
    checker_explicit.set_deadlock_check(false);
    let result_explicit = checker_explicit.check();

    let states_explicit = match result_explicit {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success with explicit symmetry, got {:?}", other),
    };

    // Config WITHOUT explicit symmetry, but with TLA2_AUTO_SYMMETRY=1.
    let config_auto = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constants: config_explicit.constants.clone(),
        constants_order: config_explicit.constants_order.clone(),
        // No symmetry field!
        ..Default::default()
    };

    let _env = AutoSymmetryEnvGuard::set(Some("1"));
    let mut checker_auto = ModelChecker::new(&module, &config_auto);
    checker_auto.set_deadlock_check(false);
    let result_auto = checker_auto.check();

    let (states_auto, sym_stats) = match result_auto {
        CheckResult::Success(stats) => {
            let sym = stats.symmetry_reduction.clone();
            (stats.states_found, sym)
        }
        other => panic!("Expected Success with auto symmetry, got {:?}", other),
    };

    // Both should produce the same state count.
    assert_eq!(
        states_explicit, states_auto,
        "auto-detected symmetry should produce same state count as explicit: explicit={}, auto={}",
        states_explicit, states_auto
    );

    // Auto-detected flag should be set.
    assert!(
        sym_stats.auto_detected,
        "symmetry should be marked as auto-detected"
    );

    // Permutation count should match S3 = 6.
    assert_eq!(
        sym_stats.permutation_count, 6,
        "auto-detected S3 should have 6 permutations"
    );
}

/// Verify auto-detection works with multiple independent symmetric sets.
#[cfg_attr(test, ntest::timeout(15000))]
#[test]
fn test_auto_detect_multi_group() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let _env_lock = AUTO_SYMMETRY_ENV_LOCK
        .lock()
        .expect("auto symmetry env lock must not be poisoned");

    let src = r#"
---- MODULE AutoDetectMulti ----
EXTENDS TLC
CONSTANTS Acceptors, Values
VARIABLE votes

Init == votes \in [Acceptors -> Values \cup {"none"}]
Next == UNCHANGED votes

Sym == Permutations(Acceptors) \cup Permutations(Values)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config_explicit = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config_explicit.constants.insert(
        "Acceptors".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "a1".to_string(),
            "a2".to_string(),
            "a3".to_string(),
        ]),
    );
    config_explicit.constants.insert(
        "Values".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["v1".to_string(), "v2".to_string()]),
    );

    let mut checker_explicit = ModelChecker::new(&module, &config_explicit);
    checker_explicit.set_deadlock_check(false);
    let result_explicit = checker_explicit.check();

    let states_explicit = match result_explicit {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Expected Success with explicit symmetry, got {:?}", other),
    };

    // Config with auto-detection.
    let config_auto = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constants: config_explicit.constants.clone(),
        constants_order: config_explicit.constants_order.clone(),
        ..Default::default()
    };

    let _env = AutoSymmetryEnvGuard::set(Some("1"));
    let mut checker_auto = ModelChecker::new(&module, &config_auto);
    checker_auto.set_deadlock_check(false);
    let result_auto = checker_auto.check();

    let (states_auto, sym_stats) = match result_auto {
        CheckResult::Success(stats) => {
            let sym = stats.symmetry_reduction.clone();
            (stats.states_found, sym)
        }
        other => panic!("Expected Success with auto symmetry, got {:?}", other),
    };

    assert_eq!(
        states_explicit, states_auto,
        "multi-group auto-detect should match explicit: explicit={}, auto={}",
        states_explicit, states_auto
    );

    // Should detect 2 groups.
    assert_eq!(
        sym_stats.symmetry_groups, 2,
        "should auto-detect 2 independent symmetry groups"
    );

    assert!(sym_stats.auto_detected);
}

/// Verify auto-detection does not activate when TLA2_AUTO_SYMMETRY is not set.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_auto_detect_disabled_by_default() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let _env_lock = AUTO_SYMMETRY_ENV_LOCK
        .lock()
        .expect("auto symmetry env lock must not be poisoned");

    let src = r#"
---- MODULE AutoDetectDisabled ----
EXTENDS TLC
CONSTANT Procs
VARIABLE active

Init == active \in Procs
Next == active' \in Procs /\ active' /= active
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
            "p3".to_string(),
        ]),
    );

    let _env = AutoSymmetryEnvGuard::set(None);

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    let stats = match result {
        CheckResult::Success(stats) => stats,
        other => panic!("Expected Success, got {:?}", other),
    };

    // Without auto-detection or explicit symmetry, all 3 states should be found.
    assert_eq!(
        stats.states_found, 3,
        "without auto-detect, should find all 3 states"
    );

    // Symmetry stats should be empty.
    assert_eq!(stats.symmetry_reduction.permutation_count, 0);
    assert!(!stats.symmetry_reduction.auto_detected);
}
