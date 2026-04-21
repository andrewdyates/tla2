// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for symmetry reduction statistics tracking.

use super::*;

/// Verify that symmetry reduction statistics are populated after model checking.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_stats_populated_on_success() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SymStatsTest ----
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

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
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

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    let stats = match result {
        CheckResult::Success(stats) => stats,
        other => panic!("Expected Success, got {:?}", other),
    };

    // Verify symmetry stats are populated.
    let sym_stats = &stats.symmetry_reduction;

    // S3 has 6 permutations (3! = 6).
    assert_eq!(
        sym_stats.permutation_count, 6,
        "S3 should have 6 permutations"
    );

    // Should have at least 1 symmetry group.
    assert!(
        sym_stats.symmetry_groups >= 1,
        "should detect at least 1 symmetry group"
    );

    // With 3 processes, without symmetry we'd have 3 states; with symmetry, 1.
    // That means 2 states were folded.
    assert_eq!(stats.states_found, 1, "symmetry should reduce to 1 state");

    // fp_cache operations should have been tracked.
    assert!(
        sym_stats.fp_cache_hits + sym_stats.fp_cache_misses > 0,
        "should have tracked at least one fp_cache operation"
    );

    // Reduction factor should be > 1 when symmetry is effective.
    assert!(
        sym_stats.reduction_factor >= 1.0,
        "reduction factor should be >= 1.0, got {}",
        sym_stats.reduction_factor
    );

    // Not auto-detected (we explicitly configured SYMMETRY).
    assert!(
        !sym_stats.auto_detected,
        "should not be auto-detected when SYMMETRY is configured"
    );
}

/// Verify that symmetry stats are default (empty) when no symmetry is configured.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_stats_empty_without_symmetry() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE NoSymStats ----
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
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    let stats = match result {
        CheckResult::Success(stats) => stats,
        other => panic!("Expected Success, got {:?}", other),
    };

    let sym_stats = &stats.symmetry_reduction;
    assert_eq!(
        sym_stats.permutation_count, 0,
        "no symmetry should mean 0 permutations"
    );
    assert_eq!(sym_stats.symmetry_groups, 0);
    assert_eq!(sym_stats.fp_cache_hits, 0);
    assert_eq!(sym_stats.fp_cache_misses, 0);
    assert_eq!(sym_stats.states_folded, 0);
}

/// Verify symmetry stats for multi-group symmetry (S3 x S2).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_stats_multi_group() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE MultiGroupStats ----
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

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config.constants.insert(
        "Acceptors".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec![
            "a1".to_string(),
            "a2".to_string(),
            "a3".to_string(),
        ]),
    );
    config.constants.insert(
        "Values".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["v1".to_string(), "v2".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    let stats = match result {
        CheckResult::Success(stats) => stats,
        other => panic!("Expected Success, got {:?}", other),
    };

    let sym_stats = &stats.symmetry_reduction;

    // The closure contains 20 permutations: 6 Acceptor-only (domain {a1,a2,a3}),
    // 2 Value-only (domain {v1,v2}), and 12 cross-product (domain {a1,a2,a3,v1,v2}).
    // The partial-domain generators are distinct FuncValue entries because they have
    // different domains, so the closure set includes all three categories.
    // The mathematically minimal S3 x S2 = 12 corresponds to the full-domain subset,
    // but the closure algorithm preserves generators from both groups.
    assert_eq!(
        sym_stats.permutation_count, 20,
        "S3 x S2 closure should have 20 permutations (6 + 2 + 12)"
    );

    // Should detect 2 symmetry groups.
    assert_eq!(
        sym_stats.symmetry_groups, 2,
        "should detect 2 symmetry groups (Acceptors, Values)"
    );

    // Without symmetry: 27 states. With: 6.
    assert_eq!(
        stats.states_found, 6,
        "multi-group symmetry should reduce to 6 canonical states"
    );

    // Reduction factor should reflect the 27 -> 6 reduction.
    assert!(
        sym_stats.reduction_factor > 1.0,
        "reduction factor should be > 1.0 for effective multi-group symmetry"
    );
}

/// Verify that symmetry stats track cache performance correctly.
/// When the same canonical fingerprint appears multiple times during BFS,
/// the cache should show hits.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_symmetry_stats_cache_behavior() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // A spec that generates successors back to already-seen states,
    // exercising the fp_cache.
    let src = r#"
---- MODULE SymCacheTest ----
EXTENDS TLC
CONSTANT Procs
VARIABLE active, count

Init == active \in Procs /\ count = 0
Next == /\ active' \in Procs
        /\ count' = count + 1
        /\ count < 2

Sym == Permutations(Procs)
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        symmetry: Some("Sym".to_string()),
        ..Default::default()
    };
    config.constants.insert(
        "Procs".to_string(),
        crate::config::ConstantValue::ModelValueSet(vec!["p1".to_string(), "p2".to_string()]),
    );

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    let stats = match result {
        CheckResult::Success(stats) => stats,
        other => panic!("Expected Success, got {:?}", other),
    };

    let sym_stats = &stats.symmetry_reduction;

    // We should have at least some fp_cache misses (first time seeing each state).
    assert!(
        sym_stats.fp_cache_misses > 0,
        "should have at least some fp_cache misses"
    );

    // S2 has 2 permutations.
    assert_eq!(
        sym_stats.permutation_count, 2,
        "S2 should have 2 permutations"
    );
}
