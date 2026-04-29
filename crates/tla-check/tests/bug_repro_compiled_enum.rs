// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compiled action fallback and enumerate_exists - Issues #649, #1209
//!
//! Split from bug_reproductions.rs — Part of #2850

#[cfg(not(debug_assertions))]
use std::collections::HashMap;
#[cfg(not(debug_assertions))]
use std::path::PathBuf;

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config};
#[cfg(not(debug_assertions))]
use tla_check::{ConstantValue, ModelChecker};
#[cfg(not(debug_assertions))]
use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader};

// ============================================================================
// Issue #649: btree full spec regression test
// ============================================================================

/// Issue #649: Verify btree spec produces TLC-matching state count with compiled actions.
///
/// This test loads the actual btree spec from tlaplus-examples and verifies
/// that TLA2 produces exactly 374,727 states (matching TLC baseline).
///
/// **IMPORTANT**: This test is release-only.
/// It validates full TLC parity for the btree benchmark, which is too expensive
/// for debug builds under the standard integration-test timeout.
/// Run with `cargo test -p tla-check --release --test bug_reproductions
/// test_issue_649_btree_tlc_equivalence`.
///
/// Baseline: TLC produces 374,727 states for btree with MaxOccupancy=2, MaxNode=8, MaxKey=4.
/// Bug #649: Compiled action error fallback was treating errors as "disabled action",
/// causing massive undercount (29 states instead of 374,727).
#[cfg_attr(test, ntest::timeout(600000))] // 10 minute timeout
#[cfg(not(debug_assertions))]
#[test]
fn test_issue_649_btree_tlc_equivalence() {
    // Use the in-repo btree spec (copied from tlaplus-examples)
    let btree_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../test_specs");
    let spec_path = btree_dir.join("btree.tla");

    let spec = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));

    // Parse the spec
    let tree = parse_to_syntax_tree(&spec);
    let result = lower(FileId(0), &tree);
    let module = result.module.expect("Failed to parse btree module");

    // Build config from btree.cfg
    // btree.cfg has: SPECIFICATION Spec, many constants, invariants
    let mut constants: HashMap<String, ConstantValue> = HashMap::new();

    // Model value constants (state machine states)
    for name in &[
        "READY",
        "GET_VALUE",
        "FIND_LEAF_TO_ADD",
        "WHICH_TO_SPLIT",
        "ADD_TO_LEAF",
        "SPLIT_ROOT_LEAF",
        "SPLIT_ROOT_INNER",
        "SPLIT_INNER",
        "SPLIT_LEAF",
        "UPDATE_LEAF",
        "NIL",
        "MISSING",
    ] {
        constants.insert(name.to_string(), ConstantValue::ModelValue);
    }

    // Set constants (from btree.cfg)
    // Vals = {x, y, z} - use ModelValueSet
    constants.insert(
        "Vals".to_string(),
        ConstantValue::ModelValueSet(vec!["x".to_string(), "y".to_string(), "z".to_string()]),
    );
    constants.insert(
        "MaxOccupancy".to_string(),
        ConstantValue::Value("2".to_string()),
    );
    constants.insert("MaxNode".to_string(), ConstantValue::Value("8".to_string()));
    constants.insert("MaxKey".to_string(), ConstantValue::Value("4".to_string()));

    // Set up loader to resolve EXTENDS (TLC, Naturals, FiniteSets, Sequences)
    let mut loader = ModuleLoader::with_base_dir(btree_dir.clone());
    loader.add_search_path(btree_dir.join("tla_library"));

    // Load both EXTENDS dependencies and named INSTANCE modules (Mapping == INSTANCE kvstore).
    let mut dependency_module_names = loader
        .load_extends(&module)
        .expect("Failed to load extended modules for btree");
    let instance_module_names = loader
        .load_instances(&module)
        .expect("Failed to load instance modules for btree");
    for name in instance_module_names {
        if !dependency_module_names.contains(&name) {
            dependency_module_names.push(name);
        }
    }

    let extended_modules: Vec<_> = dependency_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![
            "TypeOk".to_string(),
            "InnersMustHaveLast".to_string(),
            "LeavesCantHaveLast".to_string(),
            "KeyOrderPreserved".to_string(),
            "KeysInLeavesAreUnique".to_string(),
            "FreeNodesRemain".to_string(),
        ],
        constants,
        ..Default::default()
    };

    // Run model checker
    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    let result = checker.check();

    // Verify state count matches TLC baseline
    const TLC_BTREE_STATES: usize = 374727;

    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, TLC_BTREE_STATES,
                "Bug #649 regression: btree state count mismatch! \
                 TLA2={} states, TLC baseline={} states. \
                 Compiled action path may be causing state undercount.",
                stats.states_found, TLC_BTREE_STATES
            );
            eprintln!(
                "btree regression test PASSED: {} states (matches TLC baseline)",
                stats.states_found
            );
        }
        CheckResult::InvariantViolation {
            invariant, stats, ..
        } => {
            panic!(
                "btree test failed: invariant {} violated after {} states. \
                 Expected {} states with no violations.",
                invariant, stats.states_found, TLC_BTREE_STATES
            );
        }
        other => {
            panic!(
                "btree test unexpected result: {:?}. \
                 Expected Success with {} states.",
                other, TLC_BTREE_STATES
            );
        }
    }
}

// ============================================================================
// Issue #1209: enumerate_exists error propagation
// ============================================================================

/// Regression test for #1209: enumerate_exists must propagate genuine spec bugs
/// (UndefinedVar) as errors, not silently swallow them as disabled actions.
///
/// Before the fix, `\E y \in UndefinedSet : ...` would silently produce zero
/// successors (making the action appear disabled), potentially causing users to
/// believe their spec is correct when the domain expression has a bug.
///
/// Uses multi-bound EXISTS (`\E a \in S, b \in T`) to force execution through
/// the Tier 3 enumeration path in next_rec.rs (the actual #1209 fix location).
/// Single-bound EXISTS would be handled by Tier 1/2 (array_rec.rs) which have
/// separate error propagation logic.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_issue_1209_enumerate_exists_propagates_undefined_var() {
    let spec = r#"
---- MODULE EnumerateExistsUndefinedDomain ----
EXTENDS Integers
VARIABLES x, y
Init == x = 0 /\ y = 0
\* Multi-bound EXISTS forces Tier 3 (next_rec.rs) enumeration path
Next == \E a \in UndefinedSet, b \in {1} : x' = a /\ y' = b
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Error { error, .. } => {
            let msg = format!("{}", error);
            assert!(
                msg.contains("UndefinedSet") || msg.contains("undefined"),
                "Error should reference the undefined domain, got: {}",
                msg
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "Bug regression #1209! UndefinedVar in exists-domain was silently \
                 swallowed. Expected error, got success."
            );
        }
        CheckResult::Deadlock { .. } => {
            panic!(
                "Bug regression #1209! UndefinedVar in exists-domain was silently \
                 swallowed (zero successors → deadlock). Expected error."
            );
        }
        other => {
            panic!(
                "Unexpected result for undefined domain in exists: {:?}",
                other
            );
        }
    }
}

/// Complement to #1209: EXISTS-domain NotInDomain errors propagate fatally,
/// matching TLC semantics. TLC reports: "Attempted to apply function <<{1}>>
/// to argument 0, which is not in the domain of the function."
///
/// Fix #1552 removed top-level action error suppression, so f[x] where
/// x is not in DOMAIN f is now fatal in all contexts (including EXISTS domains).
///
/// Uses multi-bound EXISTS to force Tier 3 (next_rec.rs) enumeration path,
/// same as the propagation test above.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_issue_1209_enumerate_exists_propagates_not_in_domain_errors() {
    // This spec has a function f with domain {1}, and the exists iterates
    // over f[0] which produces a NotInDomain error.
    // Multi-bound EXISTS forces Tier 3 (next_rec.rs) enumeration path.
    let spec = r#"
---- MODULE EnumerateExistsDisabledAction ----
EXTENDS Integers
VARIABLES x, y

f == [i \in {1} |-> {i}]

Init == x = 0 /\ y = 0
\* When x = 0, f[x] triggers NotInDomain (0 not in {1}).
\* TLC: fatal error. TLA2 post-#1552: fatal error.
\* Multi-bound EXISTS ensures we hit next_rec.rs Tier 3 path.
Next == \E a \in f[x], b \in {1} : x' = a /\ y' = b
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);

    // TLC baseline: fatal error "Attempted to apply function <<{1}>> to
    // argument 0, which is not in the domain of the function."
    // Post-#1552, TLA2 propagates this fatally (no action-level suppression).
    match &result {
        CheckResult::Error { error, .. } => {
            let msg = format!("{}", error);
            assert!(
                msg.contains("out of bounds")
                    || msg.contains("not in the domain")
                    || msg.contains("NotInDomain"),
                "Expected NotInDomain/IndexOutOfBounds-style error, got: {}",
                msg
            );
        }
        CheckResult::Deadlock { .. } => {
            panic!(
                "NotInDomain in EXISTS domain should be fatal (TLC parity), \
                 not treated as disabled action producing deadlock"
            );
        }
        CheckResult::Success(_) => panic!("Expected fatal error, got success."),
        other => panic!(
            "Unexpected result for exists-domain NotInDomain: {:?}",
            other
        ),
    }
}
