// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! z4 enumeration, FunAsSeq, prime quantifier - Bugs #349, #374, #523, #633
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use std::path::PathBuf;
use tla_check::{check_module, CheckResult, Config, ModelChecker};
use tla_core::ModuleLoader;

// ============================================================================
// Bug #349: Prime guard quantification over x' fails - domain resolves to current state
// ============================================================================

/// Bug #349: Prime guard quantification domain uses wrong state reference
///
/// Root cause (from research report 2026-01-20):
/// - `compile_value_expr()` at line 5770-5784 hardcodes `StateRef::Current` and `allow_prime = false`
/// - When compiling quantifier domains inside prime context (e.g., `\A pair \in x` inside `NoSelfLoop'`),
///   the domain always resolves to current state instead of next state
/// - TLC handles this by context-shifting (`s1` becomes `s0` during prime evaluation), not textual substitution
///
/// The bug causes `\A pair \in x : P(pair)` inside `NoSelfLoop'` to iterate over `x = {}` (current)
/// instead of `x' = {<<1,2>>}` (next), making the quantifier vacuously true and missing valid transitions.
///
/// Baseline (TLC): 17 states generated, 4 distinct states found
/// Bug behavior: 1 state, 0 transitions, Deadlock
///
/// This test MUST:
/// - FAIL with Deadlock when bug exists
/// - PASS with exactly 4 states when fix is correct
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_349_prime_guard_quantifier_domain_state_reference() {
    let spec = r#"
---- MODULE Bug349PrimeGuardQuantifierDomain ----
VARIABLE x

\* Operator with quantifier over state variable
NoSelfLoop == \A pair \in x : pair[1] # pair[2]

Init == x = {}

\* Next: enumerate subsets, filter by NoSelfLoop' (prime guard)
\* When compiled, the domain `x` inside `\A pair \in x : ...` in `NoSelfLoop'`
\* SHOULD reference next-state x' (from `x' \in SUBSET(...)`)
\* BUG: domain references current-state x instead (empty set)
Next ==
    /\ x' \in SUBSET({<<1, 1>>, <<1, 2>>, <<2, 1>>})
    /\ NoSelfLoop'

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
        CheckResult::Success(stats) => {
            // TLC baseline: 17 states generated, 4 distinct states found
            // Valid successor states from x = {}:
            // - {} (NoSelfLoop trivially true for empty set)
            // - {<<1,2>>} (1 # 2 = TRUE)
            // - {<<2,1>>} (2 # 1 = TRUE)
            // - {<<1,2>>, <<2,1>>} (both pairs satisfy predicate)
            // Self-loop pair <<1,1>> is correctly filtered by NoSelfLoop'
            assert_eq!(
                stats.states_found, 4,
                "Bug #349: Prime guard quantifier domain state reference. \
                 TLC finds 4 distinct states. Got {} states. \
                 If this is 1, the domain is resolving to current state (bug exists). \
                 If this is 8, the NoSelfLoop' guard isn't being applied at all.",
                stats.states_found
            );
            // Verify transitions exist (not deadlocked)
            assert!(
                stats.transitions > 0,
                "Bug #349: Expected transitions from initial state, got 0 (deadlock behavior)"
            );
        }
        CheckResult::Deadlock { stats, .. } => {
            panic!(
                "Bug #349 EXISTS: Prime guard quantifier domain resolves to current state. \
                 Got Deadlock with {} states and {} transitions. \
                 The quantifier `\\A pair \\in x` inside NoSelfLoop' is iterating over \
                 current-state x={{}} instead of next-state x'. \
                 Fix: Thread StateRef through compile_value_expr() for quantifier domains.",
                stats.states_found, stats.transitions
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #349: Unexpected invariant violation ({}). No invariants specified.",
                invariant
            );
        }
        other => {
            panic!("Bug #349: Unexpected result: {:?}", other);
        }
    }
}

/// Test that conflicting assignments produce no successors (assign-filter behavior).
///
/// Part of #506: When `x' = 1 /\ x' = 2` appears, the second assignment should
/// filter (not overwrite), causing the branch to be disabled since 1 != 2.
///
/// This tests the "value differs" path in the FIX #506 runtime filter.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conflicting_assignments_filter() {
    let spec = r#"
---- MODULE ConflictingAssignments ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

\* Conflicting assignment: x' = 1 AND x' = 2 cannot both be satisfied
\* The second assignment should filter (not overwrite), causing branch failure
ConflictingNext == x' = 1 /\ x' = 2

\* Non-conflicting: x' = 1 AND x' = 1 is fine (same value)
SameValueNext == x' = 1 /\ x' = 1

\* Combined: should only have successor from SameValueNext
Next == ConflictingNext \/ SameValueNext

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
        CheckResult::Success(stats) => {
            // Expected: 2 states (x=0 -> x=1, then deadlock from x=1)
            // - Init: x = 0
            // - From x=0: ConflictingNext fails (1 != 2), SameValueNext succeeds -> x = 1
            // - From x=1: ConflictingNext fails (1 != 2), SameValueNext succeeds -> x = 1 (self-loop)
            assert_eq!(
                stats.states_found, 2,
                "Expected 2 states (x=0 and x=1). Got {}. \
                 If > 2, the conflicting assignment filter is not working correctly.",
                stats.states_found
            );
            // Should have 1 transition (x=0 -> x=1) since x=1 -> x=1 is a self-loop
            // TLA2 may or may not count self-loops as transitions, so just verify > 0
            assert!(
                stats.transitions >= 1,
                "Expected at least 1 transition. Got {}.",
                stats.transitions
            );
        }
        CheckResult::Deadlock { stats, .. } => {
            // This can happen if SameValueNext doesn't create a self-loop transition
            // At minimum, we should have x=0 -> x=1
            assert!(
                stats.states_found >= 1,
                "Expected at least 1 state (initial). Got {}.",
                stats.states_found
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug #374: FunAsSeq not loading from Apalache module (fixed by #451)
// ============================================================================

/// Bug #374: FunAsSeq from Apalache module now works
///
/// Issue #451 fixed underscore-prefixed identifier parsing which broke
/// Apalache.tla loading. Operators defined after `LOCAL INSTANCE` in
/// Apalache.tla (like FunAsSeq) are now correctly loaded.
///
/// This test verifies FunAsSeq works by converting a function to a sequence.
/// Note: This test requires loading Apalache.tla from test_specs/tla_library,
/// so it uses ModuleLoader to properly resolve EXTENDS.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_374_funasseq_from_apalache() {
    let spec = r#"
---- MODULE FunAsSeqTest ----
EXTENDS Apalache, Integers

f == [x \in 1..3 |-> x * 2]
s == FunAsSeq(f, 3, 3)

VARIABLE dummy
Init == dummy = s
Next == UNCHANGED dummy
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    // Load extended modules (Apalache.tla) using ModuleLoader.
    // Cargo tests run from crates/tla-check, so use paths relative to that.
    let mut loader = ModuleLoader::with_base_dir(PathBuf::from("."));
    loader.add_search_path(PathBuf::from("tests/tla_library"));
    loader.add_search_path(PathBuf::from("../../test_specs/tla_library"));
    loader.add_search_path(PathBuf::from("../../test_specs"));

    let extended_module_names = loader
        .load_extends(&module)
        .expect("Failed to load extended modules");

    let extended_modules: Vec<_> = extended_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    // Use ModelChecker::new_with_extends to include Apalache operators
    let mut checker = ModelChecker::new_with_extends(&module, &extended_modules, &config);
    let result = checker.check();

    match &result {
        CheckResult::Success(stats) => {
            // FunAsSeq should produce <<2, 4, 6>> so Init should have 1 state
            assert_eq!(
                stats.states_found, 1,
                "Expected 1 state (FunAsSeq result), got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "Bug #374: FunAsSeq from Apalache failed. Expected Success, got {:?}. \
                 This was fixed by #451 (underscore identifier parsing).",
                other
            );
        }
    }
}

// ============================================================================
// Bug #523: z4 Init enumeration unsound for heterogeneous SetEnum
// ============================================================================

/// Bug #523: Heterogeneous SetEnum must not under-enumerate
///
/// z4-based Init enumeration must either:
/// - refuse (return error, triggering fallback), OR
/// - enumerate ALL solutions
///
/// It must NOT silently under-enumerate by only returning states of one type.
///
/// This is an end-to-end test that verifies the full model checking path
/// (parse → lower → check) handles heterogeneous SetEnum correctly.
///
/// Part of #523 (P0 soundness fix), #533 (end-to-end test)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_523_heterogeneous_setenum_no_underenumeration() {
    // Set env var to force z4 enumeration attempt
    // (The z4 path should refuse heterogeneous sets and fall back)
    let _guard = common::EnvVarGuard::set("TLA2_FORCE_Z4", Some("1"));

    let spec = r#"
---- MODULE HeterogeneousSetEnum ----
VARIABLE x

\* Init with heterogeneous set: x can be Int or String
Init == x \in {1, "a"}

\* Trivial Next - just keep x unchanged
Next == x' = x

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
        CheckResult::Success(stats) => {
            // CRITICAL: Must find BOTH initial states (x=1 and x="a")
            // If only 1 state is found, z4 is under-enumerating (soundness bug!)
            assert_eq!(
                stats.initial_states, 2,
                "Bug #523 regression! Heterogeneous SetEnum must enumerate BOTH states. \
                 Found {} initial states, expected 2 (x=1 and x=\"a\"). \
                 This indicates z4 is under-enumerating.",
                stats.initial_states
            );
            // Should also have 2 total states (both are deadend states)
            assert_eq!(
                stats.states_found, 2,
                "Expected 2 total states, got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "Bug #523 test: Unexpected result {:?}. \
                 Model checking should succeed with 2 initial states.",
                other
            );
        }
    }
}

// ============================================================================
// Feature #633: z4 Init enumeration smoke test
// ============================================================================

/// Feature #633: Smoke test for z4-based Init enumeration
///
/// This test verifies that the z4 feature correctly enumerates initial states
/// for a simple spec with multiple integer-valued Init states.
///
/// Purpose: Fast verification that z4 dependency bumps don't break Init enumeration.
///
/// TLC baseline (verified 2026-01-28):
/// - Command: `java -jar tla2tools.jar -config Z4SmokeTest.cfg Z4SmokeTest.tla`
/// - Output: "5 distinct states generated" (initial), "6 distinct states found" (total)
///
/// Part of #633 (z4 smoke test)
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_feature_633_z4_init_enumeration_smoke() {
    // Force z4 enumeration for this test
    let _guard = common::EnvVarGuard::set("TLA2_FORCE_Z4", Some("1"));

    let spec = r#"
---- MODULE Z4SmokeTest ----
EXTENDS Integers
VARIABLE x

\* Init with multiple integer values - should enumerate via z4
Init == x \in 1..5

\* Simple Next - increment x up to 6
Next == x' = IF x < 6 THEN x + 1 ELSE x

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
        CheckResult::Success(stats) => {
            // z4 should enumerate all 5 initial states (x=1,2,3,4,5)
            assert_eq!(
                stats.initial_states, 5,
                "z4 smoke test: Expected 5 initial states, got {}. \
                 This may indicate z4 enumeration is broken.",
                stats.initial_states
            );
            // Total states: x=1,2,3,4,5,6 = 6 states
            assert_eq!(
                stats.states_found, 6,
                "z4 smoke test: Expected 6 total states, got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "z4 smoke test: Unexpected result {:?}. \
                 Model checking should succeed with 5 initial states and 6 total states.",
                other
            );
        }
    }
}

/// z4 Init enumeration file-based test (Part of #634)
///
/// Tests z4 enumeration using the file-based spec at test_specs/Z4SmokeTest.tla.
/// This complements the inline test above by verifying the file-based artifacts work.
///
/// TLC baseline (verified 2026-01-28):
/// - Command: `java -jar tla2tools.jar -config Z4SmokeTest.cfg Z4SmokeTest.tla`
/// - Output: "5 distinct states generated" (initial), "6 distinct states found" (total)
#[cfg(feature = "z4")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_feature_634_z4_init_file_based() {
    use std::fs;

    let _guard = common::EnvVarGuard::set("TLA2_FORCE_Z4", Some("1"));

    // Load spec from file
    let spec_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/test_specs/Z4SmokeTest.tla");
    let spec = fs::read_to_string(&spec_path).unwrap_or_else(|e| {
        panic!(
            "Failed to read {}: {}. Run test from crates/tla-check/.",
            spec_path.display(),
            e
        )
    });

    let module = parse_module(&spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            // Verify against TLC baseline
            assert_eq!(
                stats.initial_states, 5,
                "z4 file test: Expected 5 initial states (TLC baseline), got {}",
                stats.initial_states
            );
            assert_eq!(
                stats.states_found, 6,
                "z4 file test: Expected 6 total states (TLC baseline), got {}",
                stats.states_found
            );
        }
        other => {
            panic!(
                "z4 file test: Unexpected result {:?}. \
                 Expected 5 initial, 6 total states per TLC baseline.",
                other
            );
        }
    }
}
