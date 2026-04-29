// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1819: primed operator guard must correctly filter successors.
///
/// This is the end-to-end version of the guard_check.rs unit tests. The unit tests
/// in guard_check.rs use simple `y' > 0` expressions that don't trigger the
/// HashMap-vs-array binding divergence. This test uses a pattern closer to
/// MCInnerSerial where:
/// - A zero-arg operator references multiple primed variables
/// - The operator is used as a guard in the Next action
/// - Valid successors must pass the guard check
///
/// The #1819 bug: action_holds_in_next_state_array used HashMap-based binding, but
/// the enumerator used array-based binding. For complex primed operators, the eval
/// cache key and dependency tracking diverge between these paths, causing valid
/// successors to be spuriously pruned.
///
/// Expected: Init with (a=0, b=0), Next generates successors where a'>=b'.
/// Without guard: 4 successors (a' in {0,1}, b' in {0,1}). With guard: 3 valid.
/// Total: 4 states (init + 3 successors).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1819_primed_operator_guard_filters_successors() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE PrimeOpGuard ----
VARIABLES a, b

\* Zero-arg operator referencing MULTIPLE primed variables.
\* This triggers the eval_ident_shared_zero_arg_op caching path where
\* cache keys diverge between HashMap (is_next_state=true) and array
\* (is_next_state=false) bindings.
OrderedPrime == a' >= b'

Init == a = 0 /\ b = 0

\* Next generates candidates and filters via primed operator guard.
\* Without the guard: 4 candidates (a' in {0,1} x b' in {0,1}).
\* With OrderedPrime guard: 3 valid ((0,0), (1,0), (1,1)) since (0,1) fails.
Next ==
    /\ a' \in {0, 1}
    /\ b' \in {0, 1}
    /\ OrderedPrime

====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            // Init: (a=0, b=0)
            // Valid successors from init: (0,0), (1,0), (1,1) - 3 states
            // But (0,0) is the same as init, so only 2 new states are discovered.
            // Total distinct: (0,0), (1,0), (1,1) = 3 states
            // From (1,0): successors (0,0), (1,0), (1,1) - all already seen
            // From (1,1): successors (0,0), (1,0), (1,1) - all already seen
            assert_eq!(
                stats.states_found, 3,
                "#1819 regression: primed operator guard should produce exactly 3 states \
                 ((0,0), (1,0), (1,1)). If 4, the OrderedPrime guard is not being enforced \
                 (HashMap binding bug). If fewer, valid successors are being spuriously pruned. \
                 Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "#1819 regression: primed operator guard should not error. \
                 If this errors, the primed operator evaluation path is broken. \
                 Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for #1819: primed operator guard with invariant verification.
///
/// Stronger version that also checks an invariant to verify the guard is properly
/// enforced. The invariant `a >= b` should hold in all reachable states if
/// OrderedPrime' is properly enforced as a guard on Next.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1819_primed_guard_enforces_invariant() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE PrimeGuardInvariant ----
VARIABLES a, b

Ordered == a >= b
OrderedPrime == a' >= b'

Init == a = 0 /\ b = 0

Next ==
    /\ a' \in {0, 1, 2}
    /\ b' \in {0, 1, 2}
    /\ OrderedPrime

\* If the primed guard works, all reachable states satisfy a >= b
Inv == Ordered

====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            // States where a >= b from {0,1,2}x{0,1,2}:
            // (0,0), (1,0), (1,1), (2,0), (2,1), (2,2) = 6 states
            assert_eq!(
                stats.states_found, 6,
                "#1819 regression: primed guard with invariant should find 6 states \
                 (all pairs where a>=b in {{0,1,2}}x{{0,1,2}}). Found {}",
                stats.states_found
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "#1819 BUG DETECTED: Invariant '{}' violated - primed operator guard \
                 OrderedPrime is NOT being enforced, allowing states where a < b. \
                 This is the HashMap-vs-array binding divergence bug.",
                invariant
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("#1819 regression: should not error. Error: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for #1886: EXISTS domain with SetPred predicate type error must
/// propagate as a checker error, not be silently swallowed.
///
/// Before the fix, `symbolic_assignments.rs` had `Err(_) => return Ok(())` which
/// silently skipped the entire EXISTS domain enumeration when eval_iter_set failed.
/// This test verifies that a SetPred with a non-boolean predicate (type error)
/// propagates as a fatal checker error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1886_exists_domain_setpred_type_error_propagates() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // The predicate `1` is not boolean - SetPred materialization should fail with TypeError.
    // Before #1886 fix, this would be silently swallowed and the checker would report
    // 0 successors (missing states).
    let src = r#"
---- MODULE ExistsDomainTypeError ----
EXTENDS Integers
VARIABLE x
Init == x = 0
\* The EXISTS domain uses a SetPred with a non-boolean predicate.
\* Materializing {v \in {1,2} : 1} should fail with TypeError("BOOLEAN").
Next == \E v \in {n \in {1, 2} : 1} : x' = v
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Error { .. } => {
            // Expected: the type error in the SetPred predicate propagates.
        }
        CheckResult::Success(stats) => {
            panic!(
                "#1886 regression: SetPred with non-boolean predicate in EXISTS domain \
                 should produce a checker error, not silent success. \
                 States found: {} (should be 0 with old bug, error with fix)",
                stats.states_found
            );
        }
        other => panic!("#1886 regression: unexpected result: {other:?}"),
    }
}

/// Regression test for #1886: InSet assignment with SetPred materialization failure
/// must propagate as a checker error, not produce an empty value set.
///
/// Before the fix, `symbolic_assignments.rs` had `Err(_) => Vec::new()` which
/// silently replaced a failed SetPred materialization with zero candidate values.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1886_inset_assignment_setpred_type_error_propagates() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // x' \in {n \in {1,2} : 1} should fail because the predicate `1` is not boolean.
    // Before fix: silently produces Vec::new(), meaning x' gets no values -> deadlock
    // After fix: propagates as TypeError
    let src = r#"
---- MODULE InSetTypeError ----
EXTENDS Integers
VARIABLE x
Init == x = 0
\* Direct InSet with a broken SetPred predicate
Next == x' \in {n \in {1, 2} : 1}
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Error { .. } => {
            // Expected: the type error propagates as a checker error.
        }
        CheckResult::Success(stats) => {
            panic!(
                "#1886 regression: SetPred with non-boolean predicate in x' \\in S \
                 should produce a checker error, not silent success or deadlock. \
                 States found: {}",
                stats.states_found
            );
        }
        other => panic!("#1886 regression: unexpected result: {other:?}"),
    }
}
