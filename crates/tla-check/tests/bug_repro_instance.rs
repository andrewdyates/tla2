// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! INSTANCE refinement and substitution - Bugs #182, #258, #284
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use ntest::timeout;
use tla_check::{check_module, CheckResult, Config, ConstantValue};

// ============================================================================
// Bug #182: Set comprehension membership optimization missing (SetFilter)
// ============================================================================

/// Bug #182: Membership in `{x \\in S : P(x)}` must be checked lazily as `v \\in S /\\ P(v)`.
///
/// The stressor here is `SUBSET SUBSET (1..70)`, which is intractable to enumerate.
///
/// SAFETY: Uses timeout protection (#318). If lazy evaluation breaks, this test will
/// timeout after 10 seconds rather than OOM the machine attempting to enumerate
/// 2^(2^70) elements. The test passes quickly (~100ms) when lazy eval works correctly.
///
/// See #316 and #318 for details.
#[test]
#[timeout(10000)] // 10 second timeout - OOM protection if lazy eval breaks
fn test_bug_182_set_filter_membership_is_lazy() {
    let spec = r#"
---- MODULE SetFilterMembership182 ----
EXTENDS Integers

VARIABLE x

Domain == SUBSET SUBSET (1..70)

TypeOK == x \in { y \in Domain : TRUE }

Init == x = {}

Next == UNCHANGED x

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected: TypeOK holds and evaluation does not enumerate Domain.
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #182 exists! Invariant {} violated - SetFilter membership enumerated Domain",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Bug #182: Verify SetFilter membership correctness with actual predicates.
///
/// This test verifies that lazy membership in {x \in S : P(x)} is semantically
/// correct: v \in {x \in S : P(x)} <==> v \in S /\ P(v).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_182_set_filter_membership_correctness() {
    let spec = r#"
---- MODULE SetFilterCorrectnessCheck182 ----
EXTENDS Integers

VARIABLE state

\* Define set comprehension with predicate
EvenNums == { x \in 1..10 : x % 2 = 0 }
OddNums == { x \in 1..10 : x % 2 = 1 }
BigNums == { x \in 1..10 : x > 5 }

\* Invariants checking membership correctness
\* These should all be TRUE for the lazy implementation to be correct
Check2InEven == 2 \in EvenNums
Check3NotInEven == 3 \notin EvenNums
Check5InOdd == 5 \in OddNums
Check8InBig == 8 \in BigNums
Check3NotInBig == 3 \notin BigNums

\* Check intersection via nested set filter
SmallEvens == { x \in EvenNums : x < 6 }
Check4InSmallEvens == 4 \in SmallEvens
Check8NotInSmallEvens == 8 \notin SmallEvens

Init == state = 0

Next == UNCHANGED state

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![
            "Check2InEven".to_string(),
            "Check3NotInEven".to_string(),
            "Check5InOdd".to_string(),
            "Check8InBig".to_string(),
            "Check3NotInBig".to_string(),
            "Check4InSmallEvens".to_string(),
            "Check8NotInSmallEvens".to_string(),
        ],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            // Expected: All invariants hold, confirming SetFilter membership is correct.
            assert_eq!(stats.states_found, 1, "Expected exactly 1 state");
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #182: SetFilter membership incorrect! Invariant {} violated",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug #258: INSTANCE refinement property check returns false positive
// ============================================================================

/// Bug #258: ModuleRef evaluation returns FALSE during safety property checking
///
/// When checking refinement properties like `[][Sched!Next]_Sched!vars`, the
/// evaluation of `Sched!Next` incorrectly returns FALSE even when the transition
/// is a valid action from the instanced module.
///
/// Debug output shows:
/// - `left eval: Ok(FALSE)` for `Sched!Next`
/// - `right eval: Ok(FALSE)` for `UNCHANGED Sched!vars`
///
/// Fixed in commit f8de7e9: Root cause was stale state_env arrays in property checking.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_258_module_ref_instance_refinement() {
    // This test documents the bug pattern but uses a simpler spec
    // The actual fix should make AllocatorImplementation pass
    let spec = r#"
---- MODULE ModuleRefRefinement ----
EXTENDS Naturals
VARIABLE x

Next == x' = (x + 1) % 3
vars == x
Init == x = 0
Spec == Init /\ [][Next]_vars

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Spec".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "Expected 3 states");
        }
        CheckResult::PropertyViolation { property, .. } => {
            panic!("Bug #258: Property {} violated (false positive)", property);
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug #284: INSTANCE constant substitution performance - 180x overhead
// ============================================================================

/// Bug #284: INSTANCE with constant substitutions is ~180x slower than direct
///
/// When evaluating `Buffer!TypeOk` where `Buffer == INSTANCE RingBuffer WITH Values <- Int`,
/// the substitution `Values <- Int` should be cached because `Int` is a constant that
/// never changes during model checking.
///
/// Current behavior (Disruptor_SPMC):
/// - Direct TypeOk evaluation: ~1.6s for 8,496 states
/// - Instance TypeOk evaluation: ~180s for same 8,496 states (110x overhead)
/// - TLC: ~1s for same states
///
/// Root cause: Every identifier lookup in INSTANCE scope goes through the slow
/// path even for constant substitutions. The substitution `Values <- Int` is
/// re-evaluated every time instead of being cached.
///
/// Fix criteria:
/// - State counts must remain identical (correctness)
/// - Full Disruptor_SPMC should complete in < 20s (target: < 5s to match TLC)
/// - INSTANCE with constant substitutions should have < 10x overhead vs direct
///
/// This test documents the acceptance criteria. The actual performance test uses
/// the real Disruptor specs (run via CLI for full test).
///
/// To run full benchmark:
/// ```bash
/// # Original (with INSTANCE TypeOk): ~180s
/// time ./target/release/tla2 check examples/test/disruptor/Disruptor_SPMC.tla \
///   --config examples/test/disruptor/Disruptor_SPMC.cfg --workers 1
///
/// # Direct (inline TypeOk): ~1.6s
/// time ./target/release/tla2 check examples/test/disruptor/Disruptor_SPMC_direct.tla \
///   --config examples/test/disruptor/Disruptor_SPMC.cfg --workers 1
///
/// # TLC baseline: ~1s
/// cd ~/tlaplus && time java -cp tla2tools.jar tlc2.TLC \
///   -config ~/tla2/examples/test/disruptor/Disruptor_SPMC.cfg \
///   ~/tla2/examples/test/disruptor/Disruptor_SPMC.tla -workers 1
/// ```
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_284_instance_constant_substitution_correctness() {
    // This is a correctness test to ensure the fix doesn't break state counting.
    // Performance is tested via the CLI benchmark above.
    //
    // We use a simple spec that exercises CONSTANT resolution (similar to the
    // INSTANCE substitution path but doesn't require module loading).

    let spec = r#"
---- MODULE Bug284Correctness ----
EXTENDS Naturals, FiniteSets

CONSTANTS Values, NULL

VARIABLE state

\* TypeOk that uses CONSTANT Values
\* This exercises the constant resolution path
TypeOk ==
  /\ Values \subseteq Nat
  /\ state \in Values \union { NULL }

Init == state = NULL

Next ==
  \/ state' \in Values
  \/ state' = NULL

====
"#;

    let module = parse_module(spec);

    let mut constants = std::collections::HashMap::new();
    constants.insert(
        "Values".to_string(),
        ConstantValue::Value("{0, 1, 2}".to_string()),
    );
    constants.insert("NULL".to_string(), ConstantValue::ModelValue);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOk".to_string()],
        constants,
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            // Expected: 4 states (NULL, 0, 1, 2)
            assert_eq!(
                stats.states_found, 4,
                "Bug #284 correctness: Expected 4 states, got {}",
                stats.states_found
            );
        }
        other => panic!("Bug #284: Unexpected result: {:?}", other),
    }
}

// Performance test for Bug #284 moved to scripts/benchmark_performance.sh (line 64).
// Run `./scripts/benchmark_performance.sh` for Disruptor_SPMC perf testing.

/// Discriminating test for Bug #284 BigUnion fast path.
///
/// This test exercises the exact pattern that causes the slowdown:
/// `UNION { [0..N -> S] }` where S might be infinite.
///
/// WITHOUT the fix: This might be slow if eager check enumerates FuncSet
/// WITH the fix: Completes fast via singleton UNION bypass
///
/// The fix is at `crates/tla-check/src/eval.rs:3918` - a syntactic check
/// that returns `X` directly for `UNION { X }` patterns.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_284_bigunion_fast_path_discriminator() {
    use std::time::Instant;

    // This spec uses the EXACT pattern from RingBuffer.tla TypeOk:
    // `slots \in UNION { [0..LastIndex -> Values \union {NULL}] }`
    // where Values = Int (infinite).
    //
    // With finite codomain (SUBSET(S)), FuncSet enumeration is bounded.
    // With infinite codomain (Int), FuncSet.to_ord_set() returns None,
    // so we go through lazy path - but the membership test should still
    // be efficient.
    let spec = r#"
---- MODULE Bug284Discriminator ----
EXTENDS Naturals, FiniteSets

CONSTANTS S

VARIABLES state

\* This tests the finite SUBSET case from Disruptor_SPMC TypeOk.
\* The readers/writers fields use UNION { [0..3 -> SUBSET(S)] }
TypeOk ==
    state \in UNION { [0..3 -> SUBSET(S)] }

Init ==
    \* Start with empty function
    state = [x \in {0,1,2,3} |-> {}]

Next ==
    \* Add or remove an element from one slot
    \E i \in {0,1,2,3}, e \in S :
        state' = [state EXCEPT ![i] = IF e \in state[i]
                                       THEN @ \ {e}
                                       ELSE @ \union {e}]

Spec == Init /\ [][Next]_state
====
"#;

    let module = parse_module(spec);

    let mut constants = std::collections::HashMap::new();
    // S = {"a", "b", "c"} gives 2^3 = 8 possible subsets per slot
    // 4 slots means state space of 8^4 = 4096 states
    constants.insert(
        "S".to_string(),
        ConstantValue::ModelValueSet(vec!["a".into(), "b".into(), "c".into()]),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOk".to_string()],
        constants,
        ..Default::default()
    };

    let start = Instant::now();
    let result = check_module(&module, &config);
    let elapsed = start.elapsed();

    // With fix: Should complete in <5s
    // Without fix: Would timeout or take >60s
    match result {
        CheckResult::Success(stats) => {
            eprintln!(
                "Bug #284 discriminator: {} states in {:.2}s",
                stats.states_found,
                elapsed.as_secs_f64()
            );

            // This assertion will FAIL on current code, PASS with fix
            assert!(
                elapsed.as_secs_f64() < 10.0,
                "Bug #284: BigUnion fast path NOT working! Took {:.1}s (target <10s). \
                 Implement syntactic UNION {{X}} check at eval.rs:3918.",
                elapsed.as_secs_f64()
            );
        }
        other => {
            panic!("Bug #284 discriminator failed: {:?}", other);
        }
    }
}
