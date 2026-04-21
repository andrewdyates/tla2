// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Modulus operator semantics - Bug #554
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config};

// ============================================================================
// Bug #554: Modulus operator requires positive divisor (match TLC semantics)
// ============================================================================

/// Bug #554: Modulus (%) with zero divisor should error in transitions
///
/// TLC requires the second argument of % to be positive (> 0).
/// Zero is not positive, so `x % 0` should produce an error.
///
/// This test verifies that the evaluator correctly rejects modulus by zero
/// during Next transitions (where the error isn't swallowed by constraint extraction).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_554_modulus_zero_divisor_in_next() {
    let spec = r#"
---- MODULE ModulusZeroNext ----
EXTENDS Integers
VARIABLE x

Init == x = 1

\* This will trigger modulus by zero error during state generation
Next == x' = x % 0

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);

    // Should produce an evaluation error, not succeed
    match &result {
        CheckResult::Error { error, .. } => {
            // Use Display format to get human-readable error message
            let msg = format!("{}", error);
            assert!(
                msg.contains("positive number"),
                "Error should mention positive number requirement, got: {}",
                msg
            );
        }
        CheckResult::Deadlock { .. } => {
            // A deadlock result is also acceptable - it means the Next transition
            // couldn't find any successors due to the modulus error
        }
        CheckResult::Success(_) => {
            panic!("Bug #554 regression! Modulus by zero should error, not succeed");
        }
        other => {
            // Other error types are acceptable as long as it doesn't succeed
            eprintln!("Got error (acceptable): {:?}", other);
        }
    }
}

/// Bug #554: Modulus (%) with negative divisor should error
///
/// TLC requires the second argument of % to be positive (> 0).
/// Negative numbers are not positive, so `x % -5` should produce an error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_554_modulus_negative_divisor_in_next() {
    let spec = r#"
---- MODULE ModulusNegativeNext ----
EXTENDS Integers
VARIABLE x

Init == x = 10

\* This will trigger modulus by negative error during state generation
Next == x' = x % (0-5)

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);

    // Should produce an evaluation error, not succeed
    eprintln!("Result for negative divisor test: {:?}", result);
    match &result {
        CheckResult::Error { error, .. } => {
            // Use Display format to get human-readable error message
            let msg = format!("{}", error);
            assert!(
                msg.contains("positive number"),
                "Error should mention positive number requirement, got: {}",
                msg
            );
        }
        CheckResult::Deadlock { .. } => {
            // A deadlock result is also acceptable
        }
        CheckResult::Success(stats) => {
            panic!(
                "Bug #554 regression! Modulus by negative should error, not succeed. Stats: {:?}",
                stats
            );
        }
        other => {
            // Other error types are acceptable as long as it doesn't succeed
            eprintln!("Got error (acceptable): {:?}", other);
        }
    }
}

/// Bug #554: Modulus (%) with positive divisor should work
///
/// Verify that the fix for negative/zero divisors doesn't break positive divisors.
/// TLC allows `x % k` when k > 0.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_554_modulus_positive_divisor_works() {
    let spec = r#"
---- MODULE ModulusPositive ----
EXTENDS Integers
VARIABLE x

Init == x = 10 % 3  \* Positive divisor - should work, result is 1

Next == x' = x

Invariant == x = 1  \* 10 % 3 = 1

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Invariant".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "Expected 1 initial state");
        }
        other => {
            panic!(
                "Bug #554: Modulus with positive divisor should work, got: {:?}",
                other
            );
        }
    }
}

/// Bug #554: Modulus (%) with negative dividend, positive divisor
///
/// TLC's modulus is Euclidean (result is always non-negative for positive divisor).
/// -10 % 3 = 2 (not -1)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_554_modulus_negative_dividend() {
    let spec = r#"
---- MODULE ModulusNegativeDividend ----
EXTENDS Integers
VARIABLE x

\* -10 % 3 = 2 with TLC's Euclidean semantics
\* -10 = 3 * (-4) + 2, where 0 <= 2 < 3
Init == x = (0-10) % 3

Next == x' = x

Invariant == x = 2

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Invariant".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "Expected 1 initial state");
        }
        other => {
            panic!(
                "Bug #554: Euclidean modulus should give -10 % 3 = 2, got: {:?}",
                other
            );
        }
    }
}
