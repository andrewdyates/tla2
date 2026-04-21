// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for #3035: ENABLED constraint propagation must thread witness bindings
//! through negation, implication, IF/THEN/ELSE, and multi-bound quantifiers.
//!
//! Each test constructs a spec with ENABLED in an invariant (safety check)
//! to exercise the constraint propagation dispatch without requiring liveness.
//!
//! The action tested via ENABLED is separate from the Next action to avoid
//! the successor enumeration engine needing to handle the same patterns.

mod common;

use tla_check::CheckResult;
use tla_check::Config;

fn check_spec(src: &str, expect_states: usize) {
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, expect_states,
                "expected {expect_states} states"
            );
        }
        CheckResult::Error { error, .. } => {
            let msg = format!("{error}");
            assert!(
                !msg.contains("PrimedVariableNotBound"),
                "PrimedVariableNotBound: witness bindings not propagated: {msg}"
            );
            assert!(
                !msg.contains("Undefined variable"),
                "Undefined variable: witness bindings not propagated: {msg}"
            );
            panic!("expected Success, got Error: {msg}");
        }
        other => panic!("expected Success, got: {other:?}"),
    }
}

/// #3035 case 1: Negation inside ENABLED must see witness bindings.
///
/// `ENABLED ComplexAction` where ComplexAction has `x' = 5 /\ ~(x' = 3)`.
/// After binding x' = 5, the negation `~(x' = 3)` must resolve x' = 5
/// from the witness to evaluate `5 = 3` as FALSE, making `~FALSE` = TRUE.
///
/// Next is a simple stuttering action (separate from the ENABLED-tested action).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_enabled_negation_sees_witness_bindings() {
    let src = r#"
---- MODULE EnabledNegation ----
EXTENDS Naturals

VARIABLE x

ComplexAction == x' = 5 /\ ~(x' = 3)

Init == x = 0

Next == x' = x

\* ENABLED ComplexAction should be TRUE because x' = 5 satisfies both
\* x' = 5 and ~(x' = 3). If witness bindings are not propagated
\* to the negation, this fails with PrimedVariableNotBound.
Inv == ENABLED ComplexAction

====
"#;
    check_spec(src, 1); // Only 1 state (x=0), stuttering
}

/// #3035 case 2: Implication antecedent inside ENABLED must see witness bindings.
///
/// `ENABLED ComplexAction` where ComplexAction has `x' = 5 /\ (x' = 5 => x' > 0)`.
/// After binding x' = 5, the implication antecedent `x' = 5` must resolve
/// from the witness.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_enabled_implication_sees_witness_bindings() {
    let src = r#"
---- MODULE EnabledImplication ----
EXTENDS Naturals

VARIABLE x

ComplexAction == x' = 5 /\ (x' = 5 => x' > 0)

Init == x = 0

Next == x' = x

\* ENABLED ComplexAction should be TRUE: x' = 5 satisfies the conjunction,
\* and the implication (5 = 5 => 5 > 0) is TRUE.
Inv == ENABLED ComplexAction

====
"#;
    check_spec(src, 1);
}

/// #3035 case 3: Negation of a false primed condition.
///
/// `ENABLED ComplexAction` where ComplexAction has `x' = 5 /\ ~(x' = 10)`.
/// x' is bound to 5, so ~(5 = 10) = TRUE.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_enabled_negation_false_primed_eq() {
    let src = r#"
---- MODULE EnabledNegationFalse ----
EXTENDS Naturals

VARIABLE x

ComplexAction == x' = 5 /\ ~(x' = 10)

Init == x = 0

Next == x' = x

Inv == ENABLED ComplexAction

====
"#;
    check_spec(src, 1);
}

/// #3035 case 4: Negation where the negated condition is TRUE should disable.
///
/// `ENABLED ComplexAction` where ComplexAction has `x' = 5 /\ ~(x' = 5)`.
/// x' = 5, then ~(5 = 5) = FALSE → conjunction fails → not enabled.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_enabled_negation_true_primed_eq_disables() {
    let src = r#"
---- MODULE EnabledNegationDisable ----
EXTENDS Naturals

VARIABLE x

ComplexAction == x' = 5 /\ ~(x' = 5)

Init == x = 0

Next == x' = x

\* ComplexAction is never enabled (contradictory: x'=5 and ~(x'=5))
Inv == ~ENABLED ComplexAction

====
"#;
    check_spec(src, 1);
}

/// #3035 case 5: IF/THEN/ELSE condition inside ENABLED must see witness bindings.
///
/// `ENABLED ComplexAction` where ComplexAction has
/// `x' = 5 /\ IF x' > 3 THEN TRUE ELSE FALSE`.
/// After binding x' = 5, the IF condition `x' > 3` must resolve from witness.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_enabled_if_condition_sees_witness_bindings() {
    let src = r#"
---- MODULE EnabledIfCondition ----
EXTENDS Naturals

VARIABLE x

ComplexAction == x' = 5 /\ IF x' > 3 THEN TRUE ELSE FALSE

Init == x = 0

Next == x' = x

Inv == ENABLED ComplexAction

====
"#;
    check_spec(src, 1);
}

/// #3035 case 6: Implication with FALSE antecedent (vacuous truth).
///
/// `ENABLED ComplexAction` where ComplexAction has `x' = 5 /\ (x' = 3 => FALSE)`.
/// x' = 5, antecedent 5=3 is FALSE, so implication is vacuously TRUE.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_enabled_implication_vacuous_truth() {
    let src = r#"
---- MODULE EnabledImplicationVacuous ----
EXTENDS Naturals

VARIABLE x

ComplexAction == x' = 5 /\ (x' = 3 => FALSE)

Init == x = 0

Next == x' = x

Inv == ENABLED ComplexAction

====
"#;
    check_spec(src, 1);
}
