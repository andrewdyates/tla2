// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Liveness pattern verdict parity tests for #1518.
//!
//! Exercises the five core temporal property patterns against the model checker
//! and verifies that TLA2 produces the correct verdict for each:
//!   - `[]<>P` (always eventually)
//!   - `<>[]P` (eventually always)
//!   - `P ~> Q` (leads-to)
//!   - `WF_x(A)` (weak fairness)
//!   - `SF_x(A)` (strong fairness)
//!
//! Expected verdicts are validated against TLC runs documented in
//! `reports/research/issue-1518-liveness-patterns-matrix.md`.
//!
//! The 16-state tests exercise a two-variable spec (counter × phase) with
//! multiple temporal properties and both WF and SF fairness constraints,
//! covering the Prover-requested >10-state threshold.

use tla_check::Config;
use tla_check::{resolve_spec_from_config, CheckResult};
use tla_core::{lower, parse_to_syntax_tree, FileId};

mod common;

/// Helper: parse, resolve, and check a spec with a SPECIFICATION/PROPERTY config.
fn check_liveness_spec(src: &str, property: &str) -> CheckResult {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("module lowering should succeed");

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved =
        resolve_spec_from_config(&spec_config, &tree).expect("spec resolution should succeed");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec![property.to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.check()
}

/// `[]<>P` with WF: x toggles 0↔1. WF ensures Next fires, so x=1 recurs.
/// Expected: PASS (TLC: 2 states, no error).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_pattern_always_eventually_pass() {
    let src = r#"
---- MODULE AlwaysEventually ----
EXTENDS Integers

VARIABLE x

Init ==
    x = 0

Next ==
    \/ /\ x = 0
       /\ x' = 1
    \/ /\ x = 1
       /\ x' = 0

Spec ==
    Init /\ [][Next]_x /\ WF_x(Next)

P ==
    x = 1

Live ==
    []<>P

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 2, "expected 2 states (x=0, x=1)");
        }
        other => panic!("expected Success for []<>P with WF, got: {other:?}"),
    }
}

/// `<>[]P` without stable fixpoint: x nondeterministically picks from {0,1}.
/// WF ensures Next fires, but x can always flip back — never stabilizes at 1.
/// Expected: FAIL with liveness violation (TLC: 2 states, liveness error).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_pattern_eventually_always_fail() {
    let src = r#"
---- MODULE EventuallyAlways ----
EXTENDS Integers

VARIABLE x

Init ==
    x = 0

Next ==
    x' \in {0, 1}

Spec ==
    Init /\ [][Next]_x /\ WF_x(Next)

Stable ==
    x = 1

Live ==
    <>[]Stable

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::LivenessViolation { .. } => {
            // Correct: x can always flip back, so <>[]Stable is violated.
        }
        CheckResult::Success(_) => {
            panic!(
                "expected LivenessViolation for <>[]Stable with nondeterministic toggle, \
                 got Success — liveness checker may be missing a cycle"
            );
        }
        other => panic!("expected LivenessViolation for <>[]Stable, got: {other:?}"),
    }
}

/// `P ~> Q` with deterministic toggle: x flips 0→1→0→1...
/// WF ensures Next fires. From x=0 (P), fairness forces x→1 (Q).
/// Expected: PASS (TLC: 2 states, no error).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_pattern_leads_to_pass() {
    let src = r#"
---- MODULE LeadsTo ----
EXTENDS Integers

VARIABLE x

Init ==
    x = 0

Next ==
    x' = 1 - x

Spec ==
    Init /\ [][Next]_x /\ WF_x(Next)

P ==
    x = 0

Q ==
    x = 1

Live ==
    P ~> Q

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 2, "expected 2 states (x=0, x=1)");
        }
        other => panic!("expected Success for P ~> Q with deterministic toggle, got: {other:?}"),
    }
}

/// `WF_x(Act)` with competing stuttering: Act moves x 0→1, but Next also
/// allows stuttering at x=0 and x=1. WF ensures Act fires when continuously
/// enabled, so `[]<>Done` (x=1) holds.
/// Expected: PASS (TLC: 2 states, no error).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_pattern_weak_fairness_pass() {
    let src = r#"
---- MODULE WeakFairness ----
EXTENDS Integers

VARIABLE x

Act ==
    /\ x = 0
    /\ x' = 1

Init ==
    x = 0

Next ==
    \/ Act
    \/ /\ x = 0
       /\ x' = 0
    \/ /\ x = 1
       /\ x' = 1

Spec ==
    Init /\ [][Next]_x /\ WF_x(Act)

Done ==
    x = 1

Live ==
    []<>Done

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 2, "expected 2 states (x=0, x=1)");
        }
        other => panic!("expected Success for []<>Done with WF_x(Act), got: {other:?}"),
    }
}

/// `SF_Vars(Commit)`: pc toggles 0↔1, Commit requires pc=0 ∧ done=FALSE.
/// Tick can disable Commit by flipping pc to 1, but SF ensures Commit fires
/// whenever it is infinitely often enabled. So done eventually becomes TRUE.
/// Expected: PASS (TLC: 4 states, no error).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_pattern_strong_fairness_pass() {
    let src = r#"
---- MODULE StrongFairness ----
EXTENDS Integers

VARIABLES pc, done

Vars ==
    <<pc, done>>

Init ==
    /\ pc = 0
    /\ done = FALSE

Tick ==
    /\ pc' = 1 - pc
    /\ done' = done

Commit ==
    /\ done = FALSE
    /\ pc = 0
    /\ pc' = 1
    /\ done' = TRUE

StutterDone ==
    /\ done = TRUE
    /\ pc' = pc
    /\ done' = done

Next ==
    \/ Commit
    \/ Tick
    \/ StutterDone

Spec ==
    Init /\ [][Next]_Vars /\ WF_Vars(Next) /\ SF_Vars(Commit)

Live ==
    []<>(done = TRUE)

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4, "expected 4 states");
        }
        other => {
            panic!("expected Success for []<>(done=TRUE) with SF_Vars(Commit), got: {other:?}")
        }
    }
}

/// Helper: parse, resolve, and check a spec with multiple PROPERTY entries.
fn check_liveness_spec_multi(src: &str, properties: &[&str]) -> CheckResult {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("module lowering should succeed");

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved =
        resolve_spec_from_config(&spec_config, &tree).expect("spec resolution should succeed");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: properties.iter().map(|s| (*s).to_string()).collect(),
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.check()
}

/// Shared source for the 16-state counter×phase spec.
///
/// State space: counter ∈ {0,1,2,3} × phase ∈ {0,1,2,3} = 16 states.
/// - `Advance`: counter' = (counter + 1) % 4, UNCHANGED phase
/// - `Shift`:   phase'  = (phase  + 1) % 4, UNCHANGED counter
/// - `WF_Vars(Advance)` ∧ `WF_Vars(Shift)` — both actions fire infinitely often.
///
/// PASS properties:
/// - `AlwaysEventuallyZero`: `[]<>(counter = 0)` — counter cycles, recurs at 0.
/// - `ThreeLeadsToZero`:     `(counter = 3) ~> (counter = 0)` — WF forces next step.
///
/// FAIL property:
/// - `PhaseStabilizes`: `<>[](phase = 3)` — phase cycles forever, never stabilizes.
const COUNTER_PHASE_SRC: &str = r#"
---- MODULE CounterPhase ----
EXTENDS Integers

VARIABLES counter, phase

Vars ==
    <<counter, phase>>

Init ==
    /\ counter = 0
    /\ phase = 0

Advance ==
    /\ counter' = (counter + 1) % 4
    /\ phase' = phase

Shift ==
    /\ phase' = (phase + 1) % 4
    /\ counter' = counter

Next ==
    \/ Advance
    \/ Shift

Spec ==
    Init /\ [][Next]_Vars /\ WF_Vars(Advance) /\ WF_Vars(Shift)

AlwaysEventuallyZero ==
    []<>(counter = 0)

ThreeLeadsToZero ==
    (counter = 3) ~> (counter = 0)

PhaseStabilizes ==
    <>[](phase = 3)

====
"#;

/// 16-state spec, PASS property `[]<>(counter = 0)`.
/// WF_Vars(Advance) forces counter to cycle 0→1→2→3→0..., so counter=0 recurs.
/// Expected: PASS (TLC: 16 states, no error).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_16_state_always_eventually_zero_pass() {
    let result = check_liveness_spec(COUNTER_PHASE_SRC, "AlwaysEventuallyZero");
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 16,
                "expected 16 states (4 counter × 4 phase)"
            );
        }
        other => {
            panic!("expected Success for []<>(counter=0) with WF on 16-state spec, got: {other:?}")
        }
    }
}

/// 16-state spec, PASS property `(counter = 3) ~> (counter = 0)`.
/// From any state with counter=3, WF_Vars(Advance) forces Advance to fire,
/// setting counter to 0.
/// Expected: PASS (TLC: 16 states, no error).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_16_state_leads_to_zero_pass() {
    let result = check_liveness_spec(COUNTER_PHASE_SRC, "ThreeLeadsToZero");
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 16,
                "expected 16 states (4 counter × 4 phase)"
            );
        }
        other => panic!(
            "expected Success for (counter=3)~>(counter=0) with WF on 16-state spec, got: {other:?}"
        ),
    }
}

/// 16-state spec, FAIL property `<>[](phase = 3)`.
/// WF_Vars(Shift) forces phase to cycle 0→1→2→3→0..., so phase never stabilizes
/// at 3. The liveness checker must find a cycle where phase keeps changing.
/// Expected: FAIL with liveness violation (TLC: 16 states, liveness error).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_16_state_phase_stabilizes_fail() {
    let result = check_liveness_spec(COUNTER_PHASE_SRC, "PhaseStabilizes");
    match &result {
        CheckResult::LivenessViolation { property, .. } => {
            assert_eq!(
                property, "PhaseStabilizes",
                "wrong property name in violation"
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "expected LivenessViolation for <>[](phase=3) with WF cycling, \
                 got Success — liveness checker may be missing a cycle through phase values"
            );
        }
        other => {
            panic!("expected LivenessViolation for <>[](phase=3) on 16-state spec, got: {other:?}")
        }
    }
}

/// Multi-property iteration: PASS properties listed before a FAIL property.
/// The checker iterates properties in order and stops at the first violation.
/// With [AlwaysEventuallyZero, ThreeLeadsToZero, PhaseStabilizes], the first
/// two pass and the third fails, so the reported violation is PhaseStabilizes.
/// Expected: FAIL with liveness violation on PhaseStabilizes.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn liveness_multi_property_stops_at_first_violation() {
    let result = check_liveness_spec_multi(
        COUNTER_PHASE_SRC,
        &[
            "AlwaysEventuallyZero",
            "ThreeLeadsToZero",
            "PhaseStabilizes",
        ],
    );
    match &result {
        CheckResult::LivenessViolation { property, .. } => {
            assert_eq!(
                property, "PhaseStabilizes",
                "checker should pass the first two properties and report violation on the third"
            );
        }
        CheckResult::Success(_) => {
            panic!(
                "expected LivenessViolation on PhaseStabilizes when checking 3 properties, \
                 got Success — multi-property iteration may be skipping properties"
            );
        }
        other => panic!("expected LivenessViolation for multi-property check, got: {other:?}"),
    }
}
