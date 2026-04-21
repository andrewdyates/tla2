// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for merge_worker_outcome (Part of #1433 Step 4).

use super::super::terminal_outcome::{merge_worker_outcome, TerminalOutcome};
use crate::check::{CheckError, LimitType};
use crate::state::Fingerprint;
use crate::ConfigCheckError;

fn make_error() -> TerminalOutcome {
    TerminalOutcome::Error(ConfigCheckError::MissingNext.into())
}

fn make_violation() -> TerminalOutcome {
    TerminalOutcome::Violation {
        invariant: "Inv".to_string(),
        state_fp: Fingerprint(1),
    }
}

fn make_deadlock() -> TerminalOutcome {
    TerminalOutcome::Deadlock {
        state_fp: Fingerprint(2),
    }
}

fn make_limit() -> TerminalOutcome {
    TerminalOutcome::Limit(LimitType::States)
}

fn is_error(o: &TerminalOutcome) -> bool {
    matches!(o, TerminalOutcome::Error(_))
}

fn is_violation(o: &TerminalOutcome) -> bool {
    matches!(o, TerminalOutcome::Violation { .. })
}

fn is_deadlock(o: &TerminalOutcome) -> bool {
    matches!(o, TerminalOutcome::Deadlock { .. })
}

fn is_limit(o: &TerminalOutcome) -> bool {
    matches!(o, TerminalOutcome::Limit(_))
}

#[test]
fn test_merge_error_wins_over_violation() {
    let result = merge_worker_outcome(make_violation(), make_error());
    assert!(is_error(&result), "Error must win over Violation");
}

#[test]
fn test_merge_error_wins_over_deadlock() {
    let result = merge_worker_outcome(make_deadlock(), make_error());
    assert!(is_error(&result), "Error must win over Deadlock");
}

#[test]
fn test_merge_error_wins_over_limit() {
    let result = merge_worker_outcome(make_limit(), make_error());
    assert!(is_error(&result), "Error must win over Limit");
}

#[test]
fn test_merge_violation_wins_over_deadlock() {
    let result = merge_worker_outcome(make_deadlock(), make_violation());
    assert!(is_violation(&result), "Violation must win over Deadlock");
}

#[test]
fn test_merge_violation_wins_over_limit() {
    let result = merge_worker_outcome(make_limit(), make_violation());
    assert!(is_violation(&result), "Violation must win over Limit");
}

#[test]
fn test_merge_deadlock_wins_over_limit() {
    let result = merge_worker_outcome(make_limit(), make_deadlock());
    assert!(is_deadlock(&result), "Deadlock must win over Limit");
}

#[test]
fn test_merge_keeps_current_at_same_precedence() {
    // When both are the same level, current is kept (first-writer wins)
    let result = merge_worker_outcome(
        TerminalOutcome::Violation {
            invariant: "First".to_string(),
            state_fp: Fingerprint(10),
        },
        TerminalOutcome::Violation {
            invariant: "Second".to_string(),
            state_fp: Fingerprint(20),
        },
    );
    match result {
        TerminalOutcome::Violation { invariant, .. } => {
            assert_eq!(invariant, "First", "First violation must be kept");
        }
        other => panic!("Expected Violation, got: {other:?}"),
    }
}

#[test]
fn test_merge_error_not_replaced_by_violation() {
    let result = merge_worker_outcome(make_error(), make_violation());
    assert!(
        is_error(&result),
        "Existing Error must not be replaced by incoming Violation"
    );
}

#[test]
fn test_merge_violation_not_replaced_by_deadlock() {
    let result = merge_worker_outcome(make_violation(), make_deadlock());
    assert!(
        is_violation(&result),
        "Existing Violation must not be replaced by incoming Deadlock"
    );
}

#[test]
fn test_merge_deadlock_not_replaced_by_limit() {
    let result = merge_worker_outcome(make_deadlock(), make_limit());
    assert!(
        is_deadlock(&result),
        "Existing Deadlock must not be replaced by incoming Limit"
    );
}

#[test]
fn test_merge_limit_not_replaced_by_same() {
    let result = merge_worker_outcome(
        TerminalOutcome::Limit(LimitType::States),
        TerminalOutcome::Limit(LimitType::Exit),
    );
    match result {
        TerminalOutcome::Limit(LimitType::States) => {}
        other => panic!("Expected Limit(States) kept, got: {other:?}"),
    }
}

/// Verify the full 4-way chain: Error > Violation > Deadlock > Limit.
/// Start with Limit, then merge each higher-precedence outcome sequentially.
#[test]
fn test_merge_full_precedence_chain() {
    let mut current = make_limit();
    assert!(is_limit(&current));

    current = merge_worker_outcome(current, make_deadlock());
    assert!(is_deadlock(&current), "Deadlock must replace Limit");

    current = merge_worker_outcome(current, make_violation());
    assert!(is_violation(&current), "Violation must replace Deadlock");

    current = merge_worker_outcome(current, make_error());
    assert!(is_error(&current), "Error must replace Violation");
}

// --- Non-adjacent reverse pairs (Re: #1433 audit) ---
// Tests 8-10 cover adjacent reverse pairs. These cover the remaining
// 3 non-adjacent reverse pairs to complete all C(4,2)=6 reverse cases.

#[test]
fn test_merge_error_not_replaced_by_deadlock() {
    let result = merge_worker_outcome(make_error(), make_deadlock());
    assert!(
        is_error(&result),
        "Existing Error must not be replaced by incoming Deadlock"
    );
}

#[test]
fn test_merge_error_not_replaced_by_limit() {
    let result = merge_worker_outcome(make_error(), make_limit());
    assert!(
        is_error(&result),
        "Existing Error must not be replaced by incoming Limit"
    );
}

#[test]
fn test_merge_violation_not_replaced_by_limit() {
    let result = merge_worker_outcome(make_violation(), make_limit());
    assert!(
        is_violation(&result),
        "Existing Violation must not be replaced by incoming Limit"
    );
}

// --- Same-level first-writer-wins for all 4 variants (Re: #1433 audit) ---
// Tests 7 and 11 cover Violation and Limit. These cover Error and Deadlock.

#[test]
fn test_merge_error_keeps_first_at_same_level() {
    let result = merge_worker_outcome(
        TerminalOutcome::Error(ConfigCheckError::MissingNext.into()),
        TerminalOutcome::Error(ConfigCheckError::MissingInit.into()),
    );
    match result {
        TerminalOutcome::Error(CheckError::Config(ConfigCheckError::MissingNext)) => {}
        other => panic!("Expected Error(MissingNext) kept, got: {other:?}"),
    }
}

#[test]
fn test_merge_deadlock_keeps_first_at_same_level() {
    let result = merge_worker_outcome(
        TerminalOutcome::Deadlock {
            state_fp: Fingerprint(100),
        },
        TerminalOutcome::Deadlock {
            state_fp: Fingerprint(200),
        },
    );
    match result {
        TerminalOutcome::Deadlock { state_fp } => {
            assert_eq!(state_fp, Fingerprint(100), "First deadlock must be kept");
        }
        other => panic!("Expected Deadlock(fp=100) kept, got: {other:?}"),
    }
}
