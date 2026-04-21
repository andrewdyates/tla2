// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Basic checker_ops utility tests: depth mapping, storage errors,
//! state slot reservation, and invariant checking.

use super::*;
use crate::EvalCheckError;
use tla_core::ast::Expr;
use tla_core::Spanned;

#[test]
fn depth_to_tlc_level_maps_zero_based_depths() {
    assert_eq!(depth_to_tlc_level(0).unwrap(), 1);
    assert_eq!(depth_to_tlc_level(1).unwrap(), 2);
    assert_eq!(depth_to_tlc_level(100).unwrap(), 101);
    assert_eq!(
        depth_to_tlc_level((u32::MAX - 1) as usize).unwrap(),
        u32::MAX
    );
}

#[test]
fn depth_to_tlc_level_reports_overflow_instead_of_panicking() {
    // u32::MAX as depth would need level u32::MAX + 1 which overflows u32
    let result = depth_to_tlc_level(u32::MAX as usize);
    assert!(result.is_err());
    let err = result.unwrap_err();
    match err {
        CheckError::Config(ConfigCheckError::Setup(msg)) => {
            assert!(
                msg.contains("exceeds TLC level range"),
                "unexpected message: {}",
                msg
            );
        }
        _ => panic!("expected SetupError, got {:?}", err),
    }
}

#[test]
fn depth_to_tlc_level_overflow_on_usize_max() {
    let result = depth_to_tlc_level(usize::MAX);
    assert!(result.is_err());
}

#[test]
fn storage_fault_to_check_error_floors_dropped_to_one() {
    use crate::state::Fingerprint;
    use crate::InfraCheckError;
    // DashSet<Fingerprint> implements FingerprintSet with dropped_count() == 0.
    let fps = dashmap::DashSet::<Fingerprint>::new();
    // A fresh set has dropped_count() == 0, but the floor ensures dropped >= 1.
    let fault = StorageFault::new("test", "insert", "simulated fault");
    let err = storage_fault_to_check_error(&fps, &fault);
    match err {
        CheckError::Infra(InfraCheckError::FingerprintOverflow {
            dropped,
            ref detail,
        }) => {
            assert!(
                dropped >= 1,
                "dropped should be floored to 1, got {}",
                dropped
            );
            assert!(
                detail.contains("simulated fault"),
                "detail should include fault info, got: {detail}",
            );
        }
        _ => panic!("expected FingerprintStorageOverflow, got {:?}", err),
    }
}

/// Minimal FingerprintSet stub for testing error paths without I/O.
struct ErrorFpSet {
    has_errors: bool,
    dropped: usize,
}

impl tla_mc_core::FingerprintSet<crate::state::Fingerprint> for ErrorFpSet {
    fn insert_checked(&self, _fp: crate::state::Fingerprint) -> crate::storage::InsertOutcome {
        crate::storage::InsertOutcome::Inserted
    }
    fn contains_checked(&self, _fp: crate::state::Fingerprint) -> crate::storage::LookupOutcome {
        crate::storage::LookupOutcome::Absent
    }
    fn len(&self) -> usize {
        0
    }
    fn has_errors(&self) -> bool {
        self.has_errors
    }
    fn dropped_count(&self) -> usize {
        self.dropped
    }
}

impl FingerprintSet for ErrorFpSet {}

#[test]
fn check_fingerprint_errors_returns_none_when_no_errors() {
    let fps = ErrorFpSet {
        has_errors: false,
        dropped: 0,
    };
    assert!(check_fingerprint_errors(&fps).is_none());
}

#[test]
fn check_fingerprint_errors_returns_error_with_floor() {
    // has_errors is true but dropped_count is 0 — floor should yield dropped=1
    let fps = ErrorFpSet {
        has_errors: true,
        dropped: 0,
    };
    match check_fingerprint_errors(&fps) {
        Some(CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. })) => {
            assert_eq!(dropped, 1, "floor should set dropped to 1");
        }
        other => panic!("expected Some(FingerprintStorageOverflow), got {:?}", other),
    }
}

#[test]
fn check_fingerprint_errors_preserves_nonzero_dropped() {
    let fps = ErrorFpSet {
        has_errors: true,
        dropped: 42,
    };
    match check_fingerprint_errors(&fps) {
        Some(CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. })) => {
            assert_eq!(dropped, 42, "nonzero dropped should pass through");
        }
        other => panic!("expected Some(FingerprintStorageOverflow), got {:?}", other),
    }
}

#[test]
fn try_reserve_respects_limit() {
    let counter = AtomicUsize::new(0);
    assert!(try_reserve_state_slot(&counter, 3));
    assert!(try_reserve_state_slot(&counter, 3));
    assert!(try_reserve_state_slot(&counter, 3));
    assert!(!try_reserve_state_slot(&counter, 3));
    assert_eq!(counter.load(Ordering::Relaxed), 3);
}

#[test]
fn release_enables_subsequent_reserve() {
    let counter = AtomicUsize::new(0);
    assert!(try_reserve_state_slot(&counter, 1));
    assert!(!try_reserve_state_slot(&counter, 1));
    release_state_slot(&counter);
    assert!(try_reserve_state_slot(&counter, 1));
    assert_eq!(counter.load(Ordering::Relaxed), 1);
}

#[test]
fn try_reserve_at_limit_returns_false() {
    let counter = AtomicUsize::new(5);
    assert!(!try_reserve_state_slot(&counter, 5));
    assert!(!try_reserve_state_slot(&counter, 3));
}

// Part of #3354 Slice 4: compiled invariant tests removed (compiled_guard module deleted).
// Tests that used CompiledGuard::True/False are no longer applicable since invariant
// evaluation now routes exclusively through eval_op (name-based).

#[test]
fn check_invariants_array_state_empty_list_passes() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let result = check_invariants_array_state(&mut ctx, &[], &array_state)
        .expect("empty invariant list should pass");
    assert_eq!(result, None);
}

#[test]
fn check_invariants_array_state_unknown_op_is_eval_error() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let invariants = vec!["MissingInvariant".to_string()];

    let result = check_invariants_array_state(&mut ctx, &invariants, &array_state);
    assert!(
        matches!(result, Err(CheckError::Eval(EvalCheckError::Eval(_)))),
        "expected EvalError for unknown invariant operator, got {result:?}"
    );
}

#[test]
fn check_invariants_for_successor_empty_invariants_returns_ok() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let fp = Fingerprint(42);
    let outcome = check_invariants_for_successor(&mut ctx, &[], &[], &array_state, fp, 1);
    assert!(matches!(outcome, InvariantOutcome::Ok));
}

#[test]
fn check_invariants_for_successor_eval_error_returns_error() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let fp = Fingerprint(0);
    let invariants = vec!["NonexistentOp".to_string()];
    let outcome = check_invariants_for_successor(&mut ctx, &invariants, &[], &array_state, fp, 1);
    assert!(matches!(outcome, InvariantOutcome::Error(_)));
}

// === Part of #3469: Replay-loop boundary tests ===
//
// These tests exercise the same-state replay boundary behavior inside
// check_property_init_predicates and check_eval_state_invariants, ensuring
// that clear_for_state_eval_replay is called between iterations and that
// multiple expressions in the same call don't share stale cache state.

#[test]
fn check_property_init_predicates_empty_list_passes() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let result = check_property_init_predicates(&mut ctx, &[], &array_state)
        .expect("empty predicate list should pass");
    assert_eq!(result, None);
}

#[test]
fn check_eval_state_invariants_empty_list_passes() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let result = check_eval_state_invariants(&mut ctx, &[], &array_state)
        .expect("empty eval invariant list should pass");
    assert_eq!(result, None);
}

#[test]
fn check_property_init_predicates_true_expr_passes() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let preds = vec![("TrueProp".to_string(), Spanned::dummy(Expr::Bool(true)))];
    let result = check_property_init_predicates(&mut ctx, &preds, &array_state)
        .expect("TRUE predicate should not error");
    assert_eq!(result, None, "TRUE predicate should pass");
}

#[test]
fn check_property_init_predicates_false_expr_returns_violation() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let preds = vec![("FalseProp".to_string(), Spanned::dummy(Expr::Bool(false)))];
    let result = check_property_init_predicates(&mut ctx, &preds, &array_state)
        .expect("FALSE predicate should not error");
    assert_eq!(
        result,
        Some("FalseProp".to_string()),
        "FALSE predicate should return violation"
    );
}

/// Part of #3469: Multiple init predicates exercise the replay loop.
/// Each predicate gets a fresh cache boundary via clear_for_state_eval_replay.
#[test]
fn check_property_init_predicates_multiple_true_all_pass() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let preds = vec![
        ("Pred1".to_string(), Spanned::dummy(Expr::Bool(true))),
        ("Pred2".to_string(), Spanned::dummy(Expr::Bool(true))),
        ("Pred3".to_string(), Spanned::dummy(Expr::Bool(true))),
    ];
    let result = check_property_init_predicates(&mut ctx, &preds, &array_state)
        .expect("all TRUE predicates should not error");
    assert_eq!(result, None, "all TRUE predicates should pass");
}

/// Part of #3469: The loop short-circuits on first FALSE — verify which one.
#[test]
fn check_property_init_predicates_mixed_returns_first_violation() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let preds = vec![
        ("PassPred".to_string(), Spanned::dummy(Expr::Bool(true))),
        ("FailPred".to_string(), Spanned::dummy(Expr::Bool(false))),
        ("NeverReached".to_string(), Spanned::dummy(Expr::Bool(true))),
    ];
    let result =
        check_property_init_predicates(&mut ctx, &preds, &array_state).expect("should not error");
    assert_eq!(
        result,
        Some("FailPred".to_string()),
        "should return the first failing predicate"
    );
}

#[test]
fn check_eval_state_invariants_true_expr_passes() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let invs = vec![("TrueInv".to_string(), Spanned::dummy(Expr::Bool(true)))];
    let result = check_eval_state_invariants(&mut ctx, &invs, &array_state)
        .expect("TRUE invariant should not error");
    assert_eq!(result, None, "TRUE invariant should pass");
}

#[test]
fn check_eval_state_invariants_false_expr_returns_violation() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let invs = vec![("FalseInv".to_string(), Spanned::dummy(Expr::Bool(false)))];
    let result = check_eval_state_invariants(&mut ctx, &invs, &array_state)
        .expect("FALSE invariant should not error");
    assert_eq!(
        result,
        Some("FalseInv".to_string()),
        "FALSE invariant should return violation"
    );
}

/// Part of #3469: Multiple eval state invariants exercise the replay loop.
#[test]
fn check_eval_state_invariants_multiple_true_all_pass() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let invs = vec![
        ("Inv1".to_string(), Spanned::dummy(Expr::Bool(true))),
        ("Inv2".to_string(), Spanned::dummy(Expr::Bool(true))),
        ("Inv3".to_string(), Spanned::dummy(Expr::Bool(true))),
    ];
    let result = check_eval_state_invariants(&mut ctx, &invs, &array_state)
        .expect("all TRUE invariants should not error");
    assert_eq!(result, None, "all TRUE invariants should pass");
}

/// Part of #3469: Mixed eval state invariants — first FALSE short-circuits.
#[test]
fn check_eval_state_invariants_mixed_returns_first_violation() {
    let mut ctx = EvalCtx::new();
    let array_state = ArrayState::from_values(vec![]);
    let invs = vec![
        ("PassInv".to_string(), Spanned::dummy(Expr::Bool(true))),
        ("FailInv".to_string(), Spanned::dummy(Expr::Bool(false))),
        ("NeverReached".to_string(), Spanned::dummy(Expr::Bool(true))),
    ];
    let result =
        check_eval_state_invariants(&mut ctx, &invs, &array_state).expect("should not error");
    assert_eq!(
        result,
        Some("FailInv".to_string()),
        "should return the first failing invariant"
    );
}

/// Part of #3469: Replay loop with operator-based invariants via parsed TLA+.
/// Verifies that check_invariants_array_state works with multiple operators
/// that all return TRUE.
#[test]
fn check_invariants_array_state_multiple_ops_via_parsed_tla() {
    let src = r#"
---- MODULE TestInv ----
VARIABLE x
Inv1 == TRUE
Inv2 == TRUE
Inv3 == TRUE
===="#;
    let (_, mut ctx, _) = setup_for_classification(src);
    let array_state = ArrayState::from_values(vec![crate::Value::int(1)]);
    let invariants = vec!["Inv1".to_string(), "Inv2".to_string(), "Inv3".to_string()];
    let result = check_invariants_array_state(&mut ctx, &invariants, &array_state)
        .expect("all TRUE invariants should not error");
    assert_eq!(result, None, "all TRUE operators should pass");
}

/// Part of #3469: Replay loop with a FALSE invariant returns the violating name.
#[test]
fn check_invariants_array_state_false_op_returns_violation() {
    let src = r#"
---- MODULE TestInvFail ----
VARIABLE x
GoodInv == TRUE
BadInv == FALSE
===="#;
    let (_, mut ctx, _) = setup_for_classification(src);
    let array_state = ArrayState::from_values(vec![crate::Value::int(1)]);
    let invariants = vec!["GoodInv".to_string(), "BadInv".to_string()];
    let result = check_invariants_array_state(&mut ctx, &invariants, &array_state)
        .expect("should not error on FALSE invariant");
    assert_eq!(
        result,
        Some("BadInv".to_string()),
        "should return the FALSE invariant name"
    );
}
