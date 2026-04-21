// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test that unknown_reason returns correct reason for quantifier-related Unknown
#[test]
fn test_unknown_reason_quantifiers() {
    // Create a formula with quantifiers that will return Unknown
    let smt = r#"
        (set-logic LIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((x Int)) (P x)))
        (assert (not (P 0)))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let _result = exec.execute_all(&commands).unwrap();

    // After check-sat with quantifiers, if result is Unknown, reason should be
    // one of the quantifier sub-reasons (not the generic Incomplete/Unknown).
    if exec.last_result() == Some(SolveResult::Unknown) {
        let reason = exec.unknown_reason();
        assert!(reason.is_some(), "Should have a reason for Unknown result");
        let r = reason.unwrap();
        assert!(
            matches!(
                r,
                UnknownReason::QuantifierRoundLimit
                    | UnknownReason::QuantifierDeferred
                    | UnknownReason::QuantifierUnhandled
                    | UnknownReason::QuantifierCegqiIncomplete
            ),
            "Reason should be a quantifier sub-reason, got: {r:?}"
        );
    }
}
/// Test that unknown_reason returns None when result is SAT or UNSAT
#[test]
fn test_unknown_reason_sat_unsat() {
    // SAT case
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 5))
        (check-sat)
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let _result = exec.execute_all(&commands).unwrap();
    assert_eq!(exec.last_result(), Some(SolveResult::Sat));
    assert!(
        exec.unknown_reason().is_none(),
        "Should be None for SAT result"
    );

    // UNSAT case
    let smt2 = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (and (> x 5) (< x 3)))
        (check-sat)
    "#;
    let commands2 = parse(smt2).unwrap();
    let mut exec2 = Executor::new();
    let _result2 = exec2.execute_all(&commands2).unwrap();
    assert_eq!(exec2.last_result(), Some(SolveResult::Unsat));
    assert!(
        exec2.unknown_reason().is_none(),
        "Should be None for UNSAT result"
    );
}
/// Test that UnknownReason Display formats correctly for SMT-LIB output
#[test]
fn test_unknown_reason_display() {
    assert_eq!(format!("{}", UnknownReason::Timeout), "timeout");
    assert_eq!(format!("{}", UnknownReason::Interrupted), "interrupted");
    assert_eq!(format!("{}", UnknownReason::Incomplete), "incomplete");
    assert_eq!(
        format!("{}", UnknownReason::QuantifierRoundLimit),
        "(incomplete quantifier-round-limit)"
    );
    assert_eq!(
        format!("{}", UnknownReason::QuantifierDeferred),
        "(incomplete quantifier-deferred)"
    );
    assert_eq!(
        format!("{}", UnknownReason::QuantifierUnhandled),
        "(incomplete quantifier-unhandled)"
    );
    assert_eq!(
        format!("{}", UnknownReason::QuantifierCegqiIncomplete),
        "(incomplete quantifier-cegqi)"
    );
    assert_eq!(format!("{}", UnknownReason::SplitLimit), "incomplete");
    assert_eq!(format!("{}", UnknownReason::ResourceLimit), "resourceout");
    assert_eq!(format!("{}", UnknownReason::MemoryLimit), "memout");
    assert_eq!(format!("{}", UnknownReason::Unsupported), "unsupported");
    assert_eq!(format!("{}", UnknownReason::Unknown), "unknown");
}

// ============================================================================
// #5042: Enumerative instantiation fallback for triggerless quantifiers
// ============================================================================
/// Triggerless forall over uninterpreted sort with ground terms: enumerative
/// instantiation should produce x:=a and x:=b, yielding UNSAT from (= b a)
/// contradicting (not (= b a)).
#[test]
fn test_enumerative_instantiation_uninterpreted_sort_5042() {
    let input = r#"
        (declare-sort S 0)
        (declare-fun a () S)
        (declare-fun b () S)
        (assert (forall ((x S)) (= x a)))
        (assert (not (= b a)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}
/// Triggerless forall over uninterpreted sort with no ground terms: should
/// return unknown (enumerative instantiation cannot produce any bindings).
#[test]
fn test_enumerative_instantiation_no_ground_terms_5042() {
    let input = r#"
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (assert (forall ((x U)) (P x)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unknown"]);
}
/// Multi-variable enumerative instantiation: forall x y. x=y with two distinct
/// ground constants should find x:=c1, y:=c2 producing (= c1 c2), contradicting
/// (not (= c1 c2)).
#[test]
fn test_enumerative_instantiation_multi_var_5042() {
    let input = r#"
        (declare-sort T 0)
        (declare-fun c1 () T)
        (declare-fun c2 () T)
        (assert (forall ((x T) (y T)) (= x y)))
        (assert (not (= c1 c2)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}
/// CEGQI with div operator: forall x. (x > 0) => (div x 2) > 0
/// INVALID: x=1 gives div(1,2)=0, not > 0.
/// Expected: unsat (asserting an invalid forall).
///
/// The key challenge is that `pv` appears under `(div pv 2)`, so bound extraction
/// fails for that assertion. CEGQI must rely on:
/// 1. The `x > 0` bound (tightened to `x >= 1` for integers) for selection
/// 2. The model-value fallback or neighbor enumeration to find x=1
///
/// (#5888: div/mod in quantified formulas is a key certus pattern)
#[test]
fn test_cegqi_div_counterexample_5888() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::time::Duration;

    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (> x 0)
                (> (div x 2) 0))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();

    // Set a 15s timeout to prevent debug-mode hangs (#6889).
    // The CEGQI div/mod refinement loop can diverge in debug builds
    // where each LIA solve iteration is much slower.
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&interrupt));
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(15));
        timer_interrupt.store(true, Ordering::Relaxed);
    });

    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let () = interrupt.store(true, Ordering::Relaxed); // cancel timer
    let _ = timer.join();

    // INVALID formula — x=1 is a counterexample. Should be UNSAT.
    // Currently returns "unknown" due to CEGQI div/mod incompleteness gap
    // (see #5888). Accepting "unsat" (complete) or "unknown" (sound-but-incomplete).
    // "sat" would be unsound — the formula is invalid.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "Must not return sat — formula is invalid (x=1 counterexample). Got: {outputs:?}",
    );
}
/// Diagnostic test for #6045: 13-chain E-matching budget exhaustion.
///
/// Z3 returns UNSAT on this formula. Z4 should return either UNSAT (if
/// all 13 instantiation rounds complete) or UNKNOWN (if budget is exhausted).
/// Returning SAT is unsound.
///
/// This test inspects `last_result()` and `unknown_reason()` to determine
/// whether the SAT-to-Unknown guard in `map_quantifier_result` fired.
#[test]
fn test_6045_13chain_ematching_budget_must_not_return_sat() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P0 (Int) Bool)
        (declare-fun P1 (Int) Bool)
        (declare-fun P2 (Int) Bool)
        (declare-fun P3 (Int) Bool)
        (declare-fun P4 (Int) Bool)
        (declare-fun P5 (Int) Bool)
        (declare-fun P6 (Int) Bool)
        (declare-fun P7 (Int) Bool)
        (declare-fun P8 (Int) Bool)
        (declare-fun P9 (Int) Bool)
        (declare-fun P10 (Int) Bool)
        (declare-fun P11 (Int) Bool)
        (declare-fun P12 (Int) Bool)
        (assert (forall ((x Int)) (! (=> (P0 x) (P1 x)) :pattern ((P0 x)))))
        (assert (forall ((x Int)) (! (=> (P1 x) (P2 x)) :pattern ((P1 x)))))
        (assert (forall ((x Int)) (! (=> (P2 x) (P3 x)) :pattern ((P2 x)))))
        (assert (forall ((x Int)) (! (=> (P3 x) (P4 x)) :pattern ((P3 x)))))
        (assert (forall ((x Int)) (! (=> (P4 x) (P5 x)) :pattern ((P4 x)))))
        (assert (forall ((x Int)) (! (=> (P5 x) (P6 x)) :pattern ((P5 x)))))
        (assert (forall ((x Int)) (! (=> (P6 x) (P7 x)) :pattern ((P6 x)))))
        (assert (forall ((x Int)) (! (=> (P7 x) (P8 x)) :pattern ((P7 x)))))
        (assert (forall ((x Int)) (! (=> (P8 x) (P9 x)) :pattern ((P8 x)))))
        (assert (forall ((x Int)) (! (=> (P9 x) (P10 x)) :pattern ((P9 x)))))
        (assert (forall ((x Int)) (! (=> (P10 x) (P11 x)) :pattern ((P10 x)))))
        (assert (forall ((x Int)) (! (=> (P11 x) (P12 x)) :pattern ((P11 x)))))
        (assert (forall ((x Int)) (! (=> (P12 x) false) :pattern ((P12 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    let result = exec.last_result();
    let reason = exec.unknown_reason();

    let assertion_count = exec.context().assertions.len();

    // SAT is unsound: Z3 confirms this is UNSAT.
    // Acceptable: UNSAT (correct) or UNKNOWN (conservative).
    assert_ne!(
        outputs,
        vec!["sat"],
        "BUG #6045: returning SAT on an UNSAT formula is unsound.\n\
         last_result={result:?}, reason_unknown={reason:?}, assertions={assertion_count}"
    );
}
