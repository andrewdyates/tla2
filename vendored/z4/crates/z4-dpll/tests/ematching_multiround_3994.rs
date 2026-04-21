// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for #3994: multi-round E-matching must chain instantiations.

use ntest::timeout;
mod common;

/// Round 1:
///   forall x. P(x) => Q(f(x)) with P(0) produces Q(f(0)).
/// Round 2:
///   forall y. Q(y) => false uses Q(f(0)) to derive contradiction.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_chained_trigger_unsat_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int))
            (! (=> (P x) (Q (f x)))
               :pattern ((P x)))))
        (assert (forall ((y Int))
            (! (=> (Q y) false)
               :pattern ((Q y)))))
        (assert (P 0))
        (check-sat)
    "#;

    let outputs = common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Exactly 3 rounds are required:
/// Round 1: P(0) -> Q(0)
/// Round 2: Q(0) -> R(0)
/// Round 3: R(0) -> false
#[test]
#[timeout(60000)]
fn test_multiround_ematching_round_budget_boundary_unsat_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun R (Int) Bool)
        (assert (forall ((x Int))
            (! (=> (P x) (Q x))
               :pattern ((P x)))))
        (assert (forall ((x Int))
            (! (=> (Q x) (R x))
               :pattern ((Q x)))))
        (assert (forall ((x Int))
            (! (=> (R x) false)
               :pattern ((R x)))))
        (assert (P 0))
        (check-sat)
    "#;

    let outputs = common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// 4 rounds are required:
/// Round 1: P(0) -> Q(0)
/// Round 2: Q(0) -> R(0)
/// Round 3: R(0) -> S(0)
/// Round 4: S(0) -> false
///
/// With `MAX_EMATCHING_ROUNDS = 8`, this now resolves to unsat.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_4chain_unsat_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun R (Int) Bool)
        (declare-fun S (Int) Bool)
        (assert (forall ((x Int))
            (! (=> (P x) (Q x))
               :pattern ((P x)))))
        (assert (forall ((x Int))
            (! (=> (Q x) (R x))
               :pattern ((Q x)))))
        (assert (forall ((x Int))
            (! (=> (R x) (S x))
               :pattern ((R x)))))
        (assert (forall ((x Int))
            (! (=> (S x) false)
               :pattern ((S x)))))
        (assert (P 0))
        (check-sat)
    "#;

    let outputs = common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// 8 rounds required (exactly `MAX_EMATCHING_ROUNDS = 8`):
/// P0(0) -> P1(0) -> ... -> P7(0) -> false
///
/// This is the boundary case: the deepest chain that resolves within budget.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_8chain_boundary_unsat_3994() {
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
        (assert (forall ((x Int)) (! (=> (P0 x) (P1 x)) :pattern ((P0 x)))))
        (assert (forall ((x Int)) (! (=> (P1 x) (P2 x)) :pattern ((P1 x)))))
        (assert (forall ((x Int)) (! (=> (P2 x) (P3 x)) :pattern ((P2 x)))))
        (assert (forall ((x Int)) (! (=> (P3 x) (P4 x)) :pattern ((P3 x)))))
        (assert (forall ((x Int)) (! (=> (P4 x) (P5 x)) :pattern ((P4 x)))))
        (assert (forall ((x Int)) (! (=> (P5 x) (P6 x)) :pattern ((P5 x)))))
        (assert (forall ((x Int)) (! (=> (P6 x) (P7 x)) :pattern ((P6 x)))))
        (assert (forall ((x Int)) (! (=> (P7 x) false) :pattern ((P7 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let outputs = common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// 9 rounds required — exceeds MAX_EMATCHING_ROUNDS=8, returns `unknown`.
///
/// B1c refinement (`try_ematching_refinement_round`) exists as dead code but
/// is NOT wired into the solve loop (has `#[allow(dead_code)]`, zero callers).
/// When B1c is integrated, this should return `unsat` (effective budget 8+4=12).
/// See #3325 for B1c integration work.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_9chain_now_unsat_with_b1c_3994() {
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
        (assert (forall ((x Int)) (! (=> (P0 x) (P1 x)) :pattern ((P0 x)))))
        (assert (forall ((x Int)) (! (=> (P1 x) (P2 x)) :pattern ((P1 x)))))
        (assert (forall ((x Int)) (! (=> (P2 x) (P3 x)) :pattern ((P2 x)))))
        (assert (forall ((x Int)) (! (=> (P3 x) (P4 x)) :pattern ((P3 x)))))
        (assert (forall ((x Int)) (! (=> (P4 x) (P5 x)) :pattern ((P4 x)))))
        (assert (forall ((x Int)) (! (=> (P5 x) (P6 x)) :pattern ((P5 x)))))
        (assert (forall ((x Int)) (! (=> (P6 x) (P7 x)) :pattern ((P6 x)))))
        (assert (forall ((x Int)) (! (=> (P7 x) (P8 x)) :pattern ((P7 x)))))
        (assert (forall ((x Int)) (! (=> (P8 x) false) :pattern ((P8 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let outputs = common::solve_vec(smt);
    // B1c interleaved E-matching (#5927) now resolves this: the effective budget
    // is 8 (preprocessing) + 4 (interleaved) = 12 rounds, enough for 9 steps.
    assert_eq!(outputs, vec!["unsat"]);
}

/// 14-step implication chain: P0(0) -> P1(0) -> ... -> P13(0) -> false
///
/// Preprocessing E-matching (8 rounds) discovers P0→P8. Post-CEGQI
/// E-matching (#7979) adds 1 round (P8→P9). The remaining 5 chain steps
/// (P9→P10→P11→P12→P13→false) exceed MAX_INTERLEAVED_EMATCHING_ROUNDS=4,
/// so the interleaved loop cannot complete the chain. Returns `unknown`.
///
/// The CEGQI trigger routing guard (#6045) skips CE lemma creation for
/// trigger-annotated quantifiers, so the total effective budget is
/// 8 (preprocessing) + 1 (post-CEGQI) + 4 (interleaved) = 13 rounds,
/// insufficient for 14 steps.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_exhausted_budget_returns_unknown_3994() {
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
        (declare-fun P13 (Int) Bool)
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
        (assert (forall ((x Int)) (! (=> (P12 x) (P13 x)) :pattern ((P12 x)))))
        (assert (forall ((x Int)) (! (=> (P13 x) false) :pattern ((P13 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let outputs = common::solve_vec(smt);
    // 14 steps > 13 (8 preprocessing + 1 post-CEGQI + 4 interleaved) = budget exhausted.
    assert_eq!(outputs, vec!["unknown"]);
}
