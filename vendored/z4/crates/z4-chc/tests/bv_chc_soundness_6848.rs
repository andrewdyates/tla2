// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BV CHC soundness regression for #6848: gulwani_fig1a.c_000.
//!
//! Z3 returns `unsat` (unsafe). Z4 incorrectly returns `sat` (safe).
//! This is a false-safe soundness bug — the solver claims a system is safe
//! when it is actually unsafe.
//!
//! The benchmark has 3 Bool + 3 BV32 state variables with a bounded loop
//! involving signed comparison (`extract 31 31`), addition, and
//! constant `#xffffffce` (-50 as signed i32).
//!
//! Part of #6848

use ntest::timeout;
use std::time::Duration;
use z4_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};

/// gulwani_fig1a.c_000.smt2 from CHC-COMP 2025 BV track.
/// Z3 returns unsat (unsafe). Z4 must NOT return sat (safe).
const GULWANI_FIG1A_BENCHMARK: &str = r#"(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C Bool) (D Bool) (E Bool) (F (_ BitVec 32)) )
    (=>
      (and
        (and (not D) (not E) (not C))
      )
      (state E D C A B F)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M (_ BitVec 32)) )
    (=>
      (and
        (state I H G C D M)
        (let ((a!1 (and (not L)
                K
                (not J)
                (not G)
                (not H)
                I
                (= C B)
                (= E D)
                (= A M)
                (not (= ((_ extract 31 31) D) #b1))
                (bvsle M #x00000000))))
  (or (and (not L)
           (not K)
           J
           (not G)
           (not H)
           (not I)
           (= C B)
           (= E #xffffffce)
           (= A F))
      a!1
      (and (not L)
           (not K)
           J
           (not G)
           (not H)
           I
           (= C B)
           (= E (bvadd D M))
           (= A (bvadd #x00000001 M))
           (= ((_ extract 31 31) D) #b1))
      (and L (not K) (not J) (not G) H (not I) (= C B) (= E D) (= A M))
      (and L (not K) (not J) G (not H) (not I))))
      )
      (state J K L B E A)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C Bool) (D Bool) (E Bool) (F (_ BitVec 32)) )
    (=>
      (and
        (state E D C A B F)
        (and (not D) (not E) (= C true))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

/// Soundness regression for #6848: gulwani_fig1a must return Unsafe.
///
/// Z3 returns unsat (the system IS unsafe). Z4 with exact BV-to-Int encoding
/// correctly finds a counterexample. If Z4 returns Safe, that's a false-safe
/// soundness bug. If Z4 returns Unknown, the exact encoding regressed.
#[test]
#[timeout(25_000)]
fn test_bv_chc_gulwani_fig1a_unsafe_6848() {
    let problem = ChcParser::parse(GULWANI_FIG1A_BENCHMARK).expect("gulwani_fig1a should parse");

    let config = AdaptiveConfig::with_budget(Duration::from_secs(15), false);
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "#6848: gulwani_fig1a is UNSAFE (Z3 returns unsat). \
         Z4 returned {result:?} — expected Unsafe with exact BV-to-Int encoding."
    );
}
