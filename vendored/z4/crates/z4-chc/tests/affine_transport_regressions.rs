// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::time::Duration;
use z4_chc::{engines, ChcEngineResult, ChcParser, PdrConfig};

fn pdr_test_config() -> PdrConfig {
    let mut config = PdrConfig::default()
        .with_max_frames(12)
        .with_max_iterations(400)
        .with_verbose(false);
    config.solve_timeout = Some(Duration::from_secs(10));
    config
}

fn assert_pdr_safe(input: &str, label: &str) {
    let problem = ChcParser::parse(input).unwrap_or_else(|err| panic!("parse {label}: {err}"));
    let mut solver = engines::new_pdr_solver(problem, pdr_test_config());
    match solver.solve() {
        ChcEngineResult::Safe(model) => {
            assert!(
                !model.is_empty(),
                "{label}: expected a non-empty safe model from PDR"
            );
        }
        ChcEngineResult::Unsafe(cex) => {
            panic!(
                "{label}: guarded affine transport regression returned Unsafe at depth {}",
                cex.steps.len()
            );
        }
        ChcEngineResult::Unknown => {
            panic!("{label}: guarded affine transport regression returned Unknown");
        }
        ChcEngineResult::NotApplicable => {
            panic!("{label}: PDR unexpectedly returned NotApplicable");
        }
        other => {
            panic!("{label}: unexpected result variant: {other:?}");
        }
    }
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn pdr_phase_chain_guarded_affine_transport_is_safe() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun R (Int) Bool)

(assert
  (forall ((A Int) (B Int) (C Int))
    (=>
      (and (= A 0) (= B 2) (= C 2))
      (P A B C)
    )
  )
)
(assert
  (forall ((A Int) (B Int) (C Int))
    (=>
      (and (P A B C) (= A 0))
      (Q B C)
    )
  )
)
(assert
  (forall ((A Int) (B Int))
    (=>
      (Q A B)
      (Q A B)
    )
  )
)
(assert
  (forall ((A Int) (B Int))
    (=>
      (and (Q A B) (= A 0))
      (R B)
    )
  )
)
(assert
  (forall ((A Int))
    (=>
      (R A)
      (R A)
    )
  )
)
(assert
  (forall ((A Int))
    (=>
      (and (R A) (< A 0))
      false
    )
  )
)

(check-sat)
"#;

    assert_pdr_safe(smt2, "phase-chain guarded affine transport");
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn pdr_fun_sad_guarded_band_transport_is_safe() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun FUN (Int Int Int) Bool)
(declare-fun SAD (Int Int Int) Bool)

(assert
  (forall ((A Int) (B Int) (E Int))
    (=>
      (and (= A 0) (= B 0) (> E 0))
      (FUN A B E)
    )
  )
)
(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
    (=>
      (and
        (FUN A B E)
        (= C (+ 1 A))
        (= D (+ 2 B))
      )
      (FUN C D E)
    )
  )
)
(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
    (=>
      (and
        (FUN B A E)
        (= C B)
        (>= A E)
        (= D 1)
      )
      (SAD C D E)
    )
  )
)
(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
    (=>
      (and
        (SAD A B E)
        (= C (+ 1 A))
        (= D (+ 2 B))
      )
      (SAD C D E)
    )
  )
)
(assert
  (forall ((A Int) (B Int) (E Int))
    (=>
      (and (SAD A B E) (< (* 2 A) B))
      false
    )
  )
)
(assert
  (forall ((A Int) (B Int) (E Int))
    (=>
      (and (SAD A B E) (> (- (* 2 A) B) E))
      false
    )
  )
)

(check-sat)
"#;

    assert_pdr_safe(smt2, "FUN/SAD guarded band transport");
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn pdr_s_multipl_08_benchmark_is_safe() {
    let smt2 =
        include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_08_000.smt2");

    assert_pdr_safe(smt2, "s_multipl_08 benchmark");
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn pdr_s_multipl_10_benchmark_is_safe() {
    let smt2 =
        include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_10_000.smt2");

    assert_pdr_safe(smt2, "s_multipl_10 benchmark");
}
