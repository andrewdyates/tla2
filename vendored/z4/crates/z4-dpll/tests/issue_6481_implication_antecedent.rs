// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for issue #6481: implication antecedents containing a
//! ground atom alongside a quantified atom must not flip polarity during
//! Skolemization.

use ntest::timeout;
mod common;

#[test]
#[timeout(10000)]
fn implication_antecedent_with_ground_and_forall_stays_sat_issue_6481() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort Seq 0)
        (declare-fun seq_len (Seq) Int)
        (declare-fun seq_array (Seq) (Array Int Int))
        (declare-fun seq_offset (Seq) Int)
        (declare-const a_view Seq)
        (declare-const b_view Seq)

        (define-fun len_eq () Bool
          (= (seq_len a_view) (seq_len b_view)))

        (assert (forall ((i Int))
          (=> (and (>= i 0) (< i (seq_len a_view)))
              (= (select (seq_array a_view) (+ (seq_offset a_view) i))
                 (select (seq_array b_view) (+ (seq_offset b_view) i))))))

        (declare-const ext_eq Bool)
        (assert ext_eq)
        (assert (=> ext_eq len_eq))
        (assert
          (=> (and len_eq
                   (forall ((i Int))
                     (=> (and (>= i 0) (< i (seq_len a_view)))
                         (= (select (seq_array a_view) (+ (seq_offset a_view) i))
                            (select (seq_array b_view) (+ (seq_offset b_view) i))))))
              ext_eq))
        (check-sat)
    "#;

    assert_eq!(
        common::solve_vec(smt),
        vec!["sat"],
        "mixed ground+forall implication antecedent should stay SAT"
    );
}
