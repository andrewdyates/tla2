// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #4025.
//!
//! Under the soundness-first policy, all string logics are temporarily gated
//! to `unknown` until wrong-answer classes are resolved.

use ntest::timeout;
mod common;

#[test]
#[timeout(10_000)]
fn string_logics_return_unknown_while_gate_is_active() {
    let cases = [
        (
            "QF_S",
            r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= x "abc"))
(check-sat)
"#,
            "unknown",
        ),
        (
            "QF_SLIA",
            r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 3))
(check-sat)
"#,
            "unknown",
        ),
    ];

    for (logic, smt, expected) in cases {
        let result = common::solve(smt);
        assert_eq!(
            common::sat_result(&result),
            Some(expected),
            "{logic}: expected {expected}"
        );
    }
}

/// QF_SNIA with string terms is also gated to `unknown`.
#[test]
#[timeout(10_000)]
fn qf_snia_to_int_is_incomplete() {
    let smt = r#"
(set-logic QF_SNIA)
(declare-fun x () String)
(assert (= (str.to_int x) 42))
(check-sat)
"#;
    let result = common::solve(smt);
    assert_eq!(
        common::sat_result(&result),
        Some("unknown"),
        "QF_SNIA str.to_int should be gated to unknown"
    );
}

#[test]
#[timeout(10_000)]
fn check_sat_assuming_on_string_logic_is_unknown() {
    let implication_sat = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun a () Bool)
(assert (=> a (= x "a")))
(check-sat-assuming (a))
"#;
    let result = common::solve(implication_sat);
    assert_eq!(
        common::sat_result(&result),
        Some("unknown"),
        "check-sat-assuming on QF_S should be gated to unknown"
    );

    // Requires endpoint-empty reasoning with no explicit "" literal.
    // Assumptions-mode must pre-register the empty string exactly like
    // solve_strings()/solve_strings_lia() to keep this SAT.
    let endpoint_empty_sat = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun a () Bool)
(assert (=> a (= (str.++ x "a") "a")))
(check-sat-assuming (a))
"#;
    let result = common::solve(endpoint_empty_sat);
    assert_eq!(
        common::sat_result(&result),
        Some("unknown"),
        "check-sat-assuming endpoint-empty case should be gated to unknown"
    );
}
