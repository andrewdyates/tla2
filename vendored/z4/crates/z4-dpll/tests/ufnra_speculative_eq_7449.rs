// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #7449: UfNraSolver must route speculative equalities
//! through NeedModelEquality (SAT-level decisions) instead of asserting them
//! directly into EUF with empty reasons. The old code could cause false-UNSAT
//! when coincidentally-equal NRA model values for UF terms conflicted with
//! an EUF disequality.

use ntest::timeout;
mod common;

/// Two UF-Real terms whose NRA model values may coincide, with a disequality
/// between them. The formula is SAT: f(x) and f(y) can be made unequal by
/// choosing different x/y values. Before #7449, if the NRA model happened to
/// assign equal values to the arithmetic arguments, the speculative equality
/// was asserted into EUF with empty reasons, conflicting with the disequality
/// and causing false-UNSAT.
#[test]
#[timeout(10_000)]
fn ufnra_speculative_eq_must_not_cause_false_unsat_7449() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= x 0.0))
(assert (<= x 10.0))
(assert (>= y 0.0))
(assert (<= y 10.0))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let output = common::solve(smt);
    let result = common::sat_result(&output).expect("expected sat/unsat/unknown");
    // The formula is SAT: x != y lets f(x) != f(y). Must not return unsat.
    assert_ne!(
        result, "unsat",
        "#7449: speculative NRA equalities must not cause false-UNSAT in QF_UFNRA"
    );
}

/// Stronger variant: explicit disequality between UF applications where the
/// arithmetic arguments are forced to the same region. If the NRA model
/// evaluates both arguments to the same value, speculative equality routing
/// must still allow the SAT solver to explore alternatives.
#[test]
#[timeout(10_000)]
fn ufnra_speculative_eq_with_constrained_args_7449() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun g (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (>= a 1.0))
(assert (<= a 2.0))
(assert (>= b 1.0))
(assert (<= b 2.0))
(assert (not (= a b)))
(assert (not (= (g a) (g b))))
(check-sat)
"#;
    let output = common::solve(smt);
    let result = common::sat_result(&output).expect("expected sat/unsat/unknown");
    // SAT: a and b in [1,2] with a != b, g is uninterpreted so g(a) != g(b) is fine.
    assert_ne!(
        result, "unsat",
        "#7449: constrained UFNRA speculative equalities must not cause false-UNSAT"
    );
}

/// UNSAT case: known unsat formula must still return unsat.
/// f(x) = f(y) and not (f(x) = f(y)) is always unsat.
#[test]
#[timeout(10_000)]
fn ufnra_genuine_unsat_preserved_7449() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let output = common::solve(smt);
    let result = common::sat_result(&output).expect("expected sat/unsat/unknown");
    // x = y implies f(x) = f(y) by congruence, so not(f(x) = f(y)) is UNSAT.
    assert_ne!(
        result, "sat",
        "#7449 soundness: genuine UNSAT must not become SAT"
    );
}
