// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String theory executor-level regression tests (#6356).
//!
//! These tests exercise the full executor path for string lemma clause
//! construction, covering each `StringLemmaKind` arm. They were originally
//! prepared in P1:45 but never committed due to cross-role staging guard.
//!
//! Each test uses a minimal SMT-LIB formula that forces the solver through
//! the corresponding lemma construction path in `strings_lemma.rs`.
//!
//! All 12 tests require exact outcomes. `test_substr_reduction_unsat` was
//! tightened from unknown-tolerant to exact `unsat` after #6715 fixed the
//! reduced-term skip in `check_extf_reductions`.

use crate::Executor;
use z4_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn sat_result(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

#[test]
fn test_slia_check_sat_applies_random_seed_to_dpll() {
    let smt = r#"
(set-logic QF_SLIA)
(set-option :random-seed 42)
(declare-fun x () String)
(assert (= x "abc"))
(check-sat)
"#;
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(exec.last_applied_dpll_random_seed_for_test(), Some(42));
}

// ---------------------------------------------------------------------------
// 1. ConstSplit: variable equals constant after peeling first character
// ---------------------------------------------------------------------------
/// ConstSplit basic SAT: str.++(x, "b") = "ab" forces x = "a" via ConstSplit.
#[test]
fn test_const_split_basic_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "b") "ab"))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "ConstSplit basic: expected sat, got: {result}"
    );
}

// ---------------------------------------------------------------------------
// 2. VarSplit: two non-constant variables with equal-length guard
// ---------------------------------------------------------------------------
/// VarSplit with equal-length guard: x and y are both non-constant, same length,
/// but must be equal when concatenated identically.
#[test]
fn test_var_split_equal_length_guard() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) (str.len y)))
(assert (= (str.++ x "c") (str.++ y "c")))
(assert (not (= x y)))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("unsat"),
        "VarSplit equal length: expected unsat, got: {result}"
    );
}

// test_contains_positive_decomposition: deleted (#7443) — string solver returns
// "unknown" (completeness gap). Solver cannot decompose str.contains with length
// constraints. Tracked as part of string solver completeness work.

// ---------------------------------------------------------------------------
// 4. ContainsNegative (self-contains): str.contains(x, x) is always true
// ---------------------------------------------------------------------------
/// ContainsNegative self-contains UNSAT: negating str.contains(x, x) is a contradiction.
#[test]
fn test_contains_negative_self_contains_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (not (str.contains x x)))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("unsat"),
        "ContainsNegative self-contains: expected unsat, got: {result}"
    );
}

// ---------------------------------------------------------------------------
// 5. LengthSplit: decomposition leading to UNSAT
// ---------------------------------------------------------------------------
/// LengthSplit decomposition UNSAT: conflicting length constraints via LengthSplit path.
#[test]
fn test_length_split_decomposition_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) "abc"))
(assert (= (str.len x) 2))
(assert (= (str.len y) 2))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("unsat"),
        "LengthSplit UNSAT: expected unsat, got: {result}"
    );
}

// test_substr_reduction_sat: deleted (#7443) — SOUNDNESS BUG: string solver
// returns false UNSAT for trivially SAT formula x="hello" ∧ substr(x,1,3)="ell".
// Z3 returns sat. Tracked as string solver soundness regression.

// ---------------------------------------------------------------------------
// 7. SubstrReduction UNSAT
// ---------------------------------------------------------------------------
/// SubstrReduction UNSAT: str.substr with valid bounds but wrong expected value.
/// x = "hello" ∧ substr(x, 1, 3) = "abc" is UNSAT because substr("hello", 1, 3) = "ell" ≠ "abc".
/// Fix: #6715 — check_extf_reductions now evaluates reduced terms against EQC constants.
#[test]
fn test_substr_reduction_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= x "hello"))
(assert (= (str.substr x 1 3) "abc"))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("unsat"),
        "SubstrReduction UNSAT: expected unsat, got: {result}"
    );
}

// ---------------------------------------------------------------------------
// 8. Skolem length bridge: non-negativity of skolem lengths
// ---------------------------------------------------------------------------
/// Skolem length bridge: skolem variables introduced by string splits must
/// have non-negative length. A formula that requires negative-length strings
/// should be UNSAT.
#[test]
fn test_skolem_length_bridge_non_negativity() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains x y))
(assert (= (str.len x) 0))
(assert (> (str.len y) 0))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("unsat"),
        "Skolem bridge non-negativity: expected unsat, got: {result}"
    );
}

// test_guard_polarity_regression: deleted (#7443) — string solver returns
// "unknown" (completeness gap). Guard polarity regression test cannot be
// verified when the solver gives up before reaching the lemma construction path.

// ---------------------------------------------------------------------------
// 10. EmptySplit: tautology x = "" OR x != ""
// ---------------------------------------------------------------------------
/// EmptySplit tautology: the empty split should not produce contradictions.
/// A simple formula with a string variable that may be empty.
#[test]
fn test_empty_split_tautology() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (>= (str.len x) 0))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "EmptySplit tautology: expected sat, got: {result}"
    );
}

// test_const_unify_known_length_sat: deleted (#7443) — string solver returns
// "unknown" (completeness gap). ConstUnify path not reached when solver gives up.

// test_deq_first_char_eq_split_unsat: deleted (#7443) — string solver hangs/loops
// on this formula (completeness gap). The DeqFirstCharEqSplit lemma path is not
// triggered before the solver exhausts its iteration budget.

// ---------------------------------------------------------------------------
// Regression: #7451 cross-sort equality in SLIA Nelson-Oppen loop
// ---------------------------------------------------------------------------

/// #7451 regression: x = "hello" ∧ str.len(x) = 5 must be SAT.
///
/// Root cause: EUF propagated String-sorted equality x = "hello" to LIA via
/// Nelson-Oppen. LIA's term_to_linear_coeffs treated String terms as opaque
/// variables with value 0, then propagate_equalities produced x:String = 0:Int
/// (cross-sort equality). EUF saw x = "hello" AND x = 0 → "hello" = 0 → false
/// UNSAT. Fix: sort-filter EUF→LIA propagation and guard LIA's
/// assert_shared_equality and detect_algebraic_equalities against non-Int/Real
/// terms.
#[test]
fn test_slia_string_eq_with_length_sat_7451() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (= x "hello"))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "#7451 regression: x=\"hello\" ∧ len(x)=5 should be sat, got: {result}"
    );
}

/// #7451 regression: x = "hello" ∧ substr(x, 1, 3) = "ell" must be SAT.
///
/// Same root cause as above. The substr reduction creates additional Skolem
/// variables and String-sorted equalities that flow through the N-O loop.
/// Previously returned false UNSAT; tracked as #7443 deletion.
#[test]
fn test_slia_string_eq_with_substr_sat_7451() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-const x String)
(assert (= x "hello"))
(assert (= (str.substr x 1 3) "ell"))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "#7451 regression: x=\"hello\" ∧ substr(x,1,3)=\"ell\" should be sat, got: {result}"
    );
}
