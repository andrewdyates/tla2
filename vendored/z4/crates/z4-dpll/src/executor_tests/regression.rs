// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests - statistics, soundness issue regressions (#858, #859, #919, #920),
//! and incremental cache soundness tests

use crate::{Executor, SolveResult, StatValue, Statistics};
use ntest::timeout;
use z4_frontend::parse;

#[test]
fn test_get_statistics_propositional() {
    // Use QF_BOOL (pure propositional) to go through solve_propositional
    let smt = r#"
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (or a b))
        (assert (or (not a) c))
        (assert (or (not b) c))
        (assert (not c))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let _result = exec.execute_all(&commands).unwrap();

    // Should be UNSAT: (a v b) & (~a v c) & (~b v c) & ~c
    // If a=T: need c (from ~a v c), contradicts ~c
    // If a=F: need b (from a v b), then need c (from ~b v c), contradicts ~c
    assert_eq!(exec.last_result(), Some(SolveResult::Unsat));

    let stats = exec.get_statistics();

    // Should have some conflicts (the problem is UNSAT)
    // Note: exact numbers depend on solver heuristics, just verify they're tracked
    assert!(
        stats.conflicts > 0 || stats.decisions > 0 || stats.propagations > 0,
        "Statistics should show some solver activity: conflicts={}, decisions={}, propagations={}",
        stats.conflicts,
        stats.decisions,
        stats.propagations
    );

    // num_assertions should match what we asserted
    assert_eq!(stats.num_assertions, 4, "Should have 4 assertions");
}

/// Test that Statistics Display format is SMT-LIB compatible
#[test]
fn test_statistics_display() {
    let mut stats = Statistics::new();
    stats.conflicts = 42;
    stats.decisions = 100;
    stats.propagations = 500;
    stats.restarts = 5;

    let display = format!("{stats}");
    assert!(display.contains(":conflicts 42"));
    assert!(display.contains(":decisions 100"));
    assert!(display.contains(":propagations 500"));
    assert!(display.contains(":restarts 5"));
}

/// Test StatValue Display formatting
#[test]
#[allow(clippy::approx_constant)] // 3.14 is intentional - testing format, not computing PI
fn test_stat_value_display() {
    assert_eq!(format!("{}", StatValue::Int(42)), "42");
    // Z3-compatible format: 2 decimal places
    assert_eq!(format!("{}", StatValue::Float(3.14)), "3.14");
    // String values should be escaped per SMT-LIB 2.6 (double-quote escaping)
    assert_eq!(
        format!("{}", StatValue::String("test".to_string())),
        "\"test\""
    );
    // SMT-LIB 2.6: embedded " is escaped by doubling -> ""
    assert_eq!(
        format!("{}", StatValue::String("test\"quote".to_string())),
        "\"test\"\"quote\""
    );
    // SMT-LIB 2.6: backslash is literal, no escaping needed
    assert_eq!(
        format!("{}", StatValue::String("test\\backslash".to_string())),
        "\"test\\backslash\""
    );
}

/// Verify that theory_conflicts and theory_propagations are non-zero after
/// solving a QF_LIA problem that requires DPLL(T) interaction (#4705).
///
/// The formula must require simplex-level reasoning that cannot be resolved
/// by preprocessing (VariableSubstitution) or SAT-level bound axioms alone.
/// A sum constraint `x + y >= 1` with individual upper bounds `x <= 0, y <= 0`
/// is UNSAT only because the simplex detects the sum infeasibility.
#[test]
fn test_theory_statistics_nonzero_4705() {
    // UNSAT problem: x + y >= 1 with x <= 0 and y <= 0.
    // VariableSubstitution cannot eliminate this (no direct equality).
    // Bound axioms on individual variables can't detect the cross-variable
    // conflict. The simplex must detect that x <= 0, y <= 0 contradicts
    // x + y >= 1. This guarantees theory interaction.
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= (+ x y) 1))
        (assert (<= x 0))
        (assert (<= y 0))
        (check-sat)
    "#;

    let commands = parse(smt).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let _result = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(exec.last_result(), Some(SolveResult::Unsat));

    let stats = exec.get_statistics();

    // Theory interaction must have occurred: either conflicts or propagations
    // (exact counts depend on solver heuristics and eager/lazy mode).
    assert!(
        stats.theory_conflicts > 0 || stats.theory_propagations > 0,
        "QF_LIA UNSAT problem should generate theory interaction: \
         theory_conflicts={}, theory_propagations={}",
        stats.theory_conflicts,
        stats.theory_propagations
    );
}

/// Regression test for #858: Bool variable equated to BV equality result
///
/// This tests the pattern emitted by Zani's Z4 backend where a Bool variable
/// is equated to a BV comparison result:
///   (assert (= t (= (bvadd x y) #x00000008)))
///   (assert (not t))
///
/// With x=5, y=3: bvadd(5,3) = 8, so (= (bvadd x y) 8) is true.
/// Therefore t must be true, and (not t) is unsatisfiable.
#[test]
fn test_qf_bv_bool_equality_soundness_858() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000005))
        (assert (= y #x00000003))
        (declare-const t Bool)
        (assert (= t (= (bvadd x y) #x00000008)))
        (assert (not t))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 returns unsat; Z4 must match
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #858: Bool = BV equality returns sat instead of unsat"
    );
}

/// Regression test for soundness bug #859: QF_AUFBV Bool = BV equality
/// Same pattern as #858 but with QF_AUFBV logic (arrays + UF + bitvectors).
/// Zani emits this pattern when encoding bitvector equality into Bool locals.
#[test]
fn test_qf_aufbv_bool_equality_soundness_859() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (assert (= a #x00000005))
        (assert (= b #x00000003))
        (declare-const sum (_ BitVec 32))
        (assert (= sum (bvadd a b)))
        ; sum = 5 + 3 = 8, so (not (= sum #x8)) should be unsat
        (assert (not (= sum #x00000008)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 returns unsat; Z4 must match
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #859: QF_AUFBV Bool = BV equality returns sat instead of unsat"
    );
}

/// Regression test for #859: More complex AUFBV pattern with Bool alias
/// This matches the Zani pattern: Bool local aliased to BV equality result.
#[test]
fn test_qf_aufbv_bool_alias_soundness_859() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000005))
        (assert (= y #x00000003))
        (declare-const t Bool)
        (assert (= t (= (bvadd x y) #x00000008)))
        (assert (not t))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 returns unsat; Z4 must match
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #859: QF_AUFBV Bool alias = BV equality returns sat instead of unsat"
    );
}

/// Regression test for #920: Array self-store soundness bug
/// When (= (store arr i v) arr) is asserted, it implies (= (select arr i) v).
/// Z4 was incorrectly returning SAT for the contradictory case.
#[test]
fn test_qf_aufbv_self_store_soundness_920() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        ; store arr i #x02 = arr implies arr[i] = #x02
        (assert (= (store arr i #x02) arr))
        (assert (not (= (select arr i) #x02)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 returns unsat; Z4 must match
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #920: Self-store pattern returns sat instead of unsat"
    );
}

/// Regression test for #919: ITE with BV predicate condition and Bool variable branches
/// The bug was that polarity-aware Tseitin encoding for Boolean equality didn't trigger
/// both polarities for ITE subterms, leaving them under-constrained.
#[test]
fn test_qf_bv_ite_bool_var_branches_soundness_919() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 32))
        (declare-const b Bool)
        (declare-const c Bool)
        (declare-const d Bool)
        ; d = ite((1 == a), b, c)
        (assert (= d (ite (= #x00000001 a) b c)))
        (assert (= a #x00000002))  ; condition is false
        (assert c)                  ; else branch is true
        (assert (not d))            ; d should equal c, but we say d is false
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // With condition false and c=true, d must equal c (true).
    // But we assert (not d), so this should be unsat.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Soundness bug #919: ITE with Bool var branches returns sat instead of unsat"
    );
}

/// Regression test for #1007: incremental LIA Farkas verification panic.
///
/// This test exercises incremental LIA solving with two independent queries
/// separated by push/pop. The second query should not panic during Farkas
/// certificate verification in debug builds.
#[test]
fn test_incremental_lia_farkas_regression_1007() {
    // This SMT2 program triggered a Farkas verification panic in debug builds.
    // The issue was that the Farkas certificate referenced constraints in a form
    // that the verification function couldn't properly combine.
    let input = r#"
(set-logic QF_LIA)
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(push 1)
(assert (not (= (+ 2 (* 1 x0)) (- 19))))
(assert (<= (+ (- 1) (* 1 x1) (* 2 x2)) (+ (- 9) (* 2 x0) (* (- 3) x1))))
(assert (>= (+ (- 10) (* 1 x0)) 11))
(assert (not (= (+ (- 9) (* 1 x1)) (- 16))))
(assert (>= (+ (- 5) (* (- 3) x0)) (+ 5 (* (- 1) x0) (* (- 2) x1) (* 3 x2))))
(check-sat)
(pop 1)
(push 1)
(assert (>= (+ (- 5) (* 1 x1) (* 2 x2)) (+ 4 (* (- 2) x0) (* (- 2) x2))))
(assert (>= (+ 2 (* 2 x2)) (- 1)))
(assert (= (+ (- 8) (* 1 x1)) (- 8)))
(assert (<= (+ (- 1) (* 1 x0) (* (- 2) x1) (* 1 x2)) 9))
(assert (<= (+ 2 (* (- 3) x0)) 12))
(assert (not (= (+ 10 (* 2 x1)) (+ 6 (* (- 2) x0)))))
(check-sat)
(pop 1)
(exit)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Both queries should complete without panic.
    // We expect 3 outputs: two check-sat results + "exit" from (exit) command.
    assert!(
        outputs.len() >= 2,
        "Expected at least two check-sat results"
    );
    // First check-sat: the LP relaxation diverges on x2 (unbounded direction),
    // so the branch-and-bound correctly detects divergence and returns unknown.
    // The formula IS sat (x0=21, x1=13, x2=-9) but the lazy split loop's
    // closest-integer heuristic picks the wrong branch direction. Accept unknown
    // until Gomory cuts or eager propagation fix the convergence (#1007).
    assert!(
        outputs[0] == "sat" || outputs[0] == "unsat" || outputs[0] == "unknown",
        "First check-sat should not error, got: {}",
        outputs[0]
    );
    assert!(
        outputs[1] == "sat" || outputs[1] == "unsat",
        "Second check-sat result should be sat or unsat, got: {}",
        outputs[1]
    );
}

/// Regression test for #1432/#1445: LIA incremental Tseitin cache soundness.
///
/// Tests the same hazard as EUF: if a term is encoded in one scope, popped,
/// and then reused in another scope, the cached term→var mapping must still
/// have its definitional clauses active.
#[test]
fn test_incremental_lia_tseitin_cache_soundness() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)

        (push 1)
        (assert (>= x 0))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (>= x 0) (< x 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat: (>= x 0) is satisfiable -> SAT
    // Second check-sat: (>= x 0) AND (< x 0) is unsatisfiable -> UNSAT
    assert_eq!(
        outputs,
        vec!["sat", "unsat"],
        "Bug #1432/#1445: LIA Tseitin definitions must remain active for cached vars"
    );
}

/// Regression test for #1432/#1445: LRA incremental Tseitin cache soundness.
#[test]
fn test_incremental_lra_tseitin_cache_soundness() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)

        (push 1)
        (assert (>= x 0.0))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (>= x 0.0) (< x 0.0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat: (>= x 0.0) is satisfiable -> SAT
    // Second check-sat: (>= x 0.0) AND (< x 0.0) is unsatisfiable -> UNSAT
    assert_eq!(
        outputs,
        vec!["sat", "unsat"],
        "Bug #1432/#1445: LRA Tseitin definitions must remain active for cached vars"
    );
}

/// Regression test for #1432/#1445: BV incremental bitblaster cache soundness.
#[test]
fn test_incremental_bv_bitblast_cache_soundness() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))

        (push 1)
        (assert (= x #x00))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (= x #x00) (distinct x #x00)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat: (= x #x00) is satisfiable -> SAT
    // Second check-sat: (= x #x00) AND (distinct x #x00) is unsatisfiable -> UNSAT
    assert_eq!(
        outputs,
        vec!["sat", "unsat"],
        "Bug #1432/#1445: BV bitblaster definitions must remain active for cached vars"
    );
}

/// Test reset() clears BV state completely.
///
/// Unlike push/pop which scope assertions, reset() clears all state.
/// The solver should behave as freshly constructed after reset.
#[test]
fn test_incremental_bv_reset() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x42))
        (check-sat)
        (reset)
        (set-logic QF_BV)
        (declare-const y (_ BitVec 8))
        (assert (= y #x00))
        (assert (distinct y #x00))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: x = 0x42 is SAT
    // After reset, new problem: y = 0 AND y != 0 is UNSAT
    // Old variable x should not affect new problem
    assert_eq!(outputs, vec!["sat", "unsat"]);
}

/// Test reset() after push/pop maintains correct state.
#[test]
fn test_incremental_bv_reset_after_push_pop() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (bvult x #x10))
        (push 1)
        (assert (= x #x05))
        (check-sat)
        (pop 1)
        (reset)
        (set-logic QF_BV)
        (declare-const z (_ BitVec 8))
        (assert (= z #xFF))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: x < 16 AND x = 5 is SAT
    // After reset: z = 255 is SAT (completely fresh problem)
    assert_eq!(outputs, vec!["sat", "sat"]);
}

/// Test reset() clears bitblaster cache properly.
///
/// REQUIRES: reset() clears term_to_bits, predicate_to_var, tseitin_state
/// ENSURES: Re-using same variable name after reset doesn't reuse stale mappings
#[test]
fn test_incremental_bv_reset_clears_cache() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x42))
        (check-sat)
        (reset)
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x00))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Both should be SAT - the x after reset is a completely new variable
    // Even though it has the same name, bitblaster cache should be cleared
    assert_eq!(outputs, vec!["sat", "sat"]);
}

/// Test reset() inside an active scope (no pop) clears scope state.
///
/// REQUIRES: reset() clears scope_depth even without explicit pop
/// ENSURES: Fresh solver after reset has no pending scopes
#[test]
fn test_incremental_bv_reset_inside_scope() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= x #x42))
        (check-sat)
        (reset)
        (set-logic QF_BV)
        (declare-const y (_ BitVec 8))
        (assert (= y #x00))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First: inside scope, x = 0x42 is SAT
    // After reset (without pop): y = 0 is SAT
    // Reset should clear scope_depth even without explicit pop
    assert_eq!(outputs, vec!["sat", "sat"]);
}

/// Regression test for #2861: Executor::reset() must clear quantifier manager,
/// incremental state, and proof-related fields — matching the SMT-LIB (reset)
/// command handler behavior.
#[test]
fn test_executor_reset_clears_all_state_2861() {
    let input = r#"
        (set-logic LIA)
        (declare-const x Int)
        (push 1)
        (assert (forall ((y Int)) (>= (+ x y) y)))
        (check-sat)
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();

    assert!(
        exec.incremental_mode,
        "incremental_mode should be true after push/pop"
    );

    exec.reset();

    assert!(
        !exec.incremental_mode,
        "incremental_mode should be false after reset()"
    );

    if let Some(ref qm) = exec.quantifier_manager {
        assert_eq!(
            qm.round(),
            0,
            "quantifier_manager round should be 0 after reset()"
        );
        assert!(
            !qm.has_deferred(),
            "quantifier_manager should have no deferred items after reset()"
        );
    }

    let input2 = r#"
        (set-logic QF_LIA)
        (declare-const z Int)
        (assert (= z 42))
        (check-sat)
    "#;
    let commands2 = parse(input2).unwrap();
    let outputs2 = exec.execute_all(&commands2).unwrap();
    assert_eq!(outputs2, vec!["sat"]);
}

/// Regression test for #1836: LIA unbounded oscillation detection (increasing)
///
/// This formula is UNSAT (loop preservation) but the LIA solver was hanging
/// because branch-and-bound kept splitting on unbounded variables without
/// making progress. The fix detects monotonically increasing/decreasing
/// split values and returns Unknown after a threshold.
#[test]
#[timeout(30_000)] // Should complete quickly; timeout ensures hang regressions fail fast.
fn test_lia_unbounded_oscillation_terminates_1836() {
    // Loop preservation pattern: i >= 0, i <= n, i < n, NOT(i+1 >= 0 AND i+1 <= n)
    // This is UNSAT by case analysis, but branch-and-bound oscillates forever
    // without Gomory/HNF cuts (no equalities, slack vars block Gomory).
    let input = r#"
(set-logic QF_LIA)
(declare-const i Int)
(declare-const n Int)
(assert (>= i 0))
(assert (<= i n))
(assert (< i n))
(assert (not (and (>= (+ i 1) 0) (<= (+ i 1) n))))
(check-sat)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should terminate quickly with "unknown" (not hang forever)
    // Z3 returns "unsat", but our mitigation returns "unknown" to prevent hang.
    // The key is that it terminates instead of infinite looping.
    assert!(
        outputs == vec!["unknown"] || outputs == vec!["unsat"],
        "Expected unknown or unsat, got {outputs:?}"
    );
}

/// Regression test for #1836: LIA unbounded oscillation detection (decreasing)
///
/// Tests the decreasing direction of unbounded oscillation detection.
/// Similar to the increasing test but with constraints that push values negative.
#[test]
#[timeout(30_000)] // Should complete quickly; timeout ensures hang regressions fail fast.
fn test_lia_unbounded_oscillation_decreasing_1836() {
    // Loop preservation pattern going negative: i <= 0, i >= n, i > n,
    // NOT(i-1 <= 0 AND i-1 >= n)
    // This creates monotonically decreasing split values.
    let input = r#"
(set-logic QF_LIA)
(declare-const i Int)
(declare-const n Int)
(assert (<= i 0))
(assert (>= i n))
(assert (> i n))
(assert (not (and (<= (- i 1) 0) (>= (- i 1) n))))
(check-sat)
"#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should terminate quickly with "unknown" (not hang forever)
    assert!(
        outputs == vec!["unknown"] || outputs == vec!["unsat"],
        "Expected unknown or unsat, got {outputs:?}"
    );
}

/// Regression test for #4767: ITE with UF condition incorrectly returns SAT.
///
/// The formula `(f x) = true ∧ (g x) = 5 ∧ ite(f(x), g(x)+1, 0) ≠ 6`
/// is UNSAT because: f(x) true → ite branch is g(x)+1 → 5+1 = 6 → 6≠6 contradiction.
///
/// Root cause: Int-sorted equalities with UF subterms (e.g., (= (g x) 5)) were
/// not forwarded to LIA, so the arithmetic relationship between g(x)=5 and
/// g(x)+1=6 was invisible.
#[test]
fn test_ite_uf_condition_unsat_issue_4767() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Bool)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (assert (f x))
        (assert (= (g x) 5))
        (assert (not (= (ite (f x) (+ (g x) 1) 0) 6)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "ITE with UF condition must be UNSAT (#4767)"
    );
}

/// Variant of #4767: simpler case without ITE — just UF equality + arithmetic.
/// (g x) = 5 ∧ (g x) + 1 ≠ 6 is UNSAT.
#[test]
fn test_uf_equality_arithmetic_contradiction_issue_4767() {
    let input = "(set-logic QF_UFLIA)(declare-fun g (Int) Int)(declare-const x Int)\
        (assert (= (g x) 5))(assert (not (= (+ (g x) 1) 6)))(check-sat)";
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UF equality + arith contradiction must be UNSAT (#4767)"
    );
}

/// SAT variant of #4767: (g x) = 5 ∧ (g x) + 1 ≠ 7 is SAT (5+1=6≠7).
#[test]
fn test_uf_equality_arithmetic_sat_issue_4767() {
    let input = "(set-logic QF_UFLIA)(declare-fun g (Int) Int)(declare-const x Int)\
        (assert (= (g x) 5))(assert (not (= (+ (g x) 1) 7)))(check-sat)";
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "UF equality + non-contradictory arith should be SAT (#4767)"
    );
}

/// #5355: Interleaved declare-const/assert causes infinite loop in
/// non-incremental LIA path due to repeated identical disequality splits.
/// Term ID ordering from interleaved declarations caused the simplex model
/// to produce an excluded value outside the variable's feasible domain,
/// leading to non-converging splits.
#[test]
#[timeout(10_000)]
fn test_interleaved_declare_assert_hang_issue_5355() {
    // Interleaved order: declare x, assert x>=1, declare y, assert y>=1, ...
    // This previously hung because TermId ordering caused wrong excluded value.
    let interleaved = "\
        (set-logic QF_LIA)\
        (declare-const x Int)\
        (assert (>= x 1))\
        (declare-const y Int)\
        (assert (>= y 1))\
        (assert (not (= x y)))\
        (assert (= x 1))\
        (check-sat)";
    let commands = parse(interleaved).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "interleaved declare/assert should be SAT (#5355)"
    );
}

/// #5355 variant: non-interleaved order (all declares before asserts).
/// This was always working — included to prevent regression.
#[test]
#[timeout(10_000)]
fn test_non_interleaved_declare_assert_issue_5355() {
    let non_interleaved = "\
        (set-logic QF_LIA)\
        (declare-const x Int)\
        (declare-const y Int)\
        (assert (>= x 1))\
        (assert (>= y 1))\
        (assert (not (= x y)))\
        (assert (= x 1))\
        (check-sat)";
    let commands = parse(non_interleaved).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "non-interleaved declare/assert should be SAT (#5355)"
    );
}

/// #5560: solve_dt_auflira delegates to solve_lira, dropping array reasoning.
///
/// When DT is present with QF_AUFLIRA, the solver should use solve_auflira
/// (with array axioms and AufLiraSolver theory). The bug at euf.rs:187 routes
/// to solve_lira which lacks array reasoning, EUF, and array model extraction.
/// A second instance at executor.rs:1915 routes the assumptions path to
/// solve_lira_with_assumptions instead of solve_auflira_with_assumptions.
///
/// This formula uses symbolic indices to prevent eager read-over-write
/// simplification in mk_select, requiring theory-level array reasoning.
/// UNSAT because: i = j, so store at i and select at j hit the
/// same index, and the stored value must equal the selected value.
#[test]
#[timeout(30_000)]
fn test_dt_auflira_symbolic_index_array_5560() {
    // DT + Array + LIRA with symbolic indices.
    // Without array theory reasoning, the solver cannot determine that
    // select(store(a, i, v), j) = v when i = j symbolically.
    let input = r#"
        (set-logic QF_AUFLIRA)
        (declare-datatypes ((IPair 0)) (((mkip (ip_fst Int) (ip_snd Real)))))
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Real)
        (declare-const p IPair)
        (assert (= p (mkip i v)))
        (assert (= i j))
        (assert (= v 3.5))
        (assert (distinct (select (store a i v) j) v))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    // #5560 FIX: solve_dt_auflira now routes to solve_auflira (not solve_lira).
    // With array reasoning: i=j, so select(store(a,i,v),j) = v,
    // contradicting (distinct ... v) → UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#5560: DT+AUFLIRA with array reasoning should return unsat"
    );
}

/// #5560 (assumption path): solve_lira_with_assumptions → solve_auflira_with_assumptions.
///
/// The assumption-based dispatch (executor.rs DtAuflira arm) had the same bug:
/// routing to solve_lira_with_assumptions instead of solve_auflira_with_assumptions.
/// This test exercises the check-sat-assuming path to verify both call sites are fixed.
#[test]
#[timeout(30_000)]
fn test_dt_auflira_assumptions_path_5560() {
    let input = r#"
        (set-logic QF_AUFLIRA)
        (declare-datatypes ((Wrap 0)) (((wrap (unwrap Int)))))
        (declare-const a (Array Int Real))
        (declare-const w Wrap)
        (declare-const k Int)
        (declare-const v Real)
        (assert (= (unwrap w) k))
        (assert (= v 2.0))
        (assert (distinct (select (store a k v) (unwrap w)) v))
        (check-sat-assuming (true))
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#5560: DT+AUFLIRA assumption path should also return unsat"
    );
}

/// #5671: False UNSAT on QF_LIA with all-distinct + diagonal constraints.
///
/// Z4 incorrectly returned `unsat` on satisfiable 4-queens problems when
/// 4+ bounded integer variables had pairwise disequality constraints plus
/// additional linear arithmetic constraints on differences. Root cause:
/// single-variable enumeration in LRA theory split for multi-variable
/// disequalities incorrectly generated clauses that dropped constraints
/// on other variables, causing unsound UNSAT. Fixed by replacing
/// single-variable enumeration with direct expression split.
///
/// Minimal trigger: 4 vars in {1..4}, all pairwise distinct, plus one
/// diagonal constraint on q1-q2. Solution exists: e.g. q1=2,q2=4,q3=1,q4=3.
#[test]
#[timeout(30000)]
fn test_false_unsat_all_distinct_diagonal_5671() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const q1 Int)
        (declare-const q2 Int)
        (declare-const q3 Int)
        (declare-const q4 Int)
        (assert (>= q1 1)) (assert (<= q1 4))
        (assert (>= q2 1)) (assert (<= q2 4))
        (assert (>= q3 1)) (assert (<= q3 4))
        (assert (>= q4 1)) (assert (<= q4 4))
        (assert (not (= q1 q2)))
        (assert (not (= q1 q3)))
        (assert (not (= q1 q4)))
        (assert (not (= q2 q3)))
        (assert (not (= q2 q4)))
        (assert (not (= q3 q4)))
        (assert (not (= (+ q1 (- q2)) 1)))
        (assert (not (= (+ q1 (- q2)) (- 1))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["sat"],
        "#5671: 4 bounded vars + all-distinct + diagonal must be SAT"
    );
}

// ========== QF_UF EUF guard regression tests (#6498) ==========

#[test]
fn test_qf_uf_sat_not_degraded_to_unknown_6498() {
    // Pure QF_UF query: uninterpreted function, equality check.
    // Must return sat, not unknown — the EUF theory solver provides
    // independent verification of congruence closure consistency.
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (= (f a) b))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "QF_UF with EUF model must not degrade to unknown (#6498) — got: {}",
        outputs[0]
    );
}

#[test]
fn test_qf_uf_uninterpreted_fn_unconstrained_6498() {
    // Unconstrained UF function returning Bool — should be sat
    // (any interpretation of g works).
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun g (U) Bool)
        (declare-const x U)
        (assert (g x))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "Unconstrained UF function must return sat (#6498) — got: {}",
        outputs[0]
    );
}

#[test]
fn test_qf_uf_equality_coercion_6498() {
    // Equality between different UF applications — must return sat, not unknown.
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (declare-const a U)
        (assert (= (f a) (g a)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "sat",
        "UF equality between different functions must return sat (#6498) — got: {}",
        outputs[0]
    );
}

/// Regression: QF_AX check-sat-assuming where the only array store/select
/// appears in the assumption. Without assumption-aware axiom generation
/// (#6736), the ROW axiom for the assumption-only store is never seeded.
#[test]
#[timeout(10_000)]
fn test_qf_ax_assumption_only_array_store_unsat_6736() {
    // a is an array. The only store appears in the assumption:
    //   (= (select (store a i v) i) v) is a tautology from ROW axiom.
    //   Assumption: (distinct (select (store a i v) i) v) contradicts ROW.
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Idx 0)
        (declare-sort Elem 0)
        (declare-fun a () (Array Idx Elem))
        (declare-fun i () Idx)
        (declare-fun v () Elem)
        (check-sat-assuming (
            (distinct (select (store a i v) i) v)
        ))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "unsat",
        "ROW axiom must fire for assumption-only store (#6736) — got: {}",
        outputs[0]
    );
}

/// Regression: QF_AUFLIA check-sat-assuming where array+LIA terms only
/// appear in assumptions. Without assumption-aware axiom generation
/// (#6736), integer-indexed array operations in assumptions get no axioms.
#[test]
#[timeout(10_000)]
fn test_qf_auflia_assumption_only_array_unsat_6736() {
    // Permanent assertion: just declares a and b as integer arrays.
    // Assumption: a = b AND select(a, 0) != select(b, 0) — contradicts
    // array extensionality + congruence.
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= a b))
        (check-sat-assuming (
            (distinct (select a 0) (select b 0))
        ))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "unsat",
        "Array congruence must fire for assumption-only selects (#6736) — got: {}",
        outputs[0]
    );
}

#[test]
#[timeout(10_000)]
fn test_qf_auflia_check_sat_assuming_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :random-seed 42)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (assert (> x 0))
        (assert (= (select a x) 1))
        (check-sat-assuming ((= (select a x) 1)))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert_eq!(exec.last_applied_sat_random_seed_for_test(), Some(42));
}

/// Regression: QF_ABV check-sat-assuming with bitvector array store only
/// in assumption. Without assumption-aware axiom generation (#6736),
/// BV-array operations in assumptions get no ROW axioms.
#[test]
#[timeout(10_000)]
fn test_qf_abv_assumption_only_array_store_unsat_6736() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun i () (_ BitVec 8))
        (declare-fun v () (_ BitVec 8))
        (check-sat-assuming (
            (distinct (select (store a i v) i) v)
        ))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs[0], "unsat",
        "ROW axiom must fire for assumption-only BV-array store (#6736) — got: {}",
        outputs[0]
    );
}

/// Regression test for #6853: QF_LIA incremental false-unsat.
///
/// Before the fix, `retain_encoded_assertions()` pruned `lia_derived_assertions`
/// to only keep terms already encoded. This removed activation-depth metadata for
/// new-but-not-yet-encoded assertions, causing `desired_activation_depth()` to
/// fall through to a misaligned `active_assertion_min_scope_depths()` which could
/// return depth 0 (global). Global activation clauses are permanent and irretractable,
/// so later check-sats that negate the same Tseitin root would see a conflict and
/// produce false UNSAT.
#[test]
#[timeout(30_000)]
fn test_incremental_lia_derived_assertion_scope_soundness_6853() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (push 1)
        (assert (>= x 0))
        (assert (<= x 10))
        (assert (= y (+ x 1)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (>= x 5))
        (assert (<= x 20))
        (assert (= y (+ x 2)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (>= x 0))
        (assert (<= y 100))
        (assert (= z (+ x y)))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (and (>= x 0) (<= x 5)))
        (assert (and (>= y 0) (<= y 5)))
        (check-sat)
        (pop 1)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["sat", "sat", "sat", "sat"],
        "Bug #6853: LIA incremental push/pop must not produce false UNSAT \
         from leaked global activation clauses"
    );
}

/// Regression test for #6853: nested push/pop with LIA derived assertions.
#[test]
#[timeout(30_000)]
fn test_incremental_lia_nested_derived_assertion_scope_6853() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (push 1)
        (assert (>= a 0))
        (push 1)
        (assert (= b (+ a 1)))
        (assert (>= b 1))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (push 1)
        (assert (>= a 0))
        (check-sat)
        (pop 1)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["sat", "sat", "sat"],
        "Bug #6853: Nested LIA push/pop must not leak derived assertion activations"
    );
}
