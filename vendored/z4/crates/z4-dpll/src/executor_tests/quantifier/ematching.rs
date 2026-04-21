// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test multi-round E-matching with chained triggers (#3994).
///
/// Round 1: P(0) matches pattern (P x), producing instantiation P(0) => Q(f(0)).
///          This introduces new ground term Q(f(0)).
/// Round 2: Q(f(0)) matches pattern (Q y), producing Q(f(0)) => false.
///          Combined with P(0) and round 1 result, this derives a contradiction.
///
/// Single-round E-matching cannot solve this because Q(f(0)) does not exist
/// as a ground term when the second quantifier is first processed.
#[test]
fn test_multiround_ematching_chained_trigger_unsat_3994() {
    let input = r#"
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

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// Test 3-hop multi-round E-matching chain (#3994, sat-debuggability #4172).
///
/// This exercises all 3 rounds of MAX_EMATCHING_ROUNDS with a 3-step chain:
///
/// Round 1: A(0) matches pattern (A x), producing: A(x) => B(f(x)).
///          Introduces new ground term B(f(0)).
/// Round 2: B(f(0)) matches pattern (B y), producing: B(y) => C(g(y)).
///          Introduces new ground term C(g(f(0))).
/// Round 3: C(g(f(0))) matches pattern (C z), producing: C(z) => false.
///          Contradiction reached only if all 3 rounds fire.
///
/// With MAX_EMATCHING_ROUNDS < 3, this would return unknown instead of unsat.
#[test]
fn test_multiround_ematching_3hop_chain_unsat_3994() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun A (Int) Bool)
        (declare-fun B (Int) Bool)
        (declare-fun C (Int) Bool)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int))
            (! (=> (A x) (B (f x)))
               :pattern ((A x)))))
        (assert (forall ((y Int))
            (! (=> (B y) (C (g y)))
               :pattern ((B y)))))
        (assert (forall ((z Int))
            (! (=> (C z) false)
               :pattern ((C z)))))
        (assert (A 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // This requires 3 rounds of E-matching:
    // Round 1: A(0) => B(f(0))
    // Round 2: B(f(0)) => C(g(f(0)))
    // Round 3: C(g(f(0))) => false
    assert_eq!(outputs, vec!["unsat"]);
}
/// Test for #3325 Gap 2: multi-trigger E-matching with two independent patterns.
///
/// forall x y. p(f(x), g(y)) :pattern ((f x) (g y))
/// With ground terms f(a), g(b), the multi-trigger should fire with x=a, y=b.
/// Asserting NOT(p(f(a), g(b))) creates a contradiction with the instantiation.
#[test]
fn test_multi_trigger_two_patterns_unsat_3325() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-fun g (S) S)
        (declare-fun p (S S) Bool)
        (declare-const a S)
        (declare-const b S)
        (assert (forall ((x S) (y S))
            (! (p (f x) (g y)) :pattern ((f x) (g y)))))
        (assert (not (p (f a) (g b))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // Multi-trigger [f(x), g(y)] matches with x=a, y=b.
    // Instantiation: p(f(a), g(b)). Combined with NOT(p(f(a), g(b))): UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Multi-trigger should fire with x=a, y=b producing contradiction"
    );
}
/// Test for #3325 Gap 2: multi-trigger with shared variable across patterns.
///
/// forall x. q(f(x), g(x)) :pattern ((f x) (g x))
/// Ground terms f(a), g(a), g(b). Only x=a is consistent (both patterns agree).
#[test]
fn test_multi_trigger_shared_var_3325() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-fun g (S) S)
        (declare-fun q (S S) Bool)
        (declare-const a S)
        (declare-const b S)
        (assert (forall ((x S))
            (! (q (f x) (g x)) :pattern ((f x) (g x)))))
        (assert (not (q (f a) (g a))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // Only x=a is consistent: f(a) matches f(x) with x=a, g(a) matches g(x) with x=a.
    // g(b) matches g(x) with x=b, but f(b) doesn't exist, so no f(x) match with x=b.
    // Instantiation: q(f(a), g(a)). With NOT(q(f(a), g(a))): UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Multi-trigger with shared variable should find consistent binding x=a"
    );
}
/// Test for #3325 Gap 1: equality-aware E-matching.
///
/// Trigger pattern f(g(x)) should match ground term f(c) when (= (g a) c) is asserted.
/// Z3 solves this via E-graph congruence. Z4 now extracts equalities from assertions
/// and uses them during matching.
#[test]
fn test_equality_aware_matching_3325() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-fun g (S) S)
        (declare-fun p (S) Bool)
        (declare-const a S)
        (declare-const c S)
        (assert (= (g a) c))
        (assert (forall ((x S)) (! (p (f (g x))) :pattern ((f (g x))))))
        (assert (not (p (f c))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // (g a) = c is asserted. f(c) should match f(g(x)) with x=a via equality.
    // Instantiation: p(f(g(a))) = p(f(c)). With NOT(p(f(c))): UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Equality-aware matching should use (g a) = c to match f(c) against f(g(x))"
    );
}
/// Regression test for #3442: E-matching with user trigger on multi-argument function.
///
/// The trigger pattern `(index view i)` should match the ground term `(index view 0)`
/// with binding `i = 0`. After instantiation, the formula becomes a simple arithmetic
/// check that is satisfiable.
///
/// This tests the sunder use case: element invariant with triggered forall.
#[test]
fn test_ematching_user_trigger_multiarg_3442() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun index (Int Int) Int)
        (declare-fun get_0 (Int) Int)
        (declare-fun get_1 (Int) Int)
        (declare-fun len (Int) Int)
        (declare-const view Int)
        (assert (= (len view) 1))
        (assert (forall ((i Int))
            (! (=> (and (>= i 0) (< i (len view)))
                   (= (+ (get_0 (index view i)) (get_1 (index view i))) 10))
               :pattern ((index view i)))))
        (assert (not (= (+ (get_0 (index view 0)) (get_1 (index view 0))) 20)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // The forall says get_0(index(view, i)) + get_1(index(view, i)) = 10 for valid indices.
    // The negated assertion says the sum != 20. Both can be satisfied (sum=10 != 20).
    // E-matching should trigger on (index view 0), binding i=0, instantiating the forall.
    assert_eq!(
        outputs,
        vec!["sat"],
        "E-matching should fire on (index view 0) matching trigger (index view i)"
    );
}
/// Regression test for #3442: E-matching trigger produces UNSAT via contradiction.
///
/// Same setup as test_ematching_user_trigger_multiarg_3442, but the negated assertion
/// contradicts the forall's instantiation: forall says sum=10 for valid indices,
/// but we assert NOT(sum=10) for index 0. E-matching must fire to derive the contradiction.
#[test]
fn test_ematching_user_trigger_multiarg_unsat_3442() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun index (Int Int) Int)
        (declare-fun get_0 (Int) Int)
        (declare-fun get_1 (Int) Int)
        (declare-fun len (Int) Int)
        (declare-const view Int)
        (assert (= (len view) 1))
        (assert (forall ((i Int))
            (! (=> (and (>= i 0) (< i (len view)))
                   (= (+ (get_0 (index view i)) (get_1 (index view i))) 10))
               :pattern ((index view i)))))
        (assert (>= 0 0))
        (assert (< 0 (len view)))
        (assert (not (= (+ (get_0 (index view 0)) (get_1 (index view 0))) 10)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // E-matching fires: (index view 0) matches trigger (index view i) with i=0.
    // Instantiation: (>= 0 0) AND (< 0 (len view)) => sum=10.
    // We also assert (>= 0 0), (< 0 (len view)), and NOT(sum=10).
    // Contradiction: implies both sum=10 and NOT(sum=10). UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "E-matching instantiation should derive contradiction"
    );
}
/// Regression test for #3325: binding save/restore in match_pattern_recursive.
///
/// This tests the specific fix where match_pattern_recursive_direct can
/// partially fill binding slots before failing, leaving dirty state that
/// breaks the equivalence class fallback.
///
/// Setup:
/// - Pattern: h(f(x, x)) — nested pattern requiring x bound consistently in both args
/// - Ground: h(f(a, b)) — only h-application, so only candidate for trigger
/// - Equality: f(a, b) = f(c, c) — provides eq-class alternative
///
/// Without the fix: direct match of f(x,x) against f(a,b) binds x=a then fails
/// (b ≠ a). binding[0]=Some(a) is dirty. Eq-class fallback tries f(c,c) but
/// sees binding[0]=Some(a), c ≠ a → fails. No match found.
///
/// With the fix: binding restored to clean state before eq-class loop.
/// f(c,c) matches with x=c. Instantiation: p(h(f(c,c))). Via congruence
/// h(f(a,b)) = h(f(c,c)), combined with ¬p(h(f(a,b))): UNSAT.
#[test]
fn test_ematching_binding_save_restore_3325() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S S) S)
        (declare-fun h (S) S)
        (declare-fun p (S) Bool)
        (declare-const a S)
        (declare-const b S)
        (declare-const c S)
        (assert (distinct a b))
        (assert (distinct a c))
        (assert (distinct b c))
        (assert (= (f a b) (f c c)))
        (assert (forall ((x S)) (! (p (h (f x x))) :pattern ((h (f x x))))))
        (assert (not (p (h (f a b)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // The only h-application is h(f(a,b)). Pattern h(f(x,x)) must match via
    // eq-class: f(a,b) = f(c,c), so f(x,x) matches f(c,c) with x=c.
    // Requires clean binding state after failed direct match of f(x,x) on f(a,b).
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Binding save/restore must allow eq-class match after failed direct match"
    );
}
/// Regression: E-matching subst_vars must recurse into nested quantifier bodies.
///
/// Without the fix (subst_vars returning nested Forall/Exists unchanged), the outer
/// quantifier's variable `x` is NOT substituted inside the inner forall body.
/// This leaves `x` as a dangling free variable, preventing proper instantiation.
///
/// With the fix: outer instantiation x=a produces inner forall with (f a) replacing (f x).
/// Inner forall is then instantiated with y=5 (via E-matching on `p(y)` matching `p(5)`).
/// The ground formula (=> (= 5 (f a)) (p 5)) simplifies to (p 5), contradicting ¬(p 5).
#[test]
fn test_nested_forall_subst_vars_recurse() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-fun p (Int) Bool)
        (declare-const a Int)
        (assert (= (f a) 5))
        (assert (not (p 5)))
        (assert (forall ((x Int))
          (! (forall ((y Int)) (=> (= y (f x)) (p y)))
             :pattern ((f x)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // With nested substitution fix: UNSAT
    // Round 1: E-matching instantiates outer forall with x=a (trigger f(x) matches f(a)).
    //   Body becomes: forall y. (=> (= y (f a)) (p y))
    // Round 2: Inner forall instantiated with y=5 (trigger p(y) matches p(5)).
    //   Ground: (=> (= 5 (f a)) (p 5)) = (=> true (p 5)) = (p 5).
    //   Combined with ¬(p 5): UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Nested quantifier substitution must recurse into inner forall body"
    );
}
/// Test capture-avoidance: inner quantifier's bound variable shadows same-name outer variable.
/// Frontend renames to avoid this, but subst_vars must handle it correctly for API usage.
#[test]
fn test_nested_forall_capture_avoidance() {
    // forall x. (forall x. (= x 0)) is equivalent to forall y. true (inner x is independent).
    // The outer x has trigger f(x). Instantiating outer x=a should NOT affect inner x.
    // Inner forall (= x 0) is an equality constraint on x; CEGQI handles it.
    //
    // Note: The frontend renames inner x to x_0 (or similar), so in practice the names
    // don't collide. This test verifies correctness for direct API usage where names
    // could overlap.
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (assert (= (f a) 5))
        (assert (forall ((x Int))
          (! (forall ((x Int)) (= x 0))
             :pattern ((f x)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // The inner forall (= x 0) says every Int is 0, which is false.
    // But Z4 may return unknown for this (CEGQI/enumerative limitation).
    // The key correctness requirement: outer x=a substitution must NOT
    // affect inner x. If it does, inner becomes (= a 0) which is satisfiable
    // (just set a=0), leading to an unsound SAT.
    // Accept either "unsat" or "unknown" - but NOT "sat"
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "Must not return SAT (would indicate capture-avoidance failure): got {outputs:?}",
    );
}
/// #7883: sunder's Seq concat-length axiom must match against ground Seq terms
/// in the E-matching pool.
///
/// The contradiction is only exposed if the trigger `(seq_concat s1 s2)`
/// matches the concrete ground term `(seq_concat a b)` and instantiates the
/// length equation for `a` and `b`.
#[test]
fn test_ematching_sunder_seq_concat_len_pattern_unsat_7883() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort Seq 0)
        (declare-fun seq_len (Seq) Int)
        (declare-fun seq_concat (Seq Seq) Seq)
        (declare-const a Seq)
        (declare-const b Seq)
        (assert (forall ((s1 Seq) (s2 Seq))
            (! (= (seq_len (seq_concat s1 s2))
                  (+ (seq_len s1) (seq_len s2)))
               :pattern ((seq_concat s1 s2)))))
        (assert (= (seq_len a) 1))
        (assert (= (seq_len b) 2))
        (assert (not (= (seq_len (seq_concat a b)) 3)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Seq concat trigger should instantiate on the ground term (seq_concat a b)"
    );
}
/// #7883: sunder's Seq index bridge trigger must match mixed Seq/Int ground terms.
///
/// The pattern `(seq_index_logic s i)` is the standard-library trigger shape
/// used by sunder's array-backed sequence bridge. The formula is UNSAT only if
/// E-matching picks up the concrete ground term `(seq_index_logic a 0)`.
#[test]
fn test_ematching_sunder_seq_index_logic_pattern_unsat_7883() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort Seq 0)
        (declare-fun seq_index_logic (Seq Int) Int)
        (declare-const a Seq)
        (assert (forall ((s Seq) (i Int))
            (! (= (seq_index_logic s i) i)
               :pattern ((seq_index_logic s i)))))
        (assert (not (= (seq_index_logic a 0) 0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Seq index trigger should instantiate on the ground term (seq_index_logic a 0)"
    );
}
/// Auto multi-trigger synthesis (#3325 item 2b): two disjoint-coverage patterns.
///
/// Formula:
///   (forall (x y) (=> (and (P x) (Q y)) (R x y)))
///   (P a)
///   (Q b)
///   (not (R a b))
///
/// No single auto-extracted pattern covers both x and y:
///   - P(x) covers {x}
///   - Q(y) covers {y}
///   - R(x,y) covers {x,y} but R is also under negation in the quantifier body
///
/// The auto multi-trigger synthesis should combine P(x) and Q(y) into a
/// multi-trigger group that covers both variables. The multi-trigger join
/// produces binding [x=a, y=b], and the instantiation contradicts (not (R a b)).
#[test]
fn test_auto_multi_trigger_synthesis_two_patterns() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun R (U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U) (y U)) (=> (and (P x) (Q y)) (R x y))))
        (assert (P a))
        (assert (Q b))
        (assert (not (R a b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // With auto multi-trigger synthesis: P(x)+Q(y) triggers, binds [a,b], produces
    // (=> (and (P a) (Q b)) (R a b)), combined with P(a), Q(b), not(R a b) → UNSAT
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Auto multi-trigger synthesis should combine P(x) and Q(y) to derive UNSAT"
    );
}
/// Auto multi-trigger synthesis: full-coverage single pattern takes priority.
///
/// Formula:
///   (forall (x y) (=> (F x y) (G x y)))
///   (F a b)
///   (not (G a b))
///
/// F(x,y) covers both x and y — a single trigger suffices.
/// Multi-trigger synthesis should NOT be needed.
#[test]
fn test_auto_multi_trigger_full_coverage_single_preferred() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun F (U U) Bool)
        (declare-fun G (U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U) (y U)) (=> (F x y) (G x y))))
        (assert (F a b))
        (assert (not (G a b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Single full-coverage trigger F(x,y) should suffice"
    );
}
/// Auto multi-trigger synthesis: three bound variables, three unary patterns.
///
/// Formula:
///   (forall (x y z) (=> (and (P x) (Q y) (S z)) (R x y z)))
///   (P a) (Q b) (S c)
///   (not (R a b c))
///
/// No single pattern covers all three vars. Synthesis combines P(x)+Q(y)+S(z)
/// into a triple multi-trigger.
#[test]
fn test_auto_multi_trigger_synthesis_three_vars() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun S (U) Bool)
        (declare-fun R (U U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun c () U)
        (assert (forall ((x U) (y U) (z U)) (=> (and (P x) (Q y) (S z)) (R x y z))))
        (assert (P a))
        (assert (Q b))
        (assert (S c))
        (assert (not (R a b c)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Triple multi-trigger P(x)+Q(y)+S(z) should combine to derive UNSAT"
    );
}
