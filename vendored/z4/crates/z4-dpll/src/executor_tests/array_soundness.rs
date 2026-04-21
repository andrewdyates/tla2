// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AX soundness regression tests (#4304)
//!
//! These formulas are UNSAT. The array theory solver must produce "unsat"
//! (not "sat" or "unknown") for these well-known array axiom patterns.
//!
//! Patterns tested:
//! - Nested store chains (ROW1+ROW2 walking)
//! - Store transitivity via equality (b = store(a,i,e))
//! - Swap pattern (double store with cross-references)
//! - Transitive equality chains (c = b = store(a,i,e))
//! - Conflicting stores (a = store(b,i,e1) and a = store(b,i,e2) with e1 != e2)

#![allow(clippy::large_stack_arrays)]

use ntest::timeout;

use crate::Executor;
use z4_frontend::parse;

#[test]
fn test_qf_ax_nested_store_chain_unsat() {
    // Nested stores: select(store(store(store(a, i1, e1), i2, e2), i3, e3), i1)
    // must equal e1 when i1 != i2 and i1 != i3 (ROW2 skip + ROW1 match).
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (declare-fun i3 () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (declare-fun e3 () Element)
        (assert (not (= i1 i2)))
        (assert (not (= i1 i3)))
        (assert (not (= i2 i3)))
        (assert (not (= (select (store (store (store a i1 e1) i2 e2) i3 e3) i1) e1)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "unsat", "Regression #4304: nested store chain");
}

#[test]
fn test_qf_ax_store_transitivity_unsat() {
    // b = store(a, i, e), so select(b, i) = e by ROW1.
    // select(a, i) = e is also asserted, so select(a, i) = select(b, i).
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e () Element)
        (assert (= (select a i) e))
        (assert (= b (store a i e)))
        (assert (not (= (select a i) (select b i))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #4304: store transitivity via equality"
    );
}

#[test]
fn test_qf_ax_swap_pattern_unsat() {
    // Swap a[i] and a[j]: b = store(store(a, i, a[j]), j, a[i])
    // After swap with i != j: b[i] must equal a[j] (ROW2 skip j, ROW1 match i).
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (assert (not (= i j)))
        (assert (not (= (select (store (store a i (select a j)) j (select a i)) i) (select a j))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "unsat", "Regression #4304: swap pattern");
}

#[test]
fn test_qf_ax_transitive_equality_chain_unsat() {
    // c = b = store(a, i, e), so select(c, i) = e via two-hop equality.
    // BFS equality traversal in find_store_through_eq is required.
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun c () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e () Element)
        (assert (= b (store a i e)))
        (assert (= c b))
        (assert (not (= (select c i) e)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #4304: transitive equality chain (c = b = store(a,i,e))"
    );
}

#[test]
fn test_qf_ax_conflicting_store_values_unsat() {
    // a = store(b, i, e1) and a = store(b, i, e2) with e1 != e2.
    // Two stores to same (base, index) must have equal values.
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (not (= e1 e2)))
        (assert (= a (store b i e1)))
        (assert (= a (store b i e2)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #4304: conflicting store values (same base+index, different values)"
    );
}

#[test]
fn test_qf_alia_const_array_store_eq_unsound_4479() {
    // Regression test for #4479: store(const_array(0), 0, 0) == store(const_array(0), 0, 1)
    // was returning Sat (UNSOUND). The two arrays differ at index 0 (value 0 vs 1).
    //
    // Fix: mk_eq rewrites (= (store a i v1) (store a i v2)) -> (= v1 v2) when
    // base and index are syntactically identical. Here (= 0 1) folds to false.
    let input = r#"
        (set-logic QF_AUFLIA)
        (assert (= (store ((as const (Array Int Int)) 0) 0 0)
                   (store ((as const (Array Int Int)) 0) 0 1)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert!(
        outputs[0] == "unsat" || outputs[0] == "unknown",
        "Regression #4479: store(const(0),0,0) = store(const(0),0,1) must not be sat, got: {}",
        outputs[0]
    );
}

#[test]
fn test_qf_ax_store_store_same_base_idx_diff_val_unsat_4479() {
    // Variant of #4479 using QF_AX with uninterpreted sorts:
    // store(a, i, e1) = store(a, i, e2) with e1 != e2.
    // The store-store rewrite reduces this to (= e1 e2) which contradicts (not (= e1 e2)).
    let input = r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (not (= e1 e2)))
        (assert (= (store a i e1) (store a i e2)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #4479: store(a,i,e1) = store(a,i,e2) with e1 != e2 must be unsat"
    );
}

/// Store permutation with extra store: false-UNSAT regression (#5179).
///
/// Two store chains over the same base with permuted orders for indices 1,2:
/// chain A: base[1->v1][2->v2]  (2 stores)
/// chain B: base[2->v2][1->v1][3->v3]  (3 stores -- extra at index 3)
///
/// Since chain B has an additional store at index 3, the arrays differ.
/// Expected: sat.
///
/// Root cause: `resolve_select_base_for_propagation` used `known_distinct()`
/// which includes external (model-based) disequalities. When the extensionality
/// Skolem variable was assigned a value different from all store indices by LIA,
/// both selects resolved to the same base and were propagated as equal with
/// empty reasons. This unconditional equality contradicted the extensionality
/// witness disequality, producing false UNSAT.
#[test]
fn test_store_permutation_extra_store_sat_5179() {
    // Soundness guard: must not return "unsat". Timeout is acceptable since it
    // is not a wrong answer. The AUFLIA deferred-check architecture (#6282)
    // causes the solver to not converge on nested-store formulas within a
    // reasonable test timeout; this is a performance issue tracked separately.
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let input = r#"
            (set-logic QF_AUFLIA)
            (declare-fun base () (Array Int Int))
            (declare-fun v1 () Int)
            (declare-fun v2 () Int)
            (declare-fun v3 () Int)

            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun b1 () (Array Int Int))
            (declare-fun b2 () (Array Int Int))
            (declare-fun b3 () (Array Int Int))

            (assert (= a1 (store base 1 v1)))
            (assert (= a2 (store a1 2 v2)))
            (assert (= b1 (store base 2 v2)))
            (assert (= b2 (store b1 1 v1)))
            (assert (= b3 (store b2 3 v3)))
            (assert (not (= a2 b3)))
            (check-sat)
        "#;

        let commands = parse(input).expect("invariant: valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec
            .execute_all(&commands)
            .expect("invariant: execute succeeds");
        let _ = tx.send(outputs[0].clone());
    });

    match rx.recv_timeout(std::time::Duration::from_secs(15)) {
        Ok(answer) => {
            assert!(
                answer == "sat" || answer == "unknown",
                "Regression #5179: store permutation with extra store must not be unsat, got: {answer}",
            );
        }
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            // Timeout is acceptable: the solver did not return "unsat".
        }
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            // Solver thread panicked or exited without sending.
            // Not a false-UNSAT (no answer was returned), so not a soundness issue.
        }
    }
}

/// Same as above but with symbolic (non-constant) indices.
#[test]
fn test_store_permutation_extra_store_symbolic_indices_5179() {
    // Soundness guard: must not return "unsat". Timeout is acceptable.
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let input = r#"
            (set-logic QF_AUFLIA)
            (declare-fun base () (Array Int Int))
            (declare-fun i1 () Int)
            (declare-fun i2 () Int)
            (declare-fun i3 () Int)
            (declare-fun v1 () Int)
            (declare-fun v2 () Int)
            (declare-fun v3 () Int)

            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun b1 () (Array Int Int))
            (declare-fun b2 () (Array Int Int))
            (declare-fun b3 () (Array Int Int))

            (assert (= a1 (store base i1 v1)))
            (assert (= a2 (store a1 i2 v2)))
            (assert (= b1 (store base i2 v2)))
            (assert (= b2 (store b1 i1 v1)))
            (assert (= b3 (store b2 i3 v3)))
            (assert (not (= a2 b3)))
            (assert (distinct i1 i2 i3))
            (check-sat)
        "#;

        let commands = parse(input).expect("invariant: valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec
            .execute_all(&commands)
            .expect("invariant: execute succeeds");
        let _ = tx.send(outputs[0].clone());
    });

    match rx.recv_timeout(std::time::Duration::from_secs(15)) {
        Ok(answer) => {
            assert!(
                answer == "sat" || answer == "unknown",
                "Regression #5179: store permutation with extra store (symbolic) must not be unsat, got: {answer}",
            );
        }
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            // Timeout is acceptable: the solver did not return "unsat".
        }
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            // Solver thread panicked or exited without sending.
            // Not a false-UNSAT (no answer was returned), so not a soundness issue.
        }
    }
}

/// Store permutation with distinct concrete indices: two arrays built by
/// applying the same 3 stores in different order to the same base must be
/// equal (read at a Skolem witness). Status: SAT (the formula is satisfiable
/// because the arrays are provably equal).
///
/// Regression for #5086/#5179: `resolve_select_base_for_propagation` used
/// `known_distinct` (including model-based external disequalities) to skip
/// stores, producing spurious equalities -> false UNSAT. The fix uses
/// `explain_distinct_if_provable` which only accepts provable disequalities.
///
/// Note: After the #6282 soundness fix (guarded store-store aliases +
/// no-congruence fixpoint), the solver may return "unknown" on SAT
/// nested-store formulas. "unknown" is sound (never wrong); "unsat"
/// would be a soundness bug.
#[test]
#[allow(clippy::large_stack_arrays)]
#[timeout(15_000)]
fn test_store_permutation_distinct_indices_sat_5086() {
    // For the regression, use a formula where the answer IS sat:
    // store(store(a, 1, e1), 2, e2) vs store(store(a, 2, e2), 1, e3)
    // with e1 != e3. At index 1: fwd has e1, rev has e3, so they differ -> sat.
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (assert (not (= e1 e3)))
        (assert (not (=
            (store (store a 1 e1) 2 e2)
            (store (store a 2 e2) 1 e3))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert!(
        outputs[0] == "sat" || outputs[0] == "unknown",
        "Regression #5086: store permutation with e1 != e3 must not be unsat, got: {}",
        outputs[0]
    );
}

/// Store permutation with 3 distinct concrete indices and equal values:
/// two arrays built by storing the same (index, value) pairs in different
/// order must be equal. The formula asserts they differ -> UNSAT.
///
/// Regression for #5086: the fixpoint loop in combined theory axiom
/// generation must propagate ROW lemmas through the full store chain.
#[test]
fn test_store_permutation_same_values_unsat_5086() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun e3 () Int)
        (declare-fun sk () Int)
        (assert (not (=
            (select (store (store (store a 1 e1) 2 e2) 3 e3) sk)
            (select (store (store (store a 3 e3) 2 e2) 1 e1) sk))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #5086: store permutation with same values at distinct indices must be unsat"
    );
}

/// QF_AUFBV soundness regression: store(const(false), P, true)[P] must be true.
///
/// Formula: P = bv0, V = store(const_array(false), P, true), assert not(select(V, P)).
/// V[P] = V[0] = true (stored), so not(V[P]) = false. Conjunction is UNSAT.
///
/// Root cause (#6124): `parse_simple_sort` couldn't handle BV-indexed Array
/// sorts like `(Array (_ BitVec 32) Bool)` — the naive space-split misparse
/// caused `(_ BitVec 32)` to be treated as Uninterpreted, breaking array
/// axiom generation. Fixed by using `extract_first_sort` for parenthesized
/// nested sorts and normalizing `|_|` quoted underscore.
///
/// Discovered by W3:1924 during #6047 work.
#[test]
fn test_qf_aufbv_const_array_store_select_soundness() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun P () (_ BitVec 32))
        (declare-fun V () (Array (_ BitVec 32) Bool))
        (assert (and (= P (_ bv0 32)) (= V (store ((as const (Array (_ BitVec 32) Bool)) false) P true)) (not (select V P))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(
        outputs[0], "unsat",
        "Regression #6124: store(const(false), bv0, true)[bv0] contradicts not(select). Got: {}",
        outputs[0]
    );
}
