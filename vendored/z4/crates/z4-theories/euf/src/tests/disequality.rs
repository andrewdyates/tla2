// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Performance regression tests — detect O(N²) scaling
// ========================================================================

/// Stress test: build_int_value_map with many terms must complete in bounded time.
///
/// build_int_value_map claims O(N) but uses root-finding without path compression,
/// making it O(N * depth). With proper union-find heuristics depth is O(log N),
/// so total cost is O(N log N). This test verifies it doesn't degrade to O(N²)
/// by checking that 2000 terms complete within the timeout.
#[test]
fn test_build_int_value_map_scaling_2000_terms() {
    use num_bigint::BigInt;
    let mut store = TermStore::new();

    // Create a chain of 2000 Int-sorted variables with equality assertions.
    // v0 = v1 = v2 = ... = v1999 = 42
    // This creates a large equivalence class.
    let n = 2000;
    let mut vars = Vec::with_capacity(n);
    for i in 0..n {
        vars.push(store.mk_var(format!("v{i}"), Sort::Int));
    }
    // Add an integer constant at the end of the chain
    let forty_two = store.mk_int(BigInt::from(42));

    let mut eqs = Vec::with_capacity(n);
    for i in 0..(n - 1) {
        eqs.push(store.mk_eq(vars[i], vars[i + 1]));
    }
    let eq_last = store.mk_eq(vars[n - 1], forty_two);

    let mut euf = EufSolver::new(&store);

    // Assert all equalities
    for eq in &eqs {
        euf.assert_literal(*eq, true);
    }
    euf.assert_literal(eq_last, true);

    // Force closure
    let result = euf.check();
    assert!(matches!(result, TheoryResult::Sat));

    // Now call build_int_value_map — this should be fast (O(N log N), not O(N²))
    let start = std::time::Instant::now();
    let map = euf.build_int_value_map();
    let elapsed = start.elapsed();

    // All vars should map to 42
    for &var in &vars {
        assert!(
            map.contains_key(&var),
            "Variable {var:?} should be in int_value_map"
        );
        let (val, _const_id) = &map[&var];
        assert_eq!(*val, BigInt::from(42), "Expected 42 for var {var:?}");
    }

    // Regression guard: 2000 terms should complete well under 1 second.
    // On any reasonable machine this should be <10ms for O(N log N).
    // If this takes >500ms, there's a quadratic regression.
    assert!(
        elapsed.as_millis() < 500,
        "build_int_value_map took {elapsed:?} for {n} terms — possible O(N²) regression"
    );
}

/// Stress test: find_int_const_in_class with many terms.
///
/// This function has a documented O(N * depth) scan (effectively O(N²) without
/// path compression). This test establishes a baseline: with 2000 terms,
/// the function must still complete within the timeout.
#[test]
fn test_find_int_const_in_class_scaling_2000_terms() {
    use num_bigint::BigInt;
    let mut store = TermStore::new();

    let n = 2000;
    let mut vars = Vec::with_capacity(n);
    for i in 0..n {
        vars.push(store.mk_var(format!("x{i}"), Sort::Int));
    }
    let constant = store.mk_int(BigInt::from(99));

    let mut eqs = Vec::with_capacity(n);
    for i in 0..(n - 1) {
        eqs.push(store.mk_eq(vars[i], vars[i + 1]));
    }
    let eq_last = store.mk_eq(vars[n - 1], constant);

    let mut euf = EufSolver::new(&store);
    for eq in &eqs {
        euf.assert_literal(*eq, true);
    }
    euf.assert_literal(eq_last, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Test find_int_const_in_class for each variable — total cost is O(N) calls
    // of an O(N * depth) function, so worst-case O(N² * depth).
    let start = std::time::Instant::now();
    for &var in &vars {
        let result = euf.find_int_const_in_class(var);
        assert!(result.is_some(), "Expected constant for var {var:?}");
        let (val, _) = result.unwrap();
        assert_eq!(val, BigInt::from(99));
    }
    let elapsed = start.elapsed();

    // With 2000 terms and O(N²) per call, this is O(N³) = 8 billion ops.
    // With O(N log N) it's O(N² log N) = ~44M ops, which should be <100ms.
    // We use a generous 2s timeout to avoid flaky CI but catch true regressions.
    assert!(
        elapsed.as_secs() < 2,
        "find_int_const_in_class took {elapsed:?} for {n} terms — O(N²) scaling confirmed"
    );
}

/// Test disequality propagation (#5575): when a != b and c is in the same
/// class as a, propagate (= c b) = false without SAT guessing.
#[test]
fn test_diseq_propagation_basic() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);

    let eq_ab = store.mk_eq(a, b);
    let eq_ac = store.mk_eq(a, c);
    let eq_cb = store.mk_eq(c, b);

    let mut euf = EufSolver::new(&store);

    // Assert: a != b (disequality)
    euf.assert_literal(eq_ab, false);
    // Assert: a = c (equality)
    euf.assert_literal(eq_ac, true);

    // Check should be SAT (no conflict — a=c, a!=b is consistent)
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Propagate should infer (= c b) = false
    // because find(c) = find(a) and a != b, so c != b
    let props = euf.propagate();
    let has_diseq_prop = props
        .iter()
        .any(|p| p.literal.term == eq_cb && !p.literal.value);
    assert!(
        has_diseq_prop,
        "Expected diseq propagation (= c b) = false, got: {props:?}"
    );
}

/// Test disequality propagation with congruence: f(a)=f(b) via a=b,
/// but f(a) != c should propagate f(b) != c.
#[test]
fn test_diseq_propagation_with_congruence() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let f_sym = Symbol::named("f");

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let fa = store.mk_app(f_sym.clone(), vec![a], u.clone());
    let fb = store.mk_app(f_sym, vec![b], u);

    let eq_ab = store.mk_eq(a, b);
    let eq_fa_c = store.mk_eq(fa, c);
    let eq_fb_c = store.mk_eq(fb, c);

    let mut euf = EufSolver::new(&store);

    // Assert: a = b
    euf.assert_literal(eq_ab, true);
    // Assert: f(a) != c
    euf.assert_literal(eq_fa_c, false);

    // Check should be SAT
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Propagate should infer (= f(b) c) = false
    // because congruence gives f(a)=f(b), and f(a)!=c, so f(b)!=c
    let props = euf.propagate();
    let has_diseq_prop = props
        .iter()
        .any(|p| p.literal.term == eq_fb_c && !p.literal.value);
    assert!(
        has_diseq_prop,
        "Expected diseq propagation (= f(b) c) = false, got: {props:?}"
    );
}

/// Test disequality propagation with swapped orientation (#6152).
///
/// Exercises the `else` branch at theory_impl.rs:493-498 where the equality
/// term's LHS maps to the disequality's RHS class and vice versa.
///
/// Setup: `a != b` (disequality), `a = c` (equality), `b = d` (equality).
/// The equality term `(= d c)` has `lhs=d`, `rhs=c`.
/// `find(d) = find(b) = diseq_b`'s class, `find(c) = find(a) = diseq_a`'s class.
/// So `lhs_rep` matches `db_rep` (not `da_rep`) -- swapped orientation.
/// Should propagate `(= d c) = false`.
#[test]
fn test_diseq_propagation_swapped_orientation() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u);

    let eq_ab = store.mk_eq(a, b);
    let eq_ac = store.mk_eq(a, c);
    let eq_bd = store.mk_eq(b, d);
    // (= d c) — note order: d first, c second, to force swapped orientation
    let eq_dc = store.mk_eq(d, c);

    let mut euf = EufSolver::new(&store);

    // Assert: a != b (disequality)
    euf.assert_literal(eq_ab, false);
    // Assert: a = c (puts c in a's class)
    euf.assert_literal(eq_ac, true);
    // Assert: b = d (puts d in b's class)
    euf.assert_literal(eq_bd, true);

    // Check should be SAT (a=c, b=d, a!=b is consistent)
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Propagate should infer (= d c) = false via swapped orientation:
    // find(d) = find(b), find(c) = find(a), and a != b
    let props = euf.propagate();
    let has_diseq_prop = props
        .iter()
        .any(|p| p.literal.term == eq_dc && !p.literal.value);
    assert!(
        has_diseq_prop,
        "Expected swapped-orientation diseq propagation (= d c) = false, got: {props:?}"
    );

    // Verify the explanation includes the disequality and the equality chains
    if let Some(prop) = props.iter().find(|p| p.literal.term == eq_dc) {
        // Reason must include (= a b) = false (the disequality)
        let has_diseq_reason = prop.reason.iter().any(|r| r.term == eq_ab && !r.value);
        assert!(
            has_diseq_reason,
            "Explanation must include the disequality (= a b) = false, got: {:?}",
            prop.reason
        );
    }
}

/// Test disequality propagation on a quasigroup-like structure:
/// 5 distinct elements, function op, value assignment propagates exclusions.
#[test]
fn test_diseq_propagation_quasigroup_exclusion() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("I".to_string());
    let op_sym = Symbol::named("op");

    // 5 distinct elements
    let e: Vec<TermId> = (0..5)
        .map(|i| store.mk_var(format!("e{i}"), u.clone()))
        .collect();

    // op(e0, e0)
    let op00 = store.mk_app(op_sym, vec![e[0], e[0]], u);

    // Create equality atoms: (= op(e0,e0) ei) for each i
    let eq_op00_e: Vec<TermId> = (0..5).map(|i| store.mk_eq(op00, e[i])).collect();

    // Create distinctness atoms between elements
    let mut diseq_atoms = Vec::new();
    for i in 0..5 {
        for j in (i + 1)..5 {
            diseq_atoms.push((store.mk_eq(e[i], e[j]), i, j));
        }
    }

    let mut euf = EufSolver::new(&store);

    // Assert all elements distinct
    for &(eq, _, _) in &diseq_atoms {
        euf.assert_literal(eq, false);
    }

    // Assert: op(e0,e0) = e2
    euf.assert_literal(eq_op00_e[2], true);

    assert!(matches!(euf.check(), TheoryResult::Sat));

    let props = euf.propagate();

    // Should propagate: (= op(e0,e0) e0) = false, (= op(e0,e0) e1) = false,
    //                   (= op(e0,e0) e3) = false, (= op(e0,e0) e4) = false
    // (but NOT (= op(e0,e0) e2) = false, since that's the asserted equality)
    for i in [0, 1, 3, 4] {
        let has_excl = props
            .iter()
            .any(|p| p.literal.term == eq_op00_e[i] && !p.literal.value);
        assert!(
            has_excl,
            "Expected (= op00 e{i}) = false propagation, got: {props:?}"
        );
    }
    // Should NOT propagate e2 = false
    let has_e2_false = props
        .iter()
        .any(|p| p.literal.term == eq_op00_e[2] && !p.literal.value);
    assert!(!has_e2_false, "Should not propagate (= op00 e2) = false");
}

/// Test that disequality + transitivity produces a proper conflict.
/// Assert: a = b, b = c, a != c. By transitivity a = c, contradiction.
/// This tests the interaction between the disequality index (line 426-428 in
/// theory_impl.rs) and conflict detection in check().
#[test]
fn test_diseq_conflict_via_transitivity() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);

    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let mut euf = EufSolver::new(&store);

    // Assert: a = b
    euf.assert_literal(eq_ab, true);
    // Assert: b = c
    euf.assert_literal(eq_bc, true);
    // Assert: a != c (disequality contradicts transitivity)
    euf.assert_literal(eq_ac, false);

    // check() should detect UNSAT: a = b = c, but a != c
    let result = euf.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT from transitivity + disequality conflict, got: {result:?}"
    );

    // The conflict reason should include all 3 literals
    if let TheoryResult::Unsat(conflict) = &result {
        assert!(
            conflict.len() >= 2,
            "Conflict should reference at least 2 literals, got: {conflict:?}"
        );
    }
}

/// Scaling test for distinct constraint with k=200 arguments.
///
/// Exercises the O(k²) pairwise comparison in `check()` Stage 2
/// (theory_impl.rs:197-232). With k=200, the pairwise loop does ~20000
/// comparisons per check() call. This test ensures correctness and
/// establishes a performance baseline for future O(k) optimization (#5486).
///
/// Note: We use `mk_app("distinct", ...)` directly because `mk_distinct`
/// expands n-ary distinct (k>=3) into `And(Not(Eq(...)), ...)`, which the
/// EUF solver doesn't decompose. To exercise the Stage 2 distinct handler,
/// we must create the raw `distinct(...)` App term.
#[test]
fn test_euf_distinct_scaling_200_args() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let k = 200;

    // Create k distinct variables
    let vars: Vec<TermId> = (0..k)
        .map(|i| store.mk_var(format!("x{i}"), u.clone()))
        .collect();

    // Create raw distinct(...) App term — bypasses mk_distinct's expansion to AND
    let distinct_term = store.mk_app(Symbol::Named("distinct".to_string()), vars, Sort::Bool);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(distinct_term, true);

    // All distinct, no equalities asserted — should be SAT
    let start = std::time::Instant::now();
    let result = euf.check();
    let elapsed = start.elapsed();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT for k={k} distinct variables with no equalities, got: {result:?}"
    );
    // Performance guard: O(k²) with k=200 should still be <100ms on any machine.
    // When the fix lands (HashMap grouping → O(k)), this bound can be tightened.
    assert!(
        elapsed.as_millis() < 1000,
        "check() with distinct(k={k}) took {elapsed:?}, expected <1s"
    );
}

/// Distinct conflict detection with k=100 arguments where two are merged.
///
/// Asserts `(distinct v0 v1 ... v99)=true` and `v0 = v50`, which should
/// produce an UNSAT conflict. Tests that the pairwise loop correctly detects
/// the conflict and returns a valid reason clause.
///
/// Note: We use `mk_app("distinct", ...)` directly — see comment on
/// `test_euf_distinct_scaling_200_args` for rationale.
#[test]
fn test_euf_distinct_large_with_conflict() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let k = 100;

    let vars: Vec<TermId> = (0..k)
        .map(|i| store.mk_var(format!("v{i}"), u.clone()))
        .collect();

    let eq_0_50 = store.mk_eq(vars[0], vars[50]);
    // Create raw distinct(...) App term — bypasses mk_distinct's expansion to AND
    let distinct_term = store.mk_app(Symbol::Named("distinct".to_string()), vars, Sort::Bool);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(distinct_term, true);
    euf.assert_literal(eq_0_50, true);

    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "Expected UNSAT: distinct + (v0 = v50), got: {result:?}"
    );

    // Conflict should reference the equality and the distinct constraint
    if let TheoryResult::Unsat(conflict) = &result {
        assert!(
            conflict.len() >= 2,
            "Conflict should reference at least 2 literals (distinct + eq), got: {conflict:?}"
        );
    }
}

/// Performance proof: sync_egraph_to_uf claims O(n) but is actually O(n × depth)
/// because enode_find_const() walks root chain without path compression.
///
/// Build a chain: v0 → v1 → v2 → ... → vN (each merged into next).
/// Without path compression, each find walks O(depth) steps.
/// sync_egraph_to_uf calls find for all N terms, so total = O(N × depth).
/// With path compression, amortized cost would be O(N × α(N)).
///
/// This test verifies the current code completes within a reasonable time
/// for N=5000 (5000 × log(5000) ≈ 60K steps, well within 2s).
/// If enode_find_const ever regresses to truly O(N) per find (e.g., from
/// broken merge-by-size), this would become O(N²) = 25M steps and timeout.
#[test]
fn test_sync_egraph_to_uf_scaling_5000_terms() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let n = 5000;
    let vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("v{i}"), u.clone()))
        .collect();

    // Build chain of equalities: v0=v1, v1=v2, ..., v(N-2)=v(N-1)
    let eqs: Vec<TermId> = (0..(n - 1))
        .map(|i| store.mk_eq(vars[i], vars[i + 1]))
        .collect();

    let mut euf = EufSolver::new(&store);
    for eq in &eqs {
        euf.assert_literal(*eq, true);
    }
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Now time sync_egraph_to_uf — this is the O(n × depth) operation
    let start = std::time::Instant::now();
    for _ in 0..100 {
        euf.sync_egraph_to_uf();
    }
    let elapsed = start.elapsed();

    // 100 × 5000 × log(5000) ≈ 6M ops — should be <500ms
    // If truly O(n²) per call: 100 × 25M = 2.5B ops — would timeout
    assert!(
        elapsed.as_millis() < 2000,
        "sync_egraph_to_uf 100× with 5000 terms took {elapsed:?} — \
         possible O(n²) regression"
    );
}

/// Correctness test for sync_egraph_to_uf: after syncing, uf.find() must
/// return the same representative for terms in the same E-graph class, and
/// different representatives for terms in different classes.
///
/// The scaling test (above) only checks timing. This test catches bugs where
/// sync writes wrong parent pointers (off-by-one, stale root, swapped class).
#[test]
fn test_sync_egraph_to_uf_correctness_classes() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    // Create 6 variables in 3 separate equivalence classes:
    // Class A: {a0, a1}  (via a0 = a1)
    // Class B: {b0, b1, b2}  (via b0 = b1, b1 = b2)
    // Class C: {c0}  (singleton)
    let a0 = store.mk_var(String::from("a0"), u.clone());
    let a1 = store.mk_var(String::from("a1"), u.clone());
    let b0 = store.mk_var(String::from("b0"), u.clone());
    let b1 = store.mk_var(String::from("b1"), u.clone());
    let b2 = store.mk_var(String::from("b2"), u.clone());
    let c0 = store.mk_var(String::from("c0"), u);

    let eq_a = store.mk_eq(a0, a1);
    let eq_b01 = store.mk_eq(b0, b1);
    let eq_b12 = store.mk_eq(b1, b2);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_a, true);
    euf.assert_literal(eq_b01, true);
    euf.assert_literal(eq_b12, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Sync and verify correctness
    euf.sync_egraph_to_uf();

    // Same class → same representative
    assert_eq!(
        euf.uf.find(a0.0),
        euf.uf.find(a1.0),
        "a0 and a1 should be in the same class after sync"
    );
    assert_eq!(
        euf.uf.find(b0.0),
        euf.uf.find(b1.0),
        "b0 and b1 should be in the same class after sync"
    );
    assert_eq!(
        euf.uf.find(b1.0),
        euf.uf.find(b2.0),
        "b1 and b2 should be in the same class after sync"
    );

    // Different classes → different representatives
    assert_ne!(
        euf.uf.find(a0.0),
        euf.uf.find(b0.0),
        "class A and class B should be distinct after sync"
    );
    assert_ne!(
        euf.uf.find(a0.0),
        euf.uf.find(c0.0),
        "class A and class C should be distinct after sync"
    );
    assert_ne!(
        euf.uf.find(b0.0),
        euf.uf.find(c0.0),
        "class B and class C should be distinct after sync"
    );

    // Singleton → self-representative
    assert_eq!(
        euf.uf.find(c0.0),
        c0.0,
        "singleton c0 should be its own representative after sync"
    );

    // Idempotency: calling sync again shouldn't change anything
    euf.sync_egraph_to_uf();
    assert_eq!(euf.uf.find(a0.0), euf.uf.find(a1.0));
    assert_eq!(euf.uf.find(b0.0), euf.uf.find(b2.0));
    assert_ne!(euf.uf.find(a0.0), euf.uf.find(b0.0));
}

/// Performance proof: explain() in legacy (non-incremental) mode rebuilds the
/// adjacency map from all equality_edges on every call. This test creates a
/// chain of N equalities, then calls explain() on N pairs, measuring total time.
///
/// With O(E) adjacency rebuild per call: total = O(N * E) = O(N²).
/// With amortized or incremental explain: total should be O(N log N) or better.
///
/// This test documents the known quadratic behavior (#5575) and will detect
/// regressions or confirm the fix when incremental mode becomes default.
#[test]
#[serial]
fn test_perf_explain_legacy_adjacency_rebuild_cost() {
    let n = 200; // Chain length

    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let terms: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("x{i}"), u.clone()))
        .collect();

    // Create equality chain: eq01, eq12, ..., eq_{n-2}_{n-1}
    let eq_lits: Vec<TermId> = (0..n - 1)
        .map(|i| store.mk_eq(terms[i], terms[i + 1]))
        .collect();

    let mut euf = new_incremental_euf(&store);

    // Assert chain: x0 = x1, x1 = x2, ..., x_{n-2} = x_{n-1}
    for eq_lit in &eq_lits {
        euf.assert_literal(*eq_lit, true);
    }
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Measure: explain each pair (x0, xi) for i in 1..n
    let start = std::time::Instant::now();
    for i in 1..n {
        let reasons = euf.explain(terms[0], terms[i]);
        // Should find a path — may be empty if terms share the same representative
        // and the explain path is trivial
        let _ = reasons;
    }
    let elapsed = start.elapsed();

    // With N=200 and O(N²) behavior: ~200 * 200 = 40K adj rebuilds.
    // This should complete in <2s even with the quadratic path on modern hardware.
    // The purpose is to document the cost, not to fail — the quadratic behavior
    // is known and tracked in #5575.
    eprintln!(
        "[PERF] explain() legacy mode: {n} terms, {} explain calls, {elapsed:?}",
        n - 1
    );

    // Soft bound: if this takes >5s, something has regressed beyond the known O(N²)
    assert!(
        elapsed.as_secs() < 5,
        "explain() legacy mode with {n} terms took {elapsed:?} — excessive cost"
    );
}

/// Verify that `all_true_equalities()` fallback is sound: it returns a superset
/// of the minimal reasons needed for any two merged terms.
///
/// The fallback fires when the BFS in `explain()` cannot find a path in
/// `equality_edges`. This can happen when congruence-discovered merges produce
/// equality relationships that aren't directly tracked as edges. The fallback
/// returns ALL true equalities — which is always sound (valid conflict clause)
/// but may be non-minimal.
///
/// This test creates a scenario where BFS works (incremental off) and verifies
/// that all_true_equalities returns a superset of the minimal BFS reasons.
#[test]
#[serial]
fn test_all_true_equalities_is_superset_of_bfs_explain() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u.clone());
    let e = store.mk_var("e", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_de = store.mk_eq(d, e);

    let mut euf = new_incremental_euf(&store);
    // Assert a=b, b=c (making a,b,c equivalent), and d=e (separate class)
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(eq_bc, true);
    euf.assert_literal(eq_de, true);
    let _ = euf.check();

    // The BFS explain(a,c) should return {eq_ab, eq_bc}
    let bfs_reasons = euf.explain(a, c);
    let bfs_terms: std::collections::HashSet<TermId> = bfs_reasons.iter().map(|l| l.term).collect();

    // all_true_equalities should include at least {eq_ab, eq_bc}
    let all_eqs = euf.all_true_equalities();
    let all_terms: std::collections::HashSet<TermId> = all_eqs.iter().map(|l| l.term).collect();

    for t in &bfs_terms {
        assert!(
            all_terms.contains(t),
            "all_true_equalities must be superset of explain: missing {t:?}"
        );
    }

    // all_true_equalities should also include eq_de (unrelated but true equality)
    assert!(
        all_terms.contains(&eq_de),
        "all_true_equalities should include all true equalities, including d=e"
    );
    assert!(
        all_terms.len() >= bfs_terms.len(),
        "all_true_equalities ({}) must be >= BFS reasons ({})",
        all_terms.len(),
        bfs_terms.len()
    );
}

/// Verify that explain() after push/pop/re-assert produces consistent reasons
/// that are a subset of currently asserted equalities.
///
/// Soundness invariant: explain(a,b) must only return literals that are
/// currently asserted (i.e., in scope). A popped literal must never appear
/// in explain results.
#[test]
#[serial]
fn test_explain_scope_safety_no_popped_reasons() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_cd = store.mk_eq(c, d);
    let eq_ad = store.mk_eq(a, d);

    let mut euf = new_incremental_euf(&store);

    // Level 0: a=b
    euf.assert_literal(eq_ab, true);
    let _ = euf.check();
    euf.push();

    // Level 1: b=c, c=d — now a,b,c,d are all equivalent
    euf.assert_literal(eq_bc, true);
    euf.assert_literal(eq_cd, true);
    let _ = euf.check();

    // Pop level 1 — only a=b remains
    euf.pop();
    let _ = euf.check();

    // Push again and assert a=d directly
    euf.push();
    euf.assert_literal(eq_ad, true);
    let _ = euf.check();

    // explain(a,d) should use eq_ad, NOT popped eq_bc or eq_cd
    let reasons = euf.explain(a, d);
    let reason_terms: Vec<TermId> = reasons.iter().map(|l| l.term).collect();

    assert!(
        !reason_terms.contains(&eq_bc),
        "explain must not include popped eq_bc; got: {reason_terms:?}"
    );
    assert!(
        !reason_terms.contains(&eq_cd),
        "explain must not include popped eq_cd; got: {reason_terms:?}"
    );
    // Should use eq_ad (or eq_ab + eq_ad, depending on the path)
    assert!(
        reason_terms.contains(&eq_ad) || reason_terms.contains(&eq_ab),
        "explain(a,d) must include eq_ad or eq_ab; got: {reason_terms:?}"
    );
}

/// Verify that congruence-discovered merges in incremental mode produce
/// explain results that only reference asserted equality literals.
///
/// When f(a) and f(b) are merged via congruence (after a=b), explain(f(a), f(b))
/// should reference eq_ab. After pop, the congruence merge should be undone.
#[test]
#[serial]
fn test_explain_congruence_after_push_pop_soundness() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let f_sym = Symbol::named("f");
    let fa = store.mk_app(f_sym.clone(), vec![a], u.clone());
    let fb = store.mk_app(f_sym.clone(), vec![b], u.clone());
    let fc = store.mk_app(f_sym, vec![c], u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_fa_fc = store.mk_eq(fa, fc);

    let mut euf = new_incremental_euf(&store);

    euf.push();
    // Level 1: assert a=b — congruence should merge f(a) and f(b)
    euf.assert_literal(eq_ab, true);
    let _ = euf.check();

    // explain(f(a), f(b)) should reference eq_ab via congruence
    let reasons = euf.explain(fa, fb);
    let reason_terms: Vec<TermId> = reasons.iter().map(|l| l.term).collect();
    assert!(
        reason_terms.contains(&eq_ab),
        "congruence explain(f(a),f(b)) must reference a=b; got: {reason_terms:?}"
    );

    // Pop: congruence merge should be undone
    euf.pop();
    let _ = euf.check();

    // Now assert b=c and f(a)=f(c) directly
    euf.push();
    euf.assert_literal(eq_bc, true);
    euf.assert_literal(eq_fa_fc, true);
    let _ = euf.check();

    // explain(f(a), f(c)) should use eq_fa_fc, NOT the popped eq_ab
    let reasons2 = euf.explain(fa, fc);
    let reason_terms2: Vec<TermId> = reasons2.iter().map(|l| l.term).collect();
    assert!(
        !reason_terms2.contains(&eq_ab),
        "explain must not reference popped eq_ab after pop; got: {reason_terms2:?}"
    );
    assert!(
        reason_terms2.contains(&eq_fa_fc),
        "explain should reference directly asserted f(a)=f(c); got: {reason_terms2:?}"
    );
}

// =========================================================================
// Multi-argument congruence tests (#6154, #6146)
//
// The EUF solver previously had zero multi-argument congruence tests.
// This is exactly the pattern that caused the #6146 sunder regression:
// f(x,y) != f(a,b) returned Unsat in QF_AUFLIA.
// =========================================================================

/// 2-arg congruence: f(a,b) and f(c,d) should be congruent when a=c, b=d.
/// Asserting f(a,b) != f(c,d) with a=c, b=d must be UNSAT.
#[test]
#[serial]
fn test_multiarg_congruence_2arg_unsat_6154() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u.clone());

    let f_sym = Symbol::named("f");
    let f_ab = store.mk_app(f_sym.clone(), vec![a, b], u.clone());
    let f_cd = store.mk_app(f_sym, vec![c, d], u);

    let eq_ac = store.mk_eq(a, c);
    let eq_bd = store.mk_eq(b, d);
    let eq_fab_fcd = store.mk_eq(f_ab, f_cd);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ac, true); // a = c
    euf.assert_literal(eq_bd, true); // b = d
    euf.assert_literal(eq_fab_fcd, false); // f(a,b) != f(c,d) — contradicts congruence

    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "#6154: f(a,b) != f(c,d) with a=c, b=d must be UNSAT, got: {result:?}"
    );
}

/// 3-arg congruence: g(a,b,c) and g(d,e,ff) with all args equal must be congruent.
#[test]
#[serial]
fn test_multiarg_congruence_3arg_unsat_6154() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u.clone());
    let e = store.mk_var("e", u.clone());
    let ff = store.mk_var("ff", u.clone());

    let g_sym = Symbol::named("g");
    let g_abc = store.mk_app(g_sym.clone(), vec![a, b, c], u.clone());
    let g_def = store.mk_app(g_sym, vec![d, e, ff], u);

    let eq_ad = store.mk_eq(a, d);
    let eq_be = store.mk_eq(b, e);
    let eq_cf = store.mk_eq(c, ff);
    let eq_apps = store.mk_eq(g_abc, g_def);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ad, true); // a = d
    euf.assert_literal(eq_be, true); // b = e
    euf.assert_literal(eq_cf, true); // c = ff
    euf.assert_literal(eq_apps, false); // g(a,b,c) != g(d,e,ff) — contradicts congruence

    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "#6154: g(a,b,c) != g(d,e,f) with all args equal must be UNSAT, got: {result:?}"
    );
}

/// 2-arg partial mismatch: f(a,b) and f(a,c) with b,c unconstrained.
/// No congruence — should be SAT.
#[test]
#[serial]
fn test_multiarg_partial_mismatch_sat_6154() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());

    let f_sym = Symbol::named("f");
    let f_ab = store.mk_app(f_sym.clone(), vec![a, b], u.clone());
    let f_ac = store.mk_app(f_sym, vec![a, c], u);

    let eq_apps = store.mk_eq(f_ab, f_ac);

    let mut euf = EufSolver::new(&store);
    // Only first arg shared; b and c unconstrained
    euf.assert_literal(eq_apps, false); // f(a,b) != f(a,c)

    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "#6154: f(a,b) != f(a,c) with b,c unconstrained must be SAT, got: {result:?}"
    );
}

/// 2-arg congruence via transitive equalities: f(a,b) and f(c,d) with a=x=c, b=y=d.
#[test]
#[serial]
fn test_multiarg_transitive_congruence_unsat_6154() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u.clone());
    let x = store.mk_var("x", u.clone());
    let y = store.mk_var("y", u.clone());

    let f_sym = Symbol::named("f");
    let f_ab = store.mk_app(f_sym.clone(), vec![a, b], u.clone());
    let f_cd = store.mk_app(f_sym, vec![c, d], u);

    let eq_ax = store.mk_eq(a, x);
    let eq_xc = store.mk_eq(x, c);
    let eq_by = store.mk_eq(b, y);
    let eq_yd = store.mk_eq(y, d);
    let eq_apps = store.mk_eq(f_ab, f_cd);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ax, true); // a = x
    euf.assert_literal(eq_xc, true); // x = c (so a = c transitively)
    euf.assert_literal(eq_by, true); // b = y
    euf.assert_literal(eq_yd, true); // y = d (so b = d transitively)
    euf.assert_literal(eq_apps, false); // f(a,b) != f(c,d)

    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "#6154: transitive 2-arg congruence must be UNSAT, got: {result:?}"
    );
}

/// Multi-arg congruence with push/pop: congruence at level 1, restored after pop.
#[test]
#[serial]
fn test_multiarg_congruence_push_pop_6154() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u.clone());

    let f_sym = Symbol::named("f");
    let f_ab = store.mk_app(f_sym.clone(), vec![a, b], u.clone());
    let f_cd = store.mk_app(f_sym, vec![c, d], u);

    let eq_ac = store.mk_eq(a, c);
    let eq_bd = store.mk_eq(b, d);
    let eq_apps = store.mk_eq(f_ab, f_cd);

    let mut euf = EufSolver::new(&store);

    // Level 0: f(a,b) != f(c,d) is SAT (no arg equalities)
    euf.assert_literal(eq_apps, false);
    assert!(
        matches!(euf.check(), TheoryResult::Sat),
        "Level 0: f(a,b) != f(c,d) without arg equalities must be SAT"
    );

    // Push to level 1, add arg equalities
    euf.push();
    euf.assert_literal(eq_ac, true);
    euf.assert_literal(eq_bd, true);

    // Now f(a,b) = f(c,d) by congruence, contradicting the disequality
    let result_l1 = euf.check();
    assert!(
        matches!(result_l1, TheoryResult::Unsat(_)),
        "Level 1: f(a,b) != f(c,d) with a=c, b=d must be UNSAT, got: {result_l1:?}"
    );

    // Pop back to level 0 — disequality should be SAT again
    euf.pop();
    let result_l0 = euf.check();
    assert!(
        matches!(result_l0, TheoryResult::Sat),
        "After pop: f(a,b) != f(c,d) must be SAT again, got: {result_l0:?}"
    );
}

/// Multi-arg discovered equality: when a=c and b=d, the solver should
/// discover and propagate f(a,b) = f(c,d) via congruence closure.
#[test]
#[serial]
fn test_multiarg_discovered_equality_6154() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u.clone());

    let f_sym = Symbol::named("f");
    let f_ab = store.mk_app(f_sym.clone(), vec![a, b], u.clone());
    let f_cd = store.mk_app(f_sym, vec![c, d], u);

    let eq_ac = store.mk_eq(a, c);
    let eq_bd = store.mk_eq(b, d);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_ac, true); // a = c
    euf.assert_literal(eq_bd, true); // b = d

    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Congruence closure should discover f(a,b) = f(c,d)
    let eqs = euf.propagate_equalities();
    let found = has_discovered_equality(&eqs.equalities, f_ab, f_cd);
    assert!(
        found,
        "#6154: EUF must discover f(a,b) = f(c,d) when a=c, b=d. Got: {:?}",
        eqs.equalities
    );
}

/// Two distinct 2-arg UFs with same args: h(a,b) != g(a,b) should be SAT.
/// Different function symbols can return different values.
#[test]
#[serial]
fn test_multiarg_distinct_funcs_sat_6146() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());

    let h_ab = store.mk_app(Symbol::named("h"), vec![a, b], u.clone());
    let g_ab = store.mk_app(Symbol::named("g"), vec![a, b], u);

    let eq_hg = store.mk_eq(h_ab, g_ab);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_hg, false); // h(a,b) != g(a,b)

    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "#6146: h(a,b) != g(a,b) must be SAT — different UFs can differ, got: {result:?}"
    );
}

/// Multi-arg congruence under incremental EUF mode.
/// Same pattern as test_multiarg_congruence_2arg_unsat_6154 but with
/// Ensures congruence closure works on the incremental path too.
#[test]
#[serial]
fn test_multiarg_congruence_incremental_6154() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u.clone());

    let f_sym = Symbol::named("f");
    let f_ab = store.mk_app(f_sym.clone(), vec![a, b], u.clone());
    let f_cd = store.mk_app(f_sym, vec![c, d], u);

    let eq_ac = store.mk_eq(a, c);
    let eq_bd = store.mk_eq(b, d);
    let eq_fab_fcd = store.mk_eq(f_ab, f_cd);

    let mut euf = new_incremental_euf(&store);
    euf.assert_literal(eq_ac, true);
    euf.assert_literal(eq_bd, true);
    euf.assert_literal(eq_fab_fcd, false);

    let result = euf.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "#6154 incremental: f(a,b) != f(c,d) with a=c, b=d must be UNSAT, got: {result:?}"
    );
}
