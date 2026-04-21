// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Performance regression tests (#3192)
// ========================================================================

/// Tests that congruence closure with many function applications completes
/// in bounded time. Creates N function applications f(x_i) and a chain
/// x_0 = x_1 = ... = x_{N-1}, forcing the closure to discover that all
/// f(x_i) are congruent. With the current O(F^2) rebuild_closure, doubling
/// N should ~4x the time. This test catches regressions and serves as a
/// baseline for fixing #3192 Finding 1.
#[test]
#[serial]
fn test_congruence_closure_scaling_many_func_apps() {
    let n = 50; // 50 function applications with chained equalities
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    // Create N variables x_0..x_{N-1}
    let vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("x{i}"), u.clone()))
        .collect();

    // Create N function applications f(x_i)
    let f_apps: Vec<TermId> = vars
        .iter()
        .map(|&v| store.mk_app(Symbol::named("f"), vec![v], u.clone()))
        .collect();

    // Create equality chain: x_0 = x_1, x_1 = x_2, ..., x_{N-2} = x_{N-1}
    let eqs: Vec<TermId> = (0..n - 1)
        .map(|i| store.mk_eq(vars[i], vars[i + 1]))
        .collect();

    // Assert disequality between f(x_0) and f(x_{N-1})
    let diseq = store.mk_eq(f_apps[0], f_apps[n - 1]);

    let mut euf = EufSolver::new(&store);

    // Assert all equalities
    for &eq in &eqs {
        euf.assert_literal(eq, true);
    }
    // Assert f(x_0) != f(x_{N-1}) -- should conflict via congruence
    euf.assert_literal(diseq, false);

    let start = std::time::Instant::now();
    let result = euf.check();
    let elapsed = start.elapsed();

    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "Should detect conflict: f(x_0) = f(x_N-1) via congruence, but f(x_0) != f(x_N-1)"
    );

    // Canary: with N=50, this should complete well under 100ms even with O(F^2).
    // If this exceeds 1s, the quadratic behavior is hurting.
    assert!(
        elapsed.as_millis() < 1000,
        "Congruence closure with {n} func apps took {elapsed:?}, expected < 1s"
    );
}

/// Tests that explain() with a long equality chain completes in bounded time.
/// Creates a chain a_0 = a_1 = ... = a_{N-1} and asks for explanation of
/// a_0 = a_{N-1}. The explain() function rebuilds the full adjacency graph
/// from scratch (O(E*logE)) on every call (#3192 Finding 2).
#[test]
#[serial]
fn test_explain_scaling_long_equality_chain() {
    let n = 100; // 100-variable equality chain
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    // Create N variables
    let vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("a{i}"), u.clone()))
        .collect();

    // Create equality chain
    let eqs: Vec<TermId> = (0..n - 1)
        .map(|i| store.mk_eq(vars[i], vars[i + 1]))
        .collect();

    // Assert a_0 != a_{N-1} to force conflict + explanation
    let diseq = store.mk_eq(vars[0], vars[n - 1]);

    let mut euf = EufSolver::new(&store);
    for &eq in &eqs {
        euf.assert_literal(eq, true);
    }
    euf.assert_literal(diseq, false);

    let start = std::time::Instant::now();
    let result = euf.check();
    let elapsed = start.elapsed();

    match &result {
        TheoryResult::Unsat(conflict) => {
            // The conflict should include the disequality and enough equalities
            // to form a path from a_0 to a_{N-1}
            assert!(!conflict.is_empty(), "Conflict clause should be non-empty");
            // Should include the disequality
            assert!(
                conflict.iter().any(|l| l.term == diseq && !l.value),
                "Conflict should include a_0 != a_N-1"
            );
        }
        _ => panic!("Expected UNSAT from equality chain conflict, got: {result:?}"),
    }

    assert!(
        elapsed.as_millis() < 1000,
        "Explain with {n}-variable chain took {elapsed:?}, expected < 1s"
    );
}

// #3734 coverage gap: explain() must not produce stale conflict clauses
// after pop() in incremental mode. The HashMap-level test below verifies
// mechanism (edge removal), but this test verifies observable behavior
// (correct check() result and conflict clause after pop).
#[test]
#[serial]
fn test_incremental_explain_no_stale_edges_after_pop() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_ac = store.mk_eq(a, c);

    let mut euf = new_incremental_euf(&store);
    euf.init_enodes();

    // Level 0: assert a = b
    euf.assert_literal(eq_ab, true);
    let r0 = euf.check();
    assert!(
        matches!(r0, TheoryResult::Sat),
        "a=b alone should be SAT, got: {r0:?}"
    );

    // Push to level 1: assert b = c, then assert a != c -> conflict
    euf.push();
    euf.assert_literal(eq_bc, true);
    euf.assert_literal(eq_ac, false);
    let r1 = euf.check();
    match &r1 {
        TheoryResult::Unsat(clause) => {
            // Conflict clause must reference the relevant equalities
            assert!(!clause.is_empty(), "conflict clause should be non-empty");
        }
        other => unreachable!("expected UNSAT conflict at level 1, got: {other:?}"),
    }

    // Pop back to level 0: only a = b holds
    euf.pop();

    // Assert a != c at level 0 — should be SAT (a and c are unrelated)
    euf.assert_literal(eq_ac, false);
    let r2 = euf.check();
    assert!(
        matches!(r2, TheoryResult::Sat),
        "after pop, a=b with a!=c should be SAT (no stale b=c edge), got: {r2:?}"
    );
}

// #3734 regression: equality_edges must be scoped on pop() in incremental mode
#[test]
#[serial]
fn test_equality_edges_scoped_on_pop() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);
    let mut euf = new_incremental_euf(&store);
    euf.init_enodes();
    let ek = EufSolver::edge_key(a.0, b.0);
    euf.push();
    euf.assert_literal(eq_ab, true);
    euf.incremental_rebuild();
    assert!(euf.equality_edges.contains_key(&ek));
    euf.pop();
    assert!(!euf.equality_edges.contains_key(&ek));
}

// =========================================================================
// soft_reset: clears assignments but preserves learned state
// =========================================================================

#[test]
#[serial]
fn test_euf_soft_reset_clears_assignments_preserves_structure() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);

    let mut euf = EufSolver::new(&store);

    // Assert and check
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(eq_bc, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    assert!(!euf.assigns.is_empty());

    // soft_reset must clear assignments
    euf.soft_reset();
    assert!(
        euf.assigns.is_empty(),
        "assigns must be empty after soft_reset"
    );
    assert!(euf.trail.is_empty(), "trail must be empty after soft_reset");
    assert!(
        euf.scopes.is_empty(),
        "scopes must be empty after soft_reset"
    );
    assert!(
        euf.pending_propagations.is_empty(),
        "pending_propagations must be cleared"
    );
    assert!(
        euf.propagated_eq_pairs.is_empty(),
        "propagated_eq_pairs must be cleared"
    );

    // After soft_reset, re-asserting the same equalities should still work
    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
}

#[test]
#[serial]
fn test_euf_soft_reset_incremental_clears_egraph() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = new_incremental_euf(&store);
    euf.init_enodes();

    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));
    assert!(euf.enodes_init);

    euf.soft_reset();

    // In incremental mode, soft_reset must also clear the e-graph
    assert!(
        !euf.enodes_init,
        "enodes_init must be reset in incremental mode"
    );
    assert!(
        euf.enodes.is_empty(),
        "enodes must be cleared in incremental mode"
    );
    assert!(
        euf.equality_edges.is_empty(),
        "equality_edges must be cleared in incremental soft_reset"
    );
}

// =========================================================================
// propagate_equalities: Nelson-Oppen interface
// =========================================================================

#[test]
fn test_euf_propagate_equalities_drains_pending() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);

    // Assert equality and check to trigger rebuild_closure
    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // propagate_equalities should drain the pending propagations
    let result = euf.propagate_equalities();
    assert!(
        !result.equalities.is_empty(),
        "propagate_equalities must return the asserted equality for N-O"
    );

    // Verify the equality is for a=b
    let eq = &result.equalities[0];
    assert!(
        (eq.lhs == a && eq.rhs == b) || (eq.lhs == b && eq.rhs == a),
        "propagated equality must be a=b"
    );

    // Second call should return empty (already drained)
    let result2 = euf.propagate_equalities();
    assert!(
        result2.equalities.is_empty(),
        "second propagate_equalities must return empty"
    );
}

#[test]
fn test_euf_propagate_equalities_empty_when_no_equalities() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);
    let eq_ab = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);

    // Assert disequality (not equality)
    euf.assert_literal(eq_ab, false);
    let _ = euf.check();

    // No equality was asserted, so no propagation
    let result = euf.propagate_equalities();
    assert!(
        result.equalities.is_empty(),
        "no equality to propagate when only disequality asserted"
    );
}

// =========================================================================
// assert_shared_equality: Nelson-Oppen incoming equality
// =========================================================================

#[test]
#[serial]
fn test_euf_assert_shared_equality_stores_reason() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);

    let mut euf = EufSolver::new(&store);

    // Simulate another theory (e.g., LIA) discovering a = b
    let reason = vec![TheoryLit::new(TermId::new(100), true)];
    euf.assert_shared_equality(a, b, &reason);

    let key = EufSolver::edge_key(a.0, b.0);
    assert!(
        euf.shared_equality_reasons.contains_key(&key),
        "shared equality reason must be stored"
    );
    assert!(
        euf.dirty,
        "solver must be marked dirty after shared equality"
    );
}

#[test]
#[serial]
fn test_euf_assert_shared_equality_incremental_queues_merge() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u);

    let mut euf = new_incremental_euf(&store);
    euf.init_enodes();

    let reason = vec![TheoryLit::new(TermId::new(100), true)];
    euf.assert_shared_equality(a, b, &reason);

    // In incremental mode, the merge should be queued
    assert!(
        !euf.to_merge.is_empty(),
        "incremental mode must queue merge for shared equality"
    );
}

/// Regression test for #3934: proof-forest explain() survives push/pop.
/// Before the fix, pop() cleared ALL equality_edges, breaking explain() in incremental mode.
#[test]
#[serial]
fn test_proof_forest_explain_survives_push_pop() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let eq_cd = store.mk_eq(c, d);
    let mut euf = new_incremental_euf(&store);

    // Level 0: a=b | push | b=c | push | c=d
    euf.assert_literal(eq_ab, true);
    let _ = euf.check();
    euf.push();
    euf.assert_literal(eq_bc, true);
    let _ = euf.check();
    euf.push();
    euf.assert_literal(eq_cd, true);
    let _ = euf.check();

    // Pop c=d, check explain(a,c) includes {eq_ab, eq_bc} but not eq_cd
    euf.pop();
    let _ = euf.check();
    let r: Vec<TermId> = euf.explain(a, c).iter().map(|l| l.term).collect();
    assert!(r.contains(&eq_ab), "must include a=b after pop; got: {r:?}");
    assert!(r.contains(&eq_bc), "must include b=c after pop; got: {r:?}");
    assert!(
        !r.contains(&eq_cd),
        "must NOT include popped c=d; got: {r:?}"
    );

    // Pop b=c, check explain(a,b) includes eq_ab only
    euf.pop();
    let _ = euf.check();
    let r2: Vec<TermId> = euf.explain(a, b).iter().map(|l| l.term).collect();
    assert!(r2.contains(&eq_ab), "must include a=b; got: {r2:?}");
    assert!(
        !r2.contains(&eq_bc),
        "must NOT include popped b=c; got: {r2:?}"
    );
}

/// Proof-forest transitive chain: explain(a,c) after a=b, b=c returns both reasons.
#[test]
#[serial]
fn test_proof_forest_transitive_chain_explain() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u);
    let eq_ab = store.mk_eq(a, b);
    let eq_bc = store.mk_eq(b, c);
    let mut euf = new_incremental_euf(&store);
    euf.assert_literal(eq_ab, true);
    euf.assert_literal(eq_bc, true);
    let _ = euf.check();

    let r: Vec<TermId> = euf.explain(a, c).iter().map(|l| l.term).collect();
    assert!(
        r.contains(&eq_ab) && r.contains(&eq_bc),
        "must include both; got: {r:?}"
    );
    // Commutativity
    let r2: Vec<TermId> = euf.explain(c, a).iter().map(|l| l.term).collect();
    assert!(
        r2.contains(&eq_ab) && r2.contains(&eq_bc),
        "commutative; got: {r2:?}"
    );
}

/// Regression test for #4083: shared equalities must be processed after soft_reset.
///
/// After soft_reset, re-asserting the SAME assigns but adding a NEW shared equality
/// must still process the shared equality via incremental rebuild.
#[test]
fn test_euf_shared_equality_after_soft_reset_regression_4083() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let a = store.mk_var("a", u.clone());
    let b = store.mk_var("b", u.clone());
    let c = store.mk_var("c", u.clone());
    let d = store.mk_var("d", u);

    let eq_ab = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);

    // Phase 1: Assert a=b, check SAT.
    euf.assert_literal(eq_ab, true);
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Phase 2: soft_reset, re-assert the same assign equality, add a shared equality.
    euf.soft_reset();

    euf.assert_literal(eq_ab, true);
    // Simulate Nelson-Oppen: LIA discovered c = d.
    euf.assert_shared_equality(c, d, &[]);

    // check() must process the shared equality via incremental rebuild.
    assert!(matches!(euf.check(), TheoryResult::Sat));

    // Verify c and d are in the same equivalence class (shared equality applied).
    assert!(
        euf.are_equal(c, d),
        "c and d must be in the same equivalence class after shared equality (#4083)"
    );
}
