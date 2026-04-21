// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

use crate::checker_ops::expand_operator_body_with_primes;
use crate::coverage::detect_actions;
use crate::var_index::VarIndex;
use crate::EvalCtx;
use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_static_independence_disjoint() {
    let mut a = ActionDependencies::new();
    a.add_read(VarIndex(0));
    a.add_write(VarIndex(0));

    let mut b = ActionDependencies::new();
    b.add_read(VarIndex(1));
    b.add_write(VarIndex(1));

    assert!(check_static_independence(&a, &b));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_static_independence_overlapping_write_read() {
    let mut a = ActionDependencies::new();
    a.add_write(VarIndex(0));

    let mut b = ActionDependencies::new();
    b.add_read(VarIndex(0));

    assert!(!check_static_independence(&a, &b));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_static_independence_overlapping_write_write() {
    let mut a = ActionDependencies::new();
    a.add_write(VarIndex(0));

    let mut b = ActionDependencies::new();
    b.add_write(VarIndex(0));

    assert!(!check_static_independence(&a, &b));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_static_independence_read_read_ok() {
    let mut a = ActionDependencies::new();
    a.add_read(VarIndex(0));

    let mut b = ActionDependencies::new();
    b.add_read(VarIndex(0));

    assert!(check_static_independence(&a, &b));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_independence_matrix_empty() {
    let matrix = IndependenceMatrix::compute(&[]);
    assert_eq!(matrix.action_count(), 0);
    assert_eq!(matrix.count_independent_pairs(), 0);
    assert_eq!(matrix.total_pairs(), 0);
}

// ==================== Ample Set Tests ====================

/// Create a mock independence matrix for testing
fn make_test_matrix(n: usize, independent_pairs: &[(usize, usize)]) -> IndependenceMatrix {
    let deps: Vec<ActionDependencies> = (0..n)
        .map(|i| {
            let mut d = ActionDependencies::new();
            d.add_write(VarIndex::new(i));
            d
        })
        .collect();

    let mut matrix = vec![IndependenceStatus::Dependent; n * n];
    for i in 0..n {
        matrix[i * n + i] = IndependenceStatus::Dependent;
    }
    for &(i, j) in independent_pairs {
        matrix[i * n + j] = IndependenceStatus::Independent;
        matrix[j * n + i] = IndependenceStatus::Independent;
    }

    IndependenceMatrix {
        n,
        matrix,
        dependencies: deps,
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_empty_enabled() {
    let matrix = make_test_matrix(3, &[]);
    let visibility = VisibilitySet::new();
    let result = compute_ample_set(&[], &matrix, &visibility);
    assert!(result.actions.is_empty());
    assert!(!result.reduced);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_single_action() {
    let matrix = make_test_matrix(3, &[]);
    let visibility = VisibilitySet::new();
    let result = compute_ample_set(&[1], &matrix, &visibility);
    assert_eq!(result.actions, vec![1]);
    assert!(!result.reduced);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_no_independent_actions() {
    // Actions 0, 1, 2 all dependent on each other
    let matrix = make_test_matrix(3, &[]);
    let visibility = VisibilitySet::new();
    let result = compute_ample_set(&[0, 1, 2], &matrix, &visibility);
    assert_eq!(result.actions, vec![0, 1, 2]);
    assert!(!result.reduced);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_singleton_seed_when_independent() {
    // Action 0 is independent of actions 1 and 2.
    // Closure from seed 0 only contains 0 itself.
    // With empty visibility, action 0 is not visible, so reduction succeeds.
    let matrix = make_test_matrix(3, &[(0, 1), (0, 2)]);
    let visibility = VisibilitySet::new();
    let result = compute_ample_set(&[0, 1, 2], &matrix, &visibility);
    assert_eq!(result.actions, vec![0]);
    assert!(result.reduced);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_visibility_blocks_reduction() {
    // Action 0 is independent of 1 and 2 but visible (writes to var in invariant).
    // Actions 1 and 2 are dependent on each other (both write to their own var,
    // but default make_test_matrix marks non-listed pairs as dependent).
    let mut matrix = make_test_matrix(3, &[(0, 1), (0, 2)]);
    // Action 0 writes to var 0
    matrix.dependencies[0].writes.insert(VarIndex(0));

    let mut visibility = VisibilitySet::new();
    visibility.vars.insert(VarIndex(0)); // Var 0 in invariant

    let result = compute_ample_set(&[0, 1, 2], &matrix, &visibility);
    // Action 0 is skipped as seed due to visibility.
    // Actions 1 and 2 are dependent, so closing from either pulls in the other.
    // Neither 1 nor 2 is visible, so closure {1, 2} is valid but not a reduction
    // (size 2 < 3 is a reduction).
    // Actually: 1 and 2 are dependent, so closing from seed 1 adds 2.
    // Ample set = {1, 2}, which is a reduction from {0, 1, 2}.
    assert!(result.reduced);
    assert_eq!(result.actions.len(), 2);
    assert!(
        !result.actions.contains(&0),
        "visible action 0 should not be in ample set"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_reduces_to_singleton_when_all_independent() {
    // All three actions are mutually independent.
    // Any singleton is a valid ample set. Seed heuristic picks the first
    // non-visible action with fewest dependencies.
    let matrix = make_test_matrix(3, &[(0, 1), (0, 2), (1, 2)]);
    let visibility = VisibilitySet::new();
    let result = compute_ample_set(&[0, 1, 2], &matrix, &visibility);
    assert_eq!(result.actions.len(), 1);
    assert!(result.reduced);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_visibility_set_from_empty() {
    let visibility = VisibilitySet::from_eval_invariants(&[]);
    assert!(visibility.vars.is_empty());
}

/// Verify `from_eval_invariants` extracts state variable reads from non-empty
/// invariant expressions.  Part of #3354 Slice 4 test gap coverage: the old
/// `from_invariants(&[CompiledGuard])` replacement must produce the same
/// variable-read sets when given equivalent AST invariants.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_visibility_set_from_eval_invariants_extracts_reads() {
    use tla_core::ast::Expr;
    use tla_core::span::Spanned;
    use tla_core::NameId;

    // Invariant: x > 0  (reads state var x at index 0)
    let x_var = Spanned::dummy(Expr::StateVar("x".to_string(), 0, NameId::INVALID));
    let zero = Spanned::dummy(Expr::Int(0.into()));
    let inv_body = Spanned::dummy(Expr::Gt(Box::new(x_var), Box::new(zero)));
    let invariants = vec![("Inv1".to_string(), inv_body)];

    let visibility = VisibilitySet::from_eval_invariants(&invariants);
    assert!(
        visibility.vars.contains(&VarIndex(0)),
        "visibility set should contain var index 0 (x)"
    );
    assert_eq!(visibility.vars.len(), 1);
}

/// Verify `from_eval_invariants` collects reads across multiple invariants.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_visibility_set_from_multiple_invariants() {
    use tla_core::ast::Expr;
    use tla_core::span::Spanned;
    use tla_core::NameId;

    // Inv1: x > 0  (reads var 0)
    let inv1 = Spanned::dummy(Expr::Gt(
        Box::new(Spanned::dummy(Expr::StateVar(
            "x".to_string(),
            0,
            NameId::INVALID,
        ))),
        Box::new(Spanned::dummy(Expr::Int(0.into()))),
    ));

    // Inv2: y = TRUE  (reads var 2)
    let inv2 = Spanned::dummy(Expr::Eq(
        Box::new(Spanned::dummy(Expr::StateVar(
            "y".to_string(),
            2,
            NameId::INVALID,
        ))),
        Box::new(Spanned::dummy(Expr::Bool(true))),
    ));

    let invariants = vec![("Inv1".to_string(), inv1), ("Inv2".to_string(), inv2)];

    let visibility = VisibilitySet::from_eval_invariants(&invariants);
    assert!(
        visibility.vars.contains(&VarIndex(0)),
        "should contain x (var 0)"
    );
    assert!(
        visibility.vars.contains(&VarIndex(2)),
        "should contain y (var 2)"
    );
    assert_eq!(visibility.vars.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_stats() {
    let mut stats = PorStats::default();
    assert_eq!(stats.total_states, 0);

    stats.record(3, 1); // Reduced
    assert_eq!(stats.reductions, 1);
    assert_eq!(stats.total_states, 1);
    assert_eq!(stats.actions_skipped, 2);

    stats.record(2, 2); // Not reduced
    assert_eq!(stats.reductions, 1);
    assert_eq!(stats.total_states, 2);
    assert_eq!(stats.actions_skipped, 2);
}

// ==================== Static Analysis Limitation Tests ====================
//
// These unit tests document why static POR analysis cannot reduce most TLA+ specs:
// - TLA+ requires specifying all variables in every action (via UNCHANGED)
// - UNCHANGED x is treated as both read AND write of x (conservative for soundness)
// - This makes virtually all actions dependent
//
// z4-based semantic independence checking (Phase 3) would be needed for
// practical state space reduction.
//
// NOTE: These are unit tests that simulate dependency patterns, not integration
// tests that run the model checker. End-to-end POR verification would require
// running specs with and without --por and comparing results.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_all_visible_blocks_all_reductions() {
    // All actions are visible: no ample set can be a proper subset (C2).
    let matrix = make_test_matrix(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut visibility = VisibilitySet::new();
    visibility.vars.insert(VarIndex(0));
    visibility.vars.insert(VarIndex(1));
    visibility.vars.insert(VarIndex(2));

    let result = compute_ample_set(&[0, 1, 2], &matrix, &visibility);
    assert_eq!(result.actions, vec![0, 1, 2]);
    assert!(!result.reduced);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_closure_grows_to_full_set() {
    // All actions are pairwise dependent (no independent pairs).
    // Closure from any seed must include all enabled actions.
    let matrix = make_test_matrix(3, &[]);
    let visibility = VisibilitySet::new();
    let result = compute_ample_set(&[0, 1, 2], &matrix, &visibility);
    assert_eq!(result.actions, vec![0, 1, 2]);
    assert!(!result.reduced);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_partial_closure() {
    // 4 actions: 0 independent of all, 1-2 dependent, 3 independent of all.
    // Seed 0: closure = {0} (all others independent). Ample set = {0}.
    let matrix = make_test_matrix(4, &[(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)]);
    let visibility = VisibilitySet::new();
    let result = compute_ample_set(&[0, 1, 2, 3], &matrix, &visibility);
    assert!(result.reduced);
    assert_eq!(result.actions.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ample_set_visible_in_closure_forces_fallback() {
    // 3 actions: 0 independent of 2, but 1 is dependent on 0.
    // Action 1 is visible.
    // Seed 0: closure adds 1 (dependent), 1 is visible -> fallback.
    // Seed 2: 2 is dependent on 1 (no (1,2) in independent_pairs), closure
    // adds 1, 1 is visible -> fallback.
    // No valid ample set: return full enabled set.
    let matrix = make_test_matrix(3, &[(0, 2)]);
    let mut visibility = VisibilitySet::new();
    // Action 1 writes to var 1, which is in the invariant.
    visibility.vars.insert(VarIndex(1));

    let result = compute_ample_set(&[0, 1, 2], &matrix, &visibility);
    assert_eq!(result.actions, vec![0, 1, 2]);
    assert!(!result.reduced);
}

/// UNCHANGED with identity-write tracking makes actions with disjoint real
/// writes INDEPENDENT, even when they share variables via UNCHANGED clauses.
///
/// Part of #3993: UNCHANGED x is the identity function on x. It commutes
/// with ALL operations, including real writes. The "read" in UNCHANGED x
/// is vacuous for commutativity — the action just preserves whatever value
/// x has, regardless of what other actions did to it.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_enables_independence() {
    // IncX: reads x (guard), real-writes x, identity-writes y (UNCHANGED y)
    // IncY: reads y (guard), real-writes y, identity-writes x (UNCHANGED x)
    let mut inc_x = ActionDependencies::new();
    inc_x.add_read(VarIndex(0)); // reads x (guard: x < 3)
    inc_x.add_write(VarIndex(0)); // real write: x' = x + 1
    inc_x.add_unchanged(VarIndex(1)); // UNCHANGED y: identity write

    let mut inc_y = ActionDependencies::new();
    inc_y.add_read(VarIndex(1)); // reads y (guard: y < 3)
    inc_y.add_write(VarIndex(1)); // real write: y' = y + 1
    inc_y.add_unchanged(VarIndex(0)); // UNCHANGED x: identity write

    // IncX real-writes {x}. Check against IncY: reads={y}, writes={y}.
    // x not in {y} ∪ {y} → no conflict from A's side.
    // IncY real-writes {y}. Check against IncX: reads={x}, writes={x}.
    // y not in {x} ∪ {x} → no conflict from B's side.
    // Identity writes (unchanged) are excluded from conflict checks.
    assert!(check_static_independence(&inc_x, &inc_y));
}

/// Two actions with completely disjoint REAL access patterns are
/// independent, even though they share variables via UNCHANGED.
///
/// Part of #3993: This is the primary POR improvement case.
/// IncX only reads/writes x, IncY only reads/writes y.
/// Both have UNCHANGED on the other's variable.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_disjoint_real_access_independent() {
    let mut inc_x = ActionDependencies::new();
    inc_x.add_read(VarIndex(0)); // reads x
    inc_x.add_write(VarIndex(0)); // writes x
    inc_x.add_unchanged(VarIndex(1)); // UNCHANGED y

    let mut inc_y = ActionDependencies::new();
    inc_y.add_read(VarIndex(1)); // reads y
    inc_y.add_write(VarIndex(1)); // writes y
    inc_y.add_unchanged(VarIndex(0)); // UNCHANGED x

    // Disjoint real access: x and y are separate variables.
    // UNCHANGED does not create conflicts.
    assert!(check_static_independence(&inc_x, &inc_y));
}

/// Actions that share a REAL read/write on the same variable remain
/// dependent even with UNCHANGED tracking.
///
/// Part of #3993: If A writes x and B reads x (not via UNCHANGED),
/// they are still dependent because the read observes A's write.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_read_write_still_dependent() {
    // A: writes x, reads y (real access to y, not UNCHANGED)
    let mut action_a = ActionDependencies::new();
    action_a.add_write(VarIndex(0)); // writes x
    action_a.add_read(VarIndex(1)); // reads y

    // B: writes y, reads x (real access to x, not UNCHANGED)
    let mut action_b = ActionDependencies::new();
    action_b.add_write(VarIndex(1)); // writes y
    action_b.add_read(VarIndex(0)); // reads x

    // A writes x, B reads x → dependent
    assert!(!check_static_independence(&action_a, &action_b));
}

/// Document: explicit x' = x assignments (as real writes) still create dependency.
///
/// When the AST extractor sees x' = expr (not UNCHANGED), it's recorded
/// as a real write. This test simulates that scenario.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_identity_assignment_as_real_write_creates_dependency() {
    let mut action_a = ActionDependencies::new();
    action_a.add_write(VarIndex(0)); // writes a
    action_a.add_read(VarIndex(1)); // b' = b reads b
    action_a.add_write(VarIndex(1)); // b' = b writes b (real write at AST level)

    let mut action_b = ActionDependencies::new();
    action_b.add_write(VarIndex(1)); // writes b
    action_b.add_read(VarIndex(0)); // a' = a reads a
    action_b.add_write(VarIndex(0)); // a' = a writes a (real write at AST level)

    assert!(!check_static_independence(&action_a, &action_b));
}

/// Part of #3993: Explicit `x' = x` identity assignment is recognized as
/// an identity write (equivalent to UNCHANGED), enabling independence detection.
///
/// Without this optimization, `x' = x` would be recorded as a real write to x
/// plus a read of x, making virtually all actions dependent. The identity
/// detection in `extract_dependencies_ast_expr` recognizes the
/// `Eq(Prime(StateVar(idx)), StateVar(idx))` pattern.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_identity_assignment_detected_as_unchanged() {
    let spec = r#"
---- MODULE PorIdentityDetection ----
EXTENDS Naturals

VARIABLE x, y

IncX ==
    /\ x < 3
    /\ x' = x + 1
    /\ y' = y          \* This is x' = x — should be detected as identity

IncY ==
    /\ y < 3
    /\ x' = x          \* This is x' = x — should be detected as identity
    /\ y' = y + 1

Next == IncX \/ IncY

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    let next_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("missing Next");

    let expanded_next = expand_operator_body_with_primes(&ctx, next_def);
    let actions = detect_actions(&expanded_next);
    assert_eq!(actions.len(), 2);

    let dependencies = extract_detected_action_dependencies(&actions);
    let inc_x_deps = &dependencies[0];
    let inc_y_deps = &dependencies[1];

    // IncX: y' = y should be detected as identity write to y, NOT a real write.
    assert!(
        !inc_x_deps.writes.contains(&VarIndex(1)),
        "y' = y should NOT be a real write in IncX"
    );
    assert!(
        inc_x_deps.unchanged.contains(&VarIndex(1)),
        "y' = y should be an identity write (unchanged) in IncX"
    );

    // IncY: x' = x should be detected as identity write to x, NOT a real write.
    assert!(
        !inc_y_deps.writes.contains(&VarIndex(0)),
        "x' = x should NOT be a real write in IncY"
    );
    assert!(
        inc_y_deps.unchanged.contains(&VarIndex(0)),
        "x' = x should be an identity write (unchanged) in IncY"
    );

    // Actions should be independent (disjoint real read/write sets).
    let matrix = IndependenceMatrix::compute(&dependencies);
    assert_eq!(
        matrix.get(0, 1),
        IndependenceStatus::Independent,
        "IncX and IncY should be independent with identity assignment detection"
    );
}

/// Integration test: UNCHANGED in parsed TLA+ spec now creates identity
/// writes, enabling independence detection.
///
/// Part of #3993: IncX real-writes x, UNCHANGED y; IncY real-writes y, UNCHANGED x.
/// With identity-write tracking, UNCHANGED does not create read/write
/// dependencies. The actions are INDEPENDENT because:
/// - IncX real-writes {x}, IncY reads {y} and real-writes {y} → disjoint
/// - IncY real-writes {y}, IncX reads {x} and real-writes {x} → disjoint
/// - UNCHANGED vars are identity writes, excluded from conflict checks
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detected_action_dependencies_with_unchanged_commutativity() {
    let spec = r#"
---- MODULE PorDetectedActions ----
EXTENDS Naturals

VARIABLE x, y

IncX ==
    /\ x < 3
    /\ x' = x + 1
    /\ UNCHANGED y

IncY ==
    /\ y < 3
    /\ UNCHANGED x
    /\ y' = y + 1

Next == IncX \/ IncY

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    let next_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("missing Next");

    let expanded_next = expand_operator_body_with_primes(&ctx, next_def);
    let actions = detect_actions(&expanded_next);
    assert_eq!(actions.len(), 2, "expected two detected top-level actions");

    let dependencies = extract_detected_action_dependencies(&actions);

    // Verify UNCHANGED creates identity writes, not real writes or reads.
    let inc_x_deps = &dependencies[0];
    let inc_y_deps = &dependencies[1];

    // UNCHANGED y should be in unchanged set, not writes or reads
    assert!(
        !inc_x_deps.writes.contains(&VarIndex(1)),
        "UNCHANGED y should NOT be in IncX.writes"
    );
    assert!(
        inc_x_deps.unchanged.contains(&VarIndex(1)),
        "UNCHANGED y should be in IncX.unchanged"
    );
    assert!(
        !inc_x_deps.reads.contains(&VarIndex(1)),
        "UNCHANGED y should NOT add a read of y in IncX"
    );

    assert!(
        !inc_y_deps.writes.contains(&VarIndex(0)),
        "UNCHANGED x should NOT be in IncY.writes"
    );
    assert!(
        inc_y_deps.unchanged.contains(&VarIndex(0)),
        "UNCHANGED x should be in IncY.unchanged"
    );
    assert!(
        !inc_y_deps.reads.contains(&VarIndex(0)),
        "UNCHANGED x should NOT add a read of x in IncY"
    );

    let matrix = IndependenceMatrix::compute(&dependencies);
    // IncX and IncY are INDEPENDENT:
    // - IncX real-writes {x}, IncY reads={y}, writes={y} → disjoint
    // - IncY real-writes {y}, IncX reads={x}, writes={x} → disjoint
    // - UNCHANGED vars don't participate in conflict checks
    assert_eq!(
        matrix.get(0, 1),
        IndependenceStatus::Independent,
        "IncX and IncY should be independent with UNCHANGED commutativity"
    );
    assert_eq!(
        matrix.get(1, 0),
        IndependenceStatus::Independent,
        "IncY and IncX should be independent with UNCHANGED commutativity"
    );
}

/// Integration test: three actions on disjoint variables are all
/// mutually independent with UNCHANGED commutativity.
///
/// Part of #3993: This demonstrates the full POR win on concurrent specs.
/// All 3 pairs are independent → ample set is a singleton → 3x reduction.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_three_action_all_independent() {
    let spec = r#"
---- MODULE PorThreeActions ----
EXTENDS Naturals

VARIABLE x, y, z

IncX ==
    /\ x < 3
    /\ x' = x + 1
    /\ UNCHANGED <<y, z>>

IncY ==
    /\ y < 3
    /\ y' = y + 1
    /\ UNCHANGED <<x, z>>

IncZ ==
    /\ z < 3
    /\ z' = z + 1
    /\ UNCHANGED <<x, y>>

Next == IncX \/ IncY \/ IncZ

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    let next_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("missing Next");

    let expanded_next = expand_operator_body_with_primes(&ctx, next_def);
    let actions = detect_actions(&expanded_next);
    assert_eq!(actions.len(), 3, "expected three detected top-level actions");

    let dependencies = extract_detected_action_dependencies(&actions);
    let matrix = IndependenceMatrix::compute(&dependencies);

    // Each action real-writes one var and has UNCHANGED on the other two.
    // With UNCHANGED commutativity, identity writes don't create conflicts.
    // IncX: reads={x}, writes={x}, unchanged={y,z}
    // IncY: reads={y}, writes={y}, unchanged={x,z}
    // IncZ: reads={z}, writes={z}, unchanged={x,y}
    // All pairs have disjoint real reads and writes → all independent.
    assert_eq!(
        matrix.get(0, 1),
        IndependenceStatus::Independent,
        "IncX and IncY should be independent"
    );
    assert_eq!(
        matrix.get(0, 2),
        IndependenceStatus::Independent,
        "IncX and IncZ should be independent"
    );
    assert_eq!(
        matrix.get(1, 2),
        IndependenceStatus::Independent,
        "IncY and IncZ should be independent"
    );
}

/// Part of #3449: verify that `extend_from_expanded_expr` sees through wrapper
/// operators to extract the underlying state variable reads.
///
/// A config invariant `Inv == TypeOK` where `TypeOK == x = 0` should
/// produce visibility for `x` (VarIndex 0), not just an opaque `Ident("TypeOK")`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_visibility_extend_from_expanded_expr_sees_through_wrapper() {
    let spec = r#"
---- MODULE PorWrapperInv ----
EXTENDS Naturals

VARIABLE x

TypeOK == x = 0

Inv == TypeOK

Init == x = 0
Next == x' = x + 1
====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    // Look up the resolved "Inv" operator body from ctx (not module.units).
    // After resolve_state_vars_in_loaded_ops(), ctx has state-var-resolved bodies.
    let inv_def = ctx.get_op("Inv").expect("missing Inv operator in ctx");

    let mut visibility = VisibilitySet::new();
    visibility.extend_from_expanded_expr(&ctx, &inv_def.body);

    assert!(
        visibility.vars.contains(&VarIndex(0)),
        "visibility set should contain var index 0 (x) after expanding Inv -> TypeOK -> x = 0"
    );
}

/// Part of #3449: verify that `mark_all_visible` makes all actions visible.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_visibility_mark_all_visible_blocks_all_reductions() {
    let mut visibility = VisibilitySet::new();
    assert!(visibility.vars.is_empty());

    // Without mark_all_visible, an action writing to var 5 is not visible
    let mut deps = ActionDependencies::new();
    deps.add_write(VarIndex(5));
    assert!(
        !visibility.is_action_visible(&deps),
        "empty visibility should not see var 5"
    );

    // After mark_all_visible, ALL actions should be visible
    visibility.mark_all_visible();
    assert!(
        visibility.is_action_visible(&deps),
        "all_visible should make every action visible"
    );
}

/// Part of #3449: verify that config-level invariant reads merge with
/// PROPERTY-level invariant reads in the visibility set.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_visibility_config_and_property_invariants_merge() {
    use tla_core::ast::Expr;
    use tla_core::span::Spanned;
    use tla_core::NameId;

    let spec = r#"
---- MODULE PorMergedInv ----
EXTENDS Naturals

VARIABLE x, y

ConfigInv == y > 0

Init == x = 0 /\ y = 1
Next == x' = x + 1 /\ y' = y
====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    // Start with a PROPERTY invariant that reads x (var 0)
    let property_inv_body = Spanned::dummy(Expr::Gt(
        Box::new(Spanned::dummy(Expr::StateVar(
            "x".to_string(),
            0,
            NameId::INVALID,
        ))),
        Box::new(Spanned::dummy(Expr::Int(0.into()))),
    ));
    let property_invariants = vec![("PropertyInv".to_string(), property_inv_body)];
    let mut visibility = VisibilitySet::from_eval_invariants(&property_invariants);
    assert!(
        visibility.vars.contains(&VarIndex(0)),
        "should contain x (var 0) from PROPERTY"
    );

    // Now extend with config invariant ConfigInv that reads y (var 1).
    // Use ctx.get_op() to get the resolved body (with state vars resolved).
    let config_inv_def = ctx
        .get_op("ConfigInv")
        .expect("missing ConfigInv operator in ctx");
    visibility.extend_from_expanded_expr(&ctx, &config_inv_def.body);

    assert!(
        visibility.vars.contains(&VarIndex(0)),
        "should still contain x from PROPERTY"
    );
    assert!(
        visibility.vars.contains(&VarIndex(1)),
        "should contain y (var 1) from config invariant ConfigInv"
    );
}

// ==================== Phase 11 Enhanced Independence Tests ====================

/// Part of #3993 Phase 11: detect identity through IF/THEN/ELSE.
///
/// `x' = IF cond THEN x ELSE x` is equivalent to UNCHANGED x.
/// Both branches evaluate to x, so the net effect is identity.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_identity_through_if_then_else() {
    let spec = r#"
---- MODULE PorIfIdentity ----
EXTENDS Naturals

VARIABLE x, y

IncX ==
    /\ x < 3
    /\ x' = x + 1
    /\ y' = IF x > 0 THEN y ELSE y   \* identity through IF/THEN/ELSE

IncY ==
    /\ y < 3
    /\ y' = y + 1
    /\ x' = IF y > 0 THEN x ELSE x   \* identity through IF/THEN/ELSE

Next == IncX \/ IncY

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    let next_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("missing Next");

    let expanded_next = expand_operator_body_with_primes(&ctx, next_def);
    let actions = detect_actions(&expanded_next);
    assert_eq!(actions.len(), 2);

    let dependencies = extract_detected_action_dependencies(&actions);
    let inc_x_deps = &dependencies[0];
    let inc_y_deps = &dependencies[1];

    // IncX: y' = IF x > 0 THEN y ELSE y should be detected as identity write to y
    assert!(
        !inc_x_deps.writes.contains(&VarIndex(1)),
        "y' = IF ... THEN y ELSE y should NOT be a real write in IncX"
    );
    assert!(
        inc_x_deps.unchanged.contains(&VarIndex(1)),
        "y' = IF ... THEN y ELSE y should be an identity write (unchanged) in IncX"
    );

    // IncY: x' = IF y > 0 THEN x ELSE x should be detected as identity write to x
    assert!(
        !inc_y_deps.writes.contains(&VarIndex(0)),
        "x' = IF ... THEN x ELSE x should NOT be a real write in IncY"
    );
    assert!(
        inc_y_deps.unchanged.contains(&VarIndex(0)),
        "x' = IF ... THEN x ELSE x should be an identity write (unchanged) in IncY"
    );

    // Both actions should be independent
    let matrix = IndependenceMatrix::compute(&dependencies);
    assert_eq!(
        matrix.get(0, 1),
        IndependenceStatus::Independent,
        "IncX and IncY should be independent with IF/THEN/ELSE identity detection"
    );
}

/// Part of #3993 Phase 11: constant write detection.
///
/// `x' = 0` does not read x — the write value is constant. This reduces
/// the read set and may enable independence that would otherwise be blocked.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_constant_write_no_read_dependency() {
    let spec = r#"
---- MODULE PorConstWrite ----
EXTENDS Naturals

VARIABLE x, y

ResetX ==
    /\ x' = 0               \* constant write — does NOT read x
    /\ y' = y                \* identity write

IncrY ==
    /\ y' = y + 1            \* real write to y, reads y
    /\ x' = x                \* identity write

Next == ResetX \/ IncrY

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    let next_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("missing Next");

    let expanded_next = expand_operator_body_with_primes(&ctx, next_def);
    let actions = detect_actions(&expanded_next);
    assert_eq!(actions.len(), 2);

    let dependencies = extract_detected_action_dependencies(&actions);
    let reset_x_deps = &dependencies[0];

    // ResetX: x' = 0 should record a write but NOT a read of x
    assert!(
        reset_x_deps.writes.contains(&VarIndex(0)),
        "x' = 0 should be a write to x"
    );
    assert!(
        !reset_x_deps.reads.contains(&VarIndex(0)),
        "x' = 0 (constant write) should NOT add a read of x"
    );

    // ResetX: y' = y is identity
    assert!(
        reset_x_deps.unchanged.contains(&VarIndex(1)),
        "y' = y should be an identity write in ResetX"
    );

    // ResetX: writes={x}, reads={}, unchanged={y}
    // IncrY:  writes={y}, reads={y}, unchanged={x}
    // ResetX.writes={x} vs IncrY.{reads={y}, writes={y}} — disjoint
    // IncrY.writes={y} vs ResetX.{reads={}, writes={x}} — disjoint
    // They should be independent.
    let matrix = IndependenceMatrix::compute(&dependencies);
    assert_eq!(
        matrix.get(0, 1),
        IndependenceStatus::Independent,
        "ResetX (constant write) and IncrY should be independent"
    );
}

/// Part of #3993 Phase 11: IF/THEN/ELSE where one branch is NOT identity
/// should still be treated as a real write.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_then_else_not_identity_when_one_branch_differs() {
    let spec = r#"
---- MODULE PorIfNotIdentity ----
EXTENDS Naturals

VARIABLE x, y

MaybeIncX ==
    /\ x' = IF x > 0 THEN x + 1 ELSE x   \* NOT identity — then branch changes x
    /\ y' = y

Next == MaybeIncX

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    let next_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("missing Next");

    let expanded_next = expand_operator_body_with_primes(&ctx, next_def);
    let actions = detect_actions(&expanded_next);
    assert_eq!(actions.len(), 1);

    let dependencies = extract_detected_action_dependencies(&actions);
    let deps = &dependencies[0];

    // x' = IF x > 0 THEN x + 1 ELSE x is NOT identity — one branch changes x
    // It should be treated as a real write (and read) to x
    assert!(
        deps.writes.contains(&VarIndex(0)) || deps.reads.contains(&VarIndex(0)),
        "IF/THEN/ELSE with one non-identity branch should record real access to x"
    );
    assert!(
        !deps.unchanged.contains(&VarIndex(0)),
        "non-identity IF/THEN/ELSE should NOT be in unchanged"
    );
}

// ==================== EXCEPT Identity Detection Tests ====================

/// Part of #3993 Phase 11: EXCEPT identity `f' = [f EXCEPT ![k] = f[k]]`
/// is detected as an identity write (equivalent to UNCHANGED f).
///
/// This is the simplest EXCEPT identity case: a single key update that
/// reads back the same value.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_identity_detected_as_unchanged() {
    let spec = r#"
---- MODULE PorExceptIdentity ----
EXTENDS Naturals

VARIABLE f, g

Init ==
    /\ f = [x \in {1, 2} |-> 0]
    /\ g = [x \in {1, 2} |-> 0]

UpdateG ==
    /\ g' = [g EXCEPT ![1] = g[1] + 1]
    /\ f' = [f EXCEPT ![1] = f[1]]      \* identity: f[1] = f[1]

UpdateF ==
    /\ f' = [f EXCEPT ![1] = f[1] + 1]
    /\ g' = [g EXCEPT ![1] = g[1]]      \* identity: g[1] = g[1]

Next == UpdateG \/ UpdateF

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    let next_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("missing Next");

    let expanded_next = expand_operator_body_with_primes(&ctx, next_def);
    let actions = detect_actions(&expanded_next);
    assert_eq!(actions.len(), 2);

    let dependencies = extract_detected_action_dependencies(&actions);

    // UpdateG: f' = [f EXCEPT ![1] = f[1]] should be identity write to f
    let update_g_deps = &dependencies[0];
    assert!(
        update_g_deps.unchanged.contains(&VarIndex(0)),
        "f' = [f EXCEPT ![1] = f[1]] should be identity write (unchanged) in UpdateG"
    );
    assert!(
        !update_g_deps.writes.contains(&VarIndex(0)),
        "f' = [f EXCEPT ![1] = f[1]] should NOT be a real write in UpdateG"
    );

    // UpdateF: g' = [g EXCEPT ![1] = g[1]] should be identity write to g
    let update_f_deps = &dependencies[1];
    assert!(
        update_f_deps.unchanged.contains(&VarIndex(1)),
        "g' = [g EXCEPT ![1] = g[1]] should be identity write (unchanged) in UpdateF"
    );
    assert!(
        !update_f_deps.writes.contains(&VarIndex(1)),
        "g' = [g EXCEPT ![1] = g[1]] should NOT be a real write in UpdateF"
    );

    // With EXCEPT identity detection, UpdateG and UpdateF should be independent:
    // - UpdateG: real writes {g}, reads {g}, unchanged {f}
    // - UpdateF: real writes {f}, reads {f}, unchanged {g}
    let matrix = IndependenceMatrix::compute(&dependencies);
    assert_eq!(
        matrix.get(0, 1),
        IndependenceStatus::Independent,
        "UpdateG and UpdateF should be independent with EXCEPT identity detection"
    );
}

/// Part of #3993 Phase 11: EXCEPT with a non-identity value is NOT detected
/// as unchanged. `f' = [f EXCEPT ![1] = 42]` is a real write.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_except_non_identity_is_real_write() {
    let spec = r#"
---- MODULE PorExceptNonIdentity ----
EXTENDS Naturals

VARIABLE f

Init == f = [x \in {1, 2} |-> 0]

Update ==
    /\ f' = [f EXCEPT ![1] = 42]      \* NOT identity: writes 42, not f[1]

Next == Update

====
"#;

    let tree = parse_to_syntax_tree(spec);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut var_names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for var in vars {
                var_names.push(var.node.clone());
            }
        }
    }
    var_names.sort();
    ctx.register_vars(var_names.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    let next_def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("missing Next");

    let expanded_next = expand_operator_body_with_primes(&ctx, next_def);
    let actions = detect_actions(&expanded_next);
    assert_eq!(actions.len(), 1);

    let dependencies = extract_detected_action_dependencies(&actions);
    let deps = &dependencies[0];

    // f' = [f EXCEPT ![1] = 42] is NOT identity — should be a real write
    assert!(
        !deps.unchanged.contains(&VarIndex(0)),
        "f' = [f EXCEPT ![1] = 42] should NOT be identity (unchanged)"
    );
}

// ==================== resolve_auto_por Unit Tests ====================
//
// Part of #4167: Verify config override for auto-POR.
// `resolve_auto_por(config_override)` must respect `Some(false)` to disable
// auto-POR regardless of the TLA2_AUTO_POR env var state. The OnceLock caches
// the env var value once per process, so env var toggling is not testable, but
// the config override path (the `Some` branch) is deterministic and testable.

/// Config override `Some(false)` disables auto-POR unconditionally.
///
/// This is the primary test for issue #4167: even if TLA2_AUTO_POR would
/// default to enabled, the config override takes precedence.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_auto_por_config_false_disables() {
    let result = super::resolve_auto_por(Some(false));
    assert!(
        !result,
        "resolve_auto_por(Some(false)) must return false regardless of env var"
    );
}

/// Config override `Some(true)` enables auto-POR unconditionally.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_auto_por_config_true_enables() {
    let result = super::resolve_auto_por(Some(true));
    assert!(
        result,
        "resolve_auto_por(Some(true)) must return true regardless of env var"
    );
}

/// Config override `None` falls back to env var (default: enabled).
///
/// NOTE: The OnceLock caches the env var once per process. In a test process
/// where TLA2_AUTO_POR is not set, this returns true (the default). We cannot
/// toggle the env var mid-process due to OnceLock caching, but we verify
/// the fallback path returns a deterministic value.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_auto_por_none_falls_back_to_env() {
    // Without explicit config override, resolve_auto_por reads the env var.
    // The OnceLock means the value is fixed for the process lifetime.
    // In CI/test environments where TLA2_AUTO_POR is not set, default is true.
    let result = super::resolve_auto_por(None);
    // We can only assert the type is bool and the function does not panic.
    // The actual value depends on whether TLA2_AUTO_POR was set before the
    // OnceLock initialized. In most test runs, it defaults to true.
    let _ = result; // No panic = pass
}

/// Config override takes precedence: calling with Some(false) after Some(true)
/// (or vice versa) always returns the override value, not a cached result.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_auto_por_config_override_not_cached() {
    // Each call with Some(_) goes through the match arm directly, bypassing
    // the OnceLock entirely. Verify both directions.
    assert!(super::resolve_auto_por(Some(true)));
    assert!(!super::resolve_auto_por(Some(false)));
    assert!(super::resolve_auto_por(Some(true)));
    assert!(!super::resolve_auto_por(Some(false)));
}

/// Part of #3993 Phase 11: diagnostic summary method works.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diagnostic_summary_basic() {
    let deps: Vec<ActionDependencies> = vec![
        {
            let mut d = ActionDependencies::new();
            d.add_read(VarIndex(0));
            d.add_write(VarIndex(0));
            d.add_unchanged(VarIndex(1));
            d
        },
        {
            let mut d = ActionDependencies::new();
            d.add_read(VarIndex(1));
            d.add_write(VarIndex(1));
            d.add_unchanged(VarIndex(0));
            d
        },
    ];

    let matrix = IndependenceMatrix::compute(&deps);
    let names = vec!["IncX".to_string(), "IncY".to_string()];
    let summary = matrix.diagnostic_summary(&names);

    assert!(
        summary.contains("2 actions"),
        "summary should mention action count"
    );
    assert!(
        summary.contains("INDEPENDENT"),
        "summary should show independent pair"
    );
    assert!(
        summary.contains("IncX"),
        "summary should use action names"
    );
    assert!(
        summary.contains("IncY"),
        "summary should use action names"
    );
}
