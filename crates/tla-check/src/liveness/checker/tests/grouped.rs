// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Grouped liveness classification: single/multi clause, PEM, EA action signatures
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::helpers::{action_pred_xprime_eq_x, action_pred_xprime_eq_x_plus_1, state_pred_x_eq};
use super::*;
use crate::liveness::test_helpers::{empty_successors, make_checker};
use crate::liveness::LiveExpr;
use crate::Value;

// =====================================================
// Tests for from_formula_grouped (branch grouping logic)
// =====================================================

/// Single clause: <>[]S /\ []<>S2 /\ TF
/// Should produce 1 group with 1 PEM.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_single_clause_single_group() {
    // Build: <>[]S1 /\ []<>S2 /\ []S3
    // where S1 is ea_state, S2 is ae_state, []S3 is tf
    let s1 = state_pred_x_eq(1, 100);
    let s2 = state_pred_x_eq(2, 200);
    let s3 = state_pred_x_eq(3, 300);

    // <>[]S1 = EA state check
    let ea_s1 = LiveExpr::eventually(LiveExpr::always(s1.clone()));
    // []<>S2 = AE state check
    let ae_s2 = LiveExpr::always(LiveExpr::eventually(s2.clone()));
    // []S3 = tf term
    let tf_s3 = LiveExpr::always(s3.clone());

    let formula = LiveExpr::and(vec![ea_s1, ae_s2, tf_s3]);
    let plans = LivenessChecker::from_formula_grouped(&formula).unwrap();

    assert_eq!(plans.len(), 1, "single clause should produce 1 group");
    assert_eq!(plans[0].pems.len(), 1, "single clause should produce 1 PEM");

    // PEM should have ea_state=[S1], ae_state=[S2]
    let pem = &plans[0].pems[0];
    assert_eq!(pem.ea_state_idx.len(), 1, "1 ea_state check");
    assert_eq!(pem.ae_state_idx.len(), 1, "1 ae_state check");
    assert_eq!(pem.ea_action_idx.len(), 0, "no ea_action checks");
    assert_eq!(pem.ae_action_idx.len(), 0, "no ae_action checks");

    // Verify EA/AE classification content, not just counts (#1299).
    // A classification swap (ea_state gets S2, ae_state gets S1) would be a
    // correctness-critical bug that the count-only assertions above would miss.
    let plan = &plans[0];
    let ea_expr = &plan.check_state[pem.ea_state_idx[0]];
    let ae_expr = &plan.check_state[pem.ae_state_idx[0]];
    assert!(
        ea_expr.structurally_equal(&s1),
        "EA state check should be S1 (tag 100), got: {:?}",
        ea_expr
    );
    assert!(
        ae_expr.structurally_equal(&s2),
        "AE state check should be S2 (tag 200), got: {:?}",
        ae_expr
    );
}

/// Two clauses sharing the same tf → 1 group, 2 PEMs.
/// Formula: (<>[]S1 /\ tf) \/ (<>[]S2 /\ tf)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_two_clauses_same_tf_one_group() {
    let s1 = state_pred_x_eq(1, 100);
    let s2 = state_pred_x_eq(2, 200);
    let s3 = state_pred_x_eq(3, 300); // shared tf body

    // Clause 1: <>[]S1 /\ []S3
    let clause1 = LiveExpr::and(vec![
        LiveExpr::eventually(LiveExpr::always(s1.clone())),
        LiveExpr::always(s3.clone()),
    ]);
    // Clause 2: <>[]S2 /\ []S3 (same tf = []S3)
    let clause2 = LiveExpr::and(vec![
        LiveExpr::eventually(LiveExpr::always(s2.clone())),
        LiveExpr::always(s3.clone()),
    ]);

    let formula = LiveExpr::or(vec![clause1, clause2]);
    let plans = LivenessChecker::from_formula_grouped(&formula).unwrap();

    assert_eq!(
        plans.len(),
        1,
        "two clauses with same tf should produce 1 group"
    );
    assert_eq!(
        plans[0].pems.len(),
        2,
        "two clauses should produce 2 PEMs in the group"
    );

    // Both PEMs should have ea_state with 1 check each
    assert_eq!(plans[0].pems[0].ea_state_idx.len(), 1);
    assert_eq!(plans[0].pems[1].ea_state_idx.len(), 1);

    // The two PEMs should reference different check_state indices
    // (S1 and S2 have different tags so they're distinct expressions)
    assert_ne!(
        plans[0].pems[0].ea_state_idx[0], plans[0].pems[1].ea_state_idx[0],
        "PEMs should reference different check expressions"
    );
}

/// Two clauses with different tf → 2 groups, 1 PEM each.
/// Formula: (<>[]S1 /\ []S3) \/ (<>[]S2 /\ []S4)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_two_clauses_different_tf_two_groups() {
    let s1 = state_pred_x_eq(1, 100);
    let s2 = state_pred_x_eq(2, 200);
    let s3 = state_pred_x_eq(3, 300); // tf for clause 1
    let s4 = state_pred_x_eq(4, 400); // tf for clause 2 (different tag)

    // Clause 1: <>[]S1 /\ []S3
    let clause1 = LiveExpr::and(vec![
        LiveExpr::eventually(LiveExpr::always(s1.clone())),
        LiveExpr::always(s3.clone()),
    ]);
    // Clause 2: <>[]S2 /\ []S4 (different tf)
    let clause2 = LiveExpr::and(vec![
        LiveExpr::eventually(LiveExpr::always(s2.clone())),
        LiveExpr::always(s4.clone()),
    ]);

    let formula = LiveExpr::or(vec![clause1, clause2]);
    let plans = LivenessChecker::from_formula_grouped(&formula).unwrap();

    assert_eq!(
        plans.len(),
        2,
        "two clauses with different tf should produce 2 groups"
    );
    assert_eq!(plans[0].pems.len(), 1, "first group has 1 PEM");
    assert_eq!(plans[1].pems.len(), 1, "second group has 1 PEM");

    // TF should be different between groups
    assert!(
        !plans[0].tf.structurally_equal(&plans[1].tf),
        "groups should have different temporal formulas"
    );
}

/// Index deduplication: two PEMs in same group sharing a check expression.
/// Both PEMs use <>[]S1, so check_state should deduplicate S1.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_shared_check_deduplication() {
    let s1 = state_pred_x_eq(1, 100); // shared ea_state check
    let s2 = state_pred_x_eq(2, 200); // ae_state in PEM 1
    let s3 = state_pred_x_eq(3, 300); // ae_state in PEM 2
    let s4 = state_pred_x_eq(4, 400); // tf body

    // Clause 1: <>[]S1 /\ []<>S2 /\ []S4
    let clause1 = LiveExpr::and(vec![
        LiveExpr::eventually(LiveExpr::always(s1.clone())),
        LiveExpr::always(LiveExpr::eventually(s2.clone())),
        LiveExpr::always(s4.clone()),
    ]);
    // Clause 2: <>[]S1 /\ []<>S3 /\ []S4 (same tf, same ea_state S1)
    let clause2 = LiveExpr::and(vec![
        LiveExpr::eventually(LiveExpr::always(s1.clone())),
        LiveExpr::always(LiveExpr::eventually(s3.clone())),
        LiveExpr::always(s4.clone()),
    ]);

    let formula = LiveExpr::or(vec![clause1, clause2]);
    let plans = LivenessChecker::from_formula_grouped(&formula).unwrap();

    assert_eq!(plans.len(), 1, "same tf should produce 1 group");
    assert_eq!(plans[0].pems.len(), 2, "2 PEMs in the group");

    // S1 is used as ea_state in both PEMs — should be deduplicated to one
    // entry in check_state, with both PEMs referencing the same index
    let pem0_ea = &plans[0].pems[0].ea_state_idx;
    let pem1_ea = &plans[0].pems[1].ea_state_idx;
    assert_eq!(pem0_ea.len(), 1);
    assert_eq!(pem1_ea.len(), 1);
    assert_eq!(
        pem0_ea[0], pem1_ea[0],
        "shared S1 should be deduplicated to same index"
    );

    // AE checks (S2, S3) should be distinct
    let pem0_ae = &plans[0].pems[0].ae_state_idx;
    let pem1_ae = &plans[0].pems[1].ae_state_idx;
    assert_eq!(pem0_ae.len(), 1);
    assert_eq!(pem1_ae.len(), 1);
    assert_ne!(
        pem0_ae[0], pem1_ae[0],
        "distinct AE checks should have different indices"
    );
}

/// Action-level EA and AE checks are classified correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_action_level_classification() {
    // <>[]A1 /\ []<>A2 (no tf, so tf=TRUE)
    let a1 = action_pred_xprime_eq_x(100);
    let a2 = action_pred_xprime_eq_x_plus_1(200);

    let formula = LiveExpr::and(vec![
        LiveExpr::eventually(LiveExpr::always(a1.clone())),
        LiveExpr::always(LiveExpr::eventually(a2.clone())),
    ]);
    let plans = LivenessChecker::from_formula_grouped(&formula).unwrap();

    assert_eq!(plans.len(), 1);
    let pem = &plans[0].pems[0];

    // A1 should be ea_action (not ea_state)
    assert_eq!(pem.ea_action_idx.len(), 1, "A1 should be ea_action");
    assert_eq!(pem.ea_state_idx.len(), 0, "no ea_state for action-level");

    // A2 should be ae_action (not ae_state)
    assert_eq!(pem.ae_action_idx.len(), 1, "A2 should be ae_action");
    assert_eq!(pem.ae_state_idx.len(), 0, "no ae_state for action-level");

    // check_action should have both
    assert_eq!(
        plans[0].check_action.len(),
        2,
        "both action checks should be in check_action"
    );
}

/// Multi-PEM verdict logic: grouped checker should report violation when
/// any PEM in the group is satisfiable in an SCC.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_multi_pem_any_pem_can_violate() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Two-state cycle: x=0 <-> x=1
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert_eq!(init_nodes.len(), 1);
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .unwrap();
    assert_eq!(from_s0.len(), 1);
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .unwrap();

    // Two PEMs in one group:
    // - PEM 0 fails ([]<>(x=2) has no witness in the SCC)
    // - PEM 1 succeeds ([]<>(x=1) has a witness)
    // Grouped verdict must use disjunction over PEMs (OR), not conjunction.
    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: vec![state_pred_x_eq(2, 501), state_pred_x_eq(1, 502)],
        check_action: Vec::new(),
        pems: vec![
            PemPlan {
                ae_state_idx: vec![0],
                ae_action_idx: Vec::new(),
                ea_state_idx: Vec::new(),
                ea_action_idx: Vec::new(),
            },
            PemPlan {
                ae_state_idx: vec![1],
                ae_action_idx: Vec::new(),
                ea_state_idx: Vec::new(),
                ea_action_idx: Vec::new(),
            },
        ],
    };

    let result = checker.check_liveness_grouped(&plan, 0);
    // Verify trace contents for grouped verdict — not just variant.
    match &result {
        LivenessResult::Violated { cycle, .. } => {
            assert!(
                !cycle.is_empty(),
                "grouped violation cycle must be non-empty"
            );
            // The SCC is {s0(x=0), s1(x=1)} with no self-loops, so the witness
            // cycle must traverse both states.
            let x_vals: Vec<i64> = cycle
                .iter()
                .filter_map(|(s, _)| s.get("x").and_then(tla_value::Value::as_i64))
                .collect();
            assert!(
                x_vals.contains(&0) && x_vals.contains(&1),
                "cycle through 2-state SCC should contain both s0(x=0) and s1(x=1), got x values: {:?}",
                x_vals
            );
        }
        other => panic!(
            "grouped checker should violate when any PEM is satisfiable, got {:?}",
            other
        ),
    }
}

/// Negative control for test_grouped_multi_pem_any_pem_can_violate:
/// when ALL PEMs check for absent states, the grouped checker should
/// report Satisfied (no violation). Without this test, a trivially-
/// always-violated implementation would pass the positive test above.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_multi_pem_all_pems_unsatisfiable() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Two-state cycle: x=0 <-> x=1
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .unwrap();
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .unwrap();

    // Two PEMs, both check for absent states (x=2, x=3).
    // Neither has a witness in the SCC {x=0, x=1}.
    // Grouped verdict: Satisfied (no PEM is satisfiable).
    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: vec![state_pred_x_eq(2, 601), state_pred_x_eq(3, 602)],
        check_action: Vec::new(),
        pems: vec![
            PemPlan {
                ae_state_idx: vec![0],
                ae_action_idx: Vec::new(),
                ea_state_idx: Vec::new(),
                ea_action_idx: Vec::new(),
            },
            PemPlan {
                ae_state_idx: vec![1],
                ae_action_idx: Vec::new(),
                ea_state_idx: Vec::new(),
                ea_action_idx: Vec::new(),
            },
        ],
    };

    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(
        matches!(result, LivenessResult::Satisfied),
        "grouped checker should report Satisfied when no PEM is satisfiable in any SCC"
    );
}

/// Regression test for #2047: heterogeneous EA constraints across PEMs.
///
/// Two PEMs share a `tf` but have different EA (Enabled-Action) constraints:
/// - PEM_A: no EA constraints, AE state check [x=0] (satisfiable in SCC)
/// - PEM_B: EA state [x=99] (impossible — kills all edges), AE state [x=1]
///
/// The correct result is Violated: PEM_A has no EA filter, so the full SCC
/// is visible and its AE check (x=0) is satisfied.
///
/// Before the fix, the union of all PEMs' EA checks included PEM_B's
/// impossible x=99 constraint.  The conjunctive pre-filter required all
/// EA checks to pass on every edge, killing all edges and preventing any
/// SCC from forming — a false negative.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_heterogeneous_ea_detects_violation() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Two-state cycle: x=0 <-> x=1
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("invariant: add_initial_state");
    assert_eq!(init_nodes.len(), 1);
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .expect("invariant: add_successors s0->s1");
    assert_eq!(from_s0.len(), 1);
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .expect("invariant: add_successors s1->s0");

    // PEM_A: no EA, AE state [x=0] → violation (SCC {s0,s1} is visible, x=0 present)
    // PEM_B: EA state [x=99] (impossible), AE state [x=1] → no SCC under its EA filter
    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: vec![
            state_pred_x_eq(0, 801),  // idx 0: AE for PEM_A
            state_pred_x_eq(1, 802),  // idx 1: AE for PEM_B
            state_pred_x_eq(99, 803), // idx 2: EA for PEM_B (impossible)
        ],
        check_action: Vec::new(),
        pems: vec![
            PemPlan {
                ea_state_idx: Vec::new(), // no EA constraints
                ea_action_idx: Vec::new(),
                ae_state_idx: vec![0], // []<>(x=0)
                ae_action_idx: Vec::new(),
            },
            PemPlan {
                ea_state_idx: vec![2], // <>[](x=99) — impossible
                ea_action_idx: Vec::new(),
                ae_state_idx: vec![1], // []<>(x=1)
                ae_action_idx: Vec::new(),
            },
        ],
    };

    let result = checker.check_liveness_grouped(&plan, 0);
    match &result {
        LivenessResult::Violated { cycle, .. } => {
            assert!(!cycle.is_empty(), "violation cycle must be non-empty");
            let x_vals: Vec<i64> = cycle
                .iter()
                .filter_map(|(s, _)| s.get("x").and_then(tla_value::Value::as_i64))
                .collect();
            assert!(
                x_vals.contains(&0),
                "cycle must contain x=0 (PEM_A's AE witness), got: {:?}",
                x_vals
            );
        }
        other => panic!(
            "grouped checker should detect violation via PEM_A (no EA, AE x=0 satisfied), \
             but got {:?} — this is the #2047 false negative",
            other
        ),
    }
}
