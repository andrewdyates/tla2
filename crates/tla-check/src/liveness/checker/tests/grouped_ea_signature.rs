// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Grouped EA action signature tests — shared EA signature SCC dedup, grouping
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::helpers::{action_pred_xprime_eq_x, state_pred_x_eq};
use super::*;
use crate::liveness::test_helpers::{empty_successors, make_checker};
use crate::liveness::LiveExpr;
use crate::Value;

/// Verifies that PEMs sharing the same EA signature share a single Tarjan pass.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_shared_ea_signature_scc_dedup_correctness() {
    // Regression test for #2456: verifies that PEMs sharing the same EA
    // signature (ea_state_idx, ea_action_idx) produce correct results when
    // SCC computation is deduplicated. This exercises the bitmask precompute
    // + EA-signature grouping code path.
    //
    // Setup: 2-state cycle x=0 <-> x=1.
    // Shared EA state check: x=0 OR x=1 (passes on both states — all edges survive).
    // Since both check_state[2] (x=0, tag 903) and check_state[3] (x=1, tag 904)
    // are in ea_state_idx, the bitmask AND requires BOTH checks pass on BOTH
    // endpoints. x=0 fails check_state[3], x=1 fails check_state[2], so the
    // EA filter kills all edges. Use a single always-true EA state instead.
    //
    // PEM_A: AE state [x=0] — satisfied in the SCC → violation.
    // PEM_B: AE state [x=42] — not in the SCC → no violation from this PEM.
    // Overall: Violated (any PEM suffices).
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    assert_eq!(init_nodes.len(), 1);
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .expect("add_successors s0->s1");
    assert_eq!(from_s0.len(), 1);
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .expect("add_successors s1->s0");

    // EA state check: always true (x=0 OR x=1 covers all states, but we use
    // a single check that trivially passes). Use state_pred_x_eq on a value
    // that appears — but since EA requires the check to pass on BOTH endpoints,
    // we need a check that passes everywhere. Use check_state index pointing to
    // a True predicate. LiveExpr::Bool(true) serves as a state predicate that
    // always passes.
    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: vec![
            state_pred_x_eq(0, 901),  // idx 0: AE for PEM_A (x=0 present in SCC)
            state_pred_x_eq(42, 902), // idx 1: AE for PEM_B (x=42 absent)
            LiveExpr::Bool(true),     // idx 2: EA state (always passes)
        ],
        check_action: Vec::new(),
        pems: vec![
            PemPlan {
                ea_state_idx: vec![2], // shared EA: check_state[2] = true
                ea_action_idx: Vec::new(),
                ae_state_idx: vec![0], // []<>(x=0) — satisfied
                ae_action_idx: Vec::new(),
            },
            PemPlan {
                ea_state_idx: vec![2], // shared EA: same signature
                ea_action_idx: Vec::new(),
                ae_state_idx: vec![1], // []<>(x=42) — not satisfied
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
            "grouped checker with shared EA signature should detect violation via PEM_A, \
             but got {:?} — SCC dedup may have broken per-PEM AE checking",
            other
        ),
    }
}

/// Negative control for test_grouped_shared_ea_signature_scc_dedup_correctness:
/// when ALL PEMs sharing an EA signature have unsatisfiable AE constraints,
/// the grouped checker must report Satisfied.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_shared_ea_signature_all_ae_unsatisfiable() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .expect("add_successors s0->s1");
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .expect("add_successors s1->s0");

    // Both PEMs share the same EA but have AE constraints that are
    // unsatisfiable in the SCC.
    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: vec![
            state_pred_x_eq(42, 911), // idx 0: AE for PEM_A (absent)
            state_pred_x_eq(99, 912), // idx 1: AE for PEM_B (absent)
            LiveExpr::Bool(true),     // idx 2: EA state (always passes)
        ],
        check_action: Vec::new(),
        pems: vec![
            PemPlan {
                ea_state_idx: vec![2],
                ea_action_idx: Vec::new(),
                ae_state_idx: vec![0], // []<>(x=42) — not in SCC
                ae_action_idx: Vec::new(),
            },
            PemPlan {
                ea_state_idx: vec![2],
                ea_action_idx: Vec::new(),
                ae_state_idx: vec![1], // []<>(x=99) — not in SCC
                ae_action_idx: Vec::new(),
            },
        ],
    };

    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(
        matches!(result, LivenessResult::Satisfied),
        "all PEMs have unsatisfiable AE — should be Satisfied, got: {:?}",
        result
    );
}

/// Multi-PEM EA-signature grouping on the **action** dimension.
///
/// All existing multi-PEM tests use `ea_action_idx: Vec::new()`, so the
/// EA-signature grouping at checks.rs:78-95 is only exercised on the
/// `ea_state_idx` dimension. This test verifies that PEMs with different
/// `ea_action_idx` are placed in separate EA groups (separate Tarjan passes).
///
/// A bug where the grouping ignores `ea_action_idx` (e.g., only comparing
/// `ea_state_idx`) would merge PEM_A and PEM_B into the same group, causing
/// either: (a) PEM_B's action filter to kill edges for PEM_A (false negative),
/// or (b) PEM_A's empty filter to skip filtering for PEM_B (false positive).
///
/// Graph: x=0 <-> x=1 (two-state cycle, transitions are x'=x+1 mod 2).
///
/// PEM_A: no EA constraints, AE state [x=0] → SCC visible, x=0 present → violation.
/// PEM_B: EA action [x'=x] (stuttering step), AE state [x=1] → all edges filtered
///        (x=0→x=1 and x=1→x=0 both have x'≠x), no SCC → no violation from PEM_B.
///
/// Expected: Violated (PEM_A finds the violation).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_ea_action_signature_grouping() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Two-state cycle: x=0 <-> x=1
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    assert_eq!(init_nodes.len(), 1);
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .expect("add_successors s0->s1");
    assert_eq!(from_s0.len(), 1);
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .expect("add_successors s1->s0");

    // PEM_A: EA signature = (action=[], state=[])
    // PEM_B: EA signature = (action=[0], state=[])
    // These MUST be in separate EA groups because ea_action_idx differs.
    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: vec![
            state_pred_x_eq(0, 1001), // idx 0: AE for PEM_A (x=0 present in SCC)
            state_pred_x_eq(1, 1002), // idx 1: AE for PEM_B
        ],
        check_action: vec![
            action_pred_xprime_eq_x(1003), // idx 0: EA action for PEM_B (stuttering: x'=x)
        ],
        pems: vec![
            PemPlan {
                ea_state_idx: Vec::new(),
                ea_action_idx: Vec::new(), // no EA action filter
                ae_state_idx: vec![0],     // []<>(x=0) — satisfied in SCC
                ae_action_idx: Vec::new(),
            },
            PemPlan {
                ea_state_idx: Vec::new(),
                ea_action_idx: vec![0], // <>[](x'=x) — kills all edges (no stuttering)
                ae_state_idx: vec![1],  // []<>(x=1)
                ae_action_idx: Vec::new(),
            },
        ],
    };

    let result = checker.check_liveness_grouped(&plan, 0);
    match &result {
        LivenessResult::Violated { cycle, .. } => {
            assert!(!cycle.is_empty(), "violation cycle must be non-empty");
            // PEM_A (no EA filter) should produce the violation.
            // The SCC contains both x=0 and x=1.
            let x_vals: Vec<i64> = cycle
                .iter()
                .filter_map(|(s, _)| s.get("x").and_then(tla_value::Value::as_i64))
                .collect();
            assert!(
                x_vals.contains(&0),
                "cycle must contain x=0 (PEM_A's AE witness), got x values: {:?}",
                x_vals
            );
        }
        other => panic!(
            "grouped checker should detect violation via PEM_A (no EA action filter, AE x=0 \
             satisfied). PEM_B's ea_action_idx=[0] (stuttering filter) should NOT interfere \
             with PEM_A because they belong to different EA groups. Got: {:?}",
            other
        ),
    }
}
/// Negative control for test_grouped_heterogeneous_ea_detects_violation:
/// when the PEM with no EA constraints also has an unsatisfiable AE check,
/// the grouped checker should report Satisfied.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_heterogeneous_ea_satisfied_when_no_pem_viable() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    // Two-state cycle: x=0 <-> x=1
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("invariant: add_initial_state");
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .expect("invariant: add_successors s0->s1");
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .expect("invariant: add_successors s1->s0");

    // PEM_A: no EA, AE state [x=42] → x=42 not in SCC → no violation
    // PEM_B: EA state [x=99] (impossible), AE state [x=1] → no SCC under its EA
    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: vec![
            state_pred_x_eq(42, 811), // idx 0: AE for PEM_A (unsatisfiable)
            state_pred_x_eq(1, 812),  // idx 1: AE for PEM_B
            state_pred_x_eq(99, 813), // idx 2: EA for PEM_B (impossible)
        ],
        check_action: Vec::new(),
        pems: vec![
            PemPlan {
                ea_state_idx: Vec::new(),
                ea_action_idx: Vec::new(),
                ae_state_idx: vec![0], // []<>(x=42) — not in SCC
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
    assert!(
        matches!(result, LivenessResult::Satisfied),
        "no PEM should find a violation: PEM_A's AE is unsatisfiable, PEM_B's EA kills all edges"
    );
}

/// Test grouped EA signature SCC dedup correctness.
/// Negative control for test_grouped_ea_action_signature_grouping:
/// same setup but PEM_A also has an unsatisfiable AE check → Satisfied.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_grouped_ea_action_signature_grouping_negative() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    let from_s0 = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s1),
            &mut get_successors,
            None,
        )
        .expect("add_successors s0->s1");
    let _ = checker
        .add_successors(
            from_s0[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .expect("add_successors s1->s0");

    // PEM_A: no EA action, AE state [x=42] (not in SCC) → no violation
    // PEM_B: EA action [x'=x] (kills all edges), AE state [x=1] → no SCC
    let plan = GroupedLivenessPlan {
        tf: LiveExpr::Bool(true),
        check_state: vec![
            state_pred_x_eq(42, 1011), // idx 0: AE for PEM_A (x=42 absent)
            state_pred_x_eq(1, 1012),  // idx 1: AE for PEM_B
        ],
        check_action: vec![
            action_pred_xprime_eq_x(1013), // idx 0: EA action for PEM_B
        ],
        pems: vec![
            PemPlan {
                ea_state_idx: Vec::new(),
                ea_action_idx: Vec::new(),
                ae_state_idx: vec![0], // []<>(x=42) — not in SCC
                ae_action_idx: Vec::new(),
            },
            PemPlan {
                ea_state_idx: Vec::new(),
                ea_action_idx: vec![0], // <>[](x'=x) — kills all edges
                ae_state_idx: vec![1],
                ae_action_idx: Vec::new(),
            },
        ],
    };

    let result = checker.check_liveness_grouped(&plan, 0);
    assert!(
        matches!(result, LivenessResult::Satisfied),
        "no PEM should find a violation: PEM_A's AE x=42 is absent, PEM_B's EA action kills all edges. Got: {:?}",
        result
    );
}
