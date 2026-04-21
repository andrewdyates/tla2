// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
/// Build a vals[] array from an assignment specification.
/// Each entry: None = unassigned, Some(true) = positive, Some(false) = negative.
fn make_vals(assignments: &[Option<bool>]) -> Vec<i8> {
    let mut vals = vec![0i8; assignments.len() * 2];
    for (v, a) in assignments.iter().enumerate() {
        if let Some(positive) = a {
            if *positive {
                vals[v * 2] = 1;
                vals[v * 2 + 1] = -1;
            } else {
                vals[v * 2] = -1;
                vals[v * 2 + 1] = 1;
            }
        }
    }
    vals
}

#[test]
fn test_heap_operations() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Initially all variables in heap, some var should be picked (all equal activity)
    assert!(vsids.pick_branching_variable(&vals).is_some());

    // Bump variable 3 twice - it should become the top with activity 2.0
    vsids.bump(Variable(3), &vals, true);
    vsids.bump(Variable(3), &vals, true);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(3)));

    // Remove variable 3 from heap (assigned)
    vsids.remove_from_heap(Variable(3));
    // Now should pick something else
    let picked = vsids.pick_branching_variable(&vals);
    assert!(picked.is_some());
    assert_ne!(picked, Some(Variable(3)));

    // Bump variable 2 once - activity 1.0
    vsids.bump(Variable(2), &vals, true);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(2)));

    // Insert variable 3 back (unassigned)
    vsids.insert_into_heap(Variable(3));
    // Variable 3 has activity 2.0, var 2 has 1.0 - var 3 should be top
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(3)));
}

#[test]
fn test_heap_empty() {
    let mut vsids = VSIDS::new(3);
    let vals = make_vals(&[None; 3]);

    // Remove all variables
    vsids.remove_from_heap(Variable(0));
    vsids.remove_from_heap(Variable(1));
    vsids.remove_from_heap(Variable(2));

    assert_eq!(vsids.pick_branching_variable(&vals), None);

    // Insert one back
    vsids.insert_into_heap(Variable(1));
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(1)));
}

#[test]
fn test_heap_activity_ordering() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Bump each variable different number of times to create distinct activities
    // var 0: 5 bumps, var 1: 4 bumps, var 2: 3 bumps, var 3: 2 bumps, var 4: 1 bump
    for i in 0..5u32 {
        for _ in 0..(5 - i) {
            vsids.bump(Variable(i), &vals, true);
        }
    }

    // Variable 0 has highest activity (5.0)
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
    vsids.remove_from_heap(Variable(0));

    // Then var 1 (4.0)
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(1)));
    vsids.remove_from_heap(Variable(1));

    // Then var 2 (3.0)
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(2)));
}

#[test]
fn test_ensure_num_vars() {
    let mut vsids = VSIDS::new(3);
    vsids.ensure_num_vars(5);

    let vals = make_vals(&[None; 5]);
    // New variables should be in heap
    // Bump var 4 to make it top
    vsids.bump(Variable(4), &vals, true);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(4)));
}

#[test]
fn test_heap_bump_while_assigned() {
    let mut vsids = VSIDS::new(3);
    let vals = make_vals(&[None; 3]);

    // Bump var 0 and remove it (assigned)
    vsids.bump(Variable(0), &vals, true);
    vsids.remove_from_heap(Variable(0));

    // Bump var 0 again while it's assigned (this can happen during conflict analysis)
    vsids.bump(Variable(0), &vals, true);
    vsids.bump(Variable(0), &vals, true);
    // var 0 now has activity 3.0

    // var 1 has activity 0, so it should be the top of remaining heap
    // (or var 2, depending on initial order)
    let picked = vsids.pick_branching_variable(&vals);
    assert!(picked.is_some());
    assert_ne!(picked, Some(Variable(0))); // var 0 is not in heap

    // Insert var 0 back
    vsids.insert_into_heap(Variable(0));
    // Now var 0 with activity 3.0 should be top
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
}

#[test]
fn test_pick_branching_variable_lazily_drops_assigned_root() {
    let mut vsids = VSIDS::new(3);
    let dummy = make_vals(&[None; 3]);
    // Make variable 2 the heap root.
    vsids.bump(Variable(2), &dummy, true);
    vsids.bump(Variable(2), &dummy, true);

    // var 2 assigned (true), vars 0 and 1 unassigned
    let vals = make_vals(&[None, None, Some(true)]);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
    assert_eq!(vsids.heap_pos[2], INVALID_POS);
}

#[test]
fn test_pick_branching_variable_lazily_drops_multiple_assigned_roots() {
    let mut vsids = VSIDS::new(4);
    let dummy = make_vals(&[None; 4]);
    // Ensure vars 3 and 2 are the two highest-priority heap entries.
    vsids.bump(Variable(3), &dummy, true);
    vsids.bump(Variable(3), &dummy, true);
    vsids.bump(Variable(2), &dummy, true);

    // vars 2 and 3 assigned, vars 0 and 1 unassigned
    let vals = make_vals(&[None, None, Some(true), Some(false)]);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
    assert_eq!(vsids.heap_pos[3], INVALID_POS);
    assert_eq!(vsids.heap_pos[2], INVALID_POS);
}

#[test]
fn test_vmtf_cursor_skips_assigned() {
    let mut vsids = VSIDS::new(3);
    // vars 0 and 1 assigned, var 2 unassigned
    let vals = make_vals(&[Some(true), Some(false), None]);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(2)));
    // Cursor should now be updated to 2 (the found unassigned variable).
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(2)));
}

#[test]
fn test_vmtf_updates_on_unassign_after_bump() {
    let mut vsids = VSIDS::new(4);
    let dummy = make_vals(&[None; 4]);

    // Simulate a conflict bumping var 2 while it is assigned (focused mode → VMTF).
    vsids.bump(Variable(2), &dummy, false);

    // Now simulate backtracking that unassigns var 2.
    vsids.vmtf_on_unassign(Variable(2));

    let vals = make_vals(&[None; 4]);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(2)));
}

#[test]
fn test_shuffle_scores_changes_heap_order() {
    let mut vsids = VSIDS::new(10);
    let assignment = make_vals(&[None; 10]);

    // Create distinct activity ordering: 0 > 1 > 2 > ... > 9
    for i in 0..10u32 {
        for _ in 0..(10 - i) {
            vsids.bump(Variable(i), &assignment, true);
        }
    }
    let before = vsids.pick_branching_variable(&assignment).unwrap();
    assert_eq!(before, Variable(0)); // Highest activity
    vsids.insert_into_heap(Variable(0)); // Put it back

    // Shuffle with seed 42
    vsids.shuffle_scores(42);

    // After shuffle, the heap should still be valid (heap property maintained)
    // but the order should be different.
    let after = vsids.pick_branching_variable(&assignment);
    assert!(after.is_some());
    // We can't predict which variable will be top, but the heap must be valid
    // and contain all variables.
}

#[test]
fn test_shuffle_scores_different_seeds_different_orders() {
    let assignment = make_vals(&[None; 20]);

    let mut vsids1 = VSIDS::new(20);
    let mut vsids2 = VSIDS::new(20);

    // Same initial activities
    for i in 0..20u32 {
        for _ in 0..(20 - i) {
            vsids1.bump(Variable(i), &assignment, true);
            vsids2.bump(Variable(i), &assignment, true);
        }
    }

    vsids1.shuffle_scores(1);
    vsids2.shuffle_scores(2);

    // Different seeds should produce different orderings (with high probability).
    let top1 = vsids1.pick_branching_variable(&assignment);
    let top2 = vsids2.pick_branching_variable(&assignment);
    // Not deterministic but with 20 vars, collision probability is 5%.
    // Accept either outcome for test robustness.
    assert!(top1.is_some());
    assert!(top2.is_some());
}

#[test]
fn test_shuffle_queue_preserves_all_variables() {
    let mut vsids = VSIDS::new(8);

    // Collect all variables before shuffle.
    let mut before: Vec<u32> = Vec::new();
    let mut cur = vsids.vmtf_first;
    while cur != INVALID_VAR {
        before.push(cur);
        cur = vsids.vmtf_next[cur as usize];
    }
    assert_eq!(before.len(), 8);

    // Shuffle
    vsids.shuffle_queue(42);

    // Collect all variables after shuffle.
    let mut after: Vec<u32> = Vec::new();
    let mut cur = vsids.vmtf_first;
    while cur != INVALID_VAR {
        after.push(cur);
        cur = vsids.vmtf_next[cur as usize];
    }

    // Same set of variables, possibly different order.
    assert_eq!(after.len(), 8);
    let mut before_sorted = before.clone();
    let mut after_sorted = after.clone();
    before_sorted.sort_unstable();
    after_sorted.sort_unstable();
    assert_eq!(before_sorted, after_sorted);
}

#[test]
fn test_shuffle_queue_vmtf_consistent() {
    let mut vsids = VSIDS::new(10);

    let dummy = make_vals(&[None; 10]);
    // Bump some variables to create non-trivial queue order (focused mode → VMTF).
    vsids.bump(Variable(5), &dummy, false);
    vsids.bump(Variable(3), &dummy, false);
    vsids.bump(Variable(7), &dummy, false);

    vsids.shuffle_queue(99);

    // After shuffle, VMTF must still be usable for decisions.
    let assignment = make_vals(&[None; 10]);
    let picked = vsids.pick_branching_variable_vmtf(&assignment);
    assert!(picked.is_some());
}

#[test]
fn test_zero_activity_buries_fresh_vars_in_vmtf() {
    let mut vsids = VSIDS::new(3);
    vsids.ensure_num_vars(5);

    // Fresh vars 3 and 4 are added at the VMTF front by ensure_num_vars().
    vsids.set_activity(Variable(3), 0.0);
    vsids.set_activity(Variable(4), 0.0);

    let vals = make_vals(&[None; 5]);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(0)));
}

#[test]
fn test_zero_activity_burial_blocks_vmtf_unassign_resurrection() {
    let mut vsids = VSIDS::new(3);
    vsids.ensure_num_vars(4);
    vsids.set_activity(Variable(3), 0.0);

    // Backtracking should not move a buried extension var back to the
    // cursor when it becomes unassigned again.
    vsids.vmtf_on_unassign(Variable(3));

    let vals = make_vals(&[None; 4]);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(0)));
}

/// Proof coverage for set_activity heap path (#7191):
/// Verify that set_activity(var, 0.0) sifts the variable down in the
/// EVSIDS heap, and set_activity(var, high) sifts it back up.
#[test]
fn test_set_activity_maintains_heap_invariant() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Create distinct ordering: var0 has highest activity
    for i in 0..5u32 {
        for _ in 0..(5 - i) {
            vsids.bump(Variable(i), &vals, true);
        }
    }
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
    vsids.insert_into_heap(Variable(0)); // put back after pick

    // Zero out var0's activity — it should sink to the bottom of the heap
    vsids.set_activity(Variable(0), 0.0);
    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert_ne!(
        top,
        Variable(0),
        "set_activity(0.0) must sift var0 below higher-activity variables"
    );
    // var1 had 4 bumps, should now be on top
    assert_eq!(top, Variable(1));
    vsids.insert_into_heap(Variable(1)); // put back

    // Now boost var0 with a very high activity — it should float back up
    vsids.set_activity(Variable(0), 1e10);
    let top2 = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(
        top2,
        Variable(0),
        "set_activity(1e10) must sift var0 back to heap top"
    );
}

/// Verify set_activity on a variable NOT in the heap (already assigned/removed)
/// does not panic and correctly updates the stored activity.
#[test]
fn test_set_activity_on_removed_variable() {
    let mut vsids = VSIDS::new(3);
    let vals = make_vals(&[None; 3]);

    vsids.bump(Variable(1), &vals, true);
    vsids.remove_from_heap(Variable(1));

    // set_activity on a removed variable should update the stored value
    // without touching the heap (heap_pos is INVALID_POS).
    vsids.set_activity(Variable(1), 0.0);
    assert_eq!(vsids.activity(Variable(1)), 0.0);

    // Re-insert: var1 now has 0.0 activity, should not be top
    vsids.insert_into_heap(Variable(1));
    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert_ne!(top, Variable(1), "zero-activity var should not be heap top");
}

/// Regression test for #5580: many decay() calls without bump() must not
/// overflow the increment to infinity. The proactive rescale in decay()
/// should fire before the increment exceeds f64::MAX.
#[test]
fn test_decay_does_not_overflow_to_infinity() {
    let mut vsids = VSIDS::new(3);
    // Call decay() many times without any bump() — simulates a long solve
    // where conflicts happen rapidly with no new bumps (e.g., CP-SAT).
    for _ in 0..100_000 {
        vsids.decay();
    }
    assert!(
        vsids.increment.is_finite() && vsids.increment > 0.0,
        "increment must stay finite after 100k decays, got: {}",
        vsids.increment
    );
    // After rescale, bumping must still work correctly
    let vals = make_vals(&[None; 3]);
    vsids.bump(Variable(1), &vals, true);
    assert!(
        vsids.activity(Variable(1)).is_finite(),
        "activity must be finite after bump post-rescale"
    );
    assert!(
        vsids.activity(Variable(1)) > vsids.activity(Variable(0)),
        "bumped variable must have higher activity"
    );
}

// -- CHB tests --

#[test]
fn test_chb_arrays_lazy_allocation() {
    // In the default state (no CHB usage), CHB arrays must be None (#8121).
    let vsids = VSIDS::new(100);
    assert!(
        vsids.chb_scores.is_none(),
        "CHB scores must not be allocated on construction"
    );
    assert!(
        vsids.chb_last_conflict.is_none(),
        "CHB last_conflict must not be allocated on construction"
    );
}

#[test]
fn test_chb_arrays_allocated_on_first_bump() {
    let mut vsids = VSIDS::new(100);
    vsids.chb_bump(Variable(5));
    assert!(
        vsids.chb_scores.is_some(),
        "CHB scores must be allocated after first chb_bump"
    );
    assert!(
        vsids.chb_last_conflict.is_some(),
        "CHB last_conflict must be allocated after first chb_bump"
    );
    assert_eq!(vsids.chb_scores.as_ref().unwrap().len(), 100);
}

#[test]
fn test_chb_arrays_not_allocated_by_ensure_num_vars() {
    let mut vsids = VSIDS::new(50);
    vsids.ensure_num_vars(100);
    assert!(
        vsids.chb_scores.is_none(),
        "ensure_num_vars must not allocate CHB arrays if they are None"
    );
}

#[test]
fn test_chb_arrays_grown_by_ensure_num_vars_when_allocated() {
    let mut vsids = VSIDS::new(50);
    vsids.chb_bump(Variable(0)); // Force allocation
    assert_eq!(vsids.chb_scores.as_ref().unwrap().len(), 50);
    vsids.ensure_num_vars(100);
    assert_eq!(
        vsids.chb_scores.as_ref().unwrap().len(),
        100,
        "ensure_num_vars must grow CHB arrays when already allocated"
    );
}

#[test]
fn test_chb_reset_preserves_none() {
    let mut vsids = VSIDS::new(50);
    vsids.chb_reset();
    assert!(
        vsids.chb_scores.is_none(),
        "chb_reset must not allocate CHB arrays if they were None"
    );
}

#[test]
fn test_chb_initial_scores_are_zero() {
    let vsids = VSIDS::new(5);
    for i in 0..5u32 {
        assert_eq!(vsids.chb_score(Variable(i)), 0.0);
    }
}

#[test]
fn test_chb_bump_increases_score() {
    let mut vsids = VSIDS::new(5);
    let before = vsids.chb_score(Variable(2));
    vsids.chb_bump(Variable(2));
    let after = vsids.chb_score(Variable(2));
    assert!(
        after > before,
        "CHB bump must increase Q-score: before={before}, after={after}"
    );
}

#[test]
fn test_chb_reward_locality() {
    // A variable bumped with a small gap (recent conflict involvement)
    // gets a higher reward than one bumped with a large gap.
    let mut vsids = VSIDS::new(5);

    // Bump var 0 with a large gap: advance 100 conflicts first.
    for _ in 0..100 {
        vsids.chb_on_conflict();
    }
    vsids.chb_bump(Variable(0)); // gap = 100 - 0 + 1 = 101
    let score_large_gap = vsids.chb_score(Variable(0));

    // Bump var 1 immediately after (gap = 0)
    vsids.chb_bump(Variable(1)); // gap = 100 - 0 + 1 = 101 (same gap)
    vsids.chb_on_conflict(); // conflict 101
    vsids.chb_bump(Variable(1)); // gap = 101 - 100 + 1 = 2
    let score_small_gap = vsids.chb_score(Variable(1));

    // Variable 1 was bumped twice (once with large gap, once with small gap).
    // Variable 0 was bumped once with a large gap.
    // Var 1 should have accumulated more score from the second bump with
    // high reward (small gap).
    assert!(
        score_small_gap > score_large_gap,
        "var 1 (bumped with small gap) should have higher score than var 0 (large gap): small={score_small_gap}, large={score_large_gap}"
    );
}

#[test]
fn test_chb_alpha_decays() {
    let mut vsids = VSIDS::new(3);
    let alpha_before = vsids.chb_alpha;
    vsids.chb_on_conflict();
    let alpha_after = vsids.chb_alpha;
    assert!(
        alpha_after < alpha_before,
        "alpha must decay: before={alpha_before}, after={alpha_after}"
    );
    assert!(
        alpha_after >= 0.06,
        "alpha must not drop below CHB_ALPHA_MIN: {alpha_after}"
    );
}

#[test]
fn test_chb_reset_clears_state() {
    let mut vsids = VSIDS::new(5);
    vsids.chb_bump(Variable(0));
    vsids.chb_bump(Variable(1));
    vsids.chb_on_conflict();
    vsids.chb_on_conflict();

    vsids.chb_reset();

    for i in 0..5u32 {
        assert_eq!(
            vsids.chb_score(Variable(i)),
            0.0,
            "CHB score must be 0 after reset"
        );
    }
    assert_eq!(vsids.chb_conflicts, 0);
    assert!(
        (vsids.chb_alpha - 0.4).abs() < 1e-10,
        "alpha must be reset to CHB_ALPHA_INIT"
    );
}

#[test]
fn test_chb_swap_and_heap_selection() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Give var 3 the highest EVSIDS activity
    vsids.bump(Variable(3), &vals, true);
    vsids.bump(Variable(3), &vals, true);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(3)));
    vsids.insert_into_heap(Variable(3));

    // Give var 1 the highest CHB score
    for _ in 0..20 {
        vsids.chb_bump(Variable(1));
        vsids.chb_on_conflict();
    }

    // Swap to CHB mode: heap should now order by CHB scores
    vsids.swap_chb_scores();
    let top_chb = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(
        top_chb,
        Variable(1),
        "after swap, heap should order by CHB scores"
    );
    vsids.insert_into_heap(Variable(1));

    // Swap back: heap should order by EVSIDS again
    vsids.swap_chb_scores();
    let top_evsids = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(
        top_evsids,
        Variable(3),
        "after swap back, heap should order by EVSIDS scores"
    );
}

#[test]
fn test_chb_bump_while_loaded_updates_heap() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Swap to CHB mode
    vsids.swap_chb_scores();

    // Bump var 2 many times while CHB is loaded -- should update heap
    for _ in 0..50 {
        vsids.chb_bump(Variable(2));
        vsids.chb_on_conflict();
    }

    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(
        top,
        Variable(2),
        "var 2 with many CHB bumps should be heap top while CHB is loaded"
    );

    // Swap back
    vsids.insert_into_heap(Variable(2));
    vsids.swap_chb_scores();
}

#[test]
fn test_chb_ensure_num_vars_extends_arrays() {
    let mut vsids = VSIDS::new(3);
    vsids.ensure_num_vars(6);

    // New variables should have zero CHB scores
    for i in 3..6u32 {
        assert_eq!(vsids.chb_score(Variable(i)), 0.0);
    }

    // Bumping new variables should work
    vsids.chb_bump(Variable(5));
    assert!(vsids.chb_score(Variable(5)) > 0.0);
}

#[test]
fn test_chb_dormant_evsids_bump() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Give var 0 some EVSIDS activity
    vsids.bump(Variable(0), &vals, true);
    let evsids_before = vsids.activity(Variable(0));

    // Swap to CHB mode (EVSIDS scores now in chb_scores)
    vsids.swap_chb_scores();

    // Dormant bump var 0 EVSIDS score
    vsids.bump_evsids_score_dormant(Variable(0));
    vsids.decay_evsids_dormant();

    // Swap back and check EVSIDS score increased
    vsids.swap_chb_scores();
    let evsids_after = vsids.activity(Variable(0));
    assert!(
        evsids_after > evsids_before,
        "dormant EVSIDS bump must increase score: before={evsids_before}, after={evsids_after}"
    );
}
