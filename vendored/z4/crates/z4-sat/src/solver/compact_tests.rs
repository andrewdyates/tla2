// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

#[test]
fn remap_var_vec_handles_empty_source_vector() {
    let map = VariableMap {
        old_to_new: vec![0, 1, 2],
        new_num_vars: 3,
    };
    let mut vec: Vec<u32> = Vec::new();

    map.remap_var_vec(&mut vec);

    assert_eq!(vec, vec![0, 0, 0]);
}

#[test]
fn remap_lit_vec_handles_empty_source_vector() {
    let map = VariableMap {
        old_to_new: vec![0, 1],
        new_num_vars: 2,
    };
    let mut vec: Vec<u32> = Vec::new();

    map.remap_lit_vec(&mut vec);

    assert_eq!(vec, vec![0, 0, 0, 0]);
}

#[test]
fn remap_lit_vec_preserves_mapping_semantics() {
    let map = VariableMap {
        old_to_new: vec![UNMAPPED, 0, 1],
        new_num_vars: 2,
    };
    let mut vec = vec![10, 11, 20, 21, 30, 31];

    map.remap_lit_vec(&mut vec);

    assert_eq!(vec, vec![20, 21, 30, 31]);
}

#[test]
fn compact_resets_subsume_dirty_for_remapped_variables() {
    let mut solver: Solver = Solver::new(4);

    // Force non-trivial remap: keep vars 0 and 2, remove 1 and 3.
    solver.var_lifecycle.mark_eliminated(1);
    solver.var_lifecycle.mark_substituted(3);

    // Simulate a stale dirty-bit state from prior rounds.
    solver.subsume_dirty = vec![false; 4];

    solver.compact();

    assert_eq!(solver.num_vars, 2, "compaction should remove inactive vars");
    assert_eq!(
        solver.subsume_dirty,
        vec![true; 2],
        "all mapped vars must be dirty after compaction"
    );
}

/// Verify that `compact_watches` skips binary watchers whose blocker
/// references an eliminated variable, and falls back to the watched
/// literal for long watchers with eliminated blockers.
#[test]
fn compact_watches_binary_vs_long_unmapped_blocker() {
    use crate::literal::{Literal, Variable};
    use crate::watched::{ClauseRef, WatchedLists, Watcher};

    // 4 vars: 0 active, 1 eliminated, 2 active, 3 active.
    let map = VariableMap {
        old_to_new: vec![0, UNMAPPED, 1, 2],
        new_num_vars: 3,
    };
    let l = |v: u32| Literal::positive(Variable(v));
    let mut watches = WatchedLists::new(4);

    // Binary with eliminated blocker → SKIP (stale clause)
    watches.add_watch(l(0), Watcher::binary(ClauseRef(10), l(1)));
    // Binary with active blocker → KEEP + remap
    watches.add_watch(l(0), Watcher::binary(ClauseRef(11), l(2)));
    // Long with eliminated blocker → fallback to watched literal
    watches.add_watch(l(0), Watcher::new(ClauseRef(20), l(1)));
    // Long with active blocker → KEEP + remap
    watches.add_watch(l(0), Watcher::new(ClauseRef(21), l(3)));

    let mut solver: Solver = Solver::new(4);
    solver.watches = watches;
    solver.compact_watches(&map);

    let new_l0 = l(0); // old 0 → new 0
    let new_l2 = l(1); // old 2 → new 1
    let new_l3 = l(2); // old 3 → new 2
    let wl = solver.watches.get_watches(new_l0);

    // 1 binary skipped + 1 binary kept + 2 long kept = 3
    assert_eq!(wl.len(), 3, "stale binary watcher should be skipped");

    // Entry 0: binary, blocker remapped from old var 2 → new var 1
    assert!(wl.is_binary(0));
    assert_eq!(wl.blocker(0), new_l2);
    assert_eq!(wl.clause_ref(0), ClauseRef(11));

    // Entry 1: long, eliminated blocker falls back to watched literal
    assert!(!wl.is_binary(1));
    assert_eq!(wl.blocker(1), new_l0, "fallback to watched literal");
    assert_eq!(wl.clause_ref(1), ClauseRef(20));

    // Entry 2: long, blocker remapped from old var 3 → new var 2
    assert!(!wl.is_binary(2));
    assert_eq!(wl.blocker(2), new_l3);
    assert_eq!(wl.clause_ref(2), ClauseRef(21));
}

/// Verify root_satisfied_saved is NOT remapped during compaction (#5250).
/// With external indices, conditioning saves entries in external space.
/// Compact does not remap them — they use stable external indices.
#[test]
fn compact_does_not_remap_root_satisfied_saved() {
    use crate::literal::{Literal, Variable};

    let mut solver: Solver = Solver::new(4);

    // Eliminate vars 1 and 3 → map: {0→0, 1→UNMAPPED, 2→1, 3→UNMAPPED}
    solver.var_lifecycle.mark_eliminated(1);
    solver.var_lifecycle.mark_substituted(3);

    // Simulate conditioning having saved a root-satisfied clause
    // in external space (as condition.rs now does via externalize_lits).
    // Before compaction, external = internal (identity), so these literals
    // represent external vars 0, 2, 1.
    let saved_clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(2)),
        Literal::positive(Variable(1)), // eliminated external var
    ];
    solver.cold.root_satisfied_saved.push(saved_clause.clone());

    solver.compact();

    assert_eq!(solver.num_vars, 2);
    assert_eq!(solver.cold.root_satisfied_saved.len(), 1);

    // root_satisfied_saved should be UNCHANGED (external indices, not remapped)
    let unchanged = &solver.cold.root_satisfied_saved[0];
    assert_eq!(unchanged[0], saved_clause[0]);
    assert_eq!(unchanged[1], saved_clause[1]);
    assert_eq!(unchanged[2], saved_clause[2]);
}
