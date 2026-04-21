// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Property tests for AoS watched list operations.

use super::*;
use crate::literal::Variable;
use proptest::prelude::*;

#[test]
fn pack_unpack_roundtrip() {
    for blocker in [0u32, 1, 42, u32::MAX] {
        for clause in [0u32, 1, 42, BINARY_FLAG, u32::MAX] {
            let packed = pack(blocker, clause);
            assert_eq!(unpack_blocker(packed), blocker);
            assert_eq!(unpack_clause(packed), clause);
        }
    }
}

#[test]
fn sort_binary_first_moves_binary_to_front() {
    let mut list = WatchList::new();
    // Add: non-binary(0), binary(1), non-binary(2), binary(3), non-binary(4)
    list.push(10, 0); // non-binary clause 0
    list.push(11, 1 | BINARY_FLAG); // binary clause 1
    list.push(12, 2); // non-binary clause 2
    list.push(13, 3 | BINARY_FLAG); // binary clause 3
    list.push(14, 4); // non-binary clause 4

    assert_eq!(list.len(), 5);
    list.sort_binary_first();
    assert_eq!(list.len(), 5);

    // First two entries should be binary (in original order)
    assert!(list.is_binary(0));
    assert_eq!(list.blocker_raw(0), 11);
    assert!(list.is_binary(1));
    assert_eq!(list.blocker_raw(1), 13);

    // Last three should be non-binary (in original order)
    assert!(!list.is_binary(2));
    assert_eq!(list.blocker_raw(2), 10);
    assert!(!list.is_binary(3));
    assert_eq!(list.blocker_raw(3), 12);
    assert!(!list.is_binary(4));
    assert_eq!(list.blocker_raw(4), 14);
}

#[test]
fn sort_binary_first_all_binary_noop() {
    let mut list = WatchList::new();
    list.push(10, BINARY_FLAG);
    list.push(11, 1 | BINARY_FLAG);
    list.sort_binary_first();
    assert_eq!(list.len(), 2);
    assert_eq!(list.blocker_raw(0), 10);
    assert_eq!(list.blocker_raw(1), 11);
}

#[test]
fn sort_binary_first_no_binary_noop() {
    let mut list = WatchList::new();
    list.push(10, 0);
    list.push(11, 1);
    list.sort_binary_first();
    assert_eq!(list.len(), 2);
    assert_eq!(list.blocker_raw(0), 10);
    assert_eq!(list.blocker_raw(1), 11);
}

#[test]
fn sort_binary_first_empty_noop() {
    let mut list = WatchList::new();
    list.sort_binary_first();
    assert_eq!(list.len(), 0);
}

#[test]
fn extend_range_from_copies_only_requested_slice() {
    let mut src = WatchList::new();
    for i in 0..8u32 {
        src.push(i + 10, i + 100);
    }

    let mut dst = WatchList::new();
    dst.extend_range_from(&src, 2, 6);

    assert_eq!(dst.len(), 4);
    for j in 0..dst.len() {
        assert_eq!(dst.blocker_raw(j), (j as u32) + 12);
        assert_eq!(dst.clause_raw(j), (j as u32) + 102);
    }
}

// ── remap_clause_refs tests ─────────────────────────────────────────

#[test]
fn test_remap_clause_refs_basic() {
    let mut list = WatchList::new();
    // Non-binary entry: clause offset 10, blocker 42
    list.push(42, 10);
    // Binary entry: clause offset 20, blocker 99
    list.push(99, 20 | BINARY_FLAG);
    // Non-binary entry: clause offset 30, blocker 7
    list.push(7, 30);

    // Build remap table: 10->100, 20->200, 30->300
    let mut remap = vec![u32::MAX; 50];
    remap[10] = 100;
    remap[20] = 200;
    remap[30] = 300;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 3);

    // First entry: non-binary, offset remapped 10->100, blocker preserved
    assert!(!list.is_binary(0));
    assert_eq!(list.clause_ref(0), ClauseRef(100));
    assert_eq!(list.blocker_raw(0), 42);

    // Second entry: binary flag preserved, offset remapped 20->200
    assert!(list.is_binary(1));
    assert_eq!(list.clause_ref(1), ClauseRef(200));
    assert_eq!(list.blocker_raw(1), 99);

    // Third entry: non-binary, offset remapped 30->300
    assert!(!list.is_binary(2));
    assert_eq!(list.clause_ref(2), ClauseRef(300));
    assert_eq!(list.blocker_raw(2), 7);
}

#[test]
fn test_remap_clause_refs_binary_preserved() {
    let mut list = WatchList::new();
    // Binary entry: clause offset 5, blocker 77
    list.push(77, 5 | BINARY_FLAG);
    // Binary entry: clause offset 15, blocker 88
    list.push(88, 15 | BINARY_FLAG);

    let mut remap = vec![u32::MAX; 20];
    remap[5] = 50;
    remap[15] = 150;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 2);
    // Binary flag must be preserved on both entries
    assert!(list.is_binary(0));
    assert_eq!(list.clause_ref(0), ClauseRef(50));
    assert!(list.is_binary(1));
    assert_eq!(list.clause_ref(1), ClauseRef(150));
}

#[test]
fn test_remap_clause_refs_deleted_dropped() {
    let mut list = WatchList::new();
    list.push(42, 10); // survives
    list.push(99, 20); // remap[20] == u32::MAX → dropped
    list.push(7, 30); // survives

    let mut remap = vec![u32::MAX; 50];
    remap[10] = 5;
    // remap[20] left as u32::MAX — deleted clause
    remap[30] = 15;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 2);
    assert_eq!(list.clause_ref(0), ClauseRef(5));
    assert_eq!(list.blocker_raw(0), 42);
    assert_eq!(list.clause_ref(1), ClauseRef(15));
    assert_eq!(list.blocker_raw(1), 7);
}

#[test]
fn test_remap_clause_refs_out_of_range_dropped() {
    let mut list = WatchList::new();
    list.push(42, 10); // survives (offset 10 < remap.len())
    list.push(99, 100); // offset 100 >= remap.len() → dropped

    let mut remap = vec![u32::MAX; 50];
    remap[10] = 5;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 1);
    assert_eq!(list.clause_ref(0), ClauseRef(5));
    assert_eq!(list.blocker_raw(0), 42);
}

#[test]
fn test_remap_clause_refs_blocker_preserved() {
    let mut list = WatchList::new();
    // Use distinct blocker values to verify they are not touched
    list.push(111, 0);
    list.push(222, 5);
    list.push(333, 10 | BINARY_FLAG);

    let mut remap = vec![u32::MAX; 20];
    remap[0] = 50;
    remap[5] = 55;
    remap[10] = 60;

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 3);
    assert_eq!(list.blocker_raw(0), 111);
    assert_eq!(list.blocker_raw(1), 222);
    assert_eq!(list.blocker_raw(2), 333);
}

#[test]
fn test_remap_clause_refs_order_preserved() {
    let mut list = WatchList::new();
    // Interleave binary and non-binary with some deletions
    list.push(10, 0); // survives
    list.push(20, 5 | BINARY_FLAG); // deleted
    list.push(30, 10); // survives
    list.push(40, 15 | BINARY_FLAG); // survives
    list.push(50, 20); // survives

    let mut remap = vec![u32::MAX; 30];
    remap[0] = 100;
    // remap[5] = u32::MAX — deleted
    remap[10] = 110;
    remap[15] = 115;
    remap[20] = 120;

    list.remap_clause_refs(&remap);

    // 4 survivors in original order
    assert_eq!(list.len(), 4);
    assert_eq!(list.blocker_raw(0), 10);
    assert_eq!(list.blocker_raw(1), 30);
    assert_eq!(list.blocker_raw(2), 40);
    assert_eq!(list.blocker_raw(3), 50);
}

#[test]
fn test_remap_clause_refs_empty_noop() {
    let mut list = WatchList::new();
    let remap = vec![0u32; 10];

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 0);
}

#[test]
fn test_remap_clause_refs_all_deleted() {
    let mut list = WatchList::new();
    list.push(10, 0);
    list.push(20, 5 | BINARY_FLAG);
    list.push(30, 10);

    // All entries map to u32::MAX (deleted)
    let remap = vec![u32::MAX; 20];

    list.remap_clause_refs(&remap);

    assert_eq!(list.len(), 0);
}

// ── shrink_capacity tests ───────────────────────────────────────────

#[test]
fn test_shrink_capacity_shrinks_oversized() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));

    // Add many entries to one watch list.
    for i in 0..100u32 {
        watches.add_watch(lit, Watcher::new(ClauseRef(i), Literal::positive(Variable(1))));
    }

    let cap_before = watches.get_watches(lit).capacity();
    assert!(cap_before >= 100);

    // Clear most entries (keep only 2).
    let mut wl = watches.get_watches_mut(lit);
    wl.truncate(2);

    // capacity >> 2*len+16, so shrink should reclaim.
    watches.shrink_capacity();

    let cap_after = watches.get_watches(lit).capacity();
    assert!(
        cap_after < cap_before,
        "capacity should decrease: before={cap_before}, after={cap_after}"
    );
}

#[test]
fn test_shrink_capacity_preserves_small_lists() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));

    // Add a few entries.
    for i in 0..3u32 {
        watches.add_watch(lit, Watcher::new(ClauseRef(i), Literal::positive(Variable(1))));
    }

    let len_before = watches.len_of(lit);
    watches.shrink_capacity();
    let len_after = watches.len_of(lit);

    // Entries must be preserved regardless of whether the unified buffer
    // defragments (small dead regions from doubling may trigger compaction).
    assert_eq!(len_after, len_before);
    // Verify data integrity after potential defragmentation.
    for i in 0..3 {
        assert_eq!(watches.clause_ref(lit, i), ClauseRef(i as u32));
    }
}

proptest! {
    /// Adding a watch increases the count by one
    #[test]
    fn prop_add_watch_increases_count(var_idx in 0u32..10) {
        let mut watches = WatchedLists::new(10);
        let lit = Literal::positive(Variable(var_idx));
        let blocker = Literal::negative(Variable(var_idx));
        let clause_ref = ClauseRef(0);

        let before = watches.get_watches(lit).len();
        watches.add_watch(lit, Watcher::new(clause_ref, blocker));
        let after = watches.get_watches(lit).len();

        prop_assert_eq!(after, before + 1);
    }

    /// Watches are empty after initialization
    #[test]
    fn prop_watches_initially_empty(num_vars in 1usize..20, var_idx in 0u32..20) {
        prop_assume!(var_idx < num_vars as u32);
        let watches = WatchedLists::new(num_vars);
        let pos = Literal::positive(Variable(var_idx));
        let neg = Literal::negative(Variable(var_idx));

        prop_assert_eq!(watches.get_watches(pos).len(), 0);
        prop_assert_eq!(watches.get_watches(neg).len(), 0);
    }

    /// Blocker and clause are preserved when adding a watch
    #[test]
    fn prop_watcher_preserved(
        var1 in 0u32..10,
        var2 in 0u32..10,
        clause_id in 0u32..100
    ) {
        let mut watches = WatchedLists::new(10);
        let lit = Literal::positive(Variable(var1));
        let blocker = Literal::negative(Variable(var2));
        let clause_ref = ClauseRef(clause_id);

        watches.add_watch(lit, Watcher::new(clause_ref, blocker));

        let list = watches.get_watches(lit);
        prop_assert_eq!(list.len(), 1);
        prop_assert_eq!(list.clause_ref(0), clause_ref);
        prop_assert_eq!(list.blocker(0), blocker);
    }

    /// Multiple watches can be added to the same literal
    #[test]
    fn prop_multiple_watches(
        var_idx in 0u32..10,
        num_watches in 1usize..10
    ) {
        let mut watches = WatchedLists::new(10);
        let lit = Literal::positive(Variable(var_idx));

        for i in 0..num_watches {
            watches.add_watch(lit, Watcher::new(
                ClauseRef(i as u32),
                Literal::positive(Variable(0)),
            ));
        }

        prop_assert_eq!(watches.get_watches(lit).len(), num_watches);
    }

    /// Clear empties all watch lists
    #[test]
    fn prop_clear_empties_all(
        num_vars in 1usize..20,
        var_idx in 0u32..20
    ) {
        prop_assume!(var_idx < num_vars as u32);
        let mut watches = WatchedLists::new(num_vars);
        let pos = Literal::positive(Variable(var_idx));
        let neg = Literal::negative(Variable(var_idx));

        // Add some watches
        watches.add_watch(pos, Watcher::new(ClauseRef(0), neg));
        watches.add_watch(neg, Watcher::new(ClauseRef(1), pos));

        // Verify they were added
        prop_assert_eq!(watches.get_watches(pos).len(), 1);
        prop_assert_eq!(watches.get_watches(neg).len(), 1);

        // Clear and verify empty
        watches.clear();
        prop_assert_eq!(watches.get_watches(pos).len(), 0);
        prop_assert_eq!(watches.get_watches(neg).len(), 0);
    }

    /// AoS extend_from copies tail correctly
    #[test]
    fn prop_extend_from(
        n in 2usize..20,
        start in 0usize..20
    ) {
        prop_assume!(start < n);
        let mut src = WatchList::new();
        for i in 0..n {
            src.push(i as u32, (i as u32) * 10);
        }

        let mut dst = WatchList::new();
        dst.extend_from(&src, start);

        prop_assert_eq!(dst.len(), n - start);
        for j in 0..dst.len() {
            prop_assert_eq!(dst.blocker_raw(j), (start + j) as u32);
            prop_assert_eq!(dst.clause_raw(j), ((start + j) as u32) * 10);
        }
    }
}

// ── binary_count invariant tests ─────────────────────────────────────

#[test]
fn test_binary_first_maintained_on_push() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add long, binary, long, binary pattern.
    watches.add_watch(lit, Watcher::new(ClauseRef(0), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(1), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(2), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(3), blocker));

    assert_eq!(watches.len_of(lit), 4);
    // First two should be binary, last two should be long.
    assert!(watches.is_binary(lit, 0));
    assert!(watches.is_binary(lit, 1));
    assert!(!watches.is_binary(lit, 2));
    assert!(!watches.is_binary(lit, 3));

    // Verify debug assert passes.
    watches.debug_assert_binary_first();
}

#[test]
fn test_binary_first_maintained_on_swap_remove_binary() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add binary, binary, long, long.
    watches.add_watch(lit, Watcher::binary(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(11), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(20), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(21), blocker));

    watches.debug_assert_binary_first();

    // Remove first binary entry.
    watches.swap_remove(lit, 0);
    assert_eq!(watches.len_of(lit), 3);
    // Should still have binary-first invariant: 1 binary, 2 long.
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(!watches.is_binary(lit, 1));
    assert!(!watches.is_binary(lit, 2));
}

#[test]
fn test_binary_first_maintained_on_swap_remove_long() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add binary, long, long.
    watches.add_watch(lit, Watcher::binary(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(20), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(21), blocker));

    watches.debug_assert_binary_first();

    // Remove first long entry (index 1).
    watches.swap_remove(lit, 1);
    assert_eq!(watches.len_of(lit), 2);
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(!watches.is_binary(lit, 1));
}

#[test]
fn test_binary_first_maintained_on_clear() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    watches.add_watch(lit, Watcher::binary(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(20), blocker));
    watches.clear_lit(lit);
    assert_eq!(watches.len_of(lit), 0);
    watches.debug_assert_binary_first();
}

#[test]
fn test_binary_first_maintained_through_defragment() {
    let mut watches = WatchedLists::new(4);
    let lit0 = Literal::positive(Variable(0));
    let lit1 = Literal::negative(Variable(0));
    let blocker = Literal::positive(Variable(1));

    // Add entries to two literals.
    watches.add_watch(lit0, Watcher::binary(ClauseRef(1), blocker));
    watches.add_watch(lit0, Watcher::new(ClauseRef(2), blocker));
    watches.add_watch(lit1, Watcher::binary(ClauseRef(3), blocker));
    watches.add_watch(lit1, Watcher::new(ClauseRef(4), blocker));

    watches.debug_assert_binary_first();

    // Force defragmentation.
    watches.defragment();
    watches.debug_assert_binary_first();

    // Verify data integrity.
    assert_eq!(watches.len_of(lit0), 2);
    assert_eq!(watches.len_of(lit1), 2);
    assert!(watches.is_binary(lit0, 0));
    assert!(!watches.is_binary(lit0, 1));
    assert!(watches.is_binary(lit1, 0));
    assert!(!watches.is_binary(lit1, 1));
}

#[test]
fn test_binary_first_maintained_through_remap() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    // Add binary(10), binary(11), long(20), long(21).
    watches.add_watch(lit, Watcher::binary(ClauseRef(10), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(11), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(20), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(21), blocker));

    watches.debug_assert_binary_first();

    // Remap: delete binary(11) and long(21).
    let mut remap = vec![u32::MAX; 30];
    remap[10] = 100;
    // remap[11] = u32::MAX — deleted
    remap[20] = 200;
    // remap[21] = u32::MAX — deleted

    watches.remap_clause_refs(&remap);

    assert_eq!(watches.len_of(lit), 2);
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(!watches.is_binary(lit, 1));
}

#[test]
fn test_binary_first_maintained_through_swap_deferred() {
    let mut watches = WatchedLists::new(4);
    let lit = Literal::positive(Variable(0));
    let blocker = Literal::negative(Variable(1));

    watches.add_watch(lit, Watcher::binary(ClauseRef(1), blocker));
    watches.add_watch(lit, Watcher::binary(ClauseRef(2), blocker));
    watches.add_watch(lit, Watcher::new(ClauseRef(3), blocker));

    watches.debug_assert_binary_first();

    let mut deferred = WatchList::new();
    watches.swap_to_deferred(lit, &mut deferred);
    assert_eq!(watches.len_of(lit), 0);
    assert_eq!(deferred.len(), 3);

    watches.swap_from_deferred(lit, &mut deferred);
    assert_eq!(watches.len_of(lit), 3);
    watches.debug_assert_binary_first();
    assert!(watches.is_binary(lit, 0));
    assert!(watches.is_binary(lit, 1));
    assert!(!watches.is_binary(lit, 2));
}

proptest! {
    /// Binary-first invariant maintained through arbitrary insert sequences.
    #[test]
    fn prop_binary_first_invariant_on_mixed_insert(
        num_binary in 0usize..10,
        num_long in 0usize..10,
        interleave_seed in 0u64..1000
    ) {
        let mut watches = WatchedLists::new(4);
        let lit = Literal::positive(Variable(0));
        let blocker = Literal::negative(Variable(1));

        // Interleave binary and long inserts pseudo-randomly.
        let mut b_remaining = num_binary;
        let mut l_remaining = num_long;
        let mut seed = interleave_seed;
        let mut clause_id = 0u32;
        while b_remaining > 0 || l_remaining > 0 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let pick_binary = if b_remaining == 0 {
                false
            } else if l_remaining == 0 {
                true
            } else {
                seed % 2 == 0
            };
            if pick_binary {
                watches.add_watch(lit, Watcher::binary(ClauseRef(clause_id), blocker));
                b_remaining -= 1;
            } else {
                watches.add_watch(lit, Watcher::new(ClauseRef(clause_id), blocker));
                l_remaining -= 1;
            }
            clause_id += 1;
        }

        prop_assert_eq!(watches.len_of(lit), num_binary + num_long);
        // Verify invariant.
        watches.debug_assert_binary_first();
        // Count binaries.
        let mut bc = 0;
        for i in 0..watches.len_of(lit) {
            if watches.is_binary(lit, i) {
                bc += 1;
            }
        }
        prop_assert_eq!(bc, num_binary);
    }
}
