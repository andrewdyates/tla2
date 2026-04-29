// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_basic() {
    let registry = VarRegistry::from_names(["x", "y", "z"]);

    let mut array_state = ArrayState::new(3);
    array_state.set(VarIndex(0), Value::int(1));
    array_state.set(VarIndex(1), Value::int(2));
    array_state.set(VarIndex(2), Value::int(3));

    assert_eq!(array_state.get(VarIndex(0)), Value::int(1));
    assert_eq!(array_state.get(VarIndex(1)), Value::int(2));
    assert_eq!(array_state.get(VarIndex(2)), Value::int(3));
    assert_eq!(array_state.len(), 3);

    let state = array_state.to_state(&registry);
    assert_eq!(state.get("x"), Some(&Value::int(1)));
    assert_eq!(state.get("y"), Some(&Value::int(2)));
    assert_eq!(state.get("z"), Some(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_fingerprint_matches_state() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(2))]);

    let mut array_state = ArrayState::new(2);
    array_state.set(VarIndex(0), Value::int(1));
    array_state.set(VarIndex(1), Value::int(2));

    let state_fp = state.fingerprint();
    let array_fp = array_state.fingerprint(&registry);
    assert_eq!(
        state_fp, array_fp,
        "State fp {:016x} != ArrayState fp {:016x}",
        state_fp.0, array_fp.0
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_incremental_fingerprint_updates() {
    let registry = VarRegistry::from_names(["x", "y", "z"]);

    let mut a1 = ArrayState::new(3);
    a1.set(VarIndex(0), Value::int(1));
    let y0 = Value::set([Value::int(1), Value::int(2)]);
    a1.set(VarIndex(1), y0.clone());
    a1.set(VarIndex(2), Value::int(3));

    let fp0 = a1.fingerprint(&registry);

    let y1 = Value::set([Value::int(1), Value::int(2), Value::int(4)]);
    let y1_fp = value_fingerprint(&y1);
    a1.set_with_fp(VarIndex(1), y1.clone(), y1_fp, &registry);
    let fp1_inc = a1.fingerprint(&registry);

    let mut a2 = ArrayState::new(3);
    a2.set(VarIndex(0), Value::int(1));
    a2.set(VarIndex(1), y1);
    a2.set(VarIndex(2), Value::int(3));
    let fp1_full = a2.fingerprint(&registry);

    assert_eq!(fp1_inc, fp1_full);

    a1.set_with_registry(VarIndex(1), y0, &registry);
    let fp0_again = a1.fingerprint(&registry);
    assert_eq!(fp0_again, fp0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_from_state() {
    let registry = VarRegistry::from_names(["a", "b"]);
    let state = State::from_pairs([("a", Value::int(10)), ("b", Value::int(20))]);

    let array_state = ArrayState::from_state(&state, &registry);
    assert_eq!(array_state.get(VarIndex(0)), Value::int(10));
    assert_eq!(array_state.get(VarIndex(1)), Value::int(20));
    assert_eq!(array_state.cached_fingerprint(), None);

    let mut array_state_mut = array_state;
    let array_fp = array_state_mut.fingerprint(&registry);
    assert_eq!(array_fp, state.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_from_indexed() {
    let registry = VarRegistry::from_names(["x", "y", "z"]);
    let values = [Value::int(1), Value::int(2), Value::int(3)];

    let state_indexed = State::from_indexed(&values, &registry);
    let state_pairs = State::from_pairs([
        ("x", Value::int(1)),
        ("y", Value::int(2)),
        ("z", Value::int(3)),
    ]);

    assert_eq!(
        state_indexed.fingerprint(),
        state_pairs.fingerprint(),
        "from_indexed and from_pairs should produce same fingerprint"
    );

    assert_eq!(state_indexed.get("x"), Some(&Value::int(1)));
    assert_eq!(state_indexed.get("y"), Some(&Value::int(2)));
    assert_eq!(state_indexed.get("z"), Some(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_from_array_state() {
    let registry = VarRegistry::from_names(["a", "b"]);

    let mut array_state = ArrayState::new(2);
    array_state.set(VarIndex(0), Value::int(100));
    array_state.set(VarIndex(1), Value::int(200));

    let state = State::from_array_state(&mut array_state, &registry);

    assert_eq!(state.get("a"), Some(&Value::int(100)));
    assert_eq!(state.get("b"), Some(&Value::int(200)));

    let state_pairs = State::from_pairs([("a", Value::int(100)), ("b", Value::int(200))]);
    assert_eq!(state.fingerprint(), state_pairs.fingerprint());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_state_with_fp_incremental_update_correctness() {
    let registry = VarRegistry::from_names(["a", "b", "c"]);
    let state = State::from_pairs([
        ("a", Value::int(1)),
        ("b", Value::int(2)),
        ("c", Value::int(3)),
    ]);

    let mut array_from_fp = ArrayState::from_state_with_fp(&state, &registry);
    array_from_fp.ensure_fp_cache_with_value_fps(&registry);
    array_from_fp.set_with_registry(VarIndex(1), Value::int(20), &registry);

    let fp_from_incremental = array_from_fp.fingerprint(&registry);
    let fresh_state = State::from_pairs([
        ("a", Value::int(1)),
        ("b", Value::int(20)),
        ("c", Value::int(3)),
    ]);
    let fp_fresh = fresh_state.fingerprint();

    assert_eq!(
        fp_from_incremental, fp_fresh,
        "Incremental update from from_state_with_fp should produce same fingerprint as fresh computation"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_successor_state_incremental_fingerprint() {
    let registry = VarRegistry::from_names(["a", "b", "c"]);

    let base_state = State::from_pairs([
        ("a", Value::int(1)),
        ("b", Value::int(2)),
        ("c", Value::int(3)),
    ]);
    let mut base_array = ArrayState::from_state(&base_state, &registry);
    let _base_fp = base_array.fingerprint(&registry);

    let successor_state = State::from_pairs([
        ("a", Value::int(1)),
        ("b", Value::int(99)),
        ("c", Value::int(3)),
    ]);

    let successor_incremental =
        ArrayState::from_successor_state(&successor_state, &base_array, &registry);

    let mut successor_fresh = ArrayState::from_state(&successor_state, &registry);
    let fp_fresh = successor_fresh.fingerprint(&registry);

    let fp_incremental = successor_incremental.cached_fingerprint().unwrap();
    assert_eq!(
        fp_incremental, fp_fresh,
        "from_successor_state should produce same fingerprint as from_state + fingerprint()"
    );

    assert_eq!(successor_incremental.get(VarIndex(0)), Value::int(1));
    assert_eq!(successor_incremental.get(VarIndex(1)), Value::int(99));
    assert_eq!(successor_incremental.get(VarIndex(2)), Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_successor_state_multiple_changes() {
    let registry = VarRegistry::from_names(["a", "b", "c", "d"]);

    let base_state = State::from_pairs([
        ("a", Value::int(1)),
        ("b", Value::int(2)),
        ("c", Value::int(3)),
        ("d", Value::int(4)),
    ]);
    let mut base_array = ArrayState::from_state(&base_state, &registry);
    let _base_fp = base_array.fingerprint(&registry);

    let successor_state = State::from_pairs([
        ("a", Value::int(10)),
        ("b", Value::int(2)),
        ("c", Value::int(30)),
        ("d", Value::int(4)),
    ]);

    let successor_incremental =
        ArrayState::from_successor_state(&successor_state, &base_array, &registry);

    let mut successor_fresh = ArrayState::from_state(&successor_state, &registry);
    let fp_fresh = successor_fresh.fingerprint(&registry);

    let fp_incremental = successor_incremental.cached_fingerprint().unwrap();
    assert_eq!(
        fp_incremental, fp_fresh,
        "Incremental fingerprint should match even with multiple changed variables"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_successor_state_base_without_cache() {
    let registry = VarRegistry::from_names(["x", "y"]);

    let base_state = State::from_pairs([("x", Value::int(5)), ("y", Value::int(6))]);
    let base_array = ArrayState::from_state(&base_state, &registry);

    let successor_state = State::from_pairs([("x", Value::int(50)), ("y", Value::int(6))]);

    let successor_incremental =
        ArrayState::from_successor_state(&successor_state, &base_array, &registry);

    let mut successor_fresh = ArrayState::from_state(&successor_state, &registry);
    let fp_fresh = successor_fresh.fingerprint(&registry);

    let fp_incremental = successor_incremental.cached_fingerprint().unwrap();
    assert_eq!(
        fp_incremental, fp_fresh,
        "Should work even when base has no fp_cache"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_bind_unbind_basic() {
    let _registry = VarRegistry::from_names(["x", "y", "z"]);
    let mut state = ArrayState::new(3);
    let mut undo: Vec<UndoEntry> = Vec::new();

    assert_eq!(state.get(VarIndex(0)), Value::Bool(false));

    state.bind(VarIndex(0), Value::int(1), &mut undo);
    assert_eq!(state.get(VarIndex(0)), Value::int(1));
    assert_eq!(undo.len(), 1);

    state.bind(VarIndex(1), Value::int(2), &mut undo);
    assert_eq!(state.get(VarIndex(1)), Value::int(2));
    assert_eq!(undo.len(), 2);

    state.unbind(&mut undo);
    assert_eq!(state.get(VarIndex(1)), Value::Bool(false));
    assert_eq!(undo.len(), 1);
    assert_eq!(state.get(VarIndex(0)), Value::int(1));

    state.unbind(&mut undo);
    assert_eq!(state.get(VarIndex(0)), Value::Bool(false));
    assert_eq!(undo.len(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_unbind_to() {
    let mut state = ArrayState::new(3);
    let mut undo: Vec<UndoEntry> = Vec::new();

    state.bind(VarIndex(0), Value::int(1), &mut undo);
    state.bind(VarIndex(1), Value::int(2), &mut undo);
    let save_point = undo.len();

    state.bind(VarIndex(2), Value::int(100), &mut undo);
    assert_eq!(state.get(VarIndex(2)), Value::int(100));
    assert_eq!(undo.len(), 3);

    state.unbind_to(&mut undo, save_point);
    assert_eq!(state.get(VarIndex(2)), Value::Bool(false));
    assert_eq!(undo.len(), 2);
    assert_eq!(state.get(VarIndex(0)), Value::int(1));
    assert_eq!(state.get(VarIndex(1)), Value::int(2));

    state.bind(VarIndex(2), Value::int(200), &mut undo);
    assert_eq!(state.get(VarIndex(2)), Value::int(200));

    state.unbind_to(&mut undo, 0);
    assert_eq!(state.get(VarIndex(0)), Value::Bool(false));
    assert_eq!(state.get(VarIndex(1)), Value::Bool(false));
    assert_eq!(state.get(VarIndex(2)), Value::Bool(false));
    assert_eq!(undo.len(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_unbind_to_empty_is_noop() {
    let mut state = ArrayState::new(2);
    let mut undo: Vec<UndoEntry> = Vec::new();

    state.bind(VarIndex(0), Value::int(1), &mut undo);
    assert_eq!(undo.len(), 1);

    state.unbind_to(&mut undo, 1);
    assert_eq!(undo.len(), 1);
    assert_eq!(state.get(VarIndex(0)), Value::int(1));

    state.unbind_to(&mut undo, 100);
    assert_eq!(undo.len(), 1);
    assert_eq!(state.get(VarIndex(0)), Value::int(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_snapshot_creates_correct_state() {
    let registry = VarRegistry::from_names(["a", "b"]);
    let mut state = ArrayState::new(2);
    let mut undo: Vec<UndoEntry> = Vec::new();

    state.bind(VarIndex(0), Value::int(10), &mut undo);
    state.bind(VarIndex(1), Value::int(20), &mut undo);

    let snapshot = state.snapshot(&registry);

    assert_eq!(snapshot.get("a"), Some(&Value::int(10)));
    assert_eq!(snapshot.get("b"), Some(&Value::int(20)));

    state.unbind_to(&mut undo, 0);
    assert_eq!(state.get(VarIndex(0)), Value::Bool(false));
    assert_eq!(snapshot.get("a"), Some(&Value::int(10)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_bind_rebind_same_var() {
    let mut state = ArrayState::new(2);
    let mut undo: Vec<UndoEntry> = Vec::new();

    state.bind(VarIndex(0), Value::int(1), &mut undo);
    assert_eq!(state.get(VarIndex(0)), Value::int(1));

    state.bind(VarIndex(0), Value::int(2), &mut undo);
    assert_eq!(state.get(VarIndex(0)), Value::int(2));
    assert_eq!(undo.len(), 2);

    state.unbind(&mut undo);
    assert_eq!(state.get(VarIndex(0)), Value::int(1));

    state.unbind(&mut undo);
    assert_eq!(state.get(VarIndex(0)), Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_array_state_bind_invalidates_fingerprint() {
    let registry = VarRegistry::from_names(["x"]);
    let mut state = ArrayState::new(1);
    let mut undo: Vec<UndoEntry> = Vec::new();

    let fp1 = state.fingerprint(&registry);
    assert!(state.cached_fingerprint().is_some());

    state.bind(VarIndex(0), Value::int(1), &mut undo);
    assert!(state.cached_fingerprint().is_none());

    let fp2 = state.fingerprint(&registry);
    assert_ne!(fp1, fp2);

    state.unbind(&mut undo);
    assert!(state.cached_fingerprint().is_none());

    let fp3 = state.fingerprint(&registry);
    assert_eq!(fp1, fp3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_clone_with_complete_fp_cache_preserves_value_fps() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let mut state = ArrayState::from_values(vec![Value::int(1), Value::int(2)]);
    let fp = state.fingerprint(&registry);

    let cloned = state.clone_with_complete_fp_cache();

    assert!(cloned.has_complete_fp_cache());
    assert_eq!(cloned.cached_fingerprint(), Some(fp));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diff_successor_complete_fp_cache_updates_changed_slot_fps() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let mut base = ArrayState::from_values(vec![Value::int(1), Value::int(2)]);
    let _ = base.fingerprint(&registry);

    let diff = DiffSuccessor::from_changes(smallvec::smallvec![(VarIndex(1), Value::int(5))]);
    let (succ_fp, combined_xor) =
        compute_diff_fingerprint_with_xor(&base, &diff.changes, &registry);
    let mut succ =
        diff.into_array_state_with_complete_fp_cache(&base, succ_fp, combined_xor, &registry);

    assert!(succ.has_complete_fp_cache());

    succ.set_with_registry(VarIndex(1), Value::int(7), &registry);
    let succ_inc_fp = succ.fingerprint(&registry);

    let mut fresh = ArrayState::from_values(vec![Value::int(1), Value::int(7)]);
    let fresh_fp = fresh.fingerprint(&registry);
    assert_eq!(succ_inc_fp, fresh_fp);
}

/// Part of #3399: Verify DiffSuccessor.materialize produces correct fingerprints
/// when the base state comes from `from_state_with_fp` (which previously stored
/// `combined_xor: 0`, causing incremental fingerprint divergence).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3399_diff_materialize_from_state_with_fp_base() {
    let registry = VarRegistry::from_names(["a", "b", "c"]);
    let base_state = State::from_pairs([
        ("a", Value::int(10)),
        ("b", Value::int(20)),
        ("c", Value::int(30)),
    ]);

    // Create base via from_state_with_fp — the code path that previously had combined_xor=0.
    // Do NOT call ensure_fp_cache_with_value_fps — the bug manifests when the base
    // state is used directly as a DiffSuccessor base without the recompute path.
    let base_array = ArrayState::from_state_with_fp(&base_state, &registry);

    // Build a diff that changes variable "b" (index 1)
    let diff = DiffSuccessor::from_changes(smallvec::smallvec![(VarIndex(1), Value::int(99))]);

    // Materialize using the base with (previously broken) combined_xor
    let materialized = diff.materialize(&base_array, &registry);

    // Compute expected fingerprint from scratch
    let expected_state = State::from_pairs([
        ("a", Value::int(10)),
        ("b", Value::int(99)),
        ("c", Value::int(30)),
    ]);
    let mut expected_array = ArrayState::from_state(&expected_state, &registry);
    let expected_fp = expected_array.fingerprint(&registry);

    let materialized_fp = materialized
        .cached_fingerprint()
        .expect("should have cached fp");
    assert_eq!(
        materialized_fp, expected_fp,
        "DiffSuccessor.materialize from from_state_with_fp base must match fresh fingerprint"
    );
}

/// Part of #3399: Verify from_successor_state produces correct fingerprints
/// when the base state comes from `from_state_with_fp`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3399_from_successor_state_with_fp_base() {
    let registry = VarRegistry::from_names(["x", "y", "z"]);
    let base_state = State::from_pairs([
        ("x", Value::int(5)),
        ("y", Value::int(6)),
        ("z", Value::int(7)),
    ]);

    // Base created via from_state_with_fp (previously stored combined_xor: 0)
    let base_array = ArrayState::from_state_with_fp(&base_state, &registry);

    let succ_state = State::from_pairs([
        ("x", Value::int(5)),
        ("y", Value::int(60)),
        ("z", Value::int(7)),
    ]);

    let succ_incremental = ArrayState::from_successor_state(&succ_state, &base_array, &registry);

    let mut succ_fresh = ArrayState::from_state(&succ_state, &registry);
    let fp_fresh = succ_fresh.fingerprint(&registry);

    let fp_incremental = succ_incremental.cached_fingerprint().unwrap();
    assert_eq!(
        fp_incremental, fp_fresh,
        "from_successor_state with from_state_with_fp base must match fresh fingerprint"
    );
}

/// Regression: `set_cached_fingerprint()` stores only the final fingerprint,
/// leaving `combined_xor` unavailable for incremental successor hashing.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diff_into_array_state_with_cached_fp_only_base() {
    let registry = VarRegistry::from_names(["x"]);
    let base_state = State::from_pairs([("x", Value::int(1237))]);

    let mut base_with_fp_only = ArrayState::from_state(&base_state, &registry);
    let base_fp = base_with_fp_only.fingerprint(&registry);
    let mut base_with_fp_only = ArrayState::from_state(&base_state, &registry);
    base_with_fp_only.set_cached_fingerprint(base_fp);

    let diff = DiffSuccessor::from_changes(smallvec::smallvec![(VarIndex(0), Value::int(1238))]);
    let materialized = diff.into_array_state(&base_with_fp_only, &registry, None);

    let successor_state = State::from_pairs([("x", Value::int(1238))]);
    let mut expected = ArrayState::from_state(&successor_state, &registry);
    let expected_fp = expected.fingerprint(&registry);

    assert_eq!(materialized.cached_fingerprint(), Some(expected_fp));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_from_successor_state_with_cached_fp_only_base() {
    let registry = VarRegistry::from_names(["x"]);
    let base_state = State::from_pairs([("x", Value::int(1237))]);

    let mut base_with_fp_only = ArrayState::from_state(&base_state, &registry);
    let base_fp = base_with_fp_only.fingerprint(&registry);
    let mut base_with_fp_only = ArrayState::from_state(&base_state, &registry);
    base_with_fp_only.set_cached_fingerprint(base_fp);

    let successor_state = State::from_pairs([("x", Value::int(1238))]);
    let succ_incremental =
        ArrayState::from_successor_state(&successor_state, &base_with_fp_only, &registry);

    let mut succ_fresh = ArrayState::from_state(&successor_state, &registry);
    let fp_fresh = succ_fresh.fingerprint(&registry);

    assert_eq!(succ_incremental.cached_fingerprint(), Some(fp_fresh));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_with_registry_after_cached_fingerprint_only_base() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let base_state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(2))]);

    let mut mutated = ArrayState::from_state(&base_state, &registry);
    let base_fp = mutated.fingerprint(&registry);
    let mut mutated = ArrayState::from_state(&base_state, &registry);
    mutated.set_cached_fingerprint(base_fp);
    mutated.set_with_registry(VarIndex(1), Value::int(20), &registry);

    let expected_state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(20))]);
    let mut expected = ArrayState::from_state(&expected_state, &registry);
    let expected_fp = expected.fingerprint(&registry);

    assert_eq!(mutated.cached_fingerprint(), Some(expected_fp));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_with_fp_after_cached_fingerprint_only_base() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let base_state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(2))]);

    let mut mutated = ArrayState::from_state(&base_state, &registry);
    let base_fp = mutated.fingerprint(&registry);
    let mut mutated = ArrayState::from_state(&base_state, &registry);
    mutated.set_cached_fingerprint(base_fp);

    let new_value = Value::int(20);
    mutated.set_with_fp(
        VarIndex(1),
        new_value.clone(),
        value_fingerprint(&new_value),
        &registry,
    );

    let expected_state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(20))]);
    let mut expected = ArrayState::from_state(&expected_state, &registry);
    let expected_fp = expected.fingerprint(&registry);

    assert_eq!(mutated.cached_fingerprint(), Some(expected_fp));
}
