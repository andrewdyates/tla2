// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::dedup_fingerprint::state_value_fingerprint;
use crate::value::seq::SeqValue;
use crate::value::Value;

fn hash_seq(seq: &SeqValue) -> u64 {
    let mut hasher = DefaultHasher::new();
    seq.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn test_seqvalue_clone_preserves_flat_view_if_materialized() {
    let seq = SeqValue::from_vec(vec![Value::int(1), Value::int(2), Value::int(3)]);

    assert!(seq.cached_flat_view().is_none());

    let _ = seq.to_vec();
    let cached = Arc::clone(
        seq.cached_flat_view()
            .expect("to_vec should populate the cached flat view"),
    );

    let cloned = seq.clone();
    let cloned_cached = cloned
        .cached_flat_view()
        .expect("clone should preserve a materialized flat view");

    assert!(Arc::ptr_eq(&cached, cloned_cached));
    assert_eq!(seq, cloned);
}

#[test]
fn test_seqvalue_cmp_uses_same_result_after_append() {
    let seq = SeqValue::from_vec(vec![Value::int(1), Value::int(2), Value::int(3)]);
    let _ = seq.to_vec();

    let appended = seq.append(Value::int(4));
    let expected = SeqValue::from_vec(vec![
        Value::int(1),
        Value::int(2),
        Value::int(3),
        Value::int(4),
    ]);

    assert!(appended.cached_flat_view().is_none());
    assert_eq!(appended.cmp(&expected), Ordering::Equal);
    assert!(
        appended.cached_flat_view().is_some(),
        "cmp should populate the flat view"
    );
}

#[test]
fn test_seqvalue_eq_uses_same_result_after_except() {
    let seq = SeqValue::from_vec(vec![Value::int(10), Value::int(20), Value::int(30)]);
    let _ = seq.to_vec();

    let updated = seq.except(1, Value::int(99));
    let expected = SeqValue::from_vec(vec![Value::int(10), Value::int(99), Value::int(30)]);

    assert!(updated.cached_flat_view().is_none());
    assert_eq!(updated, expected);
    assert!(
        updated.cached_flat_view().is_some(),
        "eq should populate the flat view"
    );
}

#[test]
fn test_seqvalue_hash_stable_after_flatten() {
    let seq = SeqValue::from_vec(vec![Value::int(7), Value::int(8), Value::int(9)]);

    assert!(seq.cached_flat_view().is_none());

    let hash_before = hash_seq(&seq);
    let cached = Arc::clone(
        seq.cached_flat_view()
            .expect("hash should populate the cached flat view"),
    );
    let hash_after = hash_seq(&seq);

    assert_eq!(hash_before, hash_after);
    assert!(Arc::ptr_eq(
        &cached,
        seq.cached_flat_view()
            .expect("cached flat view should remain populated")
    ));
}

/// Part of #3316: Verify that SeqValue::tail() produces identical fingerprints
/// to manual slicing. The eval_expr.rs optimization changed SeqTail from
/// materializing via to_vec()[1..] to calling s.tail(), which uses O(log n)
/// im::Vector::split_off. This test ensures the representation change does
/// not affect state dedup fingerprints.
#[test]
fn test_seqvalue_tail_fingerprint_matches_manual_slice() {
    let elems = vec![
        Value::int(10),
        Value::int(20),
        Value::int(30),
        Value::int(40),
        Value::int(50),
    ];
    let seq = SeqValue::from_vec(elems.clone());

    // O(log n) persistent tail
    let tail_result = seq.tail();
    // Manual materialized slice (old code path)
    let manual_result = SeqValue::from_vec(elems[1..].to_vec());

    // Equality
    assert_eq!(tail_result, manual_result);

    // std Hash
    assert_eq!(hash_seq(&tail_result), hash_seq(&manual_result));

    // Additive (dedup) fingerprint
    let tail_val = Value::Seq(Arc::new(tail_result));
    let manual_val = Value::Seq(Arc::new(manual_result));
    let tail_fp = state_value_fingerprint(&tail_val).unwrap();
    let manual_fp = state_value_fingerprint(&manual_val).unwrap();
    assert_eq!(
        tail_fp, manual_fp,
        "tail() must produce same dedup fingerprint as manual slice"
    );
}

/// Part of #3316: Verify that SeqValue::append() produces identical fingerprints
/// to manual vec push. The eval_expr.rs optimization changed SeqAppend from
/// to_vec() + push to s.append(), which uses O(log n) im::Vector::push_back.
#[test]
fn test_seqvalue_append_fingerprint_matches_manual_push() {
    let elems = vec![Value::int(1), Value::int(2), Value::int(3)];
    let seq = SeqValue::from_vec(elems.clone());

    // O(log n) persistent append
    let appended = seq.append(Value::int(4));
    // Manual materialized push (old code path)
    let mut manual_elems = elems;
    manual_elems.push(Value::int(4));
    let manual = SeqValue::from_vec(manual_elems);

    // Equality
    assert_eq!(appended, manual);

    // std Hash
    assert_eq!(hash_seq(&appended), hash_seq(&manual));

    // Additive (dedup) fingerprint
    let appended_val = Value::Seq(Arc::new(appended));
    let manual_val = Value::Seq(Arc::new(manual));
    let appended_fp = state_value_fingerprint(&appended_val).unwrap();
    let manual_fp = state_value_fingerprint(&manual_val).unwrap();
    assert_eq!(
        appended_fp, manual_fp,
        "append() must produce same dedup fingerprint as manual push"
    );
}

/// Part of #3316: Verify chained tail + append operations preserve fingerprints.
/// This exercises the common TLA+ pattern: Append(Tail(seq), elem).
#[test]
fn test_seqvalue_chained_tail_append_fingerprint() {
    let seq = SeqValue::from_vec(vec![Value::int(100), Value::int(200), Value::int(300)]);

    // Chain: Tail then Append (common queue rotation pattern)
    let chained = seq.tail().append(Value::int(400));
    // Manual equivalent
    let manual = SeqValue::from_vec(vec![Value::int(200), Value::int(300), Value::int(400)]);

    assert_eq!(chained, manual);
    assert_eq!(hash_seq(&chained), hash_seq(&manual));

    let chained_fp = state_value_fingerprint(&Value::Seq(Arc::new(chained))).unwrap();
    let manual_fp = state_value_fingerprint(&Value::Seq(Arc::new(manual))).unwrap();
    assert_eq!(
        chained_fp, manual_fp,
        "chained tail+append must match manual construction"
    );
}
