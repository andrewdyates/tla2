// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use tla_check::Value;
use tla_value::SeqValue;

fn shared_backing_seq() -> SeqValue {
    // im::Vector stores small sequences inline; use enough elements to exercise
    // root sharing across clones and unchanged updates.
    SeqValue::from_vec((0..8).map(Value::int).collect())
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn test_ptr_eq_clone_behavior_matches_feature() {
    let a = shared_backing_seq();
    let b = a.clone();

    #[cfg(feature = "im")]
    assert!(a.ptr_eq(&b));
    #[cfg(not(feature = "im"))]
    assert!(!a.ptr_eq(&b));
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn test_except_if_changed_unchanged_round_trips_and_preserves_ptr_eq_when_im() {
    let a = shared_backing_seq();
    let b = a.except_if_changed(0, Value::int(0));
    assert_eq!(a, b);

    #[cfg(feature = "im")]
    assert!(a.ptr_eq(&b));
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn test_except_if_changed_changed_updates_value_and_breaks_ptr_eq_when_im() {
    let a = SeqValue::from_vec(vec![Value::int(1), Value::int(2)]);
    let b = a.except_if_changed(0, Value::int(7));
    assert_ne!(a, b);
    assert_eq!(b.get(0), Some(&Value::int(7)));

    #[cfg(feature = "im")]
    assert!(!a.ptr_eq(&b));
}

#[cfg_attr(test, timeout(10000))]
#[test]
#[should_panic(expected = "index out of bounds")]
fn test_except_if_changed_panics_on_out_of_bounds() {
    let a = SeqValue::from_vec(vec![Value::int(1)]);
    let _ = a.except_if_changed(1, Value::int(2));
}
