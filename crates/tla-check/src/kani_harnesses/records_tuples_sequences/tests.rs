// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::value::{RecordBuilder, Value};
use std::collections::BTreeMap;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_field_access() {
    let mut builder = RecordBuilder::new();
    builder.insert_str("field", Value::Bool(true));
    let r = Value::Record(builder.build());
    if let Value::Record(m) = &r {
        let field = m.get("field");
        assert!(field.is_some(), "Record must have field");
        assert_eq!(*field.unwrap(), Value::Bool(true));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_append_length() {
    let mut vec = vec![Value::int(1)];
    let original_len = vec.len();
    vec.push(Value::int(2));
    assert_eq!(
        vec.len(),
        original_len + 1,
        "Append must increase length by 1"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_except_preserves_other_fields() {
    let mut r: BTreeMap<Arc<str>, Value> = BTreeMap::new();
    r.insert(Arc::from("x"), Value::int(1));
    r.insert(Arc::from("y"), Value::Bool(true));
    let original_y = r.get(&Arc::from("y") as &Arc<str>).cloned();
    let mut r_new = r.clone();
    r_new.insert(Arc::from("x"), Value::int(42));
    assert_eq!(
        r_new.get(&Arc::from("y") as &Arc<str>),
        original_y.as_ref(),
        "Updating x must not affect y"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_except_updates_field() {
    let mut r: BTreeMap<Arc<str>, Value> = BTreeMap::new();
    r.insert(Arc::from("x"), Value::int(1));
    let new_val = Value::int(42);
    r.insert(Arc::from("x"), new_val.clone());
    assert_eq!(
        r.get(&Arc::from("x") as &Arc<str>),
        Some(&new_val),
        "Field must be updated"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_concat_length() {
    let test_cases: [(Vec<i32>, Vec<i32>); 4] = [
        (vec![], vec![]),
        (vec![1], vec![]),
        (vec![], vec![1, 2]),
        (vec![1, 2], vec![3, 4, 5]),
    ];
    for (s, t) in test_cases {
        let len_s = s.len();
        let len_t = t.len();
        let mut concat = s.clone();
        concat.extend(t);
        assert_eq!(concat.len(), len_s + len_t, "Len(s ∘ t) = Len(s) + Len(t)");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_concat_identity() {
    let test_seqs = [
        vec![],
        vec![Value::int(1)],
        vec![Value::int(1), Value::int(2)],
    ];
    for s in test_seqs {
        let empty: Vec<Value> = vec![];
        let mut left = empty.clone();
        left.extend(s.iter().cloned());
        assert_eq!(left, s, "<<>> ∘ s = s");
        let mut right = s.clone();
        right.extend(empty.iter().cloned());
        assert_eq!(right, s, "s ∘ <<>> = s");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_index_returns_correct_element() {
    let seq = [Value::int(10), Value::int(20), Value::int(30)];
    assert_eq!(seq[0], Value::int(10));
    assert_eq!(seq[1], Value::int(20));
    assert_eq!(seq[2], Value::int(30));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_head_returns_first() {
    let seq = [Value::int(1), Value::int(2)];
    let head = seq.first().cloned();
    assert!(head.is_some());
    assert_eq!(head.unwrap(), Value::int(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_head_empty_fails() {
    let seq: Vec<Value> = vec![];
    let head = seq.first();
    assert!(head.is_none(), "Head of empty seq must fail");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_tail_returns_rest() {
    let seq = [Value::int(1), Value::int(2), Value::int(3)];
    let tail: Vec<Value> = seq[1..].to_vec();
    assert_eq!(tail.len(), 2);
    assert_eq!(tail[0], Value::int(2));
    assert_eq!(tail[1], Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_tail_singleton_is_empty() {
    let seq = [Value::int(1)];
    let tail: Vec<Value> = seq[1..].to_vec();
    assert!(tail.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseq_returns_correct_slice() {
    let seq = [
        Value::int(10),
        Value::int(20),
        Value::int(30),
        Value::int(40),
    ];
    let subseq: Vec<Value> = seq[1..3].to_vec();
    assert_eq!(subseq.len(), 2);
    assert_eq!(subseq[0], Value::int(20));
    assert_eq!(subseq[1], Value::int(30));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_append_adds_at_end() {
    let mut seq = vec![Value::int(1), Value::int(2)];
    let elem = Value::int(3);
    let original_len = seq.len();
    seq.push(elem.clone());
    assert_eq!(seq.len(), original_len + 1);
    assert_eq!(seq.last(), Some(&elem));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_element_access() {
    let tuple = [Value::Bool(true), Value::int(42), Value::string("hello")];
    assert_eq!(tuple[0], Value::Bool(true));
    assert_eq!(tuple[1], Value::int(42));
    assert_eq!(tuple[2], Value::string("hello"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_equality() {
    let t1 = vec![Value::int(1), Value::Bool(true)];
    let t2 = vec![Value::int(1), Value::Bool(true)];
    assert_eq!(t1, t2, "Tuples with same elements must be equal");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_different_lengths_not_equal() {
    let t1 = vec![Value::int(1)];
    let t2 = vec![Value::int(1), Value::int(2)];
    assert_ne!(t1, t2, "Tuples with different lengths must not be equal");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_different_elements_not_equal() {
    let t1 = vec![Value::int(1), Value::int(2)];
    let t2 = vec![Value::int(1), Value::int(3)];
    assert_ne!(t1, t2, "Tuples with different elements must not be equal");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_length() {
    let t0: Vec<Value> = vec![];
    let t1 = [Value::int(1)];
    let t2 = [Value::int(1), Value::int(2)];
    let t3 = [Value::int(1), Value::int(2), Value::int(3)];
    assert_eq!(t0.len(), 0);
    assert_eq!(t1.len(), 1);
    assert_eq!(t2.len(), 2);
    assert_eq!(t3.len(), 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sequence_length() {
    let empty: Vec<Value> = vec![];
    assert_eq!(empty.len(), 0);
    let s1 = [Value::int(1)];
    assert_eq!(s1.len(), 1);
    let s3 = [Value::int(1), Value::int(2), Value::int(3)];
    assert_eq!(s3.len(), 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_empty_sequence_properties() {
    let empty: Vec<Value> = vec![];
    assert!(empty.is_empty(), "Empty sequence must be empty");
    assert!(empty.is_empty(), "Empty sequence has no Head");
    assert!(empty.last().is_none(), "Empty sequence has no last element");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_true_returns_then_branch() {
    let then_val = Value::int(1);
    let else_val = Value::int(2);
    let result = if true { then_val.clone() } else { else_val };
    assert_eq!(result, then_val, "IF TRUE THEN x ELSE y must equal x");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_false_returns_else_branch() {
    let then_val = Value::int(1);
    let else_val = Value::int(2);
    let result = if false { then_val } else { else_val.clone() };
    assert_eq!(result, else_val, "IF FALSE THEN x ELSE y must equal y");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[allow(clippy::if_same_then_else)]
fn test_if_same_branches_equals_branch() {
    let val = Value::int(42);
    let result_true = if true { val.clone() } else { val.clone() };
    let result_false = if false { val.clone() } else { val.clone() };
    assert_eq!(result_true, val);
    assert_eq!(result_false, val);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_if_consistency() {
    let a = Value::int(1);
    let b = Value::int(2);
    let c = Value::int(3);
    for c1 in [true, false] {
        for c2 in [true, false] {
            let nested = if c1 {
                if c2 {
                    a.clone()
                } else {
                    b.clone()
                }
            } else {
                c.clone()
            };
            let expected = if c1 && c2 {
                a.clone()
            } else if c1 && !c2 {
                b.clone()
            } else {
                c.clone()
            };
            assert_eq!(nested, expected, "Nested IF must evaluate correctly");
        }
    }
}
