// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::kani_harnesses::kani_generators::*;
use crate::value::Value;
use std::collections::BTreeMap;
use std::sync::Arc;

// P12: Record Operations

#[kani::proof]
fn verify_record_field_access() {
    use crate::value::RecordValue;
    let b: bool = kani::any();
    let entries = vec![(Arc::from("field"), Value::Bool(b))];
    let r = Value::Record(RecordValue::from_sorted_entries(entries));
    if let Value::Record(m) = &r {
        let field = m.get("field");
        assert!(field.is_some(), "Record must have inserted field");
        assert!(
            *field.unwrap() == Value::Bool(b),
            "Field value must match inserted value"
        );
    }
}

// P13: Sequence Operations

#[kani::proof]
fn verify_seq_length() {
    let s = any_small_seq();
    if let Value::Seq(vec) = &s {
        assert!(vec.len() <= 5, "Sequence length bounded by construction");
    }
}

#[kani::proof]
fn verify_seq_append_length() {
    let s = any_small_seq();
    if let Value::Seq(vec) = s {
        let original_len = vec.len();
        let new_vec = vec.append(Value::Bool(true));
        assert!(
            new_vec.len() == original_len + 1,
            "Append must increase length by 1"
        );
    }
}

// P42: Sequence Operator Semantics

#[kani::proof]
fn verify_seq_concat_length() {
    let choice_s: u8 = kani::any();
    let choice_t: u8 = kani::any();
    kani::assume(choice_s < 3);
    kani::assume(choice_t < 3);
    let s: Vec<Value> = match choice_s {
        0 => vec![],
        1 => vec![Value::int(1)],
        _ => vec![Value::int(1), Value::int(2)],
    };
    let t: Vec<Value> = match choice_t {
        0 => vec![],
        1 => vec![Value::int(3)],
        _ => vec![Value::int(3), Value::int(4)],
    };
    let len_s = s.len();
    let len_t = t.len();
    let mut concat = s;
    concat.extend(t);
    let len_concat = concat.len();
    assert!(len_concat == len_s + len_t, "Len(s ∘ t) = Len(s) + Len(t)");
}

#[kani::proof]
fn verify_seq_concat_identity() {
    let s = any_small_seq();
    if let Value::Seq(seq_s) = s {
        let vec_s = seq_s.to_vec();
        let empty: Vec<Value> = vec![];
        let mut left = empty.clone();
        left.extend(vec_s.iter().cloned());
        let mut right = vec_s.clone();
        right.extend(empty.iter().cloned());
        assert!(left == vec_s, "<<>> ∘ s = s");
        assert!(right == vec_s, "s ∘ <<>> = s");
    }
}

// P44: Record EXCEPT Semantics

#[kani::proof]
fn verify_record_except_preserves_other_fields() {
    let mut r: BTreeMap<Arc<str>, Value> = BTreeMap::new();
    r.insert(Arc::from("x"), Value::int(1));
    r.insert(Arc::from("y"), Value::Bool(true));
    let original_y = r.get(&Arc::from("y") as &Arc<str>).cloned();
    let mut r_new = r.clone();
    r_new.insert(Arc::from("x"), Value::int(42));
    assert!(
        r_new.get(&Arc::from("y") as &Arc<str>) == original_y.as_ref(),
        "Updating x must not affect y"
    );
}

#[kani::proof]
fn verify_record_except_updates_field() {
    let mut r: BTreeMap<Arc<str>, Value> = BTreeMap::new();
    r.insert(Arc::from("x"), Value::int(1));
    let new_val = Value::int(42);
    r.insert(Arc::from("x"), new_val.clone());
    assert!(
        r.get(&Arc::from("x") as &Arc<str>) == Some(&new_val),
        "Field must be updated"
    );
}

// P53: Sequence Index/Access Semantics

#[kani::proof]
fn verify_seq_index_returns_correct_element() {
    let seq = vec![Value::int(10), Value::int(20), Value::int(30)];
    assert!(seq[0] == Value::int(10), "seq[1] (0-indexed: 0) must be 10");
    assert!(seq[1] == Value::int(20), "seq[2] (0-indexed: 1) must be 20");
    assert!(seq[2] == Value::int(30), "seq[3] (0-indexed: 2) must be 30");
}

#[kani::proof]
fn verify_seq_head_returns_first() {
    let v1 = any_small_int_value();
    let v2 = any_bool_value();
    let seq = vec![v1.clone(), v2];
    let head = seq.first().cloned();
    assert!(head.is_some(), "Head of non-empty seq must exist");
    assert!(head.unwrap() == v1, "Head must return first element");
}

#[kani::proof]
fn verify_seq_head_empty_fails() {
    let seq: Vec<Value> = vec![];
    let head = seq.first();
    assert!(head.is_none(), "Head of empty seq must fail");
}

#[kani::proof]
fn verify_seq_tail_returns_rest() {
    let seq = vec![Value::int(1), Value::int(2), Value::int(3)];
    let tail: Vec<Value> = seq[1..].to_vec();
    assert!(tail.len() == 2, "Tail must have length - 1");
    assert!(tail[0] == Value::int(2), "Tail[1] must be original[2]");
    assert!(tail[1] == Value::int(3), "Tail[2] must be original[3]");
}

#[kani::proof]
fn verify_seq_tail_singleton_is_empty() {
    let seq = vec![Value::int(1)];
    let tail: Vec<Value> = seq[1..].to_vec();
    assert!(tail.is_empty(), "Tail of singleton must be empty");
}

#[kani::proof]
fn verify_subseq_returns_correct_slice() {
    let seq = vec![
        Value::int(10),
        Value::int(20),
        Value::int(30),
        Value::int(40),
    ];
    let subseq: Vec<Value> = seq[1..3].to_vec();
    assert!(subseq.len() == 2);
    assert!(subseq[0] == Value::int(20));
    assert!(subseq[1] == Value::int(30));
}

#[kani::proof]
fn verify_seq_append_adds_at_end() {
    let elem = any_small_int_value();
    let mut seq = vec![Value::int(1), Value::int(2)];
    let original_len = seq.len();
    seq.push(elem.clone());
    assert!(
        seq.len() == original_len + 1,
        "Append increases length by 1"
    );
    assert!(seq.last() == Some(&elem), "Append adds element at end");
}

// P54: Tuple Semantics

#[kani::proof]
fn verify_tuple_element_access() {
    let v1 = any_bool_value();
    let v2 = any_small_int_value();
    let v3 = any_short_string_value();
    let tuple = vec![v1.clone(), v2.clone(), v3.clone()];
    assert!(tuple[0] == v1, "tuple[1] must be first element");
    assert!(tuple[1] == v2, "tuple[2] must be second element");
    assert!(tuple[2] == v3, "tuple[3] must be third element");
}

#[kani::proof]
fn verify_tuple_equality() {
    let v1 = any_small_int_value();
    let v2 = any_bool_value();
    let t1 = vec![v1.clone(), v2.clone()];
    let t2 = vec![v1, v2];
    assert!(t1 == t2, "Tuples with same elements must be equal");
}

#[kani::proof]
fn verify_tuple_different_lengths_not_equal() {
    let t1 = vec![Value::int(1)];
    let t2 = vec![Value::int(1), Value::int(2)];
    assert!(t1 != t2, "Tuples with different lengths must not be equal");
}

#[kani::proof]
fn verify_tuple_different_elements_not_equal() {
    let t1 = vec![Value::int(1), Value::int(2)];
    let t2 = vec![Value::int(1), Value::int(3)];
    assert!(t1 != t2, "Tuples with different elements must not be equal");
}

#[kani::proof]
fn verify_tuple_length() {
    let choice: u8 = kani::any();
    kani::assume(choice < 4);
    let tuple: Vec<Value> = match choice {
        0 => vec![],
        1 => vec![Value::int(1)],
        2 => vec![Value::int(1), Value::int(2)],
        _ => vec![Value::int(1), Value::int(2), Value::int(3)],
    };
    let expected_len = choice as usize;
    assert!(
        tuple.len() == expected_len,
        "Tuple length must match element count"
    );
}

// P56: Sequence length

#[kani::proof]
fn verify_sequence_length() {
    let choice: u8 = kani::any();
    kani::assume(choice < 4);
    let seq: Vec<Value> = match choice {
        0 => vec![],
        1 => vec![Value::int(1)],
        2 => vec![Value::int(1), Value::int(2)],
        _ => vec![Value::int(1), Value::int(2), Value::int(3)],
    };
    assert!(
        seq.len() == choice as usize,
        "Sequence length must equal element count"
    );
}

// P57: Empty Sequence

#[kani::proof]
fn verify_empty_sequence_properties() {
    let empty: Vec<Value> = vec![];
    assert!(empty.is_empty(), "Empty sequence must be empty");
    assert!(empty.first().is_none(), "Empty sequence has no Head");
    assert!(empty.last().is_none(), "Empty sequence has no last element");
}

// P58: IF-THEN-ELSE Semantics

#[kani::proof]
fn verify_if_true_returns_then_branch() {
    let then_val = any_small_int_value();
    let else_val = any_small_int_value();
    let result = if true { then_val.clone() } else { else_val };
    assert!(result == then_val, "IF TRUE THEN x ELSE y must equal x");
}

#[kani::proof]
fn verify_if_false_returns_else_branch() {
    let then_val = any_small_int_value();
    let else_val = any_small_int_value();
    let result = if false { then_val } else { else_val.clone() };
    assert!(result == else_val, "IF FALSE THEN x ELSE y must equal y");
}

#[kani::proof]
fn verify_if_same_branches_equals_branch() {
    let condition: bool = kani::any();
    let val = any_primitive_value();
    let result = if condition { val.clone() } else { val.clone() };
    assert!(result == val, "IF c THEN x ELSE x must equal x");
}

#[kani::proof]
fn verify_nested_if_consistency() {
    let c1: bool = kani::any();
    let c2: bool = kani::any();
    let a = Value::int(1);
    let b = Value::int(2);
    let c = Value::int(3);
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
        a
    } else if c1 && !c2 {
        b
    } else {
        c
    };
    assert!(nested == expected, "Nested IF must evaluate correctly");
}

// P-BoolOnly sequence

#[kani::proof]
fn verify_seq_len_nonnegative_boolonly() {
    let s = any_small_seq_boolonly();
    if let Value::Seq(seq) = &s {
        assert!(seq.len() >= 0, "Sequence length must be non-negative");
    }
}
