// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{should_materialize_extensionally, Value};
use std::cmp::Ordering;

fn set_variant_order(v: &Value) -> u8 {
    match v {
        Value::Set(_) | Value::Interval(_) => 0,
        Value::Subset(_) => 1,
        Value::FuncSet(_) => 2,
        Value::RecordSet(_) => 3,
        Value::TupleSet(_) => 4,
        Value::SetCup(_) => 5,
        Value::SetCap(_) => 6,
        Value::SetDiff(_) => 7,
        Value::KSubset(_) => 8,
        Value::BigUnion(_) => 9,
        Value::SeqSet(_) => 10,
        Value::StringSet => 11,
        Value::AnySet => 12,
        Value::SetPred(_) => 13,
        _ => 255,
    }
}

fn cmp_set_like_structural(lhs: &Value, rhs: &Value) -> Ordering {
    let ord = set_variant_order(lhs).cmp(&set_variant_order(rhs));
    if ord != Ordering::Equal {
        return ord;
    }
    match (lhs, rhs) {
        (Value::Subset(a), Value::Subset(b)) => a.base.cmp(&b.base),
        (Value::FuncSet(a), Value::FuncSet(b)) => a.cmp(b),
        (Value::RecordSet(a), Value::RecordSet(b)) => a.cmp(b),
        (Value::TupleSet(a), Value::TupleSet(b)) => a.cmp(b),
        (Value::SetCup(a), Value::SetCup(b)) => a.cmp(b),
        (Value::SetCap(a), Value::SetCap(b)) => a.cmp(b),
        (Value::SetDiff(a), Value::SetDiff(b)) => a.cmp(b),
        (Value::KSubset(a), Value::KSubset(b)) => a.cmp(b),
        (Value::BigUnion(a), Value::BigUnion(b)) => a.cmp(b),
        (Value::SeqSet(a), Value::SeqSet(b)) => a.cmp(b),
        (Value::SetPred(a), Value::SetPred(b)) => a.cmp(b),
        (Value::Set(_), Value::Set(_)) | (Value::Interval(_), Value::Interval(_)) => {
            unreachable!("cmp_set_like_structural is only used for lazy set-like values")
        }
        _ => unreachable!("set_variant_order implies comparable set-like variants"),
    }
}

pub(super) fn cmp_set_like(lhs: &Value, rhs: &Value) -> Ordering {
    let structural = cmp_set_like_structural(lhs, rhs);
    if structural == Ordering::Equal {
        return Ordering::Equal;
    }

    if should_materialize_extensionally(lhs) && should_materialize_extensionally(rhs) {
        match (lhs.to_sorted_set(), rhs.to_sorted_set()) {
            (Some(a), Some(b)) => return a.iter().cmp(b.iter()),
            (Some(_), None) => return Ordering::Less,
            (None, Some(_)) => return Ordering::Greater,
            (None, None) => {}
        }
    }

    structural
}
