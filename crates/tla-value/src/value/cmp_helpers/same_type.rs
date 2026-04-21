// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::Value;
use super::primitives::type_order;
use super::set_like::cmp_set_like;
use num_traits::ToPrimitive;
use std::cmp::Ordering;
use std::sync::Arc;

fn cmp_interval_with_set(interval: &Value, set: &Value) -> Ordering {
    let (Value::Interval(iv), Value::Set(s)) = (interval, set) else {
        unreachable!("cmp_interval_with_set requires Interval and Set operands");
    };
    let mut iv_iter = iv.iter_values();
    let mut s_iter = s.iter();
    loop {
        match (iv_iter.next(), s_iter.next()) {
            (Some(a), Some(b)) => {
                let cmp = a.cmp(b);
                if cmp != Ordering::Equal {
                    return cmp;
                }
            }
            (Some(_), None) => return Ordering::Greater,
            (None, Some(_)) => return Ordering::Less,
            (None, None) => return Ordering::Equal,
        }
    }
}

#[inline]
pub(in crate::value) fn cmp_same_type(lhs: &Value, rhs: &Value) -> Ordering {
    match (lhs, rhs) {
        (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
        (Value::SmallInt(a), Value::SmallInt(b)) => a.cmp(b),
        (Value::SmallInt(a), Value::Int(b)) => {
            if let Some(b_i64) = b.to_i64() {
                a.cmp(&b_i64)
            } else if b.sign() == num_bigint::Sign::Minus {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        }
        (Value::Int(a), Value::SmallInt(b)) => {
            if let Some(a_i64) = a.to_i64() {
                a_i64.cmp(b)
            } else if a.sign() == num_bigint::Sign::Minus {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        }
        (Value::Int(a), Value::Int(b)) => a.cmp(b),
        (Value::String(a), Value::String(b)) => {
            if Arc::ptr_eq(a, b) {
                Ordering::Equal
            } else {
                a.cmp(b)
            }
        }
        (Value::ModelValue(a), Value::ModelValue(b)) => {
            if Arc::ptr_eq(a, b) {
                Ordering::Equal
            } else {
                a.cmp(b)
            }
        }
        (Value::Tuple(a), Value::Tuple(b)) => {
            if Arc::ptr_eq(a, b) {
                Ordering::Equal
            } else {
                a.cmp(b)
            }
        }
        (Value::Seq(a), Value::Seq(b)) => {
            if a.ptr_eq(b) {
                Ordering::Equal
            } else {
                a.cmp(b)
            }
        }
        (Value::Record(a), Value::Record(b)) => {
            if a.ptr_eq(b) {
                Ordering::Equal
            } else {
                a.cmp(b)
            }
        }
        (Value::StringSet, Value::StringSet) => Ordering::Equal,
        (Value::AnySet, Value::AnySet) => Ordering::Equal,
        (Value::StringSet, Value::AnySet) => Ordering::Less,
        (Value::AnySet, Value::StringSet) => Ordering::Greater,
        (Value::StringSet, _) => Ordering::Greater,
        (_, Value::StringSet) => Ordering::Less,
        (Value::AnySet, _) => Ordering::Greater,
        (_, Value::AnySet) => Ordering::Less,
        (Value::SeqSet(a), Value::SeqSet(b)) => a.cmp(b),
        (Value::Interval(a), Value::Interval(b)) => a.cmp(b),
        (Value::SeqSet(ssv), other @ (Value::Set(_) | Value::Interval(_) | Value::Subset(_))) => {
            if ssv.base.is_empty_set() == Some(true) {
                let empty_seq = Value::seq(Vec::<Value>::new());
                let singleton = Value::set([empty_seq]);
                singleton.cmp(other)
            } else {
                Ordering::Greater
            }
        }
        (other @ (Value::Set(_) | Value::Interval(_) | Value::Subset(_)), Value::SeqSet(ssv)) => {
            if ssv.base.is_empty_set() == Some(true) {
                let empty_seq = Value::seq(Vec::<Value>::new());
                let singleton = Value::set([empty_seq]);
                other.cmp(&singleton)
            } else {
                Ordering::Less
            }
        }
        (Value::Interval(_), Value::Set(_)) => cmp_interval_with_set(lhs, rhs),
        (Value::Set(_), Value::Interval(_)) => cmp_interval_with_set(rhs, lhs).reverse(),
        (Value::Set(a), Value::Set(b)) => {
            if a.ptr_eq(b) {
                Ordering::Equal
            } else {
                let mut ai = a.iter();
                let mut bi = b.iter();
                loop {
                    match (ai.next(), bi.next()) {
                        (Some(av), Some(bv)) => {
                            let cmp = av.cmp(bv);
                            if cmp != Ordering::Equal {
                                return cmp;
                            }
                        }
                        (Some(_), None) => return Ordering::Greater,
                        (None, Some(_)) => return Ordering::Less,
                        (None, None) => return Ordering::Equal,
                    }
                }
            }
        }
        (Value::Subset(_), Value::Subset(_)) => cmp_set_like(lhs, rhs),
        (Value::Subset(_), Value::Set(_) | Value::Interval(_))
        | (Value::Set(_) | Value::Interval(_), Value::Subset(_)) => cmp_set_like(lhs, rhs),
        (Value::FuncSet(_), Value::FuncSet(_)) => cmp_set_like(lhs, rhs),
        (Value::FuncSet(_), _) | (_, Value::FuncSet(_)) => cmp_set_like(lhs, rhs),
        (Value::RecordSet(_), Value::RecordSet(_)) => cmp_set_like(lhs, rhs),
        (Value::RecordSet(_), _) | (_, Value::RecordSet(_)) => cmp_set_like(lhs, rhs),
        (Value::TupleSet(_), Value::TupleSet(_)) => cmp_set_like(lhs, rhs),
        (Value::TupleSet(_), _) | (_, Value::TupleSet(_)) => cmp_set_like(lhs, rhs),
        (Value::SetCup(_), Value::SetCup(_)) => cmp_set_like(lhs, rhs),
        (Value::SetCap(_), Value::SetCap(_)) => cmp_set_like(lhs, rhs),
        (Value::SetDiff(_), Value::SetDiff(_)) => cmp_set_like(lhs, rhs),
        (Value::SetCup(_), _) | (_, Value::SetCup(_)) => cmp_set_like(lhs, rhs),
        (Value::SetCap(_), _) | (_, Value::SetCap(_)) => cmp_set_like(lhs, rhs),
        (Value::SetDiff(_), _) | (_, Value::SetDiff(_)) => cmp_set_like(lhs, rhs),
        (Value::Func(a), Value::Func(b)) => {
            if a.ptr_eq(b) {
                Ordering::Equal
            } else {
                a.cmp(b)
            }
        }
        (Value::IntFunc(a), Value::IntFunc(b)) => {
            if Arc::ptr_eq(&a.values, &b.values) && a.min == b.min && a.max == b.max {
                Ordering::Equal
            } else {
                match a.min.cmp(&b.min) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
                match a.max.cmp(&b.max) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
                a.values.iter().cmp(b.values.iter())
            }
        }
        (Value::LazyFunc(a), Value::LazyFunc(b)) => a.id().cmp(&b.id()),
        (Value::Closure(a), Value::Closure(b)) => a.id().cmp(&b.id()),
        (Value::SetPred(_), Value::SetPred(_)) => cmp_set_like(lhs, rhs),
        (Value::SetPred(_), _) | (_, Value::SetPred(_)) => cmp_set_like(lhs, rhs),
        (Value::KSubset(_), Value::KSubset(_)) => cmp_set_like(lhs, rhs),
        (Value::KSubset(_), _) | (_, Value::KSubset(_)) => cmp_set_like(lhs, rhs),
        (Value::BigUnion(_), Value::BigUnion(_)) => cmp_set_like(lhs, rhs),
        (Value::BigUnion(_), _) | (_, Value::BigUnion(_)) => cmp_set_like(lhs, rhs),
        _ => unreachable!(
            "Value::cmp: type_order({})={} == type_order({})={} but no match arm covered this pair",
            lhs.type_name(),
            type_order(lhs),
            rhs.type_name(),
            type_order(rhs),
        ),
    }
}
