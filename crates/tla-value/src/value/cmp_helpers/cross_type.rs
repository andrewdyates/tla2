// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{FuncValue, IntIntervalFunc, RecordValue, Value};
use super::primitives::{cmp_i64_with_value, cmp_str_with_value, eq_i64_with_value};
use std::cmp::Ordering;

// Helper to compare Tuple/Seq with FuncValue without allocation.
// In TLA+, tuples/sequences are functions with domain 1..n.
//
// CRITICAL (Bug #179): This MUST produce the same ordering as FuncValue::cmp
// to ensure binary search works correctly when searching for a Tuple in a set
// of Funcs. FuncValue::cmp compares entries lexicographically (like slice comparison).
//
// The tuple implicitly has entries [(1, tuple[0]), (2, tuple[1]), ...].
// We must compare these lexicographically with the func's entries, NOT by length first.
fn cmp_tuple_with_func(tuple: &[Value], func: &FuncValue) -> Ordering {
    let min_len = tuple.len().min(func.domain_len());
    for (i, (func_key, func_val)) in func.mapping_iter().take(min_len).enumerate() {
        match cmp_i64_with_value((i + 1) as i64, func_key) {
            Ordering::Equal => {}
            ord => return ord,
        }
        match tuple[i].cmp(func_val) {
            Ordering::Equal => {}
            ord => return ord,
        }
    }

    tuple.len().cmp(&func.domain_len())
}

// Helper to compare Tuple/Seq with IntIntervalFunc without allocation.
//
// CRITICAL (Bug #179): This MUST produce the same ordering as FuncValue::cmp
// to ensure binary search works correctly. Compare lexicographically, NOT by length first.
fn cmp_tuple_with_intfunc(tuple: &[Value], intfunc: &IntIntervalFunc) -> Ordering {
    let min_len = tuple.len().min(intfunc.values.len());
    for (i, (tuple_val, int_val)) in tuple
        .iter()
        .zip(intfunc.values.iter())
        .take(min_len)
        .enumerate()
    {
        let tuple_key = (i + 1) as i64;
        let intfunc_key = intfunc.min + i as i64;
        match tuple_key.cmp(&intfunc_key) {
            Ordering::Equal => {}
            ord => return ord,
        }
        match tuple_val.cmp(int_val) {
            Ordering::Equal => {}
            ord => return ord,
        }
    }

    tuple.len().cmp(&intfunc.values.len())
}

// Helper to compare Record with FuncValue without allocation.
// In TLA+, records are functions with string domains.
//
// CRITICAL (Bug #179): This MUST produce the same ordering as FuncValue::cmp
// to ensure binary search works correctly. Compare lexicographically, NOT by length first.
fn cmp_record_with_func(record: &RecordValue, func: &FuncValue) -> Ordering {
    let mut record_iter = record.iter_str();
    let mut entries_iter = func.mapping_iter();

    loop {
        match (record_iter.next(), entries_iter.next()) {
            (Some((rec_key, rec_val)), Some((func_key, func_val))) => {
                match cmp_str_with_value(&rec_key, func_key) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
                match rec_val.cmp(func_val) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
            }
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (None, None) => return Ordering::Equal,
        }
    }
}

// Helper to compare FuncValue with IntIntervalFunc without allocation.
//
// CRITICAL (Bug #179): This MUST produce the same ordering as FuncValue::cmp
// to ensure binary search works correctly. Compare lexicographically, NOT by length first.
fn cmp_func_with_intfunc(func: &FuncValue, intfunc: &IntIntervalFunc) -> Ordering {
    let min_len = func.domain_len().min(intfunc.values.len());

    for (i, ((func_key, func_val), int_val)) in func
        .mapping_iter()
        .zip(intfunc.values.iter())
        .take(min_len)
        .enumerate()
    {
        match cmp_i64_with_value(intfunc.min + i as i64, func_key).reverse() {
            Ordering::Equal => {}
            ord => return ord,
        }
        match func_val.cmp(int_val) {
            Ordering::Equal => {}
            ord => return ord,
        }
    }

    func.domain_len().cmp(&intfunc.values.len())
}

#[inline]
pub(in crate::value) fn cmp_cross_type(lhs: &Value, rhs: &Value) -> Option<Ordering> {
    match (lhs, rhs) {
        (Value::Tuple(a), Value::Func(b)) => Some(cmp_tuple_with_func(a.as_ref(), b)),
        (Value::Seq(a), Value::Func(b)) => Some(cmp_tuple_with_func(a.flat_slice(), b)),
        (Value::Func(a), Value::Tuple(b)) => Some(cmp_tuple_with_func(b.as_ref(), a).reverse()),
        (Value::Func(a), Value::Seq(b)) => Some(cmp_tuple_with_func(b.flat_slice(), a).reverse()),
        (Value::Tuple(a), Value::IntFunc(b)) => Some(cmp_tuple_with_intfunc(a.as_ref(), b)),
        (Value::Seq(a), Value::IntFunc(b)) => Some(cmp_tuple_with_intfunc(a.flat_slice(), b)),
        (Value::IntFunc(a), Value::Tuple(b)) => {
            Some(cmp_tuple_with_intfunc(b.as_ref(), a).reverse())
        }
        (Value::IntFunc(a), Value::Seq(b)) => {
            Some(cmp_tuple_with_intfunc(b.flat_slice(), a).reverse())
        }
        (Value::Tuple(a), Value::Seq(b)) => Some(a.iter().cmp(b.iter())),
        (Value::Seq(a), Value::Tuple(b)) => Some(a.iter().cmp(b.iter())),
        (Value::Record(r), Value::Func(f)) => Some(cmp_record_with_func(r, f)),
        (Value::Func(f), Value::Record(r)) => Some(cmp_record_with_func(r, f).reverse()),
        (Value::Func(f), Value::IntFunc(i)) => Some(cmp_func_with_intfunc(f, i)),
        (Value::IntFunc(i), Value::Func(f)) => Some(cmp_func_with_intfunc(f, i).reverse()),
        _ => None,
    }
}

fn eq_tuple_with_func(tuple: &[Value], func: &FuncValue) -> bool {
    if tuple.len() != func.domain_len() {
        return false;
    }

    for (i, (func_key, func_val)) in func.mapping_iter().enumerate() {
        if !eq_i64_with_value((i + 1) as i64, func_key) {
            return false;
        }
        if &tuple[i] != func_val {
            return false;
        }
    }
    true
}

fn eq_tuple_with_intfunc(tuple: &[Value], intfunc: &IntIntervalFunc) -> bool {
    if tuple.len() != intfunc.values.len() {
        return false;
    }

    for (i, (tuple_val, int_val)) in tuple.iter().zip(intfunc.values.iter()).enumerate() {
        let tuple_key = (i + 1) as i64;
        let intfunc_key = intfunc.min + i as i64;
        if tuple_key != intfunc_key || tuple_val != int_val {
            return false;
        }
    }
    true
}

fn eq_record_with_func(record: &RecordValue, func: &FuncValue) -> bool {
    if record.len() != func.domain_len() {
        return false;
    }

    for ((rec_key, rec_val), (func_key, func_val)) in record.iter_str().zip(func.mapping_iter()) {
        match func_key {
            Value::String(func_key_str) if **func_key_str == *rec_key => {}
            _ => return false,
        }
        if rec_val != func_val {
            return false;
        }
    }
    true
}

fn eq_func_with_intfunc(func: &FuncValue, intfunc: &IntIntervalFunc) -> bool {
    if func.domain_len() != intfunc.values.len() {
        return false;
    }

    for (i, ((func_key, func_val), int_val)) in
        func.mapping_iter().zip(intfunc.values.iter()).enumerate()
    {
        if !eq_i64_with_value(intfunc.min + i as i64, func_key) || func_val != int_val {
            return false;
        }
    }
    true
}

#[inline]
pub(in crate::value) fn eq_cross_type(lhs: &Value, rhs: &Value) -> Option<bool> {
    match (lhs, rhs) {
        (Value::Tuple(a), Value::Func(b)) | (Value::Func(b), Value::Tuple(a)) => {
            Some(eq_tuple_with_func(a.as_ref(), b))
        }
        (Value::Seq(a), Value::Func(b)) | (Value::Func(b), Value::Seq(a)) => {
            Some(eq_tuple_with_func(a.flat_slice(), b))
        }
        (Value::Tuple(a), Value::IntFunc(b)) | (Value::IntFunc(b), Value::Tuple(a)) => {
            Some(eq_tuple_with_intfunc(a.as_ref(), b))
        }
        (Value::Seq(a), Value::IntFunc(b)) | (Value::IntFunc(b), Value::Seq(a)) => {
            Some(eq_tuple_with_intfunc(a.flat_slice(), b))
        }
        (Value::Tuple(a), Value::Seq(b)) | (Value::Seq(b), Value::Tuple(a)) => {
            Some(a.iter().eq(b.iter()))
        }
        (Value::Record(r), Value::Func(f)) | (Value::Func(f), Value::Record(r)) => {
            Some(eq_record_with_func(r, f))
        }
        (Value::Func(f), Value::IntFunc(i)) | (Value::IntFunc(i), Value::Func(f)) => {
            Some(eq_func_with_intfunc(f, i))
        }
        _ => None,
    }
}
