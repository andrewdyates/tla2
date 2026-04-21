// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared benchmark fixtures and data builders for hot_path benchmarks.

use num_bigint::BigInt;
use std::sync::Arc;
use tla_check::state::ArrayState;
use tla_check::VarRegistry;
use tla_check::{FuncValue, Value};
use tla_value::SortedSet;

/// Create a small integer value
pub fn small_int(n: i64) -> Value {
    Value::SmallInt(n)
}

/// Create a big integer value
pub fn big_int(n: i64) -> Value {
    Value::Int(Arc::new(BigInt::from(n)))
}

/// Create a string value
pub fn string_val(s: &str) -> Value {
    Value::String(Arc::from(s))
}

/// Create a set of integers {0, 1, ..., n-1}
pub fn int_set(n: usize) -> Value {
    let values: Vec<Value> = (0..n as i64).map(Value::SmallInt).collect();
    Value::Set(Arc::new(SortedSet::from_sorted_vec(values)))
}

/// Create a SortedSet of integers {0, 1, ..., n-1}
pub fn sorted_int_set(n: usize) -> SortedSet {
    let values: Vec<Value> = (0..n as i64).map(Value::SmallInt).collect();
    SortedSet::from_sorted_vec(values)
}

/// Create a function from integers to integers: [i \in 0..n-1 |-> i * 2]
pub fn int_func(n: usize) -> FuncValue {
    let entries: Vec<(Value, Value)> = (0..n as i64)
        .map(|i| (Value::SmallInt(i), Value::SmallInt(i * 2)))
        .collect();
    FuncValue::from_sorted_entries(entries)
}

/// Create a VarRegistry with n variables
pub fn make_registry(n: usize) -> VarRegistry {
    let names: Vec<Arc<str>> = (0..n).map(|i| Arc::from(format!("var{}", i))).collect();
    VarRegistry::from_names(names)
}

/// Create an ArrayState with n integer variables
pub fn make_array_state(n: usize) -> ArrayState {
    let values: Vec<Value> = (0..n as i64).map(Value::SmallInt).collect();
    ArrayState::from_values(values)
}

/// Create an ArrayState simulating LamportMutex-style state (functions over processes)
pub fn make_mutex_state(num_procs: usize) -> ArrayState {
    // pc[p]: process program counters (function from process id to string)
    let pc_entries: Vec<(Value, Value)> = (0..num_procs)
        .map(|i| (Value::SmallInt(i as i64), string_val("idle")))
        .collect();
    let pc = Value::Func(Arc::new(FuncValue::from_sorted_entries(pc_entries)));

    // num[p]: bakery numbers (function from process id to int)
    let num_entries: Vec<(Value, Value)> = (0..num_procs)
        .map(|i| (Value::SmallInt(i as i64), Value::SmallInt(i as i64 + 1)))
        .collect();
    let num = Value::Func(Arc::new(FuncValue::from_sorted_entries(num_entries)));

    // flag[p]: flags (function from process id to bool)
    let flag_entries: Vec<(Value, Value)> = (0..num_procs)
        .map(|i| (Value::SmallInt(i as i64), Value::Bool(i % 2 == 0)))
        .collect();
    let flag = Value::Func(Arc::new(FuncValue::from_sorted_entries(flag_entries)));

    ArrayState::from_values(vec![pc, num, flag])
}
