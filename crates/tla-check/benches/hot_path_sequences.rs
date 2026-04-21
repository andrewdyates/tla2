// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sequence operation benchmarks: head, tail, append, IntIntervalFunc EXCEPT.

use criterion::{black_box, BenchmarkId, Criterion};
use std::sync::Arc;
use tla_check::Value;
use tla_value::SeqValue;

use crate::hot_path_fixtures::small_int;

/// Create a sequence of integers <<1, 2, ..., n>>
fn int_seq(n: usize) -> Value {
    let values: Vec<Value> = (1..=n as i64).map(Value::SmallInt).collect();
    Value::Seq(Arc::new(values.into()))
}

/// Simulate Tail operation using SeqValue's native O(log n) tail
fn seq_tail(seq: &SeqValue) -> Value {
    Value::Seq(Arc::new(seq.tail()))
}

/// Simulate Append operation using SeqValue's native O(log n) append
fn seq_append(seq: &SeqValue, elem: Value) -> Value {
    Value::Seq(Arc::new(seq.append(elem)))
}

pub fn bench_seq_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("seq_ops");

    // Head (read first element - O(log n) with im::Vector)
    for size in [5, 10, 50] {
        group.bench_with_input(BenchmarkId::new("head", size), &size, |b, &size| {
            let seq = int_seq(size);
            let seq_value = match &seq {
                Value::Seq(s) => s,
                _ => panic!("Expected Seq"),
            };
            b.iter(|| black_box(seq_value.first().cloned()));
        });
    }

    // Tail (creates new sequence without first element - O(log n) with im::Vector)
    for size in [5, 10, 50] {
        group.bench_with_input(BenchmarkId::new("tail", size), &size, |b, &size| {
            let seq = int_seq(size);
            let arc_seq = match &seq {
                Value::Seq(s) => s.clone(),
                _ => panic!("Expected Seq"),
            };
            b.iter(|| black_box(seq_tail(&arc_seq)));
        });
    }

    // Append (creates new sequence with element added - O(log n) with im::Vector)
    for size in [5, 10, 50] {
        group.bench_with_input(BenchmarkId::new("append", size), &size, |b, &size| {
            let seq = int_seq(size);
            let arc_seq = match &seq {
                Value::Seq(s) => s.clone(),
                _ => panic!("Expected Seq"),
            };
            let new_elem = small_int(999);
            b.iter(|| black_box(seq_append(&arc_seq, new_elem.clone())));
        });
    }

    // Compare with IntFunc EXCEPT (should be O(1) with COW)
    for size in [5, 10, 50] {
        group.bench_with_input(
            BenchmarkId::new("intfunc_except", size),
            &size,
            |b, &size| {
                use tla_value::IntIntervalFunc;
                let values: Vec<Value> = (1..=size as i64).map(Value::SmallInt).collect();
                let func = IntIntervalFunc::new(1, size as i64, values);
                let key = small_int(size as i64 / 2);
                let new_val = small_int(999);
                b.iter(|| black_box(func.clone().except(key.clone(), new_val.clone())));
            },
        );
    }

    group.finish();
}
