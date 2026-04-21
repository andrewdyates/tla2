// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Collection and value benchmarks: set operations, function operations, value comparison, cloning.

use criterion::{black_box, BenchmarkId, Criterion, Throughput};
use std::sync::Arc;
use tla_check::Value;
use tla_value::SortedSet;

use crate::hot_path_fixtures::*;

pub fn bench_set_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("set_ops");

    // Contains (membership test)
    for size in [10, 100, 1000] {
        group.bench_with_input(BenchmarkId::new("contains", size), &size, |b, &size| {
            let set = sorted_int_set(size);
            let target = small_int((size / 2) as i64);
            b.iter(|| black_box(set.contains(black_box(&target))));
        });
    }

    // Union
    for size in [10, 100, 1000] {
        group.throughput(Throughput::Elements(size as u64 * 2));
        group.bench_with_input(BenchmarkId::new("union", size), &size, |b, &size| {
            let set1 = sorted_int_set(size);
            // Second set: {size/2, size/2+1, ..., 3*size/2-1} (50% overlap)
            let set2: SortedSet = {
                let start = (size / 2) as i64;
                let values: Vec<Value> =
                    (start..start + size as i64).map(Value::SmallInt).collect();
                SortedSet::from_sorted_vec(values)
            };
            b.iter(|| black_box(set1.union(black_box(&set2))));
        });
    }

    // Intersection
    for size in [10, 100, 1000] {
        group.throughput(Throughput::Elements(size as u64 * 2));
        group.bench_with_input(BenchmarkId::new("intersection", size), &size, |b, &size| {
            let set1 = sorted_int_set(size);
            let set2: SortedSet = {
                let start = (size / 2) as i64;
                let values: Vec<Value> =
                    (start..start + size as i64).map(Value::SmallInt).collect();
                SortedSet::from_sorted_vec(values)
            };
            b.iter(|| black_box(set1.intersection(black_box(&set2))));
        });
    }

    // Difference
    for size in [10, 100, 1000] {
        group.throughput(Throughput::Elements(size as u64 * 2));
        group.bench_with_input(BenchmarkId::new("difference", size), &size, |b, &size| {
            let set1 = sorted_int_set(size);
            let set2: SortedSet = {
                let start = (size / 2) as i64;
                let values: Vec<Value> =
                    (start..start + size as i64).map(Value::SmallInt).collect();
                SortedSet::from_sorted_vec(values)
            };
            b.iter(|| black_box(set1.difference(black_box(&set2))));
        });
    }

    // Insert (adding one element)
    for size in [10, 100, 1000] {
        group.bench_with_input(BenchmarkId::new("insert", size), &size, |b, &size| {
            let set = sorted_int_set(size);
            let new_elem = small_int(size as i64 + 1); // Element not in set
            b.iter(|| black_box(set.insert(black_box(new_elem.clone()))));
        });
    }

    // is_subset
    for size in [10, 100, 1000] {
        group.bench_with_input(BenchmarkId::new("is_subset", size), &size, |b, &size| {
            let subset: SortedSet = {
                let values: Vec<Value> = (0..size as i64 / 2).map(Value::SmallInt).collect();
                SortedSet::from_sorted_vec(values)
            };
            let superset = sorted_int_set(size);
            b.iter(|| black_box(subset.is_subset(black_box(&superset))));
        });
    }

    group.finish();
}

pub fn bench_func_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("func_ops");

    // Apply (lookup)
    for size in [10, 100, 1000] {
        group.bench_with_input(BenchmarkId::new("apply", size), &size, |b, &size| {
            let func = int_func(size);
            let key = small_int((size / 2) as i64);
            b.iter(|| black_box(func.apply(black_box(&key))));
        });
    }

    // Apply with miss (key not in domain)
    group.bench_function("apply_miss", |b| {
        let func = int_func(100);
        let key = small_int(1000); // Not in domain
        b.iter(|| black_box(func.apply(black_box(&key))));
    });

    // Except (update one entry)
    for size in [10, 100, 1000] {
        group.bench_with_input(BenchmarkId::new("except", size), &size, |b, &size| {
            let func = int_func(size);
            let key = small_int((size / 2) as i64);
            let new_val = small_int(999);
            b.iter(|| {
                black_box(
                    func.clone()
                        .except(black_box(key.clone()), black_box(new_val.clone())),
                )
            });
        });
    }

    // Except with same value (no-op optimization)
    group.bench_function("except_same_value", |b| {
        let func = int_func(100);
        let key = small_int(50);
        let same_val = small_int(100); // Same as func[50] = 50*2 = 100
        b.iter(|| {
            black_box(
                func.clone()
                    .except(black_box(key.clone()), black_box(same_val.clone())),
            )
        });
    });

    // Domain contains
    for size in [10, 100, 1000] {
        group.bench_with_input(
            BenchmarkId::new("domain_contains", size),
            &size,
            |b, &size| {
                let func = int_func(size);
                let key = small_int((size / 2) as i64);
                b.iter(|| black_box(func.domain_contains(black_box(&key))));
            },
        );
    }

    group.finish();
}

pub fn bench_value_cmp(c: &mut Criterion) {
    let mut group = c.benchmark_group("value_cmp");

    // SmallInt comparison
    group.bench_function("smallint", |b| {
        let a = small_int(12345);
        let b_val = small_int(12346);
        b.iter(|| black_box(a.cmp(black_box(&b_val))));
    });

    // String comparison
    group.bench_function("string", |b| {
        let a = string_val("idle");
        let b_val = string_val("waiting");
        b.iter(|| black_box(a.cmp(black_box(&b_val))));
    });

    // Set comparison (same size, different elements)
    group.bench_function("set_100", |b| {
        let a = int_set(100);
        let b_val: Value = {
            let values: Vec<Value> = (1..101).map(Value::SmallInt).collect();
            Value::Set(Arc::new(SortedSet::from_sorted_vec(values)))
        };
        b.iter(|| black_box(a.cmp(black_box(&b_val))));
    });

    // Function comparison
    group.bench_function("func_100", |b| {
        let a = Value::Func(Arc::new(int_func(100)));
        let b_val = Value::Func(Arc::new(int_func(100)));
        b.iter(|| black_box(a.cmp(black_box(&b_val))));
    });

    group.finish();
}

pub fn bench_value_clone(c: &mut Criterion) {
    let mut group = c.benchmark_group("value_clone");

    // SmallInt (trivial copy)
    group.bench_function("smallint", |b| {
        let v = small_int(12345);
        b.iter(|| black_box(v.clone()));
    });

    // String (Arc increment)
    group.bench_function("string", |b| {
        let v = string_val("waiting_for_critical_section");
        b.iter(|| black_box(v.clone()));
    });

    // Set (Arc increment)
    group.bench_function("set_100", |b| {
        let v = int_set(100);
        b.iter(|| black_box(v.clone()));
    });

    // Function (Arc increment)
    group.bench_function("func_100", |b| {
        let v = Value::Func(Arc::new(int_func(100)));
        b.iter(|| black_box(v.clone()));
    });

    group.finish();
}
