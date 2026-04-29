// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fingerprinting benchmarks: value fingerprinting, hash comparison, ArrayState fingerprinting.

use criterion::{black_box, BenchmarkId, Criterion, Throughput};
use num_bigint::BigInt;
use std::sync::Arc;
use tla_check::state::{value_fingerprint, value_fingerprint_ahash, value_fingerprint_xxh3};
use tla_check::Value;
use tla_check::VarRegistry;

use crate::hot_path_fixtures::*;

pub fn bench_value_fingerprint(c: &mut Criterion) {
    let mut group = c.benchmark_group("fingerprint/value");

    // SmallInt fingerprinting
    group.bench_function("smallint", |b| {
        let v = small_int(12345);
        b.iter(|| black_box(value_fingerprint(black_box(&v))));
    });

    // BigInt fingerprinting
    group.bench_function("bigint_small", |b| {
        let v = big_int(12345);
        b.iter(|| black_box(value_fingerprint(black_box(&v))));
    });

    group.bench_function("bigint_large", |b| {
        let v = Value::Int(Arc::new(BigInt::from(10).pow(50)));
        b.iter(|| black_box(value_fingerprint(black_box(&v))));
    });

    // String fingerprinting
    group.bench_function("string_short", |b| {
        let v = string_val("idle");
        b.iter(|| black_box(value_fingerprint(black_box(&v))));
    });

    group.bench_function("string_medium", |b| {
        let v = string_val("waiting_for_critical_section");
        b.iter(|| black_box(value_fingerprint(black_box(&v))));
    });

    // Bool fingerprinting
    group.bench_function("bool", |b| {
        let v = Value::Bool(true);
        b.iter(|| black_box(value_fingerprint(black_box(&v))));
    });

    // Set fingerprinting (various sizes)
    for size in [10, 100, 1000] {
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(BenchmarkId::new("set", size), &size, |b, &size| {
            let v = int_set(size);
            b.iter(|| black_box(value_fingerprint(black_box(&v))));
        });
    }

    // Function fingerprinting (various sizes)
    for size in [10, 100, 1000] {
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(BenchmarkId::new("func", size), &size, |b, &size| {
            let func = int_func(size);
            let v = Value::Func(Arc::new(func));
            b.iter(|| {
                // Clear cache to measure actual fingerprinting work
                let v_clone = v.clone();
                black_box(value_fingerprint(black_box(&v_clone)))
            });
        });
    }

    // Function fingerprinting with cache (measures cache lookup overhead)
    group.bench_function("func_cached", |b| {
        let func = int_func(100);
        let v = Value::Func(Arc::new(func));
        // Warm the cache
        let _ = value_fingerprint(&v);
        b.iter(|| black_box(value_fingerprint(black_box(&v))));
    });

    group.finish();
}

pub fn bench_fnv_vs_xxh3(c: &mut Criterion) {
    let mut group = c.benchmark_group("fingerprint/hash_comparison");

    // SmallInt comparison
    {
        let v = small_int(12345);
        group.bench_function("smallint/fnv", |b| {
            b.iter(|| black_box(value_fingerprint(black_box(&v))));
        });
        group.bench_function("smallint/xxh3", |b| {
            b.iter(|| black_box(value_fingerprint_xxh3(black_box(&v))));
        });
        group.bench_function("smallint/ahash", |b| {
            b.iter(|| black_box(value_fingerprint_ahash(black_box(&v))));
        });
    }

    // String comparison
    {
        let v = string_val("waiting_for_critical_section");
        group.bench_function("string_medium/fnv", |b| {
            b.iter(|| black_box(value_fingerprint(black_box(&v))));
        });
        group.bench_function("string_medium/xxh3", |b| {
            b.iter(|| black_box(value_fingerprint_xxh3(black_box(&v))));
        });
        group.bench_function("string_medium/ahash", |b| {
            b.iter(|| black_box(value_fingerprint_ahash(black_box(&v))));
        });
    }

    // Set of 100 integers
    {
        let v = int_set(100);
        group.bench_function("set_100/fnv", |b| {
            b.iter(|| black_box(value_fingerprint(black_box(&v))));
        });
        group.bench_function("set_100/xxh3", |b| {
            b.iter(|| black_box(value_fingerprint_xxh3(black_box(&v))));
        });
        group.bench_function("set_100/ahash", |b| {
            b.iter(|| black_box(value_fingerprint_ahash(black_box(&v))));
        });
    }

    // Set of 1000 integers
    {
        let v = int_set(1000);
        group.bench_function("set_1000/fnv", |b| {
            b.iter(|| black_box(value_fingerprint(black_box(&v))));
        });
        group.bench_function("set_1000/xxh3", |b| {
            b.iter(|| black_box(value_fingerprint_xxh3(black_box(&v))));
        });
        group.bench_function("set_1000/ahash", |b| {
            b.iter(|| black_box(value_fingerprint_ahash(black_box(&v))));
        });
    }

    // Function of 100 entries (without cache)
    {
        let func = int_func(100);
        group.bench_function("func_100/fnv", |b| {
            let v = Value::Func(Arc::new(func.clone()));
            b.iter(|| {
                let v_clone = v.clone();
                black_box(value_fingerprint(black_box(&v_clone)))
            });
        });
        let func = int_func(100);
        group.bench_function("func_100/xxh3", |b| {
            let v = Value::Func(Arc::new(func.clone()));
            b.iter(|| {
                let v_clone = v.clone();
                black_box(value_fingerprint_xxh3(black_box(&v_clone)))
            });
        });
        let func = int_func(100);
        group.bench_function("func_100/ahash", |b| {
            let v = Value::Func(Arc::new(func.clone()));
            b.iter(|| {
                let v_clone = v.clone();
                black_box(value_fingerprint_ahash(black_box(&v_clone)))
            });
        });
    }

    // Function of 1000 entries (without cache)
    {
        let func = int_func(1000);
        group.bench_function("func_1000/fnv", |b| {
            let v = Value::Func(Arc::new(func.clone()));
            b.iter(|| {
                let v_clone = v.clone();
                black_box(value_fingerprint(black_box(&v_clone)))
            });
        });
        let func = int_func(1000);
        group.bench_function("func_1000/xxh3", |b| {
            let v = Value::Func(Arc::new(func.clone()));
            b.iter(|| {
                let v_clone = v.clone();
                black_box(value_fingerprint_xxh3(black_box(&v_clone)))
            });
        });
        let func = int_func(1000);
        group.bench_function("func_1000/ahash", |b| {
            let v = Value::Func(Arc::new(func.clone()));
            b.iter(|| {
                let v_clone = v.clone();
                black_box(value_fingerprint_ahash(black_box(&v_clone)))
            });
        });
    }

    group.finish();
}

pub fn bench_array_state_fingerprint(c: &mut Criterion) {
    let mut group = c.benchmark_group("fingerprint/array_state");

    // Small state (3 variables, simple values)
    group.bench_function("small_3vars", |b| {
        let registry = make_registry(3);
        b.iter(|| {
            let mut state = make_array_state(3);
            black_box(state.fingerprint(black_box(&registry)))
        });
    });

    // Medium state (10 variables)
    group.bench_function("medium_10vars", |b| {
        let registry = make_registry(10);
        b.iter(|| {
            let mut state = make_array_state(10);
            black_box(state.fingerprint(black_box(&registry)))
        });
    });

    // Mutex-style state (3 function variables, 4 processes)
    group.bench_function("mutex_4proc", |b| {
        let registry =
            VarRegistry::from_names(vec![Arc::from("pc"), Arc::from("num"), Arc::from("flag")]);
        b.iter(|| {
            let mut state = make_mutex_state(4);
            black_box(state.fingerprint(black_box(&registry)))
        });
    });

    // Mutex-style state (3 function variables, 8 processes)
    group.bench_function("mutex_8proc", |b| {
        let registry =
            VarRegistry::from_names(vec![Arc::from("pc"), Arc::from("num"), Arc::from("flag")]);
        b.iter(|| {
            let mut state = make_mutex_state(8);
            black_box(state.fingerprint(black_box(&registry)))
        });
    });

    // Incremental fingerprint update (simulates changing one variable)
    group.bench_function("incremental_update", |b| {
        let registry =
            VarRegistry::from_names(vec![Arc::from("pc"), Arc::from("num"), Arc::from("flag")]);
        let mut state = make_mutex_state(4);
        state.ensure_fp_cache_with_value_fps(&registry);

        b.iter(|| {
            let mut state_clone = state.clone();
            let new_value = string_val("critical");
            let new_fp = value_fingerprint(&new_value);
            state_clone.set_with_fp(tla_check::VarIndex(0), new_value, new_fp, &registry);
            black_box(state_clone.cached_fingerprint())
        });
    });

    group.finish();
}
