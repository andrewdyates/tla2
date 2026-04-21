// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Microbenchmarks for hot path components
//!
//! These benchmarks measure isolated operations in the model checking hot path:
//! - State fingerprinting (value_fingerprint, ArrayState::fingerprint)
//! - Value hashing for different value types
//! - Set operations (union, intersection, contains)
//! - Function application (apply, except)
//!
//! Run with: cargo bench -p tla-check --bench hot_path

mod hot_path_collections;
mod hot_path_fingerprint;
mod hot_path_fixtures;
mod hot_path_sequences;

use criterion::{criterion_group, criterion_main};

use hot_path_collections::{
    bench_func_operations, bench_set_operations, bench_value_clone, bench_value_cmp,
};
use hot_path_fingerprint::{
    bench_array_state_fingerprint, bench_fnv_vs_xxh3, bench_value_fingerprint,
};
use hot_path_sequences::bench_seq_operations;

criterion_group!(
    benches,
    bench_value_fingerprint,
    bench_fnv_vs_xxh3,
    bench_array_state_fingerprint,
    bench_set_operations,
    bench_func_operations,
    bench_value_cmp,
    bench_value_clone,
    bench_seq_operations,
);
criterion_main!(benches);
