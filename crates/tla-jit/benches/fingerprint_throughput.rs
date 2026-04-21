// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::collections::HashSet;
use std::hash::{Hash, Hasher, SipHasher};
use std::hint::black_box;
use tla_jit::bfs_step::jit_xxh3_fingerprint_64;
use tla_jit::{InsertResult, ResizableAtomicFpSet};
use xxhash_rust::xxh3::xxh3_64;

const NUM_STATES: usize = 10_000;
const FINGERPRINT_STATE_LENS: [usize; 6] = [4, 8, 16, 32, 64, 128];
const DEDUP_STATE_LENS: [usize; 3] = [8, 16, 32];

fn generate_states(num_states: usize, state_len: usize) -> Vec<i64> {
    let mut states = Vec::with_capacity(num_states * state_len);
    for state_idx in 0..num_states {
        let state_seed = (state_idx as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
            ^ (state_len as u64).wrapping_mul(0x94D0_49BB_1331_11EB);
        for slot_idx in 0..state_len {
            let lane_seed = (slot_idx as u64 + 1).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            let mixed = state_seed
                .wrapping_add(lane_seed)
                .rotate_left(((slot_idx * 11 + state_idx) & 63) as u32)
                ^ ((state_idx as u64) << 32)
                ^ slot_idx as u64;
            states.push(mixed as i64);
        }
    }
    states
}

fn state_bytes(state: &[i64]) -> &[u8] {
    let byte_len = std::mem::size_of_val(state);
    // SAFETY: `i64` slices are contiguous, and `u8` has alignment 1.
    unsafe { std::slice::from_raw_parts(state.as_ptr().cast::<u8>(), byte_len) }
}

fn siphash_fingerprint(state: &[i64]) -> u64 {
    let mut hasher = SipHasher::new();
    for value in state {
        value.hash(&mut hasher);
    }
    hasher.finish()
}

fn xxh3_fingerprint(state: &[i64]) -> u64 {
    xxh3_64(state_bytes(state))
}

fn bench_fingerprint_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("fingerprint_throughput");

    for &state_len in &FINGERPRINT_STATE_LENS {
        let states = generate_states(NUM_STATES, state_len);
        let total_bytes = (NUM_STATES * state_len * std::mem::size_of::<i64>()) as u64;
        group.throughput(Throughput::Bytes(total_bytes));

        group.bench_with_input(
            BenchmarkId::new("SipHash", state_len),
            &state_len,
            |b, &_len| {
                b.iter(|| {
                    let mut acc = 0u64;
                    for state in states.chunks_exact(state_len) {
                        acc = acc.wrapping_add(siphash_fingerprint(state));
                    }
                    black_box(acc)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("xxh3_rust", state_len),
            &state_len,
            |b, &_len| {
                b.iter(|| {
                    let mut acc = 0u64;
                    for state in states.chunks_exact(state_len) {
                        acc = acc.wrapping_add(xxh3_fingerprint(state));
                    }
                    black_box(acc)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("xxh3_jit", state_len),
            &state_len,
            |b, &_len| {
                b.iter(|| {
                    let mut acc = 0u64;
                    for state in states.chunks_exact(state_len) {
                        acc = acc.wrapping_add(jit_xxh3_fingerprint_64(
                            state.as_ptr(),
                            state.len() as u32,
                        ));
                    }
                    black_box(acc)
                })
            },
        );
    }

    group.finish();
}

fn bench_fingerprint_bfs_dedup(c: &mut Criterion) {
    let mut group = c.benchmark_group("fingerprint_bfs_dedup");

    for &state_len in &DEDUP_STATE_LENS {
        let states = generate_states(NUM_STATES, state_len);
        let total_bytes = (NUM_STATES * state_len * std::mem::size_of::<i64>()) as u64;
        group.throughput(Throughput::Bytes(total_bytes));

        group.bench_with_input(
            BenchmarkId::new("xxh3_atomic_fp_set", state_len),
            &state_len,
            |b, &_len| {
                b.iter(|| {
                    let set = ResizableAtomicFpSet::new(NUM_STATES);
                    let mut inserted = 0usize;

                    for state in states.chunks_exact(state_len) {
                        let fp = xxh3_fingerprint(state);
                        match set.insert_if_absent(fp) {
                            InsertResult::Inserted => inserted += 1,
                            InsertResult::AlreadyPresent => {}
                            InsertResult::TableFull => {
                                panic!("ResizableAtomicFpSet returned TableFull")
                            }
                        }
                    }

                    black_box(inserted);
                    assert_eq!(inserted, NUM_STATES);
                    assert_eq!(set.len(), NUM_STATES);
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("SipHash_HashSet", state_len),
            &state_len,
            |b, &_len| {
                b.iter(|| {
                    let mut set = HashSet::with_capacity(NUM_STATES);

                    for state in states.chunks_exact(state_len) {
                        let fp = siphash_fingerprint(state);
                        assert!(set.insert(fp), "unexpected duplicate SipHash fingerprint");
                    }

                    black_box(set.len());
                    assert_eq!(set.len(), NUM_STATES);
                })
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_fingerprint_throughput,
    bench_fingerprint_bfs_dedup
);
criterion_main!(benches);
