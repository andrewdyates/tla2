// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Criterion benchmarks comparing flat fingerprinting backends.
//!
//! Compares XOR-accumulator vs xxh3-128 for both full fingerprinting and
//! incremental diff fingerprinting at various buffer sizes.
//!
//! Part of #3987: JIT V2 Phase 4 compiled fingerprinting.
//!
//! Run:
//!   cargo bench -p tla-check --bench flat_fingerprint_bench

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use tla_check::state::flat_fingerprint::{
    FlatFingerprintStrategy, FlatFingerprinter, Xxh3FlatFingerprinter,
};

/// Buffer sizes representative of TLA+ state layouts:
///   5  = tiny (2-3 scalar variables)
///  10  = small (e.g., Dijkstra mutex with 4 procs)
///  15  = medium (EWD998 with arrays)
///  20  = typical (Raft/Paxos state)
///  50  = large (multi-array specs)
/// 100  = xlarge (CarTalkPuzzle-class)
const SIZES: &[usize] = &[5, 10, 15, 20, 50, 100];

fn make_state(n: usize) -> Vec<i64> {
    (0..n as i64).collect()
}

fn bench_full_fingerprint(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_fingerprint");
    for &size in SIZES {
        let state = make_state(size);

        group.bench_with_input(
            BenchmarkId::new("xor_accumulator", size),
            &size,
            |b, &sz| {
                let fp = FlatFingerprinter::new(sz);
                b.iter(|| fp.fingerprint(black_box(&state)));
            },
        );

        group.bench_with_input(BenchmarkId::new("xxh3_128", size), &size, |b, &sz| {
            let fp = Xxh3FlatFingerprinter::new(sz);
            b.iter(|| fp.fingerprint(black_box(&state)));
        });

        group.bench_with_input(
            BenchmarkId::new("strategy_xor", size),
            &size,
            |b, &sz| {
                let strategy = FlatFingerprintStrategy::new_xor(sz);
                b.iter(|| strategy.fingerprint(black_box(&state)));
            },
        );

        group.bench_with_input(
            BenchmarkId::new("strategy_xxh3", size),
            &size,
            |b, &sz| {
                let strategy = FlatFingerprintStrategy::new_xxh3(sz);
                b.iter(|| strategy.fingerprint(black_box(&state)));
            },
        );
    }
    group.finish();
}

fn bench_diff_fingerprint(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff_fingerprint");
    for &size in SIZES {
        let state = make_state(size);

        // 1 change (common: single variable mutation)
        let changes_1: Vec<(usize, i64, i64)> = vec![(0, 0, 999)];

        // 3 changes (typical: action modifying a few variables)
        let changes_3: Vec<(usize, i64, i64)> = if size >= 3 {
            vec![(0, 0, 100), (size / 2, size as i64 / 2, 200), (size - 1, size as i64 - 1, 300)]
        } else {
            vec![(0, 0, 100)]
        };

        // XOR-accumulator: true O(k) incremental
        let xor_fp = FlatFingerprinter::new(size);
        let xor_base = xor_fp.fingerprint(&state);

        group.bench_with_input(
            BenchmarkId::new("xor_1change", size),
            &size,
            |b, _| {
                b.iter(|| xor_fp.diff(black_box(&state), xor_base, black_box(&changes_1)));
            },
        );

        group.bench_with_input(
            BenchmarkId::new("xor_3changes", size),
            &size,
            |b, _| {
                b.iter(|| xor_fp.diff(black_box(&state), xor_base, black_box(&changes_3)));
            },
        );

        // xxh3-128: buffer-copy + rehash
        let xxh3_fp = Xxh3FlatFingerprinter::new(size);

        group.bench_with_input(
            BenchmarkId::new("xxh3_1change", size),
            &size,
            |b, _| {
                let mut scratch = Vec::new();
                b.iter(|| {
                    xxh3_fp.diff_with_buffer(black_box(&state), black_box(&changes_1), &mut scratch)
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("xxh3_3changes", size),
            &size,
            |b, _| {
                let mut scratch = Vec::new();
                b.iter(|| {
                    xxh3_fp.diff_with_buffer(black_box(&state), black_box(&changes_3), &mut scratch)
                });
            },
        );

        // Strategy dispatch overhead
        let strategy_xor = FlatFingerprintStrategy::new_xor(size);
        let strategy_xxh3 = FlatFingerprintStrategy::new_xxh3(size);
        let strategy_xor_base = strategy_xor.fingerprint(&state);
        let strategy_xxh3_base = strategy_xxh3.fingerprint(&state);

        group.bench_with_input(
            BenchmarkId::new("strategy_xor_3changes", size),
            &size,
            |b, _| {
                let mut scratch = Vec::new();
                b.iter(|| {
                    strategy_xor.diff(
                        black_box(&state),
                        strategy_xor_base,
                        black_box(&changes_3),
                        &mut scratch,
                    )
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("strategy_xxh3_3changes", size),
            &size,
            |b, _| {
                let mut scratch = Vec::new();
                b.iter(|| {
                    strategy_xxh3.diff(
                        black_box(&state),
                        strategy_xxh3_base,
                        black_box(&changes_3),
                        &mut scratch,
                    )
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, bench_full_fingerprint, bench_diff_fingerprint);
criterion_main!(benches);
