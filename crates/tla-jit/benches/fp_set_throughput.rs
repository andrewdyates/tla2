// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Benchmark: AtomicFpSet vs Mutex<HashSet<u64>> throughput under contention.
//!
//! Run with:
//! ```sh
//! cargo bench -p tla-jit --bench fp_set_throughput
//! ```

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::collections::HashSet;
use std::sync::{Arc, Barrier, Mutex};
use std::thread;
use tla_jit::{InsertResult, ResizableAtomicFpSet};

/// Deterministic fingerprint from (thread_idx, iteration).
fn thread_fp(thread_idx: usize, i: u64) -> u64 {
    ((thread_idx as u64) * 10_000_000 + i + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

fn bench_atomic_fp_set(c: &mut Criterion) {
    let mut group = c.benchmark_group("fp_set_insert");

    for &num_threads in &[1, 2, 4, 8] {
        let per_thread = 100_000u64;
        let total = num_threads * per_thread as usize;
        group.throughput(Throughput::Elements(total as u64));

        group.bench_with_input(
            BenchmarkId::new("AtomicFpSet", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let set = Arc::new(ResizableAtomicFpSet::new(total));
                    let barrier = Arc::new(Barrier::new(num_threads));

                    let handles: Vec<_> = (0..num_threads)
                        .map(|t| {
                            let set = Arc::clone(&set);
                            let barrier = Arc::clone(&barrier);
                            thread::spawn(move || {
                                barrier.wait();
                                for i in 0..per_thread {
                                    let fp = thread_fp(t, i);
                                    let _ = set.insert_if_absent(fp);
                                }
                            })
                        })
                        .collect();

                    for h in handles {
                        h.join().unwrap();
                    }

                    assert_eq!(set.len(), total);
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Mutex_HashSet", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let set = Arc::new(Mutex::new(HashSet::with_capacity(total)));
                    let barrier = Arc::new(Barrier::new(num_threads));

                    let handles: Vec<_> = (0..num_threads)
                        .map(|t| {
                            let set = Arc::clone(&set);
                            let barrier = Arc::clone(&barrier);
                            thread::spawn(move || {
                                barrier.wait();
                                for i in 0..per_thread {
                                    let fp = thread_fp(t, i);
                                    set.lock().unwrap().insert(fp);
                                }
                            })
                        })
                        .collect();

                    for h in handles {
                        h.join().unwrap();
                    }

                    assert_eq!(set.lock().unwrap().len(), total);
                })
            },
        );
    }

    group.finish();
}

fn bench_mixed_insert_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("fp_set_mixed");

    for &num_threads in &[1, 4, 8] {
        let per_thread = 50_000u64;
        let total = num_threads * per_thread as usize;
        group.throughput(Throughput::Elements(total as u64 * 2)); // insert + lookup

        group.bench_with_input(
            BenchmarkId::new("AtomicFpSet", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let set = Arc::new(ResizableAtomicFpSet::new(total));
                    let barrier = Arc::new(Barrier::new(num_threads));

                    let handles: Vec<_> = (0..num_threads)
                        .map(|t| {
                            let set = Arc::clone(&set);
                            let barrier = Arc::clone(&barrier);
                            thread::spawn(move || {
                                barrier.wait();
                                let mut new_count = 0usize;
                                for i in 0..per_thread {
                                    let fp = thread_fp(t, i);
                                    if set.insert_if_absent(fp) == InsertResult::Inserted {
                                        new_count += 1;
                                    }
                                    // 50% of operations are lookups of existing keys.
                                    if i > 0 {
                                        let lookup_fp = thread_fp(t, i / 2);
                                        let _ = set.contains(lookup_fp);
                                    }
                                }
                                new_count
                            })
                        })
                        .collect();

                    let total_new: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();
                    assert_eq!(total_new, total);
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Mutex_HashSet", num_threads),
            &num_threads,
            |b, &num_threads| {
                b.iter(|| {
                    let set = Arc::new(Mutex::new(HashSet::with_capacity(total)));
                    let barrier = Arc::new(Barrier::new(num_threads));

                    let handles: Vec<_> = (0..num_threads)
                        .map(|t| {
                            let set = Arc::clone(&set);
                            let barrier = Arc::clone(&barrier);
                            thread::spawn(move || {
                                barrier.wait();
                                let mut new_count = 0usize;
                                for i in 0..per_thread {
                                    let fp = thread_fp(t, i);
                                    if set.lock().unwrap().insert(fp) {
                                        new_count += 1;
                                    }
                                    if i > 0 {
                                        let lookup_fp = thread_fp(t, i / 2);
                                        let _ = set.lock().unwrap().contains(&lookup_fp);
                                    }
                                }
                                new_count
                            })
                        })
                        .collect();

                    let total_new: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();
                    assert_eq!(total_new, total);
                })
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_atomic_fp_set, bench_mixed_insert_lookup);
criterion_main!(benches);
