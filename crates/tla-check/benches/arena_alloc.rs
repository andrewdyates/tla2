// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Benchmark: arena bump allocation vs heap (Vec) allocation.
//!
//! Measures the per-state allocation cost of the two paths:
//! 1. **Arena path**: `WorkerArena::alloc_state()` — bump pointer, O(1), zero
//!    syscalls. Bulk-freed at BFS level boundaries via `reset()`.
//! 2. **Heap path**: `Vec::<i64>::with_capacity()` + `drop()` — malloc/free per
//!    state. This is the current allocator baseline (5.5% CPU from mi_malloc+
//!    mi_free in profiling).
//!
//! Run with: cargo bench -p tla-check --bench arena_alloc
//!
//! Part of #3990: JIT V2 Phase 7 — per-worker bump arenas, zero malloc.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::hint;
use std::mem::size_of;
use std::ptr::{self, NonNull};

// ---------------------------------------------------------------------------
// Minimal inline arena for the benchmark (avoids depending on crate internals)
// ---------------------------------------------------------------------------

/// Inline mmap-backed bump arena for benchmarking. Mirrors `WorkerArena` API
/// but is self-contained in the bench crate.
struct BenchArena {
    base: NonNull<u8>,
    byte_len: usize,
    cursor: usize,
}

impl BenchArena {
    fn new(capacity_i64s: usize) -> Self {
        let byte_len = capacity_i64s * size_of::<i64>();
        assert!(byte_len > 0);

        // SAFETY: Anonymous private mapping, no file descriptor.
        let ptr = unsafe {
            libc::mmap(
                ptr::null_mut(),
                byte_len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_ANON | libc::MAP_PRIVATE,
                -1,
                0,
            )
        };
        assert_ne!(ptr, libc::MAP_FAILED, "mmap failed");

        // SAFETY: mmap succeeded, ptr is non-null.
        let base = unsafe { NonNull::new_unchecked(ptr.cast::<u8>()) };
        Self {
            base,
            byte_len,
            cursor: 0,
        }
    }

    #[inline(always)]
    fn alloc(&mut self, state_len: usize) -> *mut i64 {
        let alloc_bytes = state_len * size_of::<i64>();
        debug_assert!(self.cursor + alloc_bytes <= self.byte_len);
        // SAFETY: cursor is within bounds (asserted in debug), base is valid mmap.
        let ptr = unsafe { self.base.as_ptr().add(self.cursor).cast::<i64>() };
        self.cursor += alloc_bytes;
        ptr
    }

    #[inline(always)]
    fn reset(&mut self) {
        self.cursor = 0;
    }
}

impl Drop for BenchArena {
    fn drop(&mut self) {
        // SAFETY: base and byte_len from a successful mmap call.
        unsafe {
            libc::munmap(self.base.as_ptr().cast(), self.byte_len);
        }
    }
}

// ---------------------------------------------------------------------------
// Benchmarks
// ---------------------------------------------------------------------------

/// Benchmark arena bump allocation: allocate `count` states, resetting every
/// `reset_every` allocations to simulate BFS level boundaries.
fn bench_arena_alloc(c: &mut Criterion) {
    let mut group = c.benchmark_group("arena_alloc");

    // Test multiple state sizes (typical TLA+ specs: 5-50 variables).
    for state_len in [8, 16, 32, 64] {
        let count: usize = 100_000;
        let reset_every: usize = 10_000;
        let capacity = reset_every * state_len;

        group.throughput(Throughput::Elements(count as u64));
        group.bench_with_input(
            BenchmarkId::new("arena", state_len),
            &state_len,
            |b, &sl| {
                let mut arena = BenchArena::new(capacity);
                b.iter(|| {
                    for i in 0..count {
                        if i > 0 && i % reset_every == 0 {
                            arena.reset();
                        }
                        let ptr = arena.alloc(sl);
                        // SAFETY: ptr points into live mmap, sl elements available.
                        unsafe {
                            *ptr = i as i64;
                        }
                        black_box(ptr);
                    }
                    arena.reset();
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("heap_vec", state_len),
            &state_len,
            |b, &sl| {
                b.iter(|| {
                    for i in 0..count {
                        let mut v = vec![0i64; sl];
                        v[0] = i as i64;
                        hint::black_box(&v);
                        drop(v);
                    }
                });
            },
        );
    }

    group.finish();
}

/// Benchmark scratch buffer reuse pattern: write + read from the same mmap
/// buffer vs creating a new Vec each time.
fn bench_scratch_reuse(c: &mut Criterion) {
    let mut group = c.benchmark_group("scratch_reuse");

    for state_len in [8, 32] {
        let count: usize = 100_000;
        group.throughput(Throughput::Elements(count as u64));

        group.bench_with_input(
            BenchmarkId::new("mmap_scratch", state_len),
            &state_len,
            |b, &sl| {
                // Pre-allocate the scratch buffer once.
                let byte_len = sl * size_of::<i64>();
                // SAFETY: Anonymous private mapping.
                let ptr = unsafe {
                    libc::mmap(
                        ptr::null_mut(),
                        byte_len,
                        libc::PROT_READ | libc::PROT_WRITE,
                        libc::MAP_ANON | libc::MAP_PRIVATE,
                        -1,
                        0,
                    )
                };
                assert_ne!(ptr, libc::MAP_FAILED);
                let buf = ptr.cast::<i64>();

                b.iter(|| {
                    for i in 0..count {
                        // SAFETY: buf points to sl i64s in live mmap.
                        unsafe {
                            *buf = i as i64;
                            ptr::write_bytes(buf.add(1), 0, sl - 1);
                        }
                        black_box(buf);
                    }
                });

                // SAFETY: Matching munmap for the mmap above.
                unsafe {
                    libc::munmap(ptr, byte_len);
                }
            },
        );

        group.bench_with_input(
            BenchmarkId::new("vec_each_time", state_len),
            &state_len,
            |b, &sl| {
                b.iter(|| {
                    for i in 0..count {
                        let mut v = vec![0i64; sl];
                        v[0] = i as i64;
                        hint::black_box(&v);
                        drop(v);
                    }
                });
            },
        );
    }

    group.finish();
}

/// Benchmark FlatQueue push/pop throughput (SPSC pattern) vs VecDeque.
fn bench_queue_throughput(c: &mut Criterion) {
    use std::collections::VecDeque;

    let mut group = c.benchmark_group("queue_throughput");

    for state_len in [8, 32] {
        let count: usize = 50_000;
        let capacity: usize = 65_536; // power of 2

        group.throughput(Throughput::Elements(count as u64));

        group.bench_with_input(
            BenchmarkId::new("flat_queue_spsc", state_len),
            &state_len,
            |b, &sl| {
                // Inline flat queue for benchmark isolation.
                let byte_len = capacity * sl * size_of::<i64>();
                // SAFETY: Anonymous private mapping.
                let ptr = unsafe {
                    libc::mmap(
                        ptr::null_mut(),
                        byte_len,
                        libc::PROT_READ | libc::PROT_WRITE,
                        libc::MAP_ANON | libc::MAP_PRIVATE,
                        -1,
                        0,
                    )
                };
                assert_ne!(ptr, libc::MAP_FAILED);
                let base = ptr.cast::<i64>();
                let mask = capacity - 1;
                let stride = sl;

                b.iter(|| {
                    let mut head: usize = 0;
                    let mut tail: usize = 0;
                    let state = vec![42i64; sl];
                    let mut out = vec![0i64; sl];

                    for _ in 0..count {
                        // Push.
                        let slot = tail & mask;
                        // SAFETY: slot < capacity, base points to capacity*sl i64s.
                        unsafe {
                            ptr::copy_nonoverlapping(
                                state.as_ptr(),
                                base.add(slot * stride),
                                sl,
                            );
                        }
                        tail += 1;
                    }

                    for _ in 0..count {
                        // Pop.
                        let slot = head & mask;
                        // SAFETY: slot < capacity, data was written above.
                        unsafe {
                            ptr::copy_nonoverlapping(
                                base.add(slot * stride),
                                out.as_mut_ptr(),
                                sl,
                            );
                        }
                        head += 1;
                        black_box(&out);
                    }
                });

                // SAFETY: Matching munmap.
                unsafe {
                    libc::munmap(ptr, byte_len);
                }
            },
        );

        group.bench_with_input(
            BenchmarkId::new("vecdeque", state_len),
            &state_len,
            |b, &sl| {
                b.iter(|| {
                    let mut queue: VecDeque<Vec<i64>> = VecDeque::with_capacity(count);
                    for _ in 0..count {
                        queue.push_back(vec![42i64; sl]);
                    }
                    for _ in 0..count {
                        let v = queue.pop_front().expect("non-empty");
                        black_box(&v);
                    }
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_arena_alloc, bench_scratch_reuse, bench_queue_throughput);
criterion_main!(benches);
