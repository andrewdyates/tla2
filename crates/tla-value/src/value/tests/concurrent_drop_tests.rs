// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Concurrent drop safety tests for iterative Value::Drop.
//! Part of #4134: Wave 3 performance optimization test coverage.
//!
//! The iterative drop implementation uses `UnsafeCell<Vec<Value>>` with a
//! thread-local work stack. These tests verify that concurrent drops across
//! threads don't corrupt the per-thread TLS drop stacks.

use crate::Value;
use std::sync::Arc;

/// Concurrent drops across threads with shared Arc<Set> values.
/// Verifies thread-local DROP_STACK isolation under concurrent access —
/// each thread's UnsafeCell<Vec<Value>> must not interfere with other
/// threads' iterative drop loops.
#[test]
fn test_concurrent_drops_shared_arc_values() {
    use std::thread;

    // Create a shared compound set value with multiple Arc clones
    let inner = Value::set([
        Value::int(1),
        Value::int(2),
        Value::set([Value::int(3), Value::int(4)]),
    ]);
    let shared_set = Value::set([
        inner.clone(),
        Value::set([Value::int(5), Value::int(6)]),
        Value::seq([Value::int(7), Value::int(8)]),
    ]);

    let num_threads = 4;
    let mut handles = Vec::new();

    for _ in 0..num_threads {
        let clone = shared_set.clone();
        handles.push(thread::spawn(move || {
            // Create additional nested compound values on this thread
            let local = Value::set([
                clone,
                Value::set([Value::int(100), Value::int(200)]),
                Value::set((0..50).map(Value::int).collect::<Vec<_>>()),
            ]);
            // Drop triggers iterative drop on each thread's own TLS stack
            drop(local);
        }));
    }

    for h in handles {
        h.join()
            .expect("thread should not panic during concurrent drop");
    }

    // Drop the original — should work fine since all Arc clones in
    // threads have already been dropped or decremented.
    drop(shared_set);
    drop(inner);
}

/// Interleaved compound value construction and drop across threads.
/// Tests that the thread-local IN_ITERATIVE_DROP flag is per-thread
/// and doesn't leak between threads.
#[test]
fn test_interleaved_drops_across_threads() {
    use std::sync::Barrier;
    use std::thread;

    let barrier = Arc::new(Barrier::new(2));

    let b1 = Arc::clone(&barrier);
    let h1 = thread::spawn(move || {
        let deep = {
            let mut v = Value::int(1);
            for _ in 0..100 {
                v = Value::set([v]);
            }
            v
        };
        b1.wait(); // synchronize with other thread
        drop(deep);
    });

    let b2 = Arc::clone(&barrier);
    let h2 = thread::spawn(move || {
        let wide = Value::set(
            (0..200)
                .map(|i| Value::set([Value::int(i)]))
                .collect::<Vec<_>>(),
        );
        b2.wait(); // synchronize with other thread
        drop(wide);
    });

    h1.join().expect("deep drop thread should not panic");
    h2.join().expect("wide drop thread should not panic");
}

/// Many threads dropping shared compound values simultaneously.
/// Stress test: 8 threads each clone a deeply nested structure and
/// drop concurrently, verifying no panics from TLS contention.
#[test]
fn test_many_threads_drop_shared_compound() {
    use std::sync::Barrier;
    use std::thread;

    let num_threads = 8;
    let barrier = Arc::new(Barrier::new(num_threads));

    // Build a moderately nested value
    let nested = Value::set([
        Value::set([Value::int(1), Value::seq([Value::int(2), Value::int(3)])]),
        Value::set([Value::int(4), Value::set([Value::int(5)])]),
        Value::seq([Value::int(6), Value::int(7), Value::int(8)]),
    ]);

    let mut handles = Vec::new();
    for _ in 0..num_threads {
        let clone = nested.clone();
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            b.wait(); // all threads start dropping at the same instant
            drop(clone);
        }));
    }

    for h in handles {
        h.join().expect("thread should not panic");
    }

    drop(nested);
}
