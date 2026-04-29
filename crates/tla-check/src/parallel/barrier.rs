// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Worker suspension barrier for periodic work (checkpoint, liveness).
//!
//! Implements TLC's `StateQueue.suspendAll()`/`resumeAll()` pattern adapted
//! for a lock-free work-stealing architecture. The main thread requests
//! suspension; workers block on the next `try_dequeue()` call; when all
//! workers are paused, the main thread is notified and can perform periodic
//! work (checkpointing, liveness checking) with no concurrent mutations.
//!
//! Part of #2749: Phase 1 prerequisite for parallel checkpoint/resume.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex};

/// Barrier that allows the main thread to suspend all BFS workers.
///
/// Workers call [`worker_check()`](WorkBarrier::worker_check) before each
/// dequeue attempt. If suspension is requested, they block until
/// [`resume_all()`](WorkBarrier::resume_all) is called.
///
/// Matches TLC's `StateQueue` suspension protocol: workers finish their
/// current state before suspending — no mid-computation interruption.
pub(crate) struct WorkBarrier {
    /// When true, workers should pause on next dequeue check.
    pause_requested: AtomicBool,
    /// Count of workers currently paused at the barrier.
    paused_count: AtomicUsize,
    /// Total number of workers that must pause before `suspend_all` returns.
    num_workers: usize,
    /// Mutex protecting the resume condition.
    mu: Mutex<()>,
    /// Signaled when `paused_count == num_workers` (all workers paused).
    all_paused: Condvar,
    /// Signaled when `pause_requested` is cleared (workers may resume).
    resume: Condvar,
}

impl WorkBarrier {
    /// Create a new barrier for `num_workers` worker threads.
    pub(crate) fn new(num_workers: usize) -> Self {
        Self {
            pause_requested: AtomicBool::new(false),
            paused_count: AtomicUsize::new(0),
            num_workers,
            mu: Mutex::new(()),
            all_paused: Condvar::new(),
            resume: Condvar::new(),
        }
    }

    /// Main thread: request all workers to pause, block until they do.
    ///
    /// After this returns, all workers are blocked at the barrier and no
    /// concurrent mutations to the seen set, parent map, or work queues
    /// are occurring. The caller may safely snapshot state for checkpointing
    /// or run liveness checks.
    ///
    /// # Panics
    ///
    /// Panics if the internal mutex is poisoned (indicates a prior panic
    /// while holding the lock — an unrecoverable state for the checker).
    pub(crate) fn suspend_all(&self) {
        // Set the pause flag. Workers will see this on their next
        // `worker_check()` call via Relaxed load (fast path).
        self.pause_requested.store(true, Ordering::SeqCst);

        let mut guard = self.mu.lock().expect("WorkBarrier mutex poisoned");
        while self.paused_count.load(Ordering::SeqCst) < self.num_workers {
            guard = self
                .all_paused
                .wait(guard)
                .expect("WorkBarrier mutex poisoned");
        }
        // All workers are now paused. Caller may perform periodic work.
    }

    /// Main thread: resume all paused workers.
    ///
    /// Must be called after [`suspend_all()`](WorkBarrier::suspend_all) to
    /// allow workers to continue BFS exploration. Workers will wake and
    /// resume dequeuing work items.
    pub(crate) fn resume_all(&self) {
        let _guard = self.mu.lock().expect("WorkBarrier mutex poisoned");
        // Reset paused count BEFORE clearing pause flag to avoid a race
        // where a worker sees pause_requested=false but paused_count is
        // still non-zero from the previous suspension cycle.
        self.paused_count.store(0, Ordering::SeqCst);
        self.pause_requested.store(false, Ordering::SeqCst);
        self.resume.notify_all();
    }

    /// Worker thread: check if suspension is requested, block if so.
    ///
    /// Called by each worker before attempting to dequeue a work item.
    /// Fast path (no suspension): single `Relaxed` atomic load.
    /// Slow path (suspension requested): increment paused count, notify
    /// main thread if last to pause, block until resumed.
    ///
    /// Workers should flush any batched counters (e.g., `local_work_delta`)
    /// before calling this method to ensure the main thread sees accurate
    /// global state during the suspension window.
    #[inline]
    pub(crate) fn worker_check(&self) {
        // Fast path: no suspension requested. Cost: one Relaxed atomic load.
        if !self.pause_requested.load(Ordering::Relaxed) {
            return;
        }

        // Slow path: suspension requested. Acquire the lock for condvar wait.
        let mut guard = self.mu.lock().expect("WorkBarrier mutex poisoned");

        // Re-check under the lock: the main thread might have called
        // resume_all() between our Relaxed check and acquiring the lock.
        if !self.pause_requested.load(Ordering::SeqCst) {
            return;
        }

        // Increment paused count. If we're the last worker, notify the
        // main thread that all workers are now paused.
        let prev = self.paused_count.fetch_add(1, Ordering::SeqCst);
        if prev + 1 >= self.num_workers {
            self.all_paused.notify_one();
        }

        // Block until resume_all() clears the pause flag.
        while self.pause_requested.load(Ordering::SeqCst) {
            guard = self.resume.wait(guard).expect("WorkBarrier mutex poisoned");
        }
    }

    /// Returns true if the main thread has requested worker suspension.
    ///
    /// This is a fast `Relaxed` atomic check suitable for polling in the
    /// worker hot path. Workers should use this to decide whether to flush
    /// batched counters before calling [`worker_check()`](WorkBarrier::worker_check).
    #[inline]
    pub(crate) fn is_pause_requested(&self) -> bool {
        self.pause_requested.load(Ordering::Relaxed)
    }

    /// Returns true if all workers are currently suspended.
    ///
    /// Useful for the main thread to check barrier state without blocking.
    // Part of #2749: test-only until checkpoint UI needs suspension status.
    #[inline]
    #[cfg(test)]
    pub(crate) fn is_suspended(&self) -> bool {
        self.pause_requested.load(Ordering::SeqCst)
            && self.paused_count.load(Ordering::SeqCst) >= self.num_workers
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_barrier_suspend_resume_basic() {
        let num_workers = 4;
        let barrier = Arc::new(WorkBarrier::new(num_workers));
        let counter = Arc::new(AtomicUsize::new(0));
        let running = Arc::new(AtomicBool::new(true));

        // Spawn worker threads that loop checking the barrier
        let mut handles = Vec::new();
        for _ in 0..num_workers {
            let barrier = Arc::clone(&barrier);
            let counter = Arc::clone(&counter);
            let running = Arc::clone(&running);
            handles.push(thread::spawn(move || {
                while running.load(Ordering::Relaxed) {
                    barrier.worker_check();
                    // Simulate doing work
                    counter.fetch_add(1, Ordering::Relaxed);
                    thread::yield_now();
                }
            }));
        }

        // Let workers run briefly
        thread::sleep(Duration::from_millis(10));

        // Suspend all workers
        barrier.suspend_all();

        // While suspended, counter should not change
        let snapshot = counter.load(Ordering::Relaxed);
        thread::sleep(Duration::from_millis(10));
        let after = counter.load(Ordering::Relaxed);
        assert_eq!(snapshot, after, "counter changed while workers suspended");
        assert!(barrier.is_suspended());

        // Resume workers
        barrier.resume_all();

        // Workers should make progress again
        thread::sleep(Duration::from_millis(10));
        let final_count = counter.load(Ordering::Relaxed);
        assert!(final_count > after, "workers did not resume");

        // Shut down workers
        running.store(false, Ordering::Relaxed);
        for h in handles {
            h.join().unwrap();
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_barrier_multiple_suspend_resume_cycles() {
        let num_workers = 3;
        let barrier = Arc::new(WorkBarrier::new(num_workers));
        let running = Arc::new(AtomicBool::new(true));
        let cycle_count = Arc::new(AtomicUsize::new(0));

        let mut handles = Vec::new();
        for _ in 0..num_workers {
            let barrier = Arc::clone(&barrier);
            let running = Arc::clone(&running);
            let cycle_count = Arc::clone(&cycle_count);
            handles.push(thread::spawn(move || {
                while running.load(Ordering::Relaxed) {
                    barrier.worker_check();
                    cycle_count.fetch_add(1, Ordering::Relaxed);
                    thread::yield_now();
                }
            }));
        }

        // Run multiple suspend/resume cycles
        for _ in 0..5 {
            thread::sleep(Duration::from_millis(5));
            barrier.suspend_all();

            // Verify suspension holds
            let snap = cycle_count.load(Ordering::Relaxed);
            thread::sleep(Duration::from_millis(5));
            assert_eq!(
                snap,
                cycle_count.load(Ordering::Relaxed),
                "work done while suspended"
            );

            barrier.resume_all();
        }

        running.store(false, Ordering::Relaxed);
        for h in handles {
            h.join().unwrap();
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_barrier_single_worker() {
        let barrier = Arc::new(WorkBarrier::new(1));
        let paused = Arc::new(AtomicBool::new(false));
        let running = Arc::new(AtomicBool::new(true));

        let b = Arc::clone(&barrier);
        let p = Arc::clone(&paused);
        let r = Arc::clone(&running);
        let handle = thread::spawn(move || {
            while r.load(Ordering::Relaxed) {
                b.worker_check();
                p.store(false, Ordering::Relaxed);
                thread::yield_now();
            }
        });

        thread::sleep(Duration::from_millis(5));
        barrier.suspend_all();
        assert!(barrier.is_suspended());
        barrier.resume_all();

        running.store(false, Ordering::Relaxed);
        handle.join().unwrap();
    }
}
