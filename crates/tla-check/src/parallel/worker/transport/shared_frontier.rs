// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared frontier with queue-owned wait/notify termination (Part of #3271, #3266).
//!
//! Extracted from `shared_queue.rs` for file-size compliance.
//!
//! Matches TLC's `StateQueue` control plane: `push_batch`/`push_single` wake
//! sleeping workers via condvar, `dequeue_batch_blocking` blocks when the queue
//! is empty and detects completion when all workers are waiting. Bounded
//! multi-worker runs use a depth-layered mode so level `d + 1` work stays
//! hidden until level `d` is fully drained.
//!
//! TLC reference: `StateQueue.java` — `sEnqueue` (`:66-72`), `sDequeue`/`isAvail`
//! (`:115-203`), `finishAll` (`:208-226`).

use super::shared_queue::SHARED_QUEUE_BATCH_SIZE;
use parking_lot::{Condvar, Mutex};
use smallvec::SmallVec;
use std::collections::VecDeque;
use std::sync::atomic::AtomicBool;
use std::time::Duration;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FrontierMode {
    Fifo,
    DepthLayered,
}

/// Outcome of a blocking dequeue attempt on the shared frontier.
///
/// Part of #3271: replaces the external `work_remaining` / `active_workers`
/// spin loop with TLC-style queue-owned wait/notify termination.
#[derive(Debug, PartialEq, Eq)]
pub(in crate::parallel) enum DequeueOutcome {
    /// Got items to process.
    Refilled,
    /// Completion detected (all workers waiting + queue empty) or finish signaled.
    Done,
    /// Timed out waiting — caller should check stop_flag/barrier and retry.
    TimedOut,
}

/// Internal state of the shared frontier, protected by the mutex.
struct FrontierState<T> {
    current: VecDeque<(T, usize)>,
    next: VecDeque<(T, usize)>,
    mode: FrontierMode,
    current_depth: usize,
    active_workers_at_level: usize,
    /// Number of workers currently blocked in `dequeue_batch_blocking`.
    num_waiting: usize,
    /// Total number of workers (for completion detection).
    num_workers: usize,
    /// Set when completion is detected or `finish()` is called.
    finished: bool,
}

/// Shared frontier with queue-owned wait/notify termination (Part of #3271, #3266).
///
/// All workers push admitted successors here and pop work from here.
/// Worker-local staging buffers amortize lock acquisitions to keep the
/// per-state lock overhead similar to TLC's buffered `StateQueue`.
///
/// FIFO mode detects completion when all workers are waiting with an empty
/// current queue. Depth-layered mode additionally tracks active workers in the
/// current BFS level and only promotes `next` after the final active worker
/// releases its local batch.
pub(in crate::parallel) struct SharedFrontier<T> {
    state: Mutex<FrontierState<T>>,
    condvar: Condvar,
}

/// Timeout for condvar wait in `dequeue_batch_blocking`. Workers wake periodically
/// to check `stop_flag` and `barrier.is_pause_requested()` even when no new work
/// arrives. 10ms is much cheaper than the old spin/backoff loop (10-100µs yields)
/// while maintaining responsiveness for infrequent stop/barrier events.
const DEQUEUE_WAIT_TIMEOUT: Duration = Duration::from_millis(10);

impl<T> SharedFrontier<T> {
    pub(in crate::parallel) fn new(num_workers: usize) -> Self {
        Self::new_with_mode(num_workers, FrontierMode::Fifo)
    }

    pub(in crate::parallel) fn new_depth_layered(num_workers: usize) -> Self {
        Self::new_with_mode(num_workers, FrontierMode::DepthLayered)
    }

    fn new_with_mode(num_workers: usize, mode: FrontierMode) -> Self {
        Self {
            state: Mutex::new(FrontierState {
                current: VecDeque::new(),
                next: VecDeque::new(),
                mode,
                current_depth: 0,
                active_workers_at_level: 0,
                num_waiting: 0,
                num_workers,
                finished: false,
            }),
            condvar: Condvar::new(),
        }
    }

    /// Seed initial states into the shared frontier (used during seeding phase).
    pub(in crate::parallel) fn push_single(&self, item: T, depth: usize) {
        let mut state = self.state.lock();
        let should_notify = enqueue_item_locked(&mut state, item, depth);
        if should_notify && state.num_waiting > 0 {
            self.condvar.notify_all();
        }
    }

    /// Flush a local batch into the shared frontier in one lock acquisition.
    ///
    /// Wakes any workers blocked in `dequeue_batch_blocking` — matches TLC's
    /// `sEnqueue(states[])` which calls `notifyAll()` after bulk insertion.
    pub(in crate::parallel) fn push_batch(
        &self,
        batch: &mut SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]>,
    ) {
        if batch.is_empty() {
            return;
        }
        let mut state = self.state.lock();
        let mut should_notify = false;
        for item in batch.drain(..) {
            let (state_item, depth) = item;
            should_notify |= enqueue_item_locked(&mut state, state_item, depth);
        }
        if should_notify && state.num_waiting > 0 {
            self.condvar.notify_all();
        }
    }

    /// Release this worker's current-level lease after it drains a local batch.
    ///
    /// Depth-layered mode tracks active workers per BFS level so `next` can
    /// only be promoted after the final worker finishes the current layer.
    /// FIFO mode ignores this bookkeeping.
    pub(in crate::parallel) fn complete_level_batch(&self) {
        let mut state = self.state.lock();
        if state.mode != FrontierMode::DepthLayered || state.active_workers_at_level == 0 {
            return;
        }
        state.active_workers_at_level -= 1;
        if maybe_advance_depth_layer_locked(&mut state) {
            self.condvar.notify_all();
            return;
        }
        if state.current.is_empty() && state.active_workers_at_level == 0 && state.next.is_empty() {
            state.finished = true;
            self.condvar.notify_all();
        }
    }

    /// Block until items are available, completion is detected, or timeout.
    ///
    /// Matches TLC's `sDequeue()` + `isAvail()` contract:
    /// - If items available: pop up to `max_count` into `dest`, return `Refilled`.
    /// - If queue empty and all workers waiting: completion → return `Done`.
    /// - If `stop_flag` set or `finished`: return `Done`.
    /// - If timeout (10ms): return `TimedOut` so caller can check barrier/stop.
    ///
    /// TLC reference: `StateQueue.java:115-203`.
    pub(in crate::parallel) fn dequeue_batch_blocking(
        &self,
        dest: &mut SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]>,
        max_count: usize,
        stop_flag: &AtomicBool,
    ) -> DequeueOutcome {
        let mut state = self.state.lock();

        loop {
            // Check terminal conditions.
            if stop_flag.load(std::sync::atomic::Ordering::Relaxed) || state.finished {
                return DequeueOutcome::Done;
            }

            if maybe_advance_depth_layer_locked(&mut state) && state.num_waiting > 0 {
                self.condvar.notify_all();
            }

            // Try to pop items (fast path).
            let available = state.current.len().min(max_count);
            if available > 0 {
                for _ in 0..available {
                    if let Some(item) = state.current.pop_front() {
                        dest.push(item);
                    }
                }
                if state.mode == FrontierMode::DepthLayered {
                    state.active_workers_at_level += 1;
                }
                return DequeueOutcome::Refilled;
            }

            if state.mode == FrontierMode::DepthLayered
                && state.active_workers_at_level == 0
                && state.next.is_empty()
            {
                state.finished = true;
                self.condvar.notify_all();
                return DequeueOutcome::Done;
            }

            // Queue empty — enter waiting state. This mirrors TLC's `isAvail()`
            // where `numWaiting` is incremented before the `wait()` call.
            state.num_waiting += 1;
            if state.mode == FrontierMode::Fifo
                && state.num_waiting >= state.num_workers
                && state.current.is_empty()
            {
                // All workers waiting with empty queue -> completion.
                // Matches TLC: `numWaiting >= TLCGlobals.getNumWorkers() && isEmpty()`.
                state.num_waiting -= 1;
                state.finished = true;
                self.condvar.notify_all();
                return DequeueOutcome::Done;
            }

            // Wait for work or timeout. The timeout ensures responsiveness to
            // stop_flag and barrier events without requiring explicit wakeup plumbing.
            let timed_out = self
                .condvar
                .wait_for(&mut state, DEQUEUE_WAIT_TIMEOUT)
                .timed_out();
            state.num_waiting -= 1;

            // After waking, check terminal conditions again.
            if stop_flag.load(std::sync::atomic::Ordering::Relaxed) || state.finished {
                return DequeueOutcome::Done;
            }

            if timed_out {
                return DequeueOutcome::TimedOut;
            }
        }
    }

    /// Signal all workers to stop blocking and exit.
    ///
    /// Called from `SharedQueueTransport::Drop` to ensure sleeping workers
    /// are woken when any worker exits (error, violation, panic, or normal
    /// completion). Matches TLC's `finishAll()` (`StateQueue.java:208-226`).
    pub(in crate::parallel) fn finish(&self) {
        let mut state = self.state.lock();
        state.finished = true;
        self.condvar.notify_all();
    }
}

fn enqueue_item_locked<T>(state: &mut FrontierState<T>, item: T, depth: usize) -> bool {
    match state.mode {
        FrontierMode::Fifo => {
            state.current.push_back((item, depth));
            true
        }
        FrontierMode::DepthLayered => {
            if depth <= state.current_depth {
                state.current.push_back((item, depth));
                true
            } else {
                debug_assert!(
                    depth == state.current_depth + 1,
                    "depth-layered frontier only expects current or next-level items: current={}, pushed={depth}",
                    state.current_depth,
                );
                state.next.push_back((item, depth));
                false
            }
        }
    }
}

fn maybe_advance_depth_layer_locked<T>(state: &mut FrontierState<T>) -> bool {
    if state.mode != FrontierMode::DepthLayered
        || !state.current.is_empty()
        || state.active_workers_at_level > 0
        || state.next.is_empty()
    {
        return false;
    }
    std::mem::swap(&mut state.current, &mut state.next);
    state.current_depth += 1;
    true
}

#[cfg(test)]
mod tests {
    use super::{DequeueOutcome, SharedFrontier, SHARED_QUEUE_BATCH_SIZE};
    use smallvec::SmallVec;
    use std::sync::atomic::AtomicBool;
    use std::sync::{mpsc, Arc};
    use std::thread;
    use std::time::{Duration, Instant};

    fn wait_until_waiting(frontier: &SharedFrontier<usize>, expected_waiters: usize) {
        let deadline = Instant::now() + Duration::from_secs(1);
        while Instant::now() < deadline {
            {
                let state = frontier.state.lock();
                if state.num_waiting == expected_waiters {
                    return;
                }
            }
            thread::sleep(Duration::from_millis(1));
        }
        panic!("timed out waiting for {expected_waiters} blocked worker(s)");
    }

    #[cfg_attr(test, ntest::timeout(5000))]
    #[test]
    fn test_dequeue_blocks_on_empty_frontier_until_enqueue_wakes_waiter() {
        let frontier = Arc::new(SharedFrontier::<usize>::new(2));
        let stop_flag = Arc::new(AtomicBool::new(false));
        let (done_tx, done_rx) = mpsc::channel();

        let waiter_frontier = Arc::clone(&frontier);
        let waiter_stop_flag = Arc::clone(&stop_flag);
        let waiter = thread::spawn(move || {
            let mut dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
            let outcome = waiter_frontier.dequeue_batch_blocking(
                &mut dest,
                SHARED_QUEUE_BATCH_SIZE,
                &waiter_stop_flag,
            );
            done_tx
                .send((outcome, dest.into_vec()))
                .expect("waiter should report dequeue result");
        });

        wait_until_waiting(&frontier, 1);
        assert!(
            done_rx.try_recv().is_err(),
            "worker should still be blocked on the empty frontier before enqueue"
        );

        let mut batch = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        batch.push((7, 3));
        frontier.push_batch(&mut batch);

        let (outcome, items) = done_rx
            .recv_timeout(Duration::from_secs(1))
            .expect("enqueue should wake the blocked worker");
        assert!(
            matches!(outcome, DequeueOutcome::Refilled),
            "enqueue should wake the worker with real work"
        );
        assert_eq!(items, vec![(7, 3)]);
        assert!(
            batch.is_empty(),
            "push_batch should drain the caller-owned staging buffer"
        );
        waiter.join().expect("waiter thread should exit cleanly");
    }

    #[cfg_attr(test, ntest::timeout(5000))]
    #[test]
    fn test_all_workers_waiting_on_empty_frontier_finish_exactly_once() {
        let frontier = Arc::new(SharedFrontier::<usize>::new(2));
        let stop_flag = Arc::new(AtomicBool::new(false));
        let (done_tx, done_rx) = mpsc::channel();

        let waiter_frontier = Arc::clone(&frontier);
        let waiter_stop_flag = Arc::clone(&stop_flag);
        let waiter = thread::spawn(move || {
            let mut dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
            let outcome = waiter_frontier.dequeue_batch_blocking(
                &mut dest,
                SHARED_QUEUE_BATCH_SIZE,
                &waiter_stop_flag,
            );
            done_tx
                .send(outcome)
                .expect("waiter should report dequeue completion");
        });

        wait_until_waiting(&frontier, 1);

        let mut main_dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        let main_outcome =
            frontier.dequeue_batch_blocking(&mut main_dest, SHARED_QUEUE_BATCH_SIZE, &stop_flag);
        assert!(
            matches!(main_outcome, DequeueOutcome::Done),
            "the final waiting worker should trigger shared completion"
        );
        assert!(
            main_dest.is_empty(),
            "completion should not fabricate queue items for the last worker"
        );

        let waiter_outcome = done_rx
            .recv_timeout(Duration::from_secs(1))
            .expect("waiting worker should wake and observe shared completion");
        assert!(
            matches!(waiter_outcome, DequeueOutcome::Done),
            "woken waiter should observe the shared finished state"
        );
        waiter.join().expect("waiter thread should exit cleanly");

        {
            let state = frontier.state.lock();
            assert!(
                state.finished,
                "completion should mark the frontier finished"
            );
            assert_eq!(
                state.num_waiting, 0,
                "finished frontier should not leave phantom waiting workers behind"
            );
        }

        let mut post_finish_dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        let post_finish_outcome = frontier.dequeue_batch_blocking(
            &mut post_finish_dest,
            SHARED_QUEUE_BATCH_SIZE,
            &stop_flag,
        );
        assert!(
            matches!(post_finish_outcome, DequeueOutcome::Done),
            "finished frontier should keep returning Done instead of re-running termination"
        );
        assert!(
            post_finish_dest.is_empty(),
            "post-finish dequeue should stay empty"
        );
    }

    #[cfg_attr(test, ntest::timeout(5000))]
    #[test]
    fn test_depth_layered_frontier_holds_next_level_until_current_batch_completes() {
        let frontier = SharedFrontier::<usize>::new_depth_layered(2);
        let stop_flag = AtomicBool::new(false);

        frontier.push_single(10, 0);
        frontier.push_single(20, 1);

        let mut current_dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        let first_outcome =
            frontier.dequeue_batch_blocking(&mut current_dest, SHARED_QUEUE_BATCH_SIZE, &stop_flag);
        assert!(matches!(first_outcome, DequeueOutcome::Refilled));
        assert_eq!(current_dest.into_vec(), vec![(10, 0)]);

        let mut blocked_dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        let blocked_outcome =
            frontier.dequeue_batch_blocking(&mut blocked_dest, SHARED_QUEUE_BATCH_SIZE, &stop_flag);
        assert!(
            matches!(blocked_outcome, DequeueOutcome::TimedOut),
            "next-level work must stay hidden while a current-level batch is still active"
        );
        assert!(blocked_dest.is_empty());

        frontier.complete_level_batch();

        let mut next_dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        let next_outcome =
            frontier.dequeue_batch_blocking(&mut next_dest, SHARED_QUEUE_BATCH_SIZE, &stop_flag);
        assert!(matches!(next_outcome, DequeueOutcome::Refilled));
        assert_eq!(next_dest.into_vec(), vec![(20, 1)]);
    }

    #[cfg_attr(test, ntest::timeout(5000))]
    #[test]
    fn test_depth_layered_frontier_finishes_only_after_active_level_completes() {
        let frontier = SharedFrontier::<usize>::new_depth_layered(2);
        let stop_flag = AtomicBool::new(false);

        frontier.push_single(7, 0);

        let mut current_dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        let first_outcome =
            frontier.dequeue_batch_blocking(&mut current_dest, SHARED_QUEUE_BATCH_SIZE, &stop_flag);
        assert!(matches!(first_outcome, DequeueOutcome::Refilled));

        let mut blocked_dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        let blocked_outcome =
            frontier.dequeue_batch_blocking(&mut blocked_dest, SHARED_QUEUE_BATCH_SIZE, &stop_flag);
        assert!(
            matches!(blocked_outcome, DequeueOutcome::TimedOut),
            "depth-layered completion must wait for the active worker to finish its batch"
        );

        frontier.complete_level_batch();

        let mut done_dest = SmallVec::<[(usize, usize); SHARED_QUEUE_BATCH_SIZE]>::new();
        let done_outcome =
            frontier.dequeue_batch_blocking(&mut done_dest, SHARED_QUEUE_BATCH_SIZE, &stop_flag);
        assert!(matches!(done_outcome, DequeueOutcome::Done));
        assert!(done_dest.is_empty());

        let state = frontier.state.lock();
        assert!(state.finished);
        assert_eq!(state.current_depth, 0);
        assert_eq!(state.active_workers_at_level, 0);
    }
}
