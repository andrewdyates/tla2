// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{WorkerResult, WorkerStats, WORK_BATCH_SIZE};
use super::coordination::{finish_if_stop_requested, record_state_completion};
use super::work_stealing::{poll_work_with_backoff, PollAction};
use crate::eval::EvalCtx;
use crossbeam_channel::unbounded;
use crossbeam_deque::{Injector, Worker as CbWorker};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

#[test]
fn test_record_state_completion_keeps_positive_delta_batched() {
    let work_remaining = AtomicUsize::new(11);
    let mut delta = 4;

    record_state_completion(&mut delta, &work_remaining);

    assert_eq!(
        delta, 3,
        "productive completion should keep positive work batched"
    );
    assert_eq!(
        work_remaining.load(Ordering::Acquire),
        11,
        "per-state completion should not flush shared work_remaining on productive runs"
    );
}

#[test]
fn test_record_state_completion_preserves_negative_batch_flush() {
    let work_remaining = AtomicUsize::new(512);
    let mut delta = -((WORK_BATCH_SIZE as isize) - 1);

    record_state_completion(&mut delta, &work_remaining);

    assert_eq!(
        delta, 0,
        "negative batch should flush once the threshold is crossed"
    );
    assert_eq!(
        work_remaining.load(Ordering::Acquire),
        256,
        "state completion must still flush large negative batches to keep work_remaining accurate"
    );
}

#[test]
fn test_finish_if_stop_requested_flushes_local_work_before_done() {
    let stop_flag = AtomicBool::new(true);
    let ctx = EvalCtx::new();
    let (result_tx, result_rx) = unbounded();
    let work_remaining = AtomicUsize::new(5);
    let mut delta = 3;
    let mut stats = WorkerStats {
        states_explored: 7,
        ..WorkerStats::default()
    };

    assert!(finish_if_stop_requested(
        &stop_flag,
        &ctx,
        &mut stats,
        &result_tx,
        &mut delta,
        &work_remaining,
    ));
    assert_eq!(
        work_remaining.load(Ordering::Acquire),
        8,
        "stop handling must publish outstanding local work before reporting done"
    );
    assert_eq!(delta, 0, "stop handling should clear the local batch");

    match result_rx
        .try_recv()
        .expect("stop handling should send Done")
    {
        WorkerResult::Done(done_stats) => {
            assert_eq!(
                done_stats.states_explored, 7,
                "Done result should carry the worker stats collected before stop"
            );
        }
        _ => panic!("expected WorkerResult::Done"),
    }
}

#[test]
fn test_poll_work_with_backoff_flushes_positive_delta_before_termination_check() {
    let local_queue: CbWorker<(u32, usize)> = CbWorker::new_fifo();
    let injector: Injector<(u32, usize)> = Injector::new();
    let stealers: Vec<crossbeam_deque::Stealer<(u32, usize)>> = Vec::new();
    let ctx = EvalCtx::new();
    let (result_tx, result_rx) = unbounded();
    let mut stats = WorkerStats::default();
    let mut consecutive_empty = 0;
    let mut delta = 2;
    let work_remaining = AtomicUsize::new(0);
    let active_workers = AtomicUsize::new(0);
    let bootstrap_injector_budget = AtomicUsize::new(0);
    let mut steal_cursor = 0;

    let action = poll_work_with_backoff(
        &local_queue,
        &injector,
        &stealers,
        &bootstrap_injector_budget,
        false,
        &ctx,
        &result_tx,
        &mut stats,
        &mut consecutive_empty,
        &mut delta,
        &work_remaining,
        &active_workers,
        1,
        0,
        &mut steal_cursor,
    );

    assert!(
        matches!(action, PollAction::Continue),
        "hidden positive work must prevent idle-loop termination"
    );
    assert_eq!(
        work_remaining.load(Ordering::Acquire),
        2,
        "idle-loop polling must publish the positive local batch before checking for termination"
    );
    assert_eq!(
        delta, 0,
        "idle-loop polling should clear the local batch after flushing it"
    );
    assert!(
        result_rx.try_recv().is_err(),
        "premature termination must not send a Done result while local work exists"
    );
}
