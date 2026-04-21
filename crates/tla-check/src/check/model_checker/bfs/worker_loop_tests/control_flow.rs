// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests covering BFS worker-loop queue, depth, and successor control flow.

use super::*;

#[test]
fn test_empty_queue_returns_complete() {
    let mut transport = ConfigurableMock::basic(0);
    let config = BfsWorkerConfig { max_depth: None };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(
        matches!(
            outcome,
            BfsLoopOutcome::Complete {
                depth_limit_reached: false
            }
        ),
        "empty queue should produce Complete with depth_limit_reached=false"
    );
    assert_eq!(transport.output_profile_calls.get(), 1);
    assert_eq!(transport.process_calls.get(), 0);
}

#[test]
fn test_phantom_dequeue_skips_to_next_item() {
    let mut transport = ConfigurableMock::basic(3);
    transport.phantom_indices.insert(0);
    transport.phantom_indices.insert(1);
    let config = BfsWorkerConfig { max_depth: None };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(matches!(outcome, BfsLoopOutcome::Complete { .. }));
    assert_eq!(
        transport.dequeue_count.get(),
        3,
        "all 3 items should be dequeued"
    );
    assert_eq!(
        transport.process_calls.get(),
        1,
        "only the non-phantom item should be processed"
    );
}

#[test]
fn test_depth_limit_skips_state_and_continues() {
    let mut transport = ConfigurableMock::basic(1);
    transport.resolve_depth = 5;
    let config = BfsWorkerConfig { max_depth: Some(5) };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(matches!(outcome, BfsLoopOutcome::Complete { .. }));
    assert_eq!(
        transport.depth_limit_skip_calls.get(),
        1,
        "on_depth_limit_skip should be called"
    );
    assert_eq!(
        transport.release_calls.get(),
        1,
        "skipped state must be released"
    );
    assert_eq!(
        transport.process_calls.get(),
        0,
        "skipped state must not be processed"
    );
}

#[test]
fn test_depth_limit_allows_states_below_limit() {
    let mut transport = ConfigurableMock::basic(1);
    transport.resolve_depth = 4;
    let config = BfsWorkerConfig { max_depth: Some(5) };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(matches!(outcome, BfsLoopOutcome::Complete { .. }));
    assert_eq!(transport.depth_limit_skip_calls.get(), 0);
    assert_eq!(transport.process_calls.get(), 1);
}

#[test]
fn test_depth_overflow_terminates() {
    let mut transport = ConfigurableMock::basic(1);
    transport.resolve_depth = usize::MAX;
    let config = BfsWorkerConfig { max_depth: None };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(
        matches!(outcome, BfsLoopOutcome::Terminated(_)),
        "depth overflow (usize::MAX + 1) should terminate"
    );
    assert_eq!(
        transport.output_profile_calls.get(),
        1,
        "profile must be emitted even on depth overflow"
    );
}

#[test]
fn test_periodic_liveness_termination() {
    let mut transport = ConfigurableMock::basic(1);
    transport.terminate_on_liveness = true;
    let config = BfsWorkerConfig { max_depth: None };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(
        matches!(outcome, BfsLoopOutcome::Terminated(_)),
        "liveness violation should terminate the loop"
    );
    assert_eq!(transport.output_profile_calls.get(), 1);
    assert_eq!(transport.release_calls.get(), 0);
    assert_eq!(transport.process_calls.get(), 0);
}

#[test]
fn test_process_successors_error_terminates() {
    let mut transport = ConfigurableMock::basic(1);
    transport.terminate_on_successors = true;
    let config = BfsWorkerConfig { max_depth: None };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(
        matches!(outcome, BfsLoopOutcome::Terminated(_)),
        "successor processing error should terminate"
    );
    assert_eq!(transport.output_profile_calls.get(), 1);
}

#[test]
fn test_checkpoint_called_when_enabled() {
    let mut transport = ConfigurableMock::basic(3);
    transport.checkpoint_enabled = true;
    let config = BfsWorkerConfig { max_depth: None };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(matches!(outcome, BfsLoopOutcome::Complete { .. }));
    assert_eq!(
        transport.checkpoint_calls.get(),
        3,
        "checkpoint should be called for each processed state"
    );
}

#[test]
fn test_depth_to_tlc_level_overflow_terminates() {
    let mut transport = ConfigurableMock::basic(1);
    transport.resolve_depth = u32::MAX as usize;
    let config = BfsWorkerConfig { max_depth: None };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(
        matches!(outcome, BfsLoopOutcome::Terminated(_)),
        "depth exceeding u32 range should terminate via depth_to_tlc_level error"
    );
    assert_eq!(transport.output_profile_calls.get(), 1);
}

#[test]
fn test_multiple_states_all_processed() {
    let mut transport = ConfigurableMock::basic(5);
    let config = BfsWorkerConfig { max_depth: None };
    let outcome = run_bfs_worker(&mut transport, &config, None);

    assert!(matches!(outcome, BfsLoopOutcome::Complete { .. }));
    assert_eq!(transport.process_calls.get(), 5);
    assert_eq!(transport.output_profile_calls.get(), 1);
}
