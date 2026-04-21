// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests covering profile output on early worker-loop termination.

use super::*;

#[test]
fn test_run_bfs_worker_outputs_profile_on_state_limit_termination() {
    let mut transport = MockTransport::new(false, true);
    let outcome = run_bfs_worker(&mut transport, &BfsWorkerConfig { max_depth: None }, None);

    assert!(
        matches!(outcome, BfsLoopOutcome::Terminated(_)),
        "state-limit stop should terminate the loop early"
    );
    assert_eq!(
        transport.output_profile_calls.get(),
        1,
        "bounded early termination must still emit the coarse BFS profile"
    );
    assert_eq!(
        transport.release_calls.get(),
        1,
        "state-limit termination should still release the resolved state"
    );
}

#[test]
fn test_run_bfs_worker_outputs_profile_on_progress_termination() {
    let mut transport = MockTransport::new(true, false);
    let outcome = run_bfs_worker(&mut transport, &BfsWorkerConfig { max_depth: None }, None);

    assert!(
        matches!(outcome, BfsLoopOutcome::Terminated(_)),
        "progress-limit stop should terminate the loop early"
    );
    assert_eq!(
        transport.output_profile_calls.get(),
        1,
        "progress termination must still emit the coarse BFS profile"
    );
    assert_eq!(
        transport.release_calls.get(),
        1,
        "progress termination should still release the resolved state"
    );
}
