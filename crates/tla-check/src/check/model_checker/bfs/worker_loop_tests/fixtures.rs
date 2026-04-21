// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::check::model_checker::bfs::transport::{BfsTermination, BfsTransport};
use crate::check::{CheckResult, CheckStats, LimitType, Trace};
use crate::state::{ArrayState, Fingerprint};
use crate::storage::StorageStats;
use std::cell::Cell;
use std::collections::{HashSet, VecDeque};

fn empty_stats() -> CheckStats {
    CheckStats {
        states_found: 0,
        initial_states: 0,
        max_queue_depth: 0,
        transitions: 0,
        max_depth: 0,
        detected_actions: Vec::new(),
        detected_action_ids: Vec::new(),
        coverage: None,
        phantom_dequeues: 0,
        suppressed_guard_errors: 0,
        trace_reconstructions: 0,
        fp_dedup_collisions: 0,
        internal_fp_collisions: 0,
        storage_stats: StorageStats {
            memory_count: 0,
            disk_count: 0,
            disk_lookups: 0,
            disk_hits: 0,
            eviction_count: 0,
            memory_bytes: 0,
        },
        collision_check_mode: Default::default(),
        collision_check_stats: Default::default(),
        symmetry_reduction: Default::default(),
        por_reduction: Default::default(),
    }
}

pub(super) struct MockTransport {
    queue: VecDeque<u8>,
    pub(super) output_profile_calls: Cell<usize>,
    pub(super) release_calls: Cell<usize>,
    terminate_on_progress: bool,
    terminate_on_state_limit: bool,
}

impl MockTransport {
    pub(super) fn new(terminate_on_progress: bool, terminate_on_state_limit: bool) -> Self {
        Self {
            queue: VecDeque::from([0]),
            output_profile_calls: Cell::new(0),
            release_calls: Cell::new(0),
            terminate_on_progress,
            terminate_on_state_limit,
        }
    }
}

impl BfsTransport for MockTransport {
    type WorkItem = u8;

    fn try_dequeue(&mut self) -> Option<Self::WorkItem> {
        self.queue.pop_front()
    }

    fn resolve(
        &mut self,
        _item: Self::WorkItem,
    ) -> Result<Option<(Fingerprint, ArrayState, usize)>, BfsTermination> {
        Ok(Some((Fingerprint(1), ArrayState::new(0), 0)))
    }

    fn report_progress(&mut self, _depth: usize, _queue_len: usize) -> Result<(), BfsTermination> {
        if self.terminate_on_progress {
            Err(BfsTermination::result(CheckResult::LimitReached {
                limit_type: LimitType::Memory,
                stats: empty_stats(),
            }))
        } else {
            Ok(())
        }
    }

    fn should_checkpoint(&self) -> bool {
        false
    }

    fn save_checkpoint(&mut self, _current: &ArrayState) {}

    fn check_state_limit(&mut self) -> Result<(), BfsTermination> {
        if self.terminate_on_state_limit {
            Err(BfsTermination::result(CheckResult::LimitReached {
                limit_type: LimitType::States,
                stats: empty_stats(),
            }))
        } else {
            Ok(())
        }
    }

    fn release_state(&mut self, _fp: Fingerprint, _current: ArrayState) {
        self.release_calls.set(self.release_calls.get() + 1);
    }

    fn on_depth_limit_skip(&mut self) {}

    fn process_successors(
        &mut self,
        _fp: Fingerprint,
        _current: ArrayState,
        _depth: usize,
        _succ_depth: usize,
        _current_level: u32,
        _succ_level: u32,
    ) -> Result<(), BfsTermination> {
        Ok(())
    }

    fn handle_error(
        &mut self,
        _fp: Fingerprint,
        _current: ArrayState,
        error: crate::check::CheckError,
    ) -> BfsTermination {
        BfsTermination::result(CheckResult::from_error(error, empty_stats()))
    }

    fn output_profile(&self) {
        self.output_profile_calls
            .set(self.output_profile_calls.get() + 1);
    }

    fn depth_limit_reached(&self) -> bool {
        false
    }
}

/// Extended mock that supports all BFS loop control paths.
pub(super) struct ConfigurableMock {
    queue: VecDeque<u8>,
    /// resolve returns Ok(None) for these indices (phantom dequeue).
    pub(super) phantom_indices: HashSet<usize>,
    pub(super) dequeue_count: Cell<usize>,
    pub(super) output_profile_calls: Cell<usize>,
    pub(super) release_calls: Cell<usize>,
    pub(super) checkpoint_calls: Cell<usize>,
    pub(super) depth_limit_skip_calls: Cell<usize>,
    pub(super) process_calls: Cell<usize>,
    /// If set, resolve returns this depth for the state.
    pub(super) resolve_depth: usize,
    /// Flags to trigger termination on specific paths.
    terminate_on_progress: bool,
    terminate_on_state_limit: bool,
    pub(super) terminate_on_liveness: bool,
    pub(super) terminate_on_successors: bool,
    /// Whether should_checkpoint returns true.
    pub(super) checkpoint_enabled: bool,
    depth_limit_flag: Cell<bool>,
}

impl ConfigurableMock {
    pub(super) fn basic(queue_size: usize) -> Self {
        Self {
            queue: (0..queue_size as u8).collect(),
            phantom_indices: HashSet::new(),
            dequeue_count: Cell::new(0),
            output_profile_calls: Cell::new(0),
            release_calls: Cell::new(0),
            checkpoint_calls: Cell::new(0),
            depth_limit_skip_calls: Cell::new(0),
            process_calls: Cell::new(0),
            resolve_depth: 0,
            terminate_on_progress: false,
            terminate_on_state_limit: false,
            terminate_on_liveness: false,
            terminate_on_successors: false,
            checkpoint_enabled: false,
            depth_limit_flag: Cell::new(false),
        }
    }
}

impl BfsTransport for ConfigurableMock {
    type WorkItem = u8;

    fn try_dequeue(&mut self) -> Option<Self::WorkItem> {
        let item = self.queue.pop_front();
        if item.is_some() {
            self.dequeue_count.set(self.dequeue_count.get() + 1);
        }
        item
    }

    fn resolve(
        &mut self,
        _item: Self::WorkItem,
    ) -> Result<Option<(Fingerprint, ArrayState, usize)>, BfsTermination> {
        let idx = self.dequeue_count.get() - 1;
        if self.phantom_indices.contains(&idx) {
            Ok(None)
        } else {
            Ok(Some((
                Fingerprint(idx as u64 + 1),
                ArrayState::new(0),
                self.resolve_depth,
            )))
        }
    }

    fn maybe_periodic_liveness(&mut self) -> Result<(), BfsTermination> {
        if self.terminate_on_liveness {
            Err(BfsTermination::result(CheckResult::LivenessViolation {
                property: "mock liveness".to_string(),
                prefix: Trace::new(),
                cycle: Trace::new(),
                stats: empty_stats(),
            }))
        } else {
            Ok(())
        }
    }

    fn report_progress(&mut self, _depth: usize, _queue_len: usize) -> Result<(), BfsTermination> {
        if self.terminate_on_progress {
            Err(BfsTermination::result(CheckResult::LimitReached {
                limit_type: LimitType::Memory,
                stats: empty_stats(),
            }))
        } else {
            Ok(())
        }
    }

    fn should_checkpoint(&self) -> bool {
        self.checkpoint_enabled
    }

    fn save_checkpoint(&mut self, _current: &ArrayState) {
        self.checkpoint_calls.set(self.checkpoint_calls.get() + 1);
    }

    fn check_state_limit(&mut self) -> Result<(), BfsTermination> {
        if self.terminate_on_state_limit {
            Err(BfsTermination::result(CheckResult::LimitReached {
                limit_type: LimitType::States,
                stats: empty_stats(),
            }))
        } else {
            Ok(())
        }
    }

    fn release_state(&mut self, _fp: Fingerprint, _current: ArrayState) {
        self.release_calls.set(self.release_calls.get() + 1);
    }

    fn on_depth_limit_skip(&mut self) {
        self.depth_limit_skip_calls
            .set(self.depth_limit_skip_calls.get() + 1);
    }

    fn process_successors(
        &mut self,
        _fp: Fingerprint,
        _current: ArrayState,
        _depth: usize,
        _succ_depth: usize,
        _current_level: u32,
        _succ_level: u32,
    ) -> Result<(), BfsTermination> {
        self.process_calls.set(self.process_calls.get() + 1);
        if self.terminate_on_successors {
            Err(BfsTermination::result(CheckResult::InvariantViolation {
                invariant: "mock invariant".to_string(),
                trace: Trace::new(),
                stats: empty_stats(),
            }))
        } else {
            Ok(())
        }
    }

    fn handle_error(
        &mut self,
        _fp: Fingerprint,
        _current: ArrayState,
        error: crate::check::CheckError,
    ) -> BfsTermination {
        BfsTermination::result(CheckResult::from_error(error, empty_stats()))
    }

    fn output_profile(&self) {
        self.output_profile_calls
            .set(self.output_profile_calls.get() + 1);
    }

    fn depth_limit_reached(&self) -> bool {
        self.depth_limit_flag.get()
    }
}
