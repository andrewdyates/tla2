// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Two-phase quiescence termination detection for distributed BFS.
//!
//! Detects global termination — all workers idle AND all channels empty — in a
//! decentralized fashion. No single coordinator polls workers; instead, the
//! workers collaboratively reach consensus via a two-phase protocol.
//!
//! # Protocol
//!
//! **Phase 1 (idle detection):** When a worker exhausts its local frontier and
//! finds its exchange channel empty, it increments the shared `idle_count`.
//! When `idle_count` reaches `total_workers`, the detecting worker advances
//! `termination_generation` and resets `confirmed_count` to 0.
//!
//! **Phase 2 (confirmation):** Each idle worker observes the new generation,
//! re-drains its channel, and either:
//! - Finds new work: clears its idle flag, decrements `idle_count`, and resumes.
//! - Confirms empty: increments `confirmed_count`. When `confirmed_count`
//!   equals `total_workers`, termination is definitive.
//!
//! This two-phase approach ensures that every channel is drained after the last
//! possible send before termination is declared. It prevents the race where
//! worker A sends a message to worker B, then both become idle, and B exits
//! without processing the message.
//!
//! Part of #3796.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// Shared termination state for the two-phase quiescence protocol.
///
/// All fields are atomic because multiple worker threads read and write
/// concurrently. `SeqCst` ordering is used throughout to ensure a total
/// order on termination-related operations.
pub(crate) struct TerminationState {
    /// Number of workers currently in the idle state.
    pub(super) idle_count: AtomicUsize,
    /// Monotonically increasing generation for the confirmation phase.
    /// Each time all workers appear idle, the generation advances.
    pub(super) termination_generation: AtomicUsize,
    /// Number of workers that confirmed "still idle" in the current generation.
    pub(super) confirmed_count: AtomicUsize,
    /// Set to true when Phase 2 confirmation succeeds.
    pub(super) all_done: AtomicBool,
    /// Total number of workers in the distributed run.
    pub(super) total_workers: usize,
}

impl TerminationState {
    /// Create a new termination state for `total_workers` workers.
    pub(crate) fn new(total_workers: usize) -> Self {
        TerminationState {
            idle_count: AtomicUsize::new(0),
            termination_generation: AtomicUsize::new(0),
            confirmed_count: AtomicUsize::new(0),
            all_done: AtomicBool::new(false),
            total_workers,
        }
    }

    /// Enter Phase 1: mark this worker as idle.
    ///
    /// Returns `true` if this worker was the last to become idle (triggering
    /// the generation advance for Phase 2).
    pub(crate) fn enter_idle(&self) -> bool {
        let prev_idle = self.idle_count.fetch_add(1, Ordering::SeqCst);
        if prev_idle + 1 == self.total_workers {
            // All workers idle — start confirmation phase.
            self.confirmed_count.store(0, Ordering::SeqCst);
            self.termination_generation.fetch_add(1, Ordering::SeqCst);
            true
        } else {
            false
        }
    }

    /// Leave idle state (found new work).
    pub(crate) fn leave_idle(&self) {
        self.idle_count.fetch_sub(1, Ordering::SeqCst);
    }

    /// Current termination generation.
    pub(crate) fn generation(&self) -> usize {
        self.termination_generation.load(Ordering::SeqCst)
    }

    /// Confirm "still idle" in Phase 2. Returns `true` if this confirmation
    /// completed the consensus (all workers confirmed).
    pub(crate) fn confirm_idle(&self) -> bool {
        let prev_confirmed = self.confirmed_count.fetch_add(1, Ordering::SeqCst);
        if prev_confirmed + 1 == self.total_workers {
            self.all_done.store(true, Ordering::SeqCst);
            true
        } else {
            false
        }
    }

    /// Retract a confirmation (found late-arriving work during Phase 2 wait).
    pub(crate) fn retract_confirmation(&self) {
        self.idle_count.fetch_sub(1, Ordering::SeqCst);
        self.confirmed_count.fetch_sub(1, Ordering::SeqCst);
    }

    /// Check whether global termination has been declared.
    pub(crate) fn is_done(&self) -> bool {
        self.all_done.load(Ordering::SeqCst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_termination_state_initial() {
        let ts = TerminationState::new(4);
        assert_eq!(ts.idle_count.load(Ordering::SeqCst), 0);
        assert_eq!(ts.generation(), 0);
        assert_eq!(ts.confirmed_count.load(Ordering::SeqCst), 0);
        assert!(!ts.is_done());
        assert_eq!(ts.total_workers, 4);
    }

    #[test]
    fn test_enter_idle_last_triggers_generation() {
        let ts = TerminationState::new(2);

        // First worker enters idle — not last.
        assert!(!ts.enter_idle());
        assert_eq!(ts.idle_count.load(Ordering::SeqCst), 1);
        assert_eq!(ts.generation(), 0);

        // Second worker enters idle — last, triggers generation advance.
        assert!(ts.enter_idle());
        assert_eq!(ts.idle_count.load(Ordering::SeqCst), 2);
        assert_eq!(ts.generation(), 1);
    }

    #[test]
    fn test_leave_idle_decrements() {
        let ts = TerminationState::new(3);
        ts.enter_idle();
        ts.enter_idle();
        assert_eq!(ts.idle_count.load(Ordering::SeqCst), 2);

        ts.leave_idle();
        assert_eq!(ts.idle_count.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_confirm_idle_all_workers() {
        let ts = TerminationState::new(3);

        // Simulate all entering idle, triggering generation advance.
        ts.enter_idle();
        ts.enter_idle();
        ts.enter_idle();
        assert_eq!(ts.generation(), 1);

        // All three confirm.
        assert!(!ts.confirm_idle());
        assert!(!ts.confirm_idle());
        assert!(ts.confirm_idle()); // Third confirms — done.
        assert!(ts.is_done());
    }

    #[test]
    fn test_retract_confirmation() {
        let ts = TerminationState::new(2);
        ts.enter_idle();
        ts.enter_idle();

        ts.confirm_idle(); // One confirms.
        ts.retract_confirmation(); // Retracts (found work).

        // Should not be done since we retracted.
        assert!(!ts.is_done());
    }

    #[test]
    fn test_single_worker_termination() {
        let ts = TerminationState::new(1);

        assert!(ts.enter_idle()); // Sole worker enters idle => generation advances.
        assert_eq!(ts.generation(), 1);

        assert!(ts.confirm_idle()); // Sole worker confirms => done.
        assert!(ts.is_done());
    }
}
