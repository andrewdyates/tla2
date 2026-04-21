// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core successor-step reducer for BFS model checking.
//!
//! Part of #2356: provides a single shared reducer (`run_core_step`) that
//! encapsulates the per-successor decision sequence:
//!   admit (dedup) → invariant check → violation handling → enqueue
//!
//! Each BFS mode (sequential, resume, parallel) implements `CoreStepAdapter`
//! to provide mode-specific storage, invariant evaluation, and stop mechanics,
//! while the reducer owns the decision flow that must be identical across all
//! modes. This mirrors TLC's `Worker.addElement()` pattern where one callback
//! body handles every successor regardless of worker count.

use crate::check::CheckError;
use crate::checker_ops::InvariantOutcome;
use crate::state::{ArrayState, Fingerprint};

/// Input context for processing one successor state.
///
/// Bundles the parent/successor state data needed by the reducer.
/// All fields are borrowed or Copy — no ownership transfer.
pub(crate) struct CoreStepInput<'a> {
    /// Fingerprint of the parent state that generated this successor.
    pub parent_fp: Fingerprint,
    /// The successor state to process.
    pub succ: &'a ArrayState,
    /// Fingerprint of the successor state.
    pub succ_fp: Fingerprint,
    /// BFS depth of the successor (typically `parent_depth + 1`).
    pub succ_depth: usize,
    /// TLC-compatible level of the successor (one-based, `succ_depth + 1`).
    pub succ_level: u32,
}

/// Outcome of the core step reducer for one successor.
#[derive(Debug)]
pub(crate) enum CoreStepAction<E> {
    /// Successor was already seen — skipped (no invariant check, no enqueue).
    SkipDuplicate,
    /// Successor passed all checks and was enqueued for further exploration.
    Enqueue,
    /// Successor caused a stop condition (violation in fatal mode, or error).
    Stop(E),
}

/// Mode-specific adapter for the core step reducer.
///
/// Each BFS mode (sequential, resume, parallel) implements this trait to
/// provide its own storage, invariant evaluation, and stop mechanics.
/// The reducer (`run_core_step`) calls these methods in a fixed sequence
/// to enforce identical decision flow across all modes.
pub(crate) trait CoreStepAdapter {
    /// Mode-specific stop payload (e.g., `CheckResult` for sequential,
    /// `WorkerResult` for parallel).
    type Stop;

    /// Check if the successor is already seen. If new, admit it to storage.
    ///
    /// Returns `Ok(true)` if the state was new and has been admitted,
    /// `Ok(false)` if it was a duplicate. `Err(stop)` on storage fault.
    fn admit(&mut self, input: &CoreStepInput<'_>) -> Result<bool, Self::Stop>;

    /// Evaluate invariants against the admitted successor state.
    ///
    /// Called only for newly admitted states (after `admit` returns `true`).
    /// Implementations should delegate to `checker_ops::check_invariants_for_successor`
    /// to maintain a single canonical invariant evaluation path.
    fn check_invariants(&mut self, input: &CoreStepInput<'_>) -> InvariantOutcome;

    /// Handle an invariant violation.
    ///
    /// Called when `check_invariants` returns `Violation`. The adapter decides
    /// whether to continue exploration (`Ok(None)`) or stop (`Ok(Some(stop))`).
    ///
    /// When this returns `Ok(None)` (continue-on-error), the reducer will call
    /// `enqueue` to add the violating state for further exploration.
    /// Matches the existing `handle_invariant_violation` -> `Option<CheckResult>`
    /// pattern in `run_helpers.rs`.
    fn on_violation(
        &mut self,
        input: &CoreStepInput<'_>,
        invariant: String,
    ) -> Result<Option<Self::Stop>, Self::Stop>;

    /// Handle a fatal invariant evaluation error.
    ///
    /// Called when `check_invariants` returns `Error`. Implementations MUST:
    /// 1. Call `update_coverage_totals()` to flush pending coverage data.
    /// 2. Use `check_error_to_result(error, stats)` (not inline `CheckResult::Error`)
    ///    so that `ExitRequested` is mapped to `LimitReached` rather than a raw error.
    fn on_error(&mut self, input: &CoreStepInput<'_>, error: CheckError) -> Self::Stop;

    /// Enqueue the successor for further BFS exploration.
    ///
    /// Called for states that passed invariants (or continued after violation).
    /// The adapter pushes the state onto its mode-specific work queue.
    fn enqueue(&mut self, input: &CoreStepInput<'_>) -> Result<(), Self::Stop>;

    /// Whether to skip invariant checks for all states.
    ///
    /// Default is `false`. Override to return `true` when a symbolic engine
    /// (e.g., PDR) has proved all invariants hold for all reachable states,
    /// allowing the BFS engine to skip per-state invariant evaluation.
    ///
    /// Part of #3773: CDEMC invariant skip when PDR proves safety.
    /// For per-invariant granularity, see [`has_partial_invariant_proofs`].
    fn skip_invariant_checks(&self) -> bool {
        false
    }

    /// Whether some (but not all) invariants have been proved by PDR.
    ///
    /// When true, the reducer still calls `check_invariants` which should
    /// internally skip proved invariants and only evaluate unproved ones.
    /// This is the partial-skip path — more expensive than full skip but
    /// cheaper than checking all invariants.
    ///
    /// Default is `false`. Override when cooperative state tracks
    /// per-invariant proofs.
    ///
    /// Part of #3773, #3810: per-invariant proof tracking for CDEMC.
    fn has_partial_invariant_proofs(&self) -> bool {
        false
    }
}

/// Unified successor-step reducer.
///
/// Processes one successor state through the canonical decision sequence:
/// 1. **Admit** — dedup check + storage insertion
/// 2. **Invariant check** — evaluate all invariants
/// 3. **Outcome dispatch** — enqueue, handle violation, or stop on error
///
/// This is the single point of truth for successor processing decisions.
/// All BFS modes call this function instead of implementing the decision
/// sequence inline.
pub(crate) fn run_core_step<A: CoreStepAdapter>(
    adapter: &mut A,
    input: &CoreStepInput<'_>,
) -> Result<CoreStepAction<A::Stop>, A::Stop> {
    // Step 1: Dedup + admit to storage
    if !adapter.admit(input)? {
        return Ok(CoreStepAction::SkipDuplicate);
    }

    // CDEMC: skip invariant evaluation when symbolic engine has proved safety.
    // Part of #3773, #3810.
    if adapter.skip_invariant_checks() {
        adapter.enqueue(input)?;
        return Ok(CoreStepAction::Enqueue);
    }

    // Step 2: Check invariants for the newly admitted state.
    // When `has_partial_invariant_proofs()` is true, the adapter's
    // `check_invariants` implementation filters to only unproved invariants
    // (Part of #3810). The reducer calls check_invariants unconditionally —
    // the adapter handles the partial-skip internally.
    let _has_partial = adapter.has_partial_invariant_proofs();
    match adapter.check_invariants(input) {
        InvariantOutcome::Ok | InvariantOutcome::ViolationContinued => {
            // Step 3a: Passed (or already handled as continue-on-error) — enqueue
            adapter.enqueue(input)?;
            Ok(CoreStepAction::Enqueue)
        }
        InvariantOutcome::Violation { invariant, .. } => {
            // Step 3b: Violation — adapter decides continue vs stop
            if let Some(stop) = adapter.on_violation(input, invariant)? {
                Ok(CoreStepAction::Stop(stop))
            } else {
                // Continue-on-error: enqueue the violating state
                adapter.enqueue(input)?;
                Ok(CoreStepAction::Enqueue)
            }
        }
        InvariantOutcome::Error(error) => {
            // Step 3c: Fatal evaluation error — always stop
            Err(adapter.on_error(input, error))
        }
    }
}

// Part of #2356: ResumeAdapter was removed — the resume path now uses
// run_bfs_loop_core with FullStateStorage/FingerprintOnlyStorage,
// which goes through SequentialBfsAdapter like the normal BFS path.


#[cfg(test)]
mod tests {
    use super::*;
    use crate::ConfigCheckError;

    /// Test stop payload.
    #[derive(Debug, PartialEq)]
    enum TestStop {
        Violation(String),
        Error(String),
        StorageFault,
    }

    /// Configurable mock adapter for testing the reducer.
    struct MockAdapter {
        /// If true, `admit` returns false (duplicate).
        is_duplicate: bool,
        /// If true, `admit` returns Err (storage fault).
        admit_fails: bool,
        /// Invariant outcome to return from `check_invariants`.
        invariant_outcome: Option<InvariantOutcome>,
        /// If true, `on_violation` returns Enqueue (continue-on-error mode).
        continue_on_error: bool,
        /// If true, `enqueue` returns Err.
        enqueue_fails: bool,
        /// If true, `skip_invariant_checks` returns true (CDEMC PDR proved safety).
        skip_invariants: bool,
        /// If true, `has_partial_invariant_proofs` returns true (CDEMC partial PDR).
        partial_proofs: bool,

        // Tracking fields
        admit_called: bool,
        check_invariants_called: bool,
        on_violation_called: bool,
        on_error_called: bool,
        enqueue_called: bool,
    }

    impl MockAdapter {
        fn new() -> Self {
            MockAdapter {
                is_duplicate: false,
                admit_fails: false,
                invariant_outcome: None,
                continue_on_error: false,
                enqueue_fails: false,
                skip_invariants: false,
                partial_proofs: false,
                admit_called: false,
                check_invariants_called: false,
                on_violation_called: false,
                on_error_called: false,
                enqueue_called: false,
            }
        }
    }

    impl CoreStepAdapter for MockAdapter {
        type Stop = TestStop;

        fn admit(&mut self, _input: &CoreStepInput<'_>) -> Result<bool, Self::Stop> {
            self.admit_called = true;
            if self.admit_fails {
                return Err(TestStop::StorageFault);
            }
            Ok(!self.is_duplicate)
        }

        fn check_invariants(&mut self, _input: &CoreStepInput<'_>) -> InvariantOutcome {
            self.check_invariants_called = true;
            self.invariant_outcome
                .take()
                .unwrap_or(InvariantOutcome::Ok)
        }

        fn on_violation(
            &mut self,
            _input: &CoreStepInput<'_>,
            invariant: String,
        ) -> Result<Option<Self::Stop>, Self::Stop> {
            self.on_violation_called = true;
            if self.continue_on_error {
                Ok(None)
            } else {
                Ok(Some(TestStop::Violation(invariant)))
            }
        }

        fn on_error(&mut self, _input: &CoreStepInput<'_>, error: CheckError) -> Self::Stop {
            self.on_error_called = true;
            TestStop::Error(format!("{error:?}"))
        }

        fn enqueue(&mut self, _input: &CoreStepInput<'_>) -> Result<(), Self::Stop> {
            self.enqueue_called = true;
            if self.enqueue_fails {
                return Err(TestStop::StorageFault);
            }
            Ok(())
        }

        fn skip_invariant_checks(&self) -> bool {
            self.skip_invariants
        }

        fn has_partial_invariant_proofs(&self) -> bool {
            self.partial_proofs
        }
    }

    fn test_input() -> CoreStepInput<'static> {
        // Leak to get 'static — acceptable in tests.
        let succ = Box::leak(Box::new(ArrayState::new(1)));
        CoreStepInput {
            parent_fp: Fingerprint(100),
            succ,
            succ_fp: Fingerprint(200),
            succ_depth: 1,
            succ_level: 2,
        }
    }

    #[test]
    fn test_core_step_duplicate_skips_invariant_check() {
        let mut adapter = MockAdapter::new();
        adapter.is_duplicate = true;
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(
            !adapter.check_invariants_called,
            "invariant check should be skipped for duplicates"
        );
        assert!(!adapter.enqueue_called);
        assert!(matches!(result, Ok(CoreStepAction::SkipDuplicate)));
    }

    #[test]
    fn test_core_step_ok_enqueues() {
        let mut adapter = MockAdapter::new();
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(adapter.check_invariants_called);
        assert!(adapter.enqueue_called);
        assert!(!adapter.on_violation_called);
        assert!(matches!(result, Ok(CoreStepAction::Enqueue)));
    }

    #[test]
    fn test_core_step_violation_fatal_stops() {
        let mut adapter = MockAdapter::new();
        adapter.invariant_outcome = Some(InvariantOutcome::Violation {
            invariant: "Inv1".to_string(),
            state_fp: Fingerprint(200),
        });
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(adapter.check_invariants_called);
        assert!(adapter.on_violation_called);
        assert!(
            !adapter.enqueue_called,
            "should not enqueue on fatal violation"
        );
        match result {
            Ok(CoreStepAction::Stop(TestStop::Violation(inv))) => {
                assert_eq!(inv, "Inv1");
            }
            other => panic!("expected Stop(Violation), got {other:?}"),
        }
    }

    #[test]
    fn test_core_step_violation_continue_on_error_enqueues() {
        let mut adapter = MockAdapter::new();
        adapter.invariant_outcome = Some(InvariantOutcome::Violation {
            invariant: "Inv1".to_string(),
            state_fp: Fingerprint(200),
        });
        adapter.continue_on_error = true;
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(adapter.check_invariants_called);
        assert!(adapter.on_violation_called);
        assert!(
            adapter.enqueue_called,
            "reducer should enqueue after on_violation returns None"
        );
        assert!(matches!(result, Ok(CoreStepAction::Enqueue)));
    }

    #[test]
    fn test_core_step_error_stops() {
        let mut adapter = MockAdapter::new();
        adapter.invariant_outcome = Some(InvariantOutcome::Error(
            ConfigCheckError::Setup("test error".to_string()).into(),
        ));
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(adapter.check_invariants_called);
        assert!(adapter.on_error_called);
        assert!(!adapter.enqueue_called);
        match result {
            Err(TestStop::Error(msg)) => {
                assert!(msg.contains("test error"));
            }
            other => panic!("expected Err(Error), got {other:?}"),
        }
    }

    #[test]
    fn test_core_step_admit_storage_fault_stops() {
        let mut adapter = MockAdapter::new();
        adapter.admit_fails = true;
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(
            !adapter.check_invariants_called,
            "should not check invariants on storage fault"
        );
        assert!(matches!(result, Err(TestStop::StorageFault)));
    }

    #[test]
    fn test_core_step_enqueue_failure_propagates() {
        let mut adapter = MockAdapter::new();
        adapter.enqueue_fails = true;
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(adapter.check_invariants_called);
        assert!(adapter.enqueue_called);
        assert!(matches!(result, Err(TestStop::StorageFault)));
    }

    #[test]
    fn test_core_step_violation_continued_enqueues() {
        let mut adapter = MockAdapter::new();
        adapter.invariant_outcome = Some(InvariantOutcome::ViolationContinued);
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(adapter.check_invariants_called);
        assert!(
            !adapter.on_violation_called,
            "ViolationContinued should not trigger on_violation"
        );
        assert!(adapter.enqueue_called);
        assert!(matches!(result, Ok(CoreStepAction::Enqueue)));
    }

    #[test]
    fn test_core_step_skip_invariants_enqueues_without_checking() {
        let mut adapter = MockAdapter::new();
        adapter.skip_invariants = true;
        // Even with a violation configured, it should never be evaluated.
        adapter.invariant_outcome = Some(InvariantOutcome::Violation {
            invariant: "Inv1".to_string(),
            state_fp: Fingerprint(200),
        });
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(
            !adapter.check_invariants_called,
            "invariant check should be skipped when skip_invariant_checks returns true"
        );
        assert!(!adapter.on_violation_called);
        assert!(adapter.enqueue_called);
        assert!(matches!(result, Ok(CoreStepAction::Enqueue)));
    }

    #[test]
    fn test_core_step_partial_proofs_still_checks_invariants() {
        let mut adapter = MockAdapter::new();
        adapter.partial_proofs = true;
        // Partial proofs means invariants ARE still checked (with a reduced
        // set), not skipped entirely. The adapter's check_invariants is called.
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(
            adapter.check_invariants_called,
            "partial proofs should still call check_invariants"
        );
        assert!(adapter.enqueue_called);
        assert!(matches!(result, Ok(CoreStepAction::Enqueue)));
    }

    #[test]
    fn test_core_step_skip_invariants_still_skips_duplicates() {
        let mut adapter = MockAdapter::new();
        adapter.skip_invariants = true;
        adapter.is_duplicate = true;
        let input = test_input();

        let result = run_core_step(&mut adapter, &input);

        assert!(adapter.admit_called);
        assert!(!adapter.check_invariants_called);
        assert!(!adapter.enqueue_called, "duplicates should not be enqueued");
        assert!(matches!(result, Ok(CoreStepAction::SkipDuplicate)));
    }
}
