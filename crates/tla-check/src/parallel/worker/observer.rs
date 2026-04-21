// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Observer hooks for parallel BFS exploration.
//!
//! Part of #3707: separate successor/state observation concerns from the
//! parallel worker pipelines so constraint filtering, invariant evaluation,
//! and deadlock detection no longer sit inline in the BFS loops.

use super::super::{WorkerResult, WorkerStats};
use super::coordination::snapshot_stop_and_send;
use super::invariant_dispatch::{check_successor_constraints_array, check_successor_invariants};
use super::{InvariantCheckCtx, StopCtx};
use crate::check::CheckError;
use crate::checker_ops::InvariantOutcome;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, Fingerprint};
use crossbeam_channel::Sender;
use smallvec::SmallVec;

/// Context for observing a candidate or admitted successor.
pub(super) struct SuccessorObservationCtx<'a> {
    pub(super) current: &'a ArrayState,
    pub(super) parent_fp: Fingerprint,
    pub(super) succ: &'a ArrayState,
    pub(super) succ_fp: Fingerprint,
    pub(super) succ_depth: usize,
    pub(super) succ_level: u32,
}

/// Context for observing completion of one explored state.
pub(super) struct StateCompletionCtx<'a> {
    pub(super) state_fp: Fingerprint,
    pub(super) state: &'a ArrayState,
    pub(super) has_successors: bool,
}

/// Signal returned by a parallel exploration observer.
pub(super) enum ObservationSignal {
    /// Continue normal exploration.
    Continue,
    /// Skip the current successor without treating it as an error.
    Skip,
    /// Stop exploration. The observer already published the stop result.
    Stop,
    /// Invariant outcome for an admitted successor.
    Invariant(InvariantOutcome),
}

/// Mutable worker state exposed to parallel observers.
struct ParallelObserverEnv<'a, 'inv> {
    ctx: &'a mut EvalCtx,
    inv_ctx: &'a InvariantCheckCtx<'inv>,
    stop: &'a StopCtx<'inv>,
    result_tx: &'a Sender<WorkerResult>,
    stats: &'a mut WorkerStats,
}

impl<'a, 'inv> ParallelObserverEnv<'a, 'inv> {
    fn new(
        ctx: &'a mut EvalCtx,
        inv_ctx: &'a InvariantCheckCtx<'inv>,
        stop: &'a StopCtx<'inv>,
        result_tx: &'a Sender<WorkerResult>,
        stats: &'a mut WorkerStats,
    ) -> Self {
        Self {
            ctx,
            inv_ctx,
            stop,
            result_tx,
            stats,
        }
    }

    fn stop_with_deadlock(&mut self, state_fp: Fingerprint) {
        snapshot_stop_and_send(self.ctx, self.stats, self.stop, self.result_tx, |stats| {
            WorkerResult::Deadlock { state_fp, stats }
        });
    }
}

trait ExplorationObserver {
    fn on_successor(
        &mut self,
        _env: &mut ParallelObserverEnv<'_, '_>,
        _ctx: &SuccessorObservationCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        Ok(ObservationSignal::Continue)
    }

    fn on_state_completion(
        &mut self,
        _env: &mut ParallelObserverEnv<'_, '_>,
        _ctx: &StateCompletionCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        Ok(ObservationSignal::Continue)
    }
}

#[derive(Clone, Copy)]
enum ObserverKind {
    Constraint,
    Invariant,
    Deadlock,
}

impl ObserverKind {
    fn on_successor(
        &mut self,
        env: &mut ParallelObserverEnv<'_, '_>,
        ctx: &SuccessorObservationCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        match self {
            ObserverKind::Constraint => ConstraintObserver.on_successor(env, ctx),
            ObserverKind::Invariant => InvariantObserver.on_successor(env, ctx),
            ObserverKind::Deadlock => DeadlockObserver.on_successor(env, ctx),
        }
    }

    fn on_state_completion(
        &mut self,
        env: &mut ParallelObserverEnv<'_, '_>,
        ctx: &StateCompletionCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        match self {
            ObserverKind::Constraint => ConstraintObserver.on_state_completion(env, ctx),
            ObserverKind::Invariant => InvariantObserver.on_state_completion(env, ctx),
            ObserverKind::Deadlock => DeadlockObserver.on_state_completion(env, ctx),
        }
    }
}

/// Sequential composition of parallel BFS observers.
#[derive(Default)]
struct CompositeObserver {
    observers: SmallVec<[ObserverKind; 2]>,
}

impl CompositeObserver {
    fn candidate_successors(check_constraints: bool) -> Self {
        let mut composite = Self::default();
        if check_constraints {
            composite.observers.push(ObserverKind::Constraint);
        }
        composite
    }

    fn admitted_successors() -> Self {
        let mut composite = Self::default();
        composite.observers.push(ObserverKind::Invariant);
        composite
    }

    fn state_completion(check_deadlock: bool) -> Self {
        let mut composite = Self::default();
        if check_deadlock {
            composite.observers.push(ObserverKind::Deadlock);
        }
        composite
    }

    fn observe_successor(
        &mut self,
        env: &mut ParallelObserverEnv<'_, '_>,
        ctx: &SuccessorObservationCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        for observer in &mut self.observers {
            match observer.on_successor(env, ctx)? {
                ObservationSignal::Continue => {}
                signal => return Ok(signal),
            }
        }
        Ok(ObservationSignal::Continue)
    }

    fn observe_state_completion(
        &mut self,
        env: &mut ParallelObserverEnv<'_, '_>,
        ctx: &StateCompletionCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        for observer in &mut self.observers {
            match observer.on_state_completion(env, ctx)? {
                ObservationSignal::Continue => {}
                signal => return Ok(signal),
            }
        }
        Ok(ObservationSignal::Continue)
    }
}

struct ConstraintObserver;

impl ExplorationObserver for ConstraintObserver {
    fn on_successor(
        &mut self,
        env: &mut ParallelObserverEnv<'_, '_>,
        ctx: &SuccessorObservationCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        if check_successor_constraints_array(
            env.ctx,
            env.inv_ctx.config,
            ctx.current,
            ctx.succ,
            env.inv_ctx.action_constraint_analysis,
        )? {
            Ok(ObservationSignal::Continue)
        } else {
            Ok(ObservationSignal::Skip)
        }
    }
}

struct InvariantObserver;

impl ExplorationObserver for InvariantObserver {
    fn on_successor(
        &mut self,
        env: &mut ParallelObserverEnv<'_, '_>,
        ctx: &SuccessorObservationCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        let _ = ctx.parent_fp;
        let _ = ctx.succ_depth;
        Ok(ObservationSignal::Invariant(check_successor_invariants(
            env.ctx,
            env.inv_ctx,
            ctx.succ,
            ctx.succ_fp,
            ctx.succ_level,
        )))
    }
}

struct DeadlockObserver;

impl ExplorationObserver for DeadlockObserver {
    fn on_state_completion(
        &mut self,
        env: &mut ParallelObserverEnv<'_, '_>,
        ctx: &StateCompletionCtx<'_>,
    ) -> Result<ObservationSignal, CheckError> {
        if ctx.has_successors {
            return Ok(ObservationSignal::Continue);
        }
        let is_terminal = crate::check::check_terminal_array(
            env.ctx,
            env.inv_ctx.config.terminal.as_ref(),
            env.inv_ctx.var_registry,
            ctx.state,
        )?;
        if is_terminal {
            Ok(ObservationSignal::Continue)
        } else {
            env.stop_with_deadlock(ctx.state_fp);
            Ok(ObservationSignal::Stop)
        }
    }
}

pub(super) fn observe_candidate_successor(
    ctx: &mut EvalCtx,
    inv_ctx: &InvariantCheckCtx<'_>,
    stop: &StopCtx<'_>,
    result_tx: &Sender<WorkerResult>,
    stats: &mut WorkerStats,
    obs_ctx: &SuccessorObservationCtx<'_>,
) -> Result<ObservationSignal, CheckError> {
    let has_constraints =
        !inv_ctx.config.constraints.is_empty() || !inv_ctx.config.action_constraints.is_empty();
    let mut observer = CompositeObserver::candidate_successors(has_constraints);
    let mut env = ParallelObserverEnv::new(ctx, inv_ctx, stop, result_tx, stats);
    observer.observe_successor(&mut env, obs_ctx)
}

pub(super) fn observe_admitted_successor(
    ctx: &mut EvalCtx,
    inv_ctx: &InvariantCheckCtx<'_>,
    stop: &StopCtx<'_>,
    result_tx: &Sender<WorkerResult>,
    stats: &mut WorkerStats,
    obs_ctx: &SuccessorObservationCtx<'_>,
) -> InvariantOutcome {
    let mut observer = CompositeObserver::admitted_successors();
    let mut env = ParallelObserverEnv::new(ctx, inv_ctx, stop, result_tx, stats);
    match observer.observe_successor(&mut env, obs_ctx) {
        Ok(ObservationSignal::Invariant(outcome)) => outcome,
        Ok(ObservationSignal::Continue) => InvariantOutcome::Ok,
        Ok(ObservationSignal::Skip | ObservationSignal::Stop) => {
            debug_assert!(
                false,
                "admitted successor observers should only return Continue or Invariant"
            );
            InvariantOutcome::Ok
        }
        Err(error) => InvariantOutcome::Error(error),
    }
}

pub(super) fn observe_state_completion(
    ctx: &mut EvalCtx,
    inv_ctx: &InvariantCheckCtx<'_>,
    stop: &StopCtx<'_>,
    result_tx: &Sender<WorkerResult>,
    stats: &mut WorkerStats,
    state_ctx: &StateCompletionCtx<'_>,
    check_deadlock: bool,
) -> Result<ObservationSignal, CheckError> {
    let mut observer = CompositeObserver::state_completion(check_deadlock);
    let mut env = ParallelObserverEnv::new(ctx, inv_ctx, stop, result_tx, stats);
    observer.observe_state_completion(&mut env, state_ctx)
}
