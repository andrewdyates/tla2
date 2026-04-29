// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::{
    storage::{
        FingerprintSet, InMemoryFingerprintSet, InsertOutcome, ShardedFingerprintSet, StorageFault,
    },
    ExplorationObserver, ParallelObserver, ParallelObserverSummary, PorPropertyClass, PorProvider,
    TransitionSystem,
};
use crossbeam::deque::{Injector, Steal, Stealer, Worker};
use crossbeam::utils::Backoff;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// BFS configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BfsOptions {
    /// Maximum depth to explore. `None` means unbounded.
    pub max_depth: Option<usize>,
    /// Maximum number of unique states to admit. `None` means unbounded.
    pub max_states: Option<usize>,
    /// Property class passed to an optional POR provider.
    pub por_property_class: PorPropertyClass,
}

impl Default for BfsOptions {
    fn default() -> Self {
        Self {
            max_depth: None,
            max_states: None,
            por_property_class: PorPropertyClass::Safety,
        }
    }
}

/// Outcome of a BFS exploration run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BfsOutcome {
    /// Whether the full reachable state space was explored.
    pub completed: bool,
    /// Whether exploration stopped because the observer requested it.
    pub stopped_by_observer: bool,
    /// Whether exploration hit the configured state limit.
    pub state_limit_reached: bool,
    /// Whether exploration skipped successors due to the configured depth limit.
    pub depth_limit_reached: bool,
    /// Number of unique states admitted during this run.
    pub states_discovered: usize,
    /// Number of transitions actually explored after POR filtering.
    pub transitions_explored: usize,
    /// Number of deadlock states observed.
    pub deadlocks_observed: usize,
    /// Maximum BFS depth reached by an explored state.
    pub max_depth_reached: usize,
}

impl Default for BfsOutcome {
    fn default() -> Self {
        Self {
            completed: true,
            stopped_by_observer: false,
            state_limit_reached: false,
            depth_limit_reached: false,
            states_discovered: 0,
            transitions_explored: 0,
            deadlocks_observed: 0,
            max_depth_reached: 0,
        }
    }
}

/// BFS exploration failure.
#[derive(Debug, thiserror::Error)]
pub enum BfsError {
    /// Fingerprint storage reported a backend fault.
    #[error(transparent)]
    StorageFault(#[from] StorageFault),
    /// Depth arithmetic overflowed `usize`.
    #[error("BFS depth overflow at depth {depth}")]
    DepthOverflow {
        /// Depth that could not be incremented.
        depth: usize,
    },
}

/// Explore a transition system with default options and in-memory dedup storage.
pub fn explore_bfs<TS, O>(system: &TS, observer: &mut O) -> Result<BfsOutcome, BfsError>
where
    TS: TransitionSystem,
    TS::Action: PartialEq,
    O: ExplorationObserver<TS>,
{
    explore_bfs_with_options(system, observer, &BfsOptions::default())
}

/// Explore a transition system with explicit options and in-memory dedup storage.
pub fn explore_bfs_with_options<TS, O>(
    system: &TS,
    observer: &mut O,
    options: &BfsOptions,
) -> Result<BfsOutcome, BfsError>
where
    TS: TransitionSystem,
    TS::Action: PartialEq,
    O: ExplorationObserver<TS>,
{
    let storage = InMemoryFingerprintSet::default();
    explore_bfs_with_storage(system, observer, &storage, options, None)
}

/// Explore a transition system with default options and sharded parallel storage.
pub fn explore_bfs_parallel<TS, O>(
    system: &TS,
    observer: &mut O,
    workers: usize,
) -> Result<BfsOutcome, BfsError>
where
    TS: TransitionSystem,
    TS::Action: PartialEq,
    O: ParallelObserver<TS>,
{
    explore_bfs_parallel_with_options(system, observer, &BfsOptions::default(), None, workers)
}

/// Explore a transition system in parallel with explicit options and sharded storage.
pub fn explore_bfs_parallel_with_options<TS, O>(
    system: &TS,
    observer: &mut O,
    options: &BfsOptions,
    por: Option<&dyn PorProvider<TS>>,
    workers: usize,
) -> Result<BfsOutcome, BfsError>
where
    TS: TransitionSystem,
    TS::Action: PartialEq,
    O: ParallelObserver<TS>,
{
    let storage = ShardedFingerprintSet::default();
    explore_bfs_parallel_with_storage(system, observer, &storage, options, por, workers)
}

/// Explore a transition system with caller-provided dedup storage and optional POR.
pub fn explore_bfs_with_storage<TS, O, FS>(
    system: &TS,
    observer: &mut O,
    storage: &FS,
    options: &BfsOptions,
    por: Option<&dyn PorProvider<TS>>,
) -> Result<BfsOutcome, BfsError>
where
    TS: TransitionSystem,
    TS::Action: PartialEq,
    O: ExplorationObserver<TS>,
    FS: FingerprintSet<TS::Fingerprint>,
{
    let mut queue = VecDeque::new();
    let mut outcome = BfsOutcome::default();

    for state in system.initial_states() {
        if observer.is_done() {
            outcome.stopped_by_observer = true;
            break;
        }

        let keep_going = admit_state(
            system,
            observer,
            storage,
            &mut queue,
            state,
            0,
            options,
            &mut outcome,
        )?;

        if !keep_going {
            outcome.stopped_by_observer = true;
            break;
        }

        if outcome.state_limit_reached {
            break;
        }
    }

    while let Some((state, depth)) = queue.pop_front() {
        if outcome.state_limit_reached {
            break;
        }

        outcome.max_depth_reached = outcome.max_depth_reached.max(depth);

        if observer.is_done() {
            outcome.stopped_by_observer = true;
            break;
        }

        if options
            .max_depth
            .is_some_and(|max_depth| depth >= max_depth)
        {
            outcome.depth_limit_reached = true;
            continue;
        }

        let all_successors = system.successors(&state);
        if all_successors.is_empty() {
            outcome.deadlocks_observed += 1;
            observer.on_deadlock(&state);
            if observer.is_done() {
                outcome.stopped_by_observer = true;
                break;
            }
            continue;
        }

        let selected_actions = select_reduced_actions(&state, &all_successors, por, options);
        for (action, next_state) in all_successors {
            if let Some(ref selected) = selected_actions {
                if !selected.iter().any(|candidate| candidate == &action) {
                    continue;
                }
            }

            outcome.transitions_explored += 1;
            if !observer.on_transition(&action, &state, &next_state) {
                outcome.stopped_by_observer = true;
                break;
            }

            let next_depth = depth
                .checked_add(1)
                .ok_or(BfsError::DepthOverflow { depth })?;

            if !admit_state(
                system,
                observer,
                storage,
                &mut queue,
                next_state,
                next_depth,
                options,
                &mut outcome,
            )? {
                outcome.stopped_by_observer = true;
                break;
            }

            if outcome.state_limit_reached {
                break;
            }
        }

        if outcome.stopped_by_observer || outcome.state_limit_reached {
            break;
        }
    }

    outcome.completed = !outcome.stopped_by_observer
        && !outcome.state_limit_reached
        && !outcome.depth_limit_reached;

    Ok(outcome)
}

/// Explore a transition system in parallel with caller-provided dedup storage and optional POR.
pub fn explore_bfs_parallel_with_storage<TS, O, FS>(
    system: &TS,
    observer: &mut O,
    storage: &FS,
    options: &BfsOptions,
    por: Option<&dyn PorProvider<TS>>,
    workers: usize,
) -> Result<BfsOutcome, BfsError>
where
    TS: TransitionSystem,
    TS::Action: PartialEq,
    O: ParallelObserver<TS>,
    FS: FingerprintSet<TS::Fingerprint>,
{
    if workers <= 1 {
        return explore_bfs_with_storage(system, observer, storage, options, por);
    }

    let injector = Injector::new();
    let admitted = AtomicUsize::new(0);
    let stop = AtomicBool::new(false);
    let stopped_by_observer = AtomicBool::new(false);
    let state_limit_reached = AtomicBool::new(false);
    let depth_limit_reached = AtomicBool::new(false);
    let in_flight = AtomicUsize::new(0);

    let mut bootstrap_summary = observer.new_summary();
    let mut bootstrap_work_delta: isize = 0;
    for state in system.initial_states() {
        if stop.load(Ordering::Acquire) {
            break;
        }
        admit_parallel_state(
            system,
            storage,
            options,
            &admitted,
            &state_limit_reached,
            &stop,
            &stopped_by_observer,
            &in_flight,
            &injector,
            None,
            &mut bootstrap_summary,
            &mut bootstrap_work_delta,
            state,
            0,
        )?;
    }
    // Flush bootstrap delta so workers see accurate in_flight count at start.
    flush_work_delta(&mut bootstrap_work_delta, &in_flight);

    if bootstrap_summary.stop_requested() {
        stopped_by_observer.store(true, Ordering::Release);
        stop.store(true, Ordering::Release);
    }

    let local_queues: Vec<Worker<(TS::State, usize)>> =
        (0..workers).map(|_| Worker::new_fifo()).collect();
    let stealers: Vec<Stealer<(TS::State, usize)>> =
        local_queues.iter().map(Worker::stealer).collect();
    let mut summaries: Vec<Option<O::Summary>> =
        (0..workers).map(|_| Some(observer.new_summary())).collect();
    let mut worker_results = Vec::with_capacity(workers);

    std::thread::scope(|scope| -> Result<(), BfsError> {
        let mut handles = Vec::with_capacity(workers);
        for (worker_id, local_queue) in local_queues.into_iter().enumerate() {
            let summary = summaries[worker_id]
                .take()
                .expect("parallel BFS worker summary should exist");
            let injector_ref = &injector;
            let stealers_ref = &stealers;
            let admitted_ref = &admitted;
            let stop_ref = &stop;
            let stopped_by_observer_ref = &stopped_by_observer;
            let state_limit_reached_ref = &state_limit_reached;
            let depth_limit_reached_ref = &depth_limit_reached;
            let in_flight_ref = &in_flight;
            handles.push(scope.spawn(move || {
                run_parallel_worker::<TS, O, FS>(
                    worker_id,
                    system,
                    options,
                    por,
                    storage,
                    injector_ref,
                    &local_queue,
                    stealers_ref,
                    admitted_ref,
                    stop_ref,
                    stopped_by_observer_ref,
                    state_limit_reached_ref,
                    depth_limit_reached_ref,
                    in_flight_ref,
                    summary,
                )
            }));
        }

        for handle in handles {
            worker_results.push(
                handle
                    .join()
                    .expect("parallel BFS worker should not panic")?,
            );
        }

        Ok(())
    })?;

    let mut outcome = BfsOutcome {
        stopped_by_observer: stopped_by_observer.load(Ordering::Acquire),
        state_limit_reached: state_limit_reached.load(Ordering::Acquire),
        depth_limit_reached: depth_limit_reached.load(Ordering::Acquire),
        states_discovered: admitted.load(Ordering::Acquire),
        ..BfsOutcome::default()
    };

    observer.merge_summary(bootstrap_summary);
    for result in worker_results {
        outcome.transitions_explored += result.outcome.transitions_explored;
        outcome.deadlocks_observed += result.outcome.deadlocks_observed;
        outcome.max_depth_reached = outcome
            .max_depth_reached
            .max(result.outcome.max_depth_reached);
        observer.merge_summary(result.summary);
    }

    outcome.completed = !outcome.stopped_by_observer
        && !outcome.state_limit_reached
        && !outcome.depth_limit_reached;

    Ok(outcome)
}

fn admit_state<TS, O, FS>(
    system: &TS,
    observer: &mut O,
    storage: &FS,
    queue: &mut VecDeque<(TS::State, usize)>,
    state: TS::State,
    depth: usize,
    options: &BfsOptions,
    outcome: &mut BfsOutcome,
) -> Result<bool, BfsError>
where
    TS: TransitionSystem,
    O: ExplorationObserver<TS>,
    FS: FingerprintSet<TS::Fingerprint>,
{
    let fingerprint = system.fingerprint(&state);
    match storage.insert_checked(fingerprint) {
        InsertOutcome::AlreadyPresent => return Ok(true),
        InsertOutcome::Inserted => {}
        InsertOutcome::StorageFault(fault) => return Err(fault.into()),
    }

    if options
        .max_states
        .is_some_and(|limit| outcome.states_discovered >= limit)
    {
        outcome.state_limit_reached = true;
        return Ok(true);
    }

    outcome.states_discovered += 1;
    if !observer.on_new_state(&state) {
        return Ok(false);
    }

    queue.push_back((state, depth));
    Ok(true)
}

fn select_reduced_actions<TS>(
    state: &TS::State,
    successors: &[(TS::Action, TS::State)],
    por: Option<&dyn PorProvider<TS>>,
    options: &BfsOptions,
) -> Option<Vec<TS::Action>>
where
    TS: TransitionSystem,
    TS::Action: PartialEq,
{
    let provider = por?;
    let mut enabled_actions = Vec::with_capacity(successors.len());
    for (action, _) in successors {
        if !enabled_actions.iter().any(|existing| existing == action) {
            enabled_actions.push(action.clone());
        }
    }
    Some(provider.reduce(state, &enabled_actions, options.por_property_class))
}

#[derive(Default)]
struct ParallelOutcome {
    transitions_explored: usize,
    deadlocks_observed: usize,
    max_depth_reached: usize,
}

struct ParallelWorkerResult<S> {
    summary: S,
    outcome: ParallelOutcome,
}

#[allow(clippy::too_many_arguments)]
fn run_parallel_worker<TS, O, FS>(
    worker_id: usize,
    system: &TS,
    options: &BfsOptions,
    por: Option<&dyn PorProvider<TS>>,
    storage: &FS,
    injector: &Injector<(TS::State, usize)>,
    local_queue: &Worker<(TS::State, usize)>,
    stealers: &[Stealer<(TS::State, usize)>],
    admitted: &AtomicUsize,
    stop: &AtomicBool,
    stopped_by_observer: &AtomicBool,
    state_limit_reached: &AtomicBool,
    depth_limit_reached: &AtomicBool,
    in_flight: &AtomicUsize,
    mut summary: O::Summary,
) -> Result<ParallelWorkerResult<O::Summary>, BfsError>
where
    TS: TransitionSystem,
    TS::Action: PartialEq,
    O: ParallelObserver<TS>,
    FS: FingerprintSet<TS::Fingerprint>,
{
    let mut outcome = ParallelOutcome::default();
    let backoff = Backoff::new();
    let mut steal_cursor: usize = (worker_id + 1) % stealers.len().max(1);
    let mut local_work_delta: isize = 0;

    loop {
        let Some((state, depth)) = pop_work_item(
            local_queue,
            injector,
            stealers,
            worker_id,
            &mut steal_cursor,
        ) else {
            // Flush any pending delta before checking termination so the
            // shared counter accurately reflects global work remaining.
            if stop.load(Ordering::Acquire)
                || (flush_work_delta(&mut local_work_delta, in_flight)
                    && in_flight.load(Ordering::Acquire) == 0)
            {
                break;
            }
            backoff.snooze();
            continue;
        };
        backoff.reset();

        if stop.load(Ordering::Acquire) {
            record_state_completion(&mut local_work_delta, in_flight);
            continue;
        }

        outcome.max_depth_reached = outcome.max_depth_reached.max(depth);

        if options
            .max_depth
            .is_some_and(|max_depth| depth >= max_depth)
        {
            depth_limit_reached.store(true, Ordering::Release);
            record_state_completion(&mut local_work_delta, in_flight);
            continue;
        }

        let all_successors = system.successors(&state);
        if all_successors.is_empty() {
            outcome.deadlocks_observed += 1;
            summary.on_deadlock(&state);
            if summary.stop_requested() {
                stopped_by_observer.store(true, Ordering::Release);
                stop.store(true, Ordering::Release);
            }
            record_state_completion(&mut local_work_delta, in_flight);
            continue;
        }

        let selected_actions = select_reduced_actions(&state, &all_successors, por, options);
        for (action, next_state) in all_successors {
            if stop.load(Ordering::Acquire) {
                break;
            }
            if let Some(ref selected) = selected_actions {
                if !selected.iter().any(|candidate| candidate == &action) {
                    continue;
                }
            }

            outcome.transitions_explored += 1;
            summary.on_transition(&action, &state, &next_state);
            if summary.stop_requested() {
                stopped_by_observer.store(true, Ordering::Release);
                stop.store(true, Ordering::Release);
                break;
            }

            let next_depth = match depth.checked_add(1) {
                Some(next_depth) => next_depth,
                None => {
                    flush_work_delta(&mut local_work_delta, in_flight);
                    stop.store(true, Ordering::Release);
                    return Err(BfsError::DepthOverflow { depth });
                }
            };

            if let Err(error) = admit_parallel_state(
                system,
                storage,
                options,
                admitted,
                state_limit_reached,
                stop,
                stopped_by_observer,
                in_flight,
                injector,
                Some(local_queue),
                &mut summary,
                &mut local_work_delta,
                next_state,
                next_depth,
            ) {
                flush_work_delta(&mut local_work_delta, in_flight);
                stop.store(true, Ordering::Release);
                return Err(error);
            }
        }

        record_state_completion(&mut local_work_delta, in_flight);
    }

    // Flush any remaining delta before returning so the shared counter is
    // accurate for post-BFS termination checks.
    flush_work_delta(&mut local_work_delta, in_flight);

    Ok(ParallelWorkerResult { summary, outcome })
}

#[allow(clippy::too_many_arguments)]
fn admit_parallel_state<TS, FS, S>(
    system: &TS,
    storage: &FS,
    options: &BfsOptions,
    admitted: &AtomicUsize,
    state_limit_reached: &AtomicBool,
    stop: &AtomicBool,
    stopped_by_observer: &AtomicBool,
    in_flight: &AtomicUsize,
    injector: &Injector<(TS::State, usize)>,
    local_queue: Option<&Worker<(TS::State, usize)>>,
    summary: &mut S,
    local_work_delta: &mut isize,
    state: TS::State,
    depth: usize,
) -> Result<(), BfsError>
where
    TS: TransitionSystem,
    FS: FingerprintSet<TS::Fingerprint>,
    S: ParallelObserverSummary<TS>,
{
    let fingerprint = system.fingerprint(&state);
    match storage.insert_checked(fingerprint) {
        InsertOutcome::AlreadyPresent => return Ok(()),
        InsertOutcome::Inserted => {}
        InsertOutcome::StorageFault(fault) => return Err(fault.into()),
    }

    if let Some(limit) = options.max_states {
        if admitted
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |count| {
                (count < limit).then_some(count + 1)
            })
            .is_err()
        {
            state_limit_reached.store(true, Ordering::Release);
            stop.store(true, Ordering::Release);
            return Ok(());
        }
    } else {
        admitted.fetch_add(1, Ordering::AcqRel);
    }

    summary.on_new_state(&state);
    if summary.stop_requested() {
        stopped_by_observer.store(true, Ordering::Release);
        stop.store(true, Ordering::Release);
        return Ok(());
    }

    record_state_admission(local_work_delta, in_flight);
    if let Some(local_queue) = local_queue {
        local_queue.push((state, depth));
    } else {
        injector.push((state, depth));
    }
    Ok(())
}

/// Batch size for in_flight counter updates.
/// Updating in_flight atomically every state causes cache-line bouncing.
/// Batching locally and flushing periodically reduces contention.
const WORK_BATCH_SIZE: usize = 256;

/// Flush a worker's batched work delta into the shared in_flight counter.
///
/// Returns true when `in_flight` is zero after the flush, indicating
/// potential termination.
#[inline]
fn flush_work_delta(delta: &mut isize, in_flight: &AtomicUsize) -> bool {
    if *delta == 0 {
        return in_flight.load(Ordering::Acquire) == 0;
    }
    if *delta > 0 {
        in_flight.fetch_add(*delta as usize, Ordering::AcqRel);
    } else {
        // Saturating subtraction via CAS loop to avoid underflow.
        let sub_amount = (-*delta) as usize;
        loop {
            let current = in_flight.load(Ordering::Acquire);
            let new_value = current.saturating_sub(sub_amount);
            match in_flight.compare_exchange_weak(
                current,
                new_value,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => {}
            }
        }
    }
    *delta = 0;
    in_flight.load(Ordering::Acquire) == 0
}

/// Record one state completion in the local work delta, flushing to the
/// shared counter when the batch threshold is reached.
#[inline]
fn record_state_completion(delta: &mut isize, in_flight: &AtomicUsize) {
    *delta -= 1;
    if *delta <= -(WORK_BATCH_SIZE as isize) {
        flush_work_delta(delta, in_flight);
    }
}

/// Record one state admission in the local work delta, flushing to the
/// shared counter when the batch threshold is reached.
#[inline]
fn record_state_admission(delta: &mut isize, in_flight: &AtomicUsize) {
    *delta += 1;
    if *delta >= WORK_BATCH_SIZE as isize {
        flush_work_delta(delta, in_flight);
    }
}

/// Pop work from local queue first, then steal from injector, then from peers.
///
/// Peer steals use `steal_batch_and_pop` to amortize the sync cost across
/// several follow-on local pops, and a rotated `steal_cursor` to distribute
/// steal traffic across victims instead of hot-spotting on the same peer.
fn pop_work_item<T>(
    local_queue: &Worker<T>,
    injector: &Injector<T>,
    stealers: &[Stealer<T>],
    worker_id: usize,
    steal_cursor: &mut usize,
) -> Option<T> {
    if let Some(item) = local_queue.pop() {
        return Some(item);
    }

    // Try to steal from global injector.
    loop {
        match injector.steal_batch_and_pop(local_queue) {
            Steal::Success(item) => return Some(item),
            Steal::Empty => break,
            Steal::Retry => {}
        }
    }

    // Try to steal from other workers with rotated victim selection.
    // Each worker starts probing from its own cursor position and wraps around,
    // skipping its own deque. The cursor advances after each attempt to
    // distribute steal traffic across victims.
    let len = stealers.len();
    if len > 1 {
        let start = *steal_cursor % len;
        for offset in 0..len {
            let idx = (start + offset) % len;
            if idx == worker_id {
                continue;
            }
            loop {
                match stealers[idx].steal_batch_and_pop(local_queue) {
                    Steal::Success(item) => {
                        *steal_cursor = (idx + 1) % len;
                        return Some(item);
                    }
                    Steal::Empty => break,
                    Steal::Retry => {}
                }
            }
        }
        // All victims empty — advance cursor so next poll starts elsewhere.
        *steal_cursor = (start + 1) % len;
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompositeObserver, ExplorationObserver, FingerprintSet, NoopObserver, ParallelObserver,
        ParallelObserverSummary, StorageFault,
    };
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Action {
        Left,
        Right,
        Step,
    }

    struct DiamondSystem;

    impl TransitionSystem for DiamondSystem {
        type State = u8;
        type Action = Action;
        type Fingerprint = u8;

        fn initial_states(&self) -> Vec<Self::State> {
            vec![0, 0]
        }

        fn successors(&self, state: &Self::State) -> Vec<(Self::Action, Self::State)> {
            match *state {
                0 => vec![(Action::Left, 1), (Action::Right, 2)],
                1 => vec![(Action::Step, 3)],
                2 => vec![(Action::Step, 3)],
                _ => Vec::new(),
            }
        }

        fn fingerprint(&self, state: &Self::State) -> Self::Fingerprint {
            *state
        }
    }

    struct StopAtState {
        stop_at: u8,
        stopped: bool,
    }

    impl ExplorationObserver<DiamondSystem> for StopAtState {
        fn on_new_state(&mut self, state: &u8) -> bool {
            if *state == self.stop_at {
                self.stopped = true;
                false
            } else {
                true
            }
        }

        fn on_transition(&mut self, _action: &Action, _from: &u8, _to: &u8) -> bool {
            true
        }

        fn on_deadlock(&mut self, _state: &u8) {}

        fn is_done(&self) -> bool {
            self.stopped
        }
    }

    #[derive(Default)]
    struct DeadlockCounter {
        deadlocks: usize,
    }

    impl ExplorationObserver<DiamondSystem> for DeadlockCounter {
        fn on_new_state(&mut self, _state: &u8) -> bool {
            true
        }

        fn on_transition(&mut self, _action: &Action, _from: &u8, _to: &u8) -> bool {
            true
        }

        fn on_deadlock(&mut self, _state: &u8) {
            self.deadlocks += 1;
        }

        fn is_done(&self) -> bool {
            false
        }
    }

    #[derive(Default)]
    struct StateCounter {
        states: usize,
    }

    impl ExplorationObserver<DiamondSystem> for StateCounter {
        fn on_new_state(&mut self, _state: &u8) -> bool {
            self.states += 1;
            true
        }

        fn on_transition(&mut self, _action: &Action, _from: &u8, _to: &u8) -> bool {
            true
        }

        fn on_deadlock(&mut self, _state: &u8) {}

        fn is_done(&self) -> bool {
            false
        }
    }

    struct LeftOnlyPor;

    impl PorProvider<DiamondSystem> for LeftOnlyPor {
        fn reduce(
            &self,
            _state: &u8,
            enabled: &[Action],
            _property: PorPropertyClass,
        ) -> Vec<Action> {
            enabled
                .iter()
                .copied()
                .filter(|action| *action != Action::Right)
                .collect()
        }
    }

    struct FaultyStorage {
        insert_calls: AtomicUsize,
    }

    impl FingerprintSet<u8> for FaultyStorage {
        fn insert_checked(&self, _fingerprint: u8) -> InsertOutcome {
            self.insert_calls.fetch_add(1, Ordering::Relaxed);
            InsertOutcome::StorageFault(StorageFault::new("test", "insert", "synthetic failure"))
        }

        fn contains_checked(&self, _fingerprint: u8) -> crate::LookupOutcome {
            crate::LookupOutcome::Absent
        }

        fn len(&self) -> usize {
            0
        }
    }

    #[derive(Default)]
    struct ParallelCounterObserver {
        states: usize,
        transitions: usize,
        deadlocks: usize,
        merged_summaries: usize,
    }

    impl ExplorationObserver<DiamondSystem> for ParallelCounterObserver {
        fn on_new_state(&mut self, _state: &u8) -> bool {
            self.states += 1;
            true
        }

        fn on_transition(&mut self, _action: &Action, _from: &u8, _to: &u8) -> bool {
            self.transitions += 1;
            true
        }

        fn on_deadlock(&mut self, _state: &u8) {
            self.deadlocks += 1;
        }

        fn is_done(&self) -> bool {
            false
        }
    }

    #[derive(Default)]
    struct ParallelCounterSummary {
        states: usize,
        transitions: usize,
        deadlocks: usize,
    }

    impl ParallelObserverSummary<DiamondSystem> for ParallelCounterSummary {
        fn on_new_state(&mut self, _state: &u8) {
            self.states += 1;
        }

        fn on_transition(&mut self, _action: &Action, _from: &u8, _to: &u8) {
            self.transitions += 1;
        }

        fn on_deadlock(&mut self, _state: &u8) {
            self.deadlocks += 1;
        }
    }

    impl ParallelObserver<DiamondSystem> for ParallelCounterObserver {
        type Summary = ParallelCounterSummary;

        fn new_summary(&self) -> Self::Summary {
            ParallelCounterSummary::default()
        }

        fn merge_summary(&mut self, summary: Self::Summary) {
            self.merged_summaries += 1;
            self.states += summary.states;
            self.transitions += summary.transitions;
            self.deadlocks += summary.deadlocks;
        }
    }

    #[test]
    fn bfs_discovers_unique_states_and_deadlocks() {
        let mut observer = DeadlockCounter::default();
        let outcome = explore_bfs(&DiamondSystem, &mut observer).expect("BFS should succeed");

        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 4);
        assert_eq!(outcome.transitions_explored, 4);
        assert_eq!(outcome.deadlocks_observed, 1);
        assert_eq!(observer.deadlocks, 1);
    }

    #[test]
    fn bfs_initial_duplicates_only_notify_once() {
        let mut observer = StateCounter::default();
        let outcome = explore_bfs(&DiamondSystem, &mut observer).expect("BFS should succeed");

        assert!(outcome.completed);
        assert_eq!(observer.states, 4);
    }

    #[test]
    fn bfs_stops_when_observer_requests_termination() {
        let mut observer = StopAtState {
            stop_at: 2,
            stopped: false,
        };
        let outcome = explore_bfs(&DiamondSystem, &mut observer).expect("BFS should succeed");

        assert!(!outcome.completed);
        assert!(outcome.stopped_by_observer);
        assert_eq!(outcome.states_discovered, 3);
    }

    #[test]
    fn bfs_honors_depth_limit() {
        let mut observer = NoopObserver::<DiamondSystem>::default();
        let outcome = explore_bfs_with_options(
            &DiamondSystem,
            &mut observer,
            &BfsOptions {
                max_depth: Some(1),
                ..BfsOptions::default()
            },
        )
        .expect("BFS should succeed");

        assert!(!outcome.completed);
        assert!(outcome.depth_limit_reached);
        assert_eq!(outcome.states_discovered, 3);
    }

    #[test]
    fn bfs_honors_state_limit() {
        let mut observer = NoopObserver::<DiamondSystem>::default();
        let outcome = explore_bfs_with_options(
            &DiamondSystem,
            &mut observer,
            &BfsOptions {
                max_states: Some(2),
                ..BfsOptions::default()
            },
        )
        .expect("BFS should succeed");

        assert!(!outcome.completed);
        assert!(outcome.state_limit_reached);
        assert_eq!(outcome.states_discovered, 2);
    }

    #[test]
    fn bfs_can_filter_actions_with_por_provider() {
        let mut observer = NoopObserver::<DiamondSystem>::default();
        let storage = InMemoryFingerprintSet::default();
        let outcome = explore_bfs_with_storage(
            &DiamondSystem,
            &mut observer,
            &storage,
            &BfsOptions::default(),
            Some(&LeftOnlyPor),
        )
        .expect("BFS should succeed");

        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 3);
        assert_eq!(outcome.transitions_explored, 2);
        assert_eq!(outcome.deadlocks_observed, 1);
    }

    #[test]
    fn bfs_propagates_storage_faults() {
        let mut observer = NoopObserver::<DiamondSystem>::default();
        let storage = FaultyStorage {
            insert_calls: AtomicUsize::new(0),
        };
        let error = explore_bfs_with_storage(
            &DiamondSystem,
            &mut observer,
            &storage,
            &BfsOptions::default(),
            None,
        )
        .expect_err("storage fault should be surfaced");

        assert!(matches!(error, BfsError::StorageFault(_)));
        assert_eq!(storage.insert_calls.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn parallel_bfs_discovers_unique_states_and_deadlocks() {
        let mut observer = ParallelCounterObserver::default();
        let outcome =
            explore_bfs_parallel(&DiamondSystem, &mut observer, 4).expect("parallel BFS succeeds");

        assert!(outcome.completed);
        assert_eq!(outcome.states_discovered, 4);
        assert_eq!(outcome.transitions_explored, 4);
        assert_eq!(outcome.deadlocks_observed, 1);
        assert_eq!(observer.states, 4);
        assert_eq!(observer.transitions, 4);
        assert_eq!(observer.deadlocks, 1);
        assert!(observer.merged_summaries > 0);
    }

    #[test]
    fn parallel_bfs_honors_state_limit_exactly() {
        let mut observer = ParallelCounterObserver::default();
        let outcome = explore_bfs_parallel_with_options(
            &DiamondSystem,
            &mut observer,
            &BfsOptions {
                max_states: Some(2),
                ..BfsOptions::default()
            },
            None,
            4,
        )
        .expect("parallel BFS succeeds");

        assert!(!outcome.completed);
        assert!(outcome.state_limit_reached);
        assert_eq!(outcome.states_discovered, 2);
        assert_eq!(observer.states, 2);
    }

    #[test]
    fn composite_observer_chains_callbacks() {
        let mut composite = CompositeObserver::<DiamondSystem>::new();
        composite.push(Box::new(DeadlockCounter::default()));
        composite.push(Box::new(NoopObserver::<DiamondSystem>::default()));

        let outcome = explore_bfs(&DiamondSystem, &mut composite).expect("BFS should succeed");
        assert!(outcome.completed);
        assert_eq!(composite.len(), 2);
    }
}
