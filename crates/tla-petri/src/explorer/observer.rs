// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::VecDeque;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Instant;

use tla_mc_core::{
    explore_bfs_parallel_with_options, explore_bfs_parallel_with_storage, BfsOptions,
    ExplorationObserver as CoreExplorationObserver, FingerprintSet, InsertOutcome,
    LookupOutcome as CoreLookupOutcome, ParallelObserver as CoreParallelObserver,
    ParallelObserverSummary as CoreParallelObserverSummary, PartitionedCasFingerprintSet,
    PorPropertyClass, PorProvider, StorageStats,
};

use super::adaptive::{analyze_observer_parallelism, Strategy};
use super::fingerprint::fingerprint_marking;
use super::seen::{LocalSeenSet, LookupOutcome};
use super::transition_selection::enabled_transitions_into;

use crate::marking::{pack_marking_config, unpack_marking_config};
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::stubborn::{DependencyGraph, PorStrategy};
use crate::system::{CompactMarking, PetriNetSystem, StubbornPorProvider};

use super::config::{
    ExplorationConfig, ExplorationObserver, ExplorationResult, FpsetBackend,
    ParallelExplorationObserver, ParallelExplorationSummary, StorageMode, DEADLINE_CHECK_INTERVAL,
};
use super::fingerprint_only::explore_fingerprint_only;
use super::setup::ExplorationSetup;

/// BFS exploration of the Petri net state space.
///
/// Explores reachable markings breadth-first, deduplicating with FxHashSet.
/// Uses compact marking storage (u8/u16/u64 per token) based on structural
/// analysis of the net, up to 8x memory savings for token-conserving nets
/// with small totals (common in MCC models). The observer receives full u64
/// markings regardless of internal storage width.
///
/// Transition firing uses delta-based mutation: O(arcs) per firing instead
/// of O(places) for copying the full marking. For typical MCC nets with
/// 100-1000 places and 2-6 arcs per transition, this is 20-500x less work.
pub(crate) fn explore(
    net: &PetriNet,
    config: &ExplorationConfig,
    observer: &mut dyn ExplorationObserver,
) -> ExplorationResult {
    let ExplorationSetup {
        marking_config,
        pack_capacity,
        num_places,
        num_transitions,
        initial_packed,
    } = ExplorationSetup::analyze(net);

    let dep_graph = match &config.por_strategy {
        PorStrategy::None => None,
        _ => Some(DependencyGraph::build(net)),
    };

    let mut visited = LocalSeenSet::new();
    let mut queue: VecDeque<Box<[u8]>> = VecDeque::new();

    if !observer.on_new_state(&net.initial_marking) {
        return ExplorationResult::new(false, 1, true);
    }
    visited.insert_checked(fingerprint_marking(&initial_packed));
    queue.push_back(initial_packed);

    let mut stopped_by_observer = false;
    let mut current_tokens = Vec::with_capacity(num_places);
    let mut deadline_counter: u32 = 0;
    let mut pack_buf = Vec::with_capacity(pack_capacity);
    let mut enabled_transitions = Vec::with_capacity(num_transitions);

    while let Some(current_packed) = queue.pop_front() {
        deadline_counter = deadline_counter.wrapping_add(1);
        if deadline_counter.is_multiple_of(DEADLINE_CHECK_INTERVAL)
            && config
                .deadline()
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return ExplorationResult::new(false, visited.len(), false);
        }

        if observer.is_done() {
            stopped_by_observer = true;
            break;
        }

        unpack_marking_config(&current_packed, &marking_config, &mut current_tokens);

        enabled_transitions_into(
            net,
            &current_tokens,
            num_transitions,
            dep_graph.as_ref(),
            &config.por_strategy,
            &mut enabled_transitions,
        );

        let has_enabled = !enabled_transitions.is_empty();

        for &trans in &enabled_transitions {
            net.apply_delta(&mut current_tokens, trans);

            if !observer.on_transition_fire(trans) {
                stopped_by_observer = true;
                break;
            }

            pack_marking_config(&current_tokens, &marking_config, &mut pack_buf);
            let fp = fingerprint_marking(&pack_buf);
            if visited.contains_checked(&fp) == LookupOutcome::Present {
                net.undo_delta(&mut current_tokens, trans);
                continue;
            }

            if visited.len() >= config.max_states() {
                return ExplorationResult::new(false, visited.len(), false);
            }

            if !observer.on_new_state(&current_tokens) {
                stopped_by_observer = true;
                break;
            }

            visited.insert_checked(fp);
            let packed: Box<[u8]> = pack_buf.as_slice().into();
            queue.push_back(packed);

            net.undo_delta(&mut current_tokens, trans);
        }

        if stopped_by_observer {
            break;
        }

        if !has_enabled {
            observer.on_deadlock(&current_tokens);
            if observer.is_done() {
                stopped_by_observer = true;
                break;
            }
        }
    }

    ExplorationResult::new(
        !stopped_by_observer && queue.is_empty(),
        visited.len(),
        stopped_by_observer,
    )
}

/// Observer-mode exploration dispatcher.
///
/// Routes to:
/// - [`explore_fingerprint_only`] when `StorageMode::FingerprintOnly` (8 bytes/state),
/// - the sequential [`explore`] when `config.workers() == 1`,
/// - or runs a small pilot to choose between sequential execution and an explicit
///   parallel worker count capped by `config.workers()`.
pub(crate) fn explore_observer<O>(
    net: &PetriNet,
    config: &ExplorationConfig,
    observer: &mut O,
) -> ExplorationResult
where
    O: ParallelExplorationObserver + Send,
{
    // Fingerprint-only mode bypasses the normal BFS path entirely.
    if config.storage_mode() == StorageMode::FingerprintOnly {
        let trace_dir = config.storage_dir().map(|dir| dir.as_path());
        let (result, stats) = explore_fingerprint_only(net, config, observer, trace_dir);
        eprintln!(
            "fingerprint-only: {} states, depth {}, fp_set {}B",
            stats.states_visited, stats.max_depth, stats.fp_set_memory_bytes,
        );
        return result;
    }

    if config.workers() <= 1 {
        if config.diff_successors() {
            return super::diff_bfs::explore_diff(net, config, observer);
        }
        return explore(net, config, observer);
    }

    match analyze_observer_parallelism(net, config).strategy {
        Strategy::Sequential => {
            if config.diff_successors() {
                super::diff_bfs::explore_diff(net, config, observer)
            } else {
                explore(net, config, observer)
            }
        }
        Strategy::Parallel(workers) => {
            explore_observer_parallel_with_workers(net, config, observer, workers)
        }
    }
}

struct PetriSummaryAdapter<S> {
    inner: S,
    system: Arc<PetriNetSystem>,
    scratch: Vec<u64>,
    deadline: Option<Instant>,
    deadline_hit: Arc<AtomicBool>,
    deadline_counter: u32,
}

impl<S> PetriSummaryAdapter<S>
where
    S: ParallelExplorationSummary,
{
    fn new(
        inner: S,
        system: Arc<PetriNetSystem>,
        deadline: Option<Instant>,
        deadline_hit: Arc<AtomicBool>,
    ) -> Self {
        Self {
            inner,
            scratch: Vec::with_capacity(system.net().num_places()),
            system,
            deadline,
            deadline_hit,
            deadline_counter: 0,
        }
    }

    fn tick_deadline(&mut self) {
        if self.deadline_hit.load(Ordering::Acquire) {
            return;
        }

        self.deadline_counter = self.deadline_counter.wrapping_add(1);
        if self
            .deadline_counter
            .is_multiple_of(DEADLINE_CHECK_INTERVAL)
            && self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            self.deadline_hit.store(true, Ordering::Release);
        }
    }

    fn with_marking<R>(
        &mut self,
        state: &CompactMarking,
        f: impl FnOnce(&mut S, &[u64]) -> R,
    ) -> R {
        self.system.unpack_marking_into(state, &mut self.scratch);
        let result = f(&mut self.inner, &self.scratch);
        self.tick_deadline();
        result
    }
}

impl<S> CoreParallelObserverSummary<PetriNetSystem> for PetriSummaryAdapter<S>
where
    S: ParallelExplorationSummary,
{
    fn on_new_state(&mut self, state: &CompactMarking) {
        self.with_marking(state, |inner, marking| inner.on_new_state(marking));
    }

    fn on_transition(
        &mut self,
        action: &TransitionIdx,
        _from: &CompactMarking,
        _to: &CompactMarking,
    ) {
        self.inner.on_transition_fire(*action);
        self.tick_deadline();
    }

    fn on_deadlock(&mut self, state: &CompactMarking) {
        self.with_marking(state, |inner, marking| inner.on_deadlock(marking));
    }

    fn stop_requested(&self) -> bool {
        self.inner.stop_requested() || self.deadline_hit.load(Ordering::Acquire)
    }
}

struct PetriObserverAdapter<'a, O> {
    inner: &'a mut O,
    system: Arc<PetriNetSystem>,
    scratch: Vec<u64>,
    deadline: Option<Instant>,
    deadline_hit: Arc<AtomicBool>,
}

impl<'a, O> PetriObserverAdapter<'a, O>
where
    O: ParallelExplorationObserver,
{
    fn new(
        inner: &'a mut O,
        system: Arc<PetriNetSystem>,
        deadline: Option<Instant>,
        deadline_hit: Arc<AtomicBool>,
    ) -> Self {
        Self {
            inner,
            scratch: Vec::with_capacity(system.net().num_places()),
            system,
            deadline,
            deadline_hit,
        }
    }

    fn with_marking<R>(
        &mut self,
        state: &CompactMarking,
        f: impl FnOnce(&mut O, &[u64]) -> R,
    ) -> R {
        self.system.unpack_marking_into(state, &mut self.scratch);
        f(self.inner, &self.scratch)
    }

    fn deadline_reached(&self) -> bool {
        self.deadline_hit.load(Ordering::Acquire)
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
    }
}

impl<O> CoreExplorationObserver<PetriNetSystem> for PetriObserverAdapter<'_, O>
where
    O: ParallelExplorationObserver + Send,
{
    fn on_new_state(&mut self, state: &CompactMarking) -> bool {
        self.with_marking(state, |inner, marking| inner.on_new_state(marking))
    }

    fn on_transition(
        &mut self,
        action: &TransitionIdx,
        _from: &CompactMarking,
        _to: &CompactMarking,
    ) -> bool {
        self.inner.on_transition_fire(*action)
    }

    fn on_deadlock(&mut self, state: &CompactMarking) {
        self.with_marking(state, |inner, marking| inner.on_deadlock(marking));
    }

    fn is_done(&self) -> bool {
        self.inner.is_done() || self.deadline_reached()
    }
}

impl<O> CoreParallelObserver<PetriNetSystem> for PetriObserverAdapter<'_, O>
where
    O: ParallelExplorationObserver + Send,
{
    type Summary = PetriSummaryAdapter<O::Summary>;

    fn new_summary(&self) -> Self::Summary {
        PetriSummaryAdapter::new(
            self.inner.new_summary(),
            Arc::clone(&self.system),
            self.deadline,
            Arc::clone(&self.deadline_hit),
        )
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        self.inner.merge_summary(summary.inner);
    }
}

/// XOR-fold a u128 fingerprint to u64 for the CAS fingerprint set.
///
/// Combines both halves to preserve entropy. This matches TLC's approach
/// of using 64-bit fingerprints with MSB-partitioned storage.
#[inline]
fn fold_u128_to_u64(fp: u128) -> u64 {
    (fp as u64) ^ ((fp >> 64) as u64)
}

/// Adapter that implements `FingerprintSet<u128>` by XOR-folding to u64 and
/// delegating to a `PartitionedCasFingerprintSet`.
///
/// This allows the generic parallel BFS (which operates on `u128` fingerprints
/// from `PetriNetSystem`) to use the lock-free CAS backend.
struct CasFpsetAdapter {
    inner: PartitionedCasFingerprintSet,
}

impl CasFpsetAdapter {
    fn new(max_states: usize) -> Self {
        // Size the CAS table to ~2x expected state count for good load factor.
        // 4 partition bits = 16 partitions, matching typical worker counts.
        let table_capacity = (max_states * 2).max(4096);
        Self {
            inner: PartitionedCasFingerprintSet::new(4, table_capacity),
        }
    }
}

impl FingerprintSet<u128> for CasFpsetAdapter {
    #[inline]
    fn insert_checked(&self, fingerprint: u128) -> InsertOutcome {
        self.inner.insert_checked(fold_u128_to_u64(fingerprint))
    }

    #[inline]
    fn contains_checked(&self, fingerprint: u128) -> CoreLookupOutcome {
        self.inner.contains_checked(fold_u128_to_u64(fingerprint))
    }

    fn len(&self) -> usize {
        FingerprintSet::len(&self.inner)
    }

    fn stats(&self) -> StorageStats {
        FingerprintSet::stats(&self.inner)
    }
}

fn build_parallel_por(
    net: &PetriNet,
    strategy: &PorStrategy,
) -> (Option<StubbornPorProvider>, PorPropertyClass) {
    match strategy {
        PorStrategy::None => (None, PorPropertyClass::Safety),
        PorStrategy::DeadlockPreserving => (
            Some(StubbornPorProvider::new(net.clone())),
            PorPropertyClass::Deadlock,
        ),
        PorStrategy::SafetyPreserving { visible } => (
            Some(StubbornPorProvider::new(net.clone()).with_visible_transitions(visible.clone())),
            PorPropertyClass::Safety,
        ),
    }
}

fn explore_observer_parallel_with_workers<O>(
    net: &PetriNet,
    config: &ExplorationConfig,
    observer: &mut O,
    workers: usize,
) -> ExplorationResult
where
    O: ParallelExplorationObserver + Send,
{
    let system = Arc::new(PetriNetSystem::new(net.clone()));
    let deadline_hit = Arc::new(AtomicBool::new(false));
    let (por_provider, por_property_class) = build_parallel_por(net, &config.por_strategy);
    let options = BfsOptions {
        max_states: Some(config.max_states()),
        por_property_class,
        ..BfsOptions::default()
    };
    let mut adapter = PetriObserverAdapter::new(
        observer,
        Arc::clone(&system),
        config.deadline(),
        Arc::clone(&deadline_hit),
    );

    let por_ref = por_provider
        .as_ref()
        .map(|provider| provider as &dyn PorProvider<PetriNetSystem>);

    let outcome = match config.fpset_backend() {
        FpsetBackend::Sharded => explore_bfs_parallel_with_options(
            system.as_ref(),
            &mut adapter,
            &options,
            por_ref,
            workers,
        ),
        FpsetBackend::Cas => {
            let storage = CasFpsetAdapter::new(config.max_states());
            explore_bfs_parallel_with_storage(
                system.as_ref(),
                &mut adapter,
                &storage,
                &options,
                por_ref,
                workers,
            )
        }
    }
    .expect("generic parallel Petri exploration should not fail");

    let deadline_reached = deadline_hit.load(Ordering::Acquire);
    ExplorationResult::new(
        !outcome.stopped_by_observer
            && !outcome.state_limit_reached
            && !outcome.depth_limit_reached
            && !deadline_reached,
        outcome.states_discovered,
        outcome.stopped_by_observer && !deadline_reached,
    )
}
