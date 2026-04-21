// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fingerprint-only BFS exploration for Petri nets.
//!
//! Uses a lock-free `CasFingerprintSet` from `tla-mc-core` for state
//! deduplication, storing only a 64-bit fingerprint per seen state instead
//! of a full 128-bit fingerprint in an `FxHashSet`. The BFS queue still
//! carries packed markings (needed to compute successors), but the seen-set
//! is dramatically more memory-efficient for large state spaces.
//!
//! For trace reconstruction on counterexample (e.g., when a deadlock
//! invariant is violated), a disk-based trace log records
//! `(fingerprint, parent_fingerprint, transition_id)` triples that can be
//! walked backward from the violating state to the initial state.
//!
//! Part of #3721.

use std::collections::VecDeque;
use std::io::{BufWriter, Write};
use std::time::Instant;

use tla_mc_core::{CasFingerprintSet, FingerprintSet, InsertOutcome};

use super::config::{
    ExplorationConfig, ExplorationObserver, ExplorationResult, DEADLINE_CHECK_INTERVAL,
};
use super::fingerprint::fingerprint_marking;
use super::setup::ExplorationSetup;
use super::transition_selection::enabled_transitions_into;
use crate::marking::{pack_marking_config, unpack_marking_config};
use crate::petri_net::PetriNet;
use crate::stubborn::{DependencyGraph, PorStrategy};

/// Statistics from fingerprint-only BFS exploration.
#[derive(Debug, Clone)]
pub(crate) struct FingerprintOnlyStats {
    /// Number of unique states visited.
    pub(crate) states_visited: usize,
    /// Maximum BFS depth reached.
    pub(crate) max_depth: usize,
    /// Memory bytes used by the CAS fingerprint set.
    pub(crate) fp_set_memory_bytes: usize,
}

/// Disk-based trace log entry for counterexample reconstruction.
///
/// Each entry is 20 bytes: `(state_fp: u64, parent_fp: u64, transition_id: u32)`.
/// Walk backward from the violating state's fingerprint to the initial state
/// (whose `parent_fp` is 0) to reconstruct the error trace.
#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
struct TraceEntry {
    state_fp: u64,
    parent_fp: u64,
    transition_id: u32,
}

/// Optional disk-based trace logger for counterexample reconstruction.
struct TraceLogger {
    writer: BufWriter<std::fs::File>,
}

impl TraceLogger {
    fn new(path: &std::path::Path) -> std::io::Result<Self> {
        let file = std::fs::File::create(path)?;
        Ok(Self {
            writer: BufWriter::new(file),
        })
    }

    fn log_entry(&mut self, state_fp: u64, parent_fp: u64, transition_id: u32) {
        // Write as raw bytes for compact, fast logging.
        let entry = TraceEntry {
            state_fp,
            parent_fp,
            transition_id,
        };
        let bytes: &[u8] = unsafe {
            std::slice::from_raw_parts(
                &entry as *const TraceEntry as *const u8,
                std::mem::size_of::<TraceEntry>(),
            )
        };
        // Best-effort: trace logging failures are non-fatal.
        let _ = self.writer.write_all(bytes);
    }

    fn flush(&mut self) {
        let _ = self.writer.flush();
    }
}

/// BFS entry carrying packed marking and its precomputed 64-bit fingerprint.
///
/// Trace data (parent fingerprint, transition ID) is logged immediately at
/// successor generation time by `TraceLogger`, so the queue entry only needs
/// the packed marking, fingerprint, and depth for BFS traversal.
struct QueueEntry {
    packed: Box<[u8]>,
    fp: u64,
    depth: usize,
}

/// Fingerprint-only BFS exploration of a Petri net state space.
///
/// Uses a lock-free `CasFingerprintSet` for deduplication, reducing per-state
/// memory from ~32 bytes (FxHashSet<u128>) to 8 bytes (CAS table slot).
/// The BFS queue still carries packed markings for successor computation.
///
/// # Arguments
///
/// * `net` - The Petri net to explore.
/// * `config` - Exploration configuration (max_states, deadline, POR).
/// * `observer` - Observer for state/transition/deadlock callbacks.
/// * `trace_dir` - Optional directory for disk-based trace logging.
///
/// # Returns
///
/// `(ExplorationResult, FingerprintOnlyStats)` with exploration outcome and
/// memory usage statistics.
pub(crate) fn explore_fingerprint_only(
    net: &PetriNet,
    config: &ExplorationConfig,
    observer: &mut dyn ExplorationObserver,
    trace_dir: Option<&std::path::Path>,
) -> (ExplorationResult, FingerprintOnlyStats) {
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

    // Size the CAS table to ~2x the expected state count for good load factor.
    let table_capacity = (config.max_states() * 2).max(4096);
    let fp_set = CasFingerprintSet::new(table_capacity);

    let mut trace_logger = trace_dir.and_then(|dir| {
        std::fs::create_dir_all(dir).ok()?;
        let path = dir.join("trace.bin");
        TraceLogger::new(&path).ok()
    });

    let mut queue: VecDeque<QueueEntry> = VecDeque::new();
    let mut max_depth: usize = 0;

    // Compute initial fingerprint (truncated to u64 for CAS table).
    let initial_fp128 = fingerprint_marking(&initial_packed);
    let initial_fp = initial_fp128 as u64;

    // Admit initial state.
    if let InsertOutcome::Inserted = fp_set.insert_checked(initial_fp) {
        if !observer.on_new_state(&net.initial_marking) {
            let stats = FingerprintOnlyStats {
                states_visited: 1,
                max_depth: 0,
                fp_set_memory_bytes: FingerprintSet::stats(&fp_set).memory_bytes,
            };
            return (ExplorationResult::new(false, 1, true), stats);
        }

        if let Some(ref mut logger) = trace_logger {
            logger.log_entry(initial_fp, 0, 0);
        }

        queue.push_back(QueueEntry {
            packed: initial_packed,
            fp: initial_fp,
            depth: 0,
        });
    }

    let mut stopped_by_observer = false;
    let mut current_tokens = Vec::with_capacity(num_places);
    let mut deadline_counter: u32 = 0;
    let mut pack_buf = Vec::with_capacity(pack_capacity);
    let mut enabled_transitions = Vec::with_capacity(num_transitions);

    while let Some(entry) = queue.pop_front() {
        deadline_counter = deadline_counter.wrapping_add(1);
        if deadline_counter.is_multiple_of(DEADLINE_CHECK_INTERVAL)
            && config
                .deadline()
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            let visited = FingerprintSet::len(&fp_set);
            let stats = FingerprintOnlyStats {
                states_visited: visited,
                max_depth,
                fp_set_memory_bytes: FingerprintSet::stats(&fp_set).memory_bytes,
            };
            return (ExplorationResult::new(false, visited, false), stats);
        }

        if observer.is_done() {
            stopped_by_observer = true;
            break;
        }

        max_depth = max_depth.max(entry.depth);

        unpack_marking_config(&entry.packed, &marking_config, &mut current_tokens);

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
            let succ_fp128 = fingerprint_marking(&pack_buf);
            let succ_fp = succ_fp128 as u64;

            match fp_set.insert_checked(succ_fp) {
                InsertOutcome::Inserted => {}
                InsertOutcome::AlreadyPresent => {
                    net.undo_delta(&mut current_tokens, trans);
                    continue;
                }
                _ => {
                    // StorageFault or unknown outcome -- treat as state limit reached.
                    net.undo_delta(&mut current_tokens, trans);
                    let visited = FingerprintSet::len(&fp_set);
                    let stats = FingerprintOnlyStats {
                        states_visited: visited,
                        max_depth,
                        fp_set_memory_bytes: FingerprintSet::stats(&fp_set).memory_bytes,
                    };
                    return (ExplorationResult::new(false, visited, false), stats);
                }
            }

            let visited = FingerprintSet::len(&fp_set);
            if visited >= config.max_states() {
                net.undo_delta(&mut current_tokens, trans);
                let stats = FingerprintOnlyStats {
                    states_visited: visited,
                    max_depth,
                    fp_set_memory_bytes: FingerprintSet::stats(&fp_set).memory_bytes,
                };
                return (ExplorationResult::new(false, visited, false), stats);
            }

            if !observer.on_new_state(&current_tokens) {
                stopped_by_observer = true;
                break;
            }

            if let Some(ref mut logger) = trace_logger {
                logger.log_entry(succ_fp, entry.fp, trans.0);
            }

            let succ_packed: Box<[u8]> = pack_buf.as_slice().into();
            queue.push_back(QueueEntry {
                packed: succ_packed,
                fp: succ_fp,
                depth: entry.depth + 1,
            });

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

    if let Some(ref mut logger) = trace_logger {
        logger.flush();
    }

    let visited = FingerprintSet::len(&fp_set);
    let stats = FingerprintOnlyStats {
        states_visited: visited,
        max_depth,
        fp_set_memory_bytes: FingerprintSet::stats(&fp_set).memory_bytes,
    };

    (
        ExplorationResult::new(
            !stopped_by_observer && queue.is_empty(),
            visited,
            stopped_by_observer,
        ),
        stats,
    )
}

/// Reconstruct a counterexample trace from the disk log.
///
/// Reads the binary trace log and walks backward from `violating_fp` to the
/// initial state (parent_fp == 0), returning the sequence of transition IDs
/// in forward order.
///
/// Returns `None` if the trace file doesn't exist or the fingerprint chain
/// is broken.
///
/// # Usage
///
/// Called by examination code when a violation (e.g., deadlock) is detected
/// during fingerprint-only BFS and `trace_dir` was provided. The examination
/// must track the violating state's 64-bit fingerprint to pass here.
///
/// # Hash collision note
///
/// With 64-bit fingerprints, birthday-paradox collision probability reaches
/// ~50% at ~2^32 (~4 billion) states. For state spaces below 10^8, the
/// probability is <10^-3. For larger explorations, use full-state mode.
#[allow(dead_code)] // Infrastructure for examination-level trace reconstruction.
pub(crate) fn reconstruct_trace(
    trace_dir: &std::path::Path,
    violating_fp: u64,
) -> Option<Vec<u32>> {
    use std::collections::HashMap;
    use std::io::Read;

    let path = trace_dir.join("trace.bin");
    let mut file = std::fs::File::open(&path).ok()?;
    let mut data = Vec::new();
    file.read_to_end(&mut data).ok()?;

    let entry_size = std::mem::size_of::<TraceEntry>();
    if data.len() % entry_size != 0 {
        return None;
    }

    // Build parent map: state_fp -> (parent_fp, transition_id)
    let mut parent_map: HashMap<u64, (u64, u32)> = HashMap::new();
    for chunk in data.chunks_exact(entry_size) {
        let entry: TraceEntry =
            unsafe { std::ptr::read_unaligned(chunk.as_ptr() as *const TraceEntry) };
        parent_map.insert(entry.state_fp, (entry.parent_fp, entry.transition_id));
    }

    // Walk backward from violating state to initial state.
    let mut trace = Vec::new();
    let mut current = violating_fp;
    let mut steps = 0;
    let max_steps = parent_map.len();

    loop {
        let (parent, trans_id) = parent_map.get(&current)?;
        if *parent == 0 {
            // Reached initial state.
            break;
        }
        trace.push(*trans_id);
        current = *parent;
        steps += 1;
        if steps > max_steps {
            // Cycle detection -- broken trace.
            return None;
        }
    }

    trace.reverse();
    Some(trace)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::explorer::config::ExplorationConfig;
    use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

    fn simple_linear_net() -> PetriNet {
        PetriNet {
            name: Some("linear".into()),
            places: vec![
                PlaceInfo {
                    id: "P0".into(),
                    name: None,
                },
                PlaceInfo {
                    id: "P1".into(),
                    name: None,
                },
            ],
            transitions: vec![TransitionInfo {
                id: "T0".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            }],
            initial_marking: vec![1, 0],
        }
    }

    fn cyclic_net() -> PetriNet {
        PetriNet {
            name: Some("cycle".into()),
            places: vec![
                PlaceInfo {
                    id: "P0".into(),
                    name: None,
                },
                PlaceInfo {
                    id: "P1".into(),
                    name: None,
                },
            ],
            transitions: vec![
                TransitionInfo {
                    id: "T0".into(),
                    name: None,
                    inputs: vec![Arc {
                        place: PlaceIdx(0),
                        weight: 1,
                    }],
                    outputs: vec![Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    }],
                },
                TransitionInfo {
                    id: "T1".into(),
                    name: None,
                    inputs: vec![Arc {
                        place: PlaceIdx(1),
                        weight: 1,
                    }],
                    outputs: vec![Arc {
                        place: PlaceIdx(0),
                        weight: 1,
                    }],
                },
            ],
            initial_marking: vec![1, 0],
        }
    }

    fn deadlock_net() -> PetriNet {
        PetriNet {
            name: Some("deadlock".into()),
            places: vec![PlaceInfo {
                id: "P0".into(),
                name: None,
            }],
            transitions: vec![],
            initial_marking: vec![1],
        }
    }

    fn counting_net(initial_tokens: u64) -> PetriNet {
        PetriNet {
            name: Some("counting".into()),
            places: vec![
                PlaceInfo {
                    id: "P0".into(),
                    name: None,
                },
                PlaceInfo {
                    id: "P1".into(),
                    name: None,
                },
            ],
            transitions: vec![TransitionInfo {
                id: "T0".into(),
                name: None,
                inputs: vec![Arc {
                    place: PlaceIdx(0),
                    weight: 1,
                }],
                outputs: vec![Arc {
                    place: PlaceIdx(1),
                    weight: 1,
                }],
            }],
            initial_marking: vec![initial_tokens, 0],
        }
    }

    struct CountingObserver {
        states: usize,
        deadlocks: usize,
        firings: usize,
    }

    impl CountingObserver {
        fn new() -> Self {
            Self {
                states: 0,
                deadlocks: 0,
                firings: 0,
            }
        }
    }

    impl ExplorationObserver for CountingObserver {
        fn on_new_state(&mut self, _marking: &[u64]) -> bool {
            self.states += 1;
            true
        }

        fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
            self.firings += 1;
            true
        }

        fn on_deadlock(&mut self, _marking: &[u64]) {
            self.deadlocks += 1;
        }

        fn is_done(&self) -> bool {
            false
        }
    }

    #[test]
    fn fingerprint_only_linear_net() {
        let net = simple_linear_net();
        let config = ExplorationConfig::default();
        let mut observer = CountingObserver::new();
        let (result, stats) = explore_fingerprint_only(&net, &config, &mut observer, None);

        assert!(result.completed);
        assert_eq!(stats.states_visited, 2);
        assert_eq!(observer.states, 2);
        assert_eq!(observer.deadlocks, 1);
        assert_eq!(observer.firings, 1);
    }

    #[test]
    fn fingerprint_only_cyclic_net() {
        let net = cyclic_net();
        let config = ExplorationConfig::default();
        let mut observer = CountingObserver::new();
        let (result, stats) = explore_fingerprint_only(&net, &config, &mut observer, None);

        assert!(result.completed);
        assert_eq!(stats.states_visited, 2);
        assert_eq!(observer.deadlocks, 0);
    }

    #[test]
    fn fingerprint_only_deadlock_net() {
        let net = deadlock_net();
        let config = ExplorationConfig::default();
        let mut observer = CountingObserver::new();
        let (result, stats) = explore_fingerprint_only(&net, &config, &mut observer, None);

        assert!(result.completed);
        assert_eq!(stats.states_visited, 1);
        assert_eq!(observer.deadlocks, 1);
    }

    #[test]
    fn fingerprint_only_state_limit() {
        let net = counting_net(100);
        let config = ExplorationConfig::new(10);
        let mut observer = CountingObserver::new();
        let (result, stats) = explore_fingerprint_only(&net, &config, &mut observer, None);

        assert!(!result.completed);
        assert!(stats.states_visited <= 11);
    }

    #[test]
    fn fingerprint_only_reports_memory_stats() {
        let net = cyclic_net();
        let config = ExplorationConfig::default();
        let mut observer = CountingObserver::new();
        let (_result, stats) = explore_fingerprint_only(&net, &config, &mut observer, None);

        // CAS table should have allocated some memory.
        assert!(stats.fp_set_memory_bytes > 0);
    }

    #[test]
    fn fingerprint_only_matches_full_bfs_state_count() {
        use crate::explorer::observer::explore;

        let nets = vec![
            simple_linear_net(),
            cyclic_net(),
            deadlock_net(),
            counting_net(5),
        ];

        for net in nets {
            let config = ExplorationConfig::default();

            let mut full_observer = CountingObserver::new();
            let full_result = explore(&net, &config, &mut full_observer);

            let mut fp_observer = CountingObserver::new();
            let (fp_result, _stats) =
                explore_fingerprint_only(&net, &config, &mut fp_observer, None);

            assert_eq!(
                full_observer.states, fp_observer.states,
                "state count mismatch for net {:?}",
                net.name
            );
            assert_eq!(
                full_observer.deadlocks, fp_observer.deadlocks,
                "deadlock count mismatch for net {:?}",
                net.name
            );
            assert_eq!(
                full_result.completed, fp_result.completed,
                "completion mismatch for net {:?}",
                net.name
            );
        }
    }

    #[test]
    fn fingerprint_only_with_trace_logging() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let net = simple_linear_net();
        let config = ExplorationConfig::default();
        let mut observer = CountingObserver::new();
        let (result, _stats) =
            explore_fingerprint_only(&net, &config, &mut observer, Some(dir.path()));

        assert!(result.completed);

        // Trace file should exist and be non-empty.
        let trace_path = dir.path().join("trace.bin");
        assert!(trace_path.exists());
        let metadata = std::fs::metadata(&trace_path).expect("trace metadata");
        assert!(metadata.len() > 0);
    }

    #[test]
    fn fingerprint_only_trace_reconstruction() {
        // counting_net(3): P0=3 -> fire T0 three times -> P0=0,P1=3
        // States: [3,0] -> [2,1] -> [1,2] -> [0,3]  (4 states, linear chain)
        let dir = tempfile::tempdir().expect("create temp dir");
        let net = counting_net(3);
        let config = ExplorationConfig::default();

        // Track the fingerprint of the last discovered (deadlock) state.
        struct DeadlockFpObserver {
            last_fp: u64,
        }
        impl ExplorationObserver for DeadlockFpObserver {
            fn on_new_state(&mut self, marking: &[u64]) -> bool {
                // Compute fingerprint the same way the explorer does.
                use crate::marking::{pack_marking_config, PreparedMarking};
                let net = counting_net(3);
                let prepared = PreparedMarking::analyze(&net);
                let mut buf = Vec::new();
                pack_marking_config(marking, &prepared.config, &mut buf);
                let fp128 = fingerprint_marking(&buf);
                self.last_fp = fp128 as u64;
                true
            }
            fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
                true
            }
            fn on_deadlock(&mut self, _marking: &[u64]) {}
            fn is_done(&self) -> bool {
                false
            }
        }

        let mut observer = DeadlockFpObserver { last_fp: 0 };
        let (result, stats) =
            explore_fingerprint_only(&net, &config, &mut observer, Some(dir.path()));

        assert!(result.completed);
        assert_eq!(stats.states_visited, 4);

        // Reconstruct trace from the final state (deadlock at [0,3]).
        let trace = reconstruct_trace(dir.path(), observer.last_fp);
        assert!(
            trace.is_some(),
            "trace reconstruction should succeed for a linear chain"
        );
        let transitions = trace.expect("verified Some above");
        // The chain [3,0]->[2,1]->[1,2]->[0,3] requires 3 firings of T0.
        assert_eq!(transitions.len(), 3, "should have 3 transition firings");
        // All firings should be T0 (index 0).
        assert!(
            transitions.iter().all(|&t| t == 0),
            "all transitions should be T0"
        );
    }

    #[test]
    fn fingerprint_only_trace_reconstruction_returns_none_without_trace() {
        let dir = tempfile::tempdir().expect("create temp dir");
        // No trace file written -- reconstruction should return None.
        assert!(reconstruct_trace(dir.path(), 12345).is_none());
    }

    #[test]
    fn fingerprint_only_early_termination() {
        struct StopAfterTwo {
            count: usize,
        }

        impl ExplorationObserver for StopAfterTwo {
            fn on_new_state(&mut self, _marking: &[u64]) -> bool {
                self.count += 1;
                self.count < 2
            }

            fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
                true
            }

            fn on_deadlock(&mut self, _marking: &[u64]) {}

            fn is_done(&self) -> bool {
                self.count >= 2
            }
        }

        let net = counting_net(100);
        let config = ExplorationConfig::default();
        let mut observer = StopAfterTwo { count: 0 };
        let (result, _stats) = explore_fingerprint_only(&net, &config, &mut observer, None);

        assert!(result.stopped_by_observer);
        assert!(!result.completed);
    }
}
