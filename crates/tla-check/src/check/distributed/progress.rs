// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Distributed progress reporting across multi-machine BFS nodes.
//!
//! Collects and aggregates progress statistics from all nodes in the
//! distributed model checking cluster. Node 0 acts as the progress
//! coordinator, periodically polling other nodes for their stats and
//! emitting a unified progress report.
//!
//! # Architecture
//!
//! ```text
//! Node 0 (coordinator)           Node 1..N
//! ┌──────────────────┐          ┌──────────────────┐
//! │ ProgressTracker   │──poll──>│ NodeStats         │
//! │  - aggregate()    │<─report─│  - distinct_states│
//! │  - display()      │         │  - max_depth      │
//! │                   │         │  - transitions    │
//! └──────────────────┘          └──────────────────┘
//! ```
//!
//! Part of Pillar 6 Phase 2: Distributed progress reporting.

#![allow(dead_code)]

use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use super::transport::NodeId;

/// Per-node statistics snapshot.
#[derive(Debug, Clone, Default)]
pub(crate) struct NodeStats {
    /// Node identifier.
    pub(crate) node_id: NodeId,
    /// Number of distinct states found by this node.
    pub(crate) distinct_states: u64,
    /// Maximum BFS depth reached by this node.
    pub(crate) max_depth: u32,
    /// Total transitions (successor computations) by this node.
    pub(crate) transitions: u64,
    /// Whether this node is currently idle.
    pub(crate) is_idle: bool,
    /// Timestamp of this snapshot.
    pub(crate) timestamp: Option<Instant>,
}

/// Local progress counters maintained by each node's BFS worker.
///
/// Updated by the BFS loop on every state processed. Read by the
/// progress reporting system when polled.
pub(crate) struct LocalProgress {
    distinct_states: AtomicU64,
    max_depth: AtomicU32,
    transitions: AtomicU64,
    states_received: AtomicU64,
    states_sent: AtomicU64,
}

impl LocalProgress {
    pub(crate) fn new() -> Self {
        LocalProgress {
            distinct_states: AtomicU64::new(0),
            max_depth: AtomicU32::new(0),
            transitions: AtomicU64::new(0),
            states_received: AtomicU64::new(0),
            states_sent: AtomicU64::new(0),
        }
    }

    /// Record a new distinct state.
    #[inline]
    pub(crate) fn inc_distinct_states(&self) {
        self.distinct_states.fetch_add(1, Ordering::Relaxed);
    }

    /// Update the maximum depth.
    #[inline]
    pub(crate) fn update_max_depth(&self, depth: u32) {
        self.max_depth.fetch_max(depth, Ordering::Relaxed);
    }

    /// Record a transition (successor computation).
    #[inline]
    pub(crate) fn inc_transitions(&self) {
        self.transitions.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a state received from another node.
    #[inline]
    pub(crate) fn inc_states_received(&self) {
        self.states_received.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a state sent to another node.
    #[inline]
    pub(crate) fn inc_states_sent(&self) {
        self.states_sent.fetch_add(1, Ordering::Relaxed);
    }

    /// Take a snapshot of current counters.
    pub(crate) fn snapshot(&self, node_id: NodeId) -> NodeStats {
        NodeStats {
            node_id,
            distinct_states: self.distinct_states.load(Ordering::Relaxed),
            max_depth: self.max_depth.load(Ordering::Relaxed),
            transitions: self.transitions.load(Ordering::Relaxed),
            is_idle: false,
            timestamp: Some(Instant::now()),
        }
    }

    /// Current distinct state count.
    pub(crate) fn distinct_states(&self) -> u64 {
        self.distinct_states.load(Ordering::Relaxed)
    }

    /// Current states received count.
    pub(crate) fn states_received(&self) -> u64 {
        self.states_received.load(Ordering::Relaxed)
    }

    /// Current states sent count.
    pub(crate) fn states_sent(&self) -> u64 {
        self.states_sent.load(Ordering::Relaxed)
    }
}

/// Aggregated progress across all nodes in the cluster.
#[derive(Debug, Clone)]
pub(crate) struct ClusterProgress {
    /// Per-node statistics snapshots.
    pub(crate) node_stats: Vec<NodeStats>,
    /// Total distinct states across all nodes.
    pub(crate) total_distinct_states: u64,
    /// Maximum BFS depth across all nodes.
    pub(crate) global_max_depth: u32,
    /// Total transitions across all nodes.
    pub(crate) total_transitions: u64,
    /// Number of nodes currently idle.
    pub(crate) idle_nodes: u32,
    /// Total nodes in the cluster.
    pub(crate) total_nodes: u32,
    /// Wall clock elapsed since start.
    pub(crate) elapsed: Duration,
}

impl ClusterProgress {
    /// Throughput in states per second.
    pub(crate) fn states_per_second(&self) -> f64 {
        let secs = self.elapsed.as_secs_f64();
        if secs > 0.0 {
            self.total_distinct_states as f64 / secs
        } else {
            0.0
        }
    }

    /// Format a human-readable progress line.
    pub(crate) fn format_progress_line(&self) -> String {
        format!(
            "Distributed BFS: {} states, depth {}, {:.0} states/s, \
             {}/{} nodes active, {:.1}s elapsed",
            self.total_distinct_states,
            self.global_max_depth,
            self.states_per_second(),
            self.total_nodes - self.idle_nodes,
            self.total_nodes,
            self.elapsed.as_secs_f64(),
        )
    }
}

/// Progress tracker that aggregates statistics from all nodes.
///
/// Maintained by the coordinator node (node 0). Other nodes report their
/// stats when polled via ProgressRequest messages.
pub(crate) struct ProgressTracker {
    /// Number of nodes in the cluster.
    num_nodes: u32,
    /// Latest stats snapshot from each node.
    snapshots: Mutex<Vec<NodeStats>>,
    /// When the distributed run started.
    start_time: Instant,
    /// How often to emit progress reports.
    report_interval: Duration,
    /// Last time a report was emitted.
    last_report: Mutex<Instant>,
}

impl ProgressTracker {
    /// Create a new progress tracker.
    pub(crate) fn new(num_nodes: u32, report_interval: Duration) -> Self {
        let now = Instant::now();
        ProgressTracker {
            num_nodes,
            snapshots: Mutex::new(
                (0..num_nodes)
                    .map(|id| NodeStats {
                        node_id: id,
                        ..Default::default()
                    })
                    .collect(),
            ),
            start_time: now,
            report_interval,
            last_report: Mutex::new(now),
        }
    }

    /// Update the stats for a specific node.
    pub(crate) fn update_node_stats(&self, stats: NodeStats) {
        let mut snapshots = self.snapshots.lock().expect("snapshots lock");
        let idx = stats.node_id as usize;
        if idx < snapshots.len() {
            snapshots[idx] = stats;
        }
    }

    /// Aggregate the current stats into a `ClusterProgress`.
    pub(crate) fn aggregate(&self) -> ClusterProgress {
        let snapshots = self.snapshots.lock().expect("snapshots lock");
        let mut total_distinct = 0u64;
        let mut max_depth = 0u32;
        let mut total_transitions = 0u64;
        let mut idle_count = 0u32;

        for stats in snapshots.iter() {
            total_distinct += stats.distinct_states;
            max_depth = max_depth.max(stats.max_depth);
            total_transitions += stats.transitions;
            if stats.is_idle {
                idle_count += 1;
            }
        }

        ClusterProgress {
            node_stats: snapshots.clone(),
            total_distinct_states: total_distinct,
            global_max_depth: max_depth,
            total_transitions,
            idle_nodes: idle_count,
            total_nodes: self.num_nodes,
            elapsed: self.start_time.elapsed(),
        }
    }

    /// Check if enough time has elapsed for a new progress report.
    pub(crate) fn should_report(&self) -> bool {
        let last = self.last_report.lock().expect("last_report lock");
        last.elapsed() >= self.report_interval
    }

    /// Mark that a report was just emitted.
    pub(crate) fn mark_reported(&self) {
        let mut last = self.last_report.lock().expect("last_report lock");
        *last = Instant::now();
    }

    /// Emit a progress report to stderr if the interval has elapsed.
    ///
    /// Returns the aggregate stats if a report was emitted.
    pub(crate) fn maybe_report(&self) -> Option<ClusterProgress> {
        if !self.should_report() {
            return None;
        }
        let progress = self.aggregate();
        eprintln!("{}", progress.format_progress_line());
        self.mark_reported();
        Some(progress)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_local_progress_counters() {
        let lp = LocalProgress::new();
        lp.inc_distinct_states();
        lp.inc_distinct_states();
        lp.inc_transitions();
        lp.update_max_depth(5);
        lp.update_max_depth(3); // Should not decrease
        lp.inc_states_sent();
        lp.inc_states_received();

        let snap = lp.snapshot(0);
        assert_eq!(snap.distinct_states, 2);
        assert_eq!(snap.transitions, 1);
        assert_eq!(snap.max_depth, 5);
        assert_eq!(lp.states_sent(), 1);
        assert_eq!(lp.states_received(), 1);
    }

    #[test]
    fn test_progress_tracker_aggregate() {
        let tracker = ProgressTracker::new(3, Duration::from_secs(5));

        tracker.update_node_stats(NodeStats {
            node_id: 0,
            distinct_states: 100,
            max_depth: 5,
            transitions: 200,
            is_idle: false,
            timestamp: Some(Instant::now()),
        });
        tracker.update_node_stats(NodeStats {
            node_id: 1,
            distinct_states: 150,
            max_depth: 7,
            transitions: 300,
            is_idle: false,
            timestamp: Some(Instant::now()),
        });
        tracker.update_node_stats(NodeStats {
            node_id: 2,
            distinct_states: 50,
            max_depth: 3,
            transitions: 100,
            is_idle: true,
            timestamp: Some(Instant::now()),
        });

        let progress = tracker.aggregate();
        assert_eq!(progress.total_distinct_states, 300);
        assert_eq!(progress.global_max_depth, 7);
        assert_eq!(progress.total_transitions, 600);
        assert_eq!(progress.idle_nodes, 1);
        assert_eq!(progress.total_nodes, 3);
    }

    #[test]
    fn test_cluster_progress_format() {
        let progress = ClusterProgress {
            node_stats: vec![],
            total_distinct_states: 10_000,
            global_max_depth: 12,
            total_transitions: 25_000,
            idle_nodes: 1,
            total_nodes: 4,
            elapsed: Duration::from_secs(10),
        };

        let line = progress.format_progress_line();
        assert!(line.contains("10000 states"));
        assert!(line.contains("depth 12"));
        assert!(line.contains("3/4 nodes active"));
    }

    #[test]
    fn test_states_per_second() {
        let progress = ClusterProgress {
            node_stats: vec![],
            total_distinct_states: 1_000,
            global_max_depth: 0,
            total_transitions: 0,
            idle_nodes: 0,
            total_nodes: 1,
            elapsed: Duration::from_secs(2),
        };
        assert!((progress.states_per_second() - 500.0).abs() < 1.0);
    }

    #[test]
    fn test_should_report_timing() {
        let tracker = ProgressTracker::new(1, Duration::from_millis(10));
        // Just created — should not report yet (interval not elapsed)
        // Note: this could be flaky if the system is very slow, but 10ms is generous
        assert!(!tracker.should_report());

        // Wait for the interval
        std::thread::sleep(Duration::from_millis(15));
        assert!(tracker.should_report());

        tracker.mark_reported();
        assert!(!tracker.should_report());
    }
}
