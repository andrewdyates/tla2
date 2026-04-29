// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Coverage-guided BFS frontier queue.
//!
//! Implements a hybrid frontier that mixes standard BFS (FIFO) ordering with
//! coverage-guided priority exploration. Every `mix_ratio` states, one state
//! is dequeued from a priority queue instead of the standard BFS queue.
//!
//! Priority is assigned at enqueue time based on the rarity of the action
//! that produced the state: states from rare/uncovered actions get higher
//! priority and are explored sooner.
//!
//! ## Queue Architecture
//!
//! ```text
//! push(entry, priority)
//!   |
//!   +---> BFS VecDeque (standard FIFO for level ordering)
//!   |
//!   +---> Priority BinaryHeap (high-priority rare-action states)
//!
//! pop()
//!   |
//!   +---> if counter % mix_ratio == 0 AND priority_queue non-empty:
//!   |       dequeue from BinaryHeap (coverage-guided pick)
//!   +---> else:
//!           dequeue from VecDeque (standard BFS FIFO)
//! ```
//!
//! The mix ratio defaults to 8: every 8th state is coverage-guided, the rest
//! maintain BFS level ordering. This preserves BFS completeness guarantees
//! (all states are still explored) while directing effort toward under-covered
//! areas of the state space.

use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};

/// A frontier entry with an associated priority score.
#[allow(dead_code)]
#[derive(Debug)]
struct PrioritizedEntry<T> {
    /// The actual queue entry (fingerprint, depth, etc.)
    entry: T,
    /// Priority score (higher = explore sooner). Based on action rarity.
    priority: u32,
    /// Insertion order (for tie-breaking within same priority level).
    sequence: u64,
}

impl<T> PartialEq for PrioritizedEntry<T> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.sequence == other.sequence
    }
}

impl<T> Eq for PrioritizedEntry<T> {}

impl<T> PartialOrd for PrioritizedEntry<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for PrioritizedEntry<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // Higher priority first; break ties by earlier insertion (lower sequence).
        self.priority
            .cmp(&other.priority)
            .then_with(|| other.sequence.cmp(&self.sequence))
    }
}

/// Hybrid BFS + coverage-guided priority frontier.
///
/// Wraps a standard `VecDeque` BFS queue with a `BinaryHeap` priority queue.
/// States with priority > 0 are placed in the priority queue; states with
/// priority 0 go to the standard BFS queue.
///
/// Every `mix_ratio` pops, one state is taken from the priority queue (if
/// non-empty); all other pops come from the standard BFS queue.
// Coverage-guided frontier is scaffolded but not yet wired into the main
// BFS loop. Suppress dead_code warnings until the feature is fully integrated.
#[allow(dead_code)]
pub(crate) struct CoverageGuidedFrontier<T> {
    /// Standard BFS FIFO queue (maintains level ordering).
    bfs_queue: VecDeque<T>,
    /// Priority queue for coverage-guided states (rare-action states).
    priority_queue: BinaryHeap<PrioritizedEntry<T>>,
    /// How often to dequeue from the priority queue (every N pops).
    mix_ratio: usize,
    /// Pop counter for mix ratio tracking.
    pop_count: usize,
    /// Sequence counter for tie-breaking in the priority queue.
    sequence: u64,
    /// Number of states dequeued from the priority queue.
    priority_pops: u64,
    /// Number of states dequeued from the BFS queue.
    bfs_pops: u64,
}

#[allow(dead_code)]
impl<T> CoverageGuidedFrontier<T> {
    /// Create a new coverage-guided frontier with the given mix ratio.
    ///
    /// `mix_ratio` controls how often to dequeue from the priority queue:
    /// - 1 = always prefer priority queue (pure coverage-guided)
    /// - 8 = every 8th pop is coverage-guided (default, good balance)
    /// - 0 = never use priority queue (pure BFS, same as VecDeque)
    pub(crate) fn new(mix_ratio: usize) -> Self {
        Self {
            bfs_queue: VecDeque::new(),
            priority_queue: BinaryHeap::new(),
            mix_ratio,
            pop_count: 0,
            sequence: 0,
            priority_pops: 0,
            bfs_pops: 0,
        }
    }

    /// Push an entry with a priority score.
    ///
    /// Entries with priority > 0 go to the priority queue.
    /// Entries with priority 0 go to the standard BFS queue.
    pub(crate) fn push_with_priority(&mut self, entry: T, priority: u32) {
        if priority > 0 && self.mix_ratio > 0 {
            self.sequence += 1;
            self.priority_queue.push(PrioritizedEntry {
                entry,
                priority,
                sequence: self.sequence,
            });
        } else {
            self.bfs_queue.push_back(entry);
        }
    }

    /// Get the number of states dequeued from the priority queue.
    pub(crate) fn priority_pops(&self) -> u64 {
        self.priority_pops
    }

    /// Get the number of states dequeued from the BFS queue.
    pub(crate) fn bfs_pops(&self) -> u64 {
        self.bfs_pops
    }
}

#[allow(dead_code)]
impl<T> CoverageGuidedFrontier<T> {
    /// Push an entry to the standard BFS queue (no explicit priority).
    pub(crate) fn push(&mut self, entry: T) {
        self.bfs_queue.push_back(entry);
    }

    /// Pop the next entry, alternating between priority and BFS queues.
    pub(crate) fn pop(&mut self) -> Option<T> {
        self.pop_count += 1;

        // Check if this pop should come from the priority queue.
        if self.mix_ratio > 0
            && self.pop_count % self.mix_ratio == 0
            && !self.priority_queue.is_empty()
        {
            self.priority_pops += 1;
            return self.priority_queue.pop().map(|pe| pe.entry);
        }

        // Standard BFS FIFO pop.
        if let Some(entry) = self.bfs_queue.pop_front() {
            self.bfs_pops += 1;
            return Some(entry);
        }

        // BFS queue empty -- drain priority queue to avoid starvation.
        if let Some(pe) = self.priority_queue.pop() {
            self.priority_pops += 1;
            return Some(pe.entry);
        }

        None
    }

    /// Total number of entries in both queues.
    #[allow(dead_code)]
    pub(crate) fn len(&self) -> usize {
        self.bfs_queue.len() + self.priority_queue.len()
    }

    /// Iterate over all entries in both queues (BFS queue first, then priority queue).
    #[cfg(test)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = &T> {
        self.bfs_queue
            .iter()
            .chain(self.priority_queue.iter().map(|pe| &pe.entry))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_frontier_pure_bfs_when_no_priority() {
        let mut frontier = CoverageGuidedFrontier::new(8);

        frontier.push(1);
        frontier.push(2);
        frontier.push(3);

        assert_eq!(frontier.len(), 3);
        assert_eq!(frontier.pop(), Some(1)); // FIFO
        assert_eq!(frontier.pop(), Some(2));
        assert_eq!(frontier.pop(), Some(3));
        assert_eq!(frontier.pop(), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_frontier_priority_entries_dequeued_at_mix_ratio() {
        let mut frontier = CoverageGuidedFrontier::new(4);

        // Push BFS entries
        frontier.push(10);
        frontier.push(20);
        frontier.push(30);
        frontier.push(40);
        frontier.push(50);

        // Push priority entry
        frontier.push_with_priority(99, 10);

        assert_eq!(frontier.len(), 6);

        // Pops 1, 2, 3 come from BFS queue
        assert_eq!(frontier.pop(), Some(10)); // pop_count=1
        assert_eq!(frontier.pop(), Some(20)); // pop_count=2
        assert_eq!(frontier.pop(), Some(30)); // pop_count=3

        // Pop 4 (pop_count=4, 4%4==0) comes from priority queue
        assert_eq!(frontier.pop(), Some(99)); // pop_count=4, priority!

        // Remaining from BFS
        assert_eq!(frontier.pop(), Some(40)); // pop_count=5
        assert_eq!(frontier.pop(), Some(50)); // pop_count=6
        assert_eq!(frontier.pop(), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_frontier_priority_ordering_highest_first() {
        let mut frontier = CoverageGuidedFrontier::new(1); // Always priority

        frontier.push_with_priority(1, 5);
        frontier.push_with_priority(2, 10);
        frontier.push_with_priority(3, 1);

        // mix_ratio=1 means every pop tries priority first
        // pop_count=1, 1%1==0, priority queue
        assert_eq!(frontier.pop(), Some(2)); // highest priority (10)
        assert_eq!(frontier.pop(), Some(1)); // next (5)
        assert_eq!(frontier.pop(), Some(3)); // lowest (1)
        assert_eq!(frontier.pop(), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_frontier_drains_priority_when_bfs_empty() {
        let mut frontier = CoverageGuidedFrontier::new(8);

        // Only priority entries, no BFS entries
        frontier.push_with_priority(42, 5);
        frontier.push_with_priority(43, 3);

        // pop_count=1, 1%8!=0, but BFS is empty, so fall through to priority
        assert_eq!(frontier.pop(), Some(42));
        assert_eq!(frontier.pop(), Some(43));
        assert_eq!(frontier.pop(), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_frontier_zero_mix_ratio_is_pure_bfs() {
        let mut frontier = CoverageGuidedFrontier::new(0);

        frontier.push_with_priority(1, 100); // Goes to BFS queue (mix_ratio=0)
        frontier.push(2);
        frontier.push(3);

        assert_eq!(frontier.pop(), Some(1)); // FIFO order
        assert_eq!(frontier.pop(), Some(2));
        assert_eq!(frontier.pop(), Some(3));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_frontier_stats_tracking() {
        let mut frontier = CoverageGuidedFrontier::new(2);

        frontier.push(10);
        frontier.push_with_priority(99, 5);
        frontier.push(20);

        let _ = frontier.pop(); // pop_count=1, BFS
        let _ = frontier.pop(); // pop_count=2, 2%2==0, priority
        let _ = frontier.pop(); // pop_count=3, BFS

        assert_eq!(frontier.bfs_pops(), 2);
        assert_eq!(frontier.priority_pops(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_frontier_len_includes_both_queues() {
        let mut frontier = CoverageGuidedFrontier::new(4);

        frontier.push(1);
        frontier.push(2);
        frontier.push_with_priority(3, 10);

        assert_eq!(frontier.len(), 3);

        let _ = frontier.pop();
        assert_eq!(frontier.len(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_frontier_iter_yields_all_entries() {
        let mut frontier = CoverageGuidedFrontier::new(4);

        frontier.push(1);
        frontier.push(2);
        frontier.push_with_priority(3, 10);

        let items: Vec<&i32> = frontier.iter().collect();
        assert_eq!(items.len(), 3);
        // BFS queue items first, then priority queue items
        assert!(items.contains(&&1));
        assert!(items.contains(&&2));
        assert!(items.contains(&&3));
    }
}
