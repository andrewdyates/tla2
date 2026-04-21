// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof obligation queue for IC3/PDR.
//!
//! A proof obligation (PO) records a state (cube) that needs to be blocked
//! at a given frame level. If the cube cannot be blocked, a predecessor
//! is found and a new PO is created at one level lower. If a PO reaches
//! frame 0 and cannot be blocked, a counterexample has been found.
//!
//! The queue is priority-ordered: lowest frame first (to find counterexamples
//! quickly), then deepest obligation (for better trace quality).

use crate::sat_types::Lit;
use std::cmp::Ordering;
use std::collections::BTreeSet;

/// A proof obligation: a cube that must be blocked at a given frame level.
#[derive(Debug, Clone)]
pub struct ProofObligation {
    /// Frame level where this cube was found reachable.
    pub frame: usize,
    /// The state cube (conjunction of literals) to be blocked.
    pub cube: Vec<Lit>,
    /// Depth in the proof tree (distance from the original bad state).
    pub depth: usize,
    /// Link to the successor obligation (for counterexample trace extraction).
    pub next: Option<Box<ProofObligation>>,
    /// Activity score: bumped each time this PO is re-encountered.
    /// High activity indicates the cube keeps getting rediscovered but
    /// cannot be efficiently blocked. Used by drop_po (GAP-2) and
    /// dynamic generalization (GAP-5) to handle thrashing cubes.
    /// Reference: rIC3 proofoblig.rs:18 — `act: f64`.
    pub act: f64,
    /// Count of times this PO has been re-queued due to Unknown SAT results.
    /// Used to detect and break infinite loops where a PO cycles forever
    /// because the solver consistently returns Unknown (even after fallback
    /// to SimpleSolver). After `MAX_UNKNOWN_REQUEUES`, the PO is dropped.
    pub unknown_requeues: usize,
}

impl ProofObligation {
    pub fn new(frame: usize, cube: Vec<Lit>, depth: usize, next: Option<ProofObligation>) -> Self {
        ProofObligation {
            frame,
            cube,
            depth,
            next: next.map(Box::new),
            act: 0.0,
            unknown_requeues: 0,
        }
    }

    /// Bump the activity score by 1.0 each time this PO is encountered.
    /// Reference: rIC3 proofoblig.rs:93 — `bump_act()`.
    pub fn bump_act(&mut self) {
        self.act += 1.0;
    }

    /// Decay activity when pushing to a higher frame.
    /// The 0.6 decay factor per frame level matches rIC3's `push_to()`.
    /// Reference: rIC3 proofoblig.rs:97 — `push_to()`.
    pub fn push_to_frame(&mut self, new_frame: usize) {
        for _ in self.frame..new_frame {
            self.act *= 0.6;
        }
        self.frame = new_frame;
    }
}

/// Ordering for proof obligations in the priority queue.
///
/// BTreeSet pops the *last* element with `pop_last()`, so we order such that
/// the highest-priority obligation is "greatest":
/// 1. Lowest frame first (so high frame = low priority = "less than")
/// 2. Within same frame, highest depth first
/// 3. Tie-break by cube content for BTreeSet uniqueness
impl PartialEq for ProofObligation {
    fn eq(&self, other: &Self) -> bool {
        self.frame == other.frame && self.depth == other.depth && self.cube == other.cube
    }
}

impl Eq for ProofObligation {}

impl PartialOrd for ProofObligation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ProofObligation {
    fn cmp(&self, other: &Self) -> Ordering {
        // We want lowest-frame obligations to be "greatest" (popped first from BTreeSet).
        match other.frame.cmp(&self.frame) {
            Ordering::Equal => {
                // Same frame: prefer deeper obligations.
                match self.depth.cmp(&other.depth) {
                    Ordering::Equal => {
                        // Tie-break by cube size (larger cubes = higher priority, matching rIC3).
                        match other.cube.len().cmp(&self.cube.len()) {
                            Ordering::Equal => {
                                // Final tie-break by cube content for total ordering.
                                self.cube
                                    .iter()
                                    .map(|l| l.code())
                                    .cmp(other.cube.iter().map(|l| l.code()))
                            }
                            ord => ord,
                        }
                    }
                    ord => ord,
                }
            }
            ord => ord,
        }
    }
}

/// Priority queue of proof obligations.
///
/// Uses a BTreeSet for O(log n) insert/remove and ordered iteration.
/// `pop_last()` returns the highest-priority obligation.
#[derive(Debug, Default)]
pub struct ObligationQueue {
    obligations: BTreeSet<ProofObligation>,
}

impl ObligationQueue {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a new proof obligation.
    pub fn push(&mut self, po: ProofObligation) {
        self.obligations.insert(po);
    }

    /// Pop the highest-priority obligation (lowest frame, then deepest).
    /// Only returns obligations at or below `max_frame`.
    pub fn pop(&mut self, max_frame: usize) -> Option<ProofObligation> {
        if let Some(po) = self.obligations.last() {
            if po.frame <= max_frame {
                return self.obligations.pop_last();
            }
        }
        None
    }

    /// Peek at the highest-priority obligation without removing it.
    #[allow(dead_code)]
    pub fn peek(&self) -> Option<&ProofObligation> {
        self.obligations.last()
    }

    /// Check if the queue is empty.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.obligations.is_empty()
    }

    /// Number of pending obligations.
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.obligations.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_types::Var;

    fn make_cube(vars: &[u32], signs: &[bool]) -> Vec<Lit> {
        vars.iter()
            .zip(signs)
            .map(|(&v, &s)| {
                if s {
                    Lit::pos(Var(v))
                } else {
                    Lit::neg(Var(v))
                }
            })
            .collect()
    }

    #[test]
    fn test_obligation_ordering_frame_priority() {
        let po1 = ProofObligation::new(2, make_cube(&[1], &[true]), 0, None);
        let po2 = ProofObligation::new(1, make_cube(&[1], &[true]), 0, None);
        // po2 (frame 1) should be "greater" (higher priority) than po1 (frame 2).
        assert!(po2 > po1);
    }

    #[test]
    fn test_obligation_ordering_depth_priority() {
        let po1 = ProofObligation::new(1, make_cube(&[1], &[true]), 0, None);
        let po2 = ProofObligation::new(1, make_cube(&[2], &[true]), 3, None);
        // Same frame, po2 deeper => higher priority.
        assert!(po2 > po1);
    }

    #[test]
    fn test_queue_pop_order() {
        let mut q = ObligationQueue::new();
        q.push(ProofObligation::new(3, make_cube(&[1], &[true]), 0, None));
        q.push(ProofObligation::new(1, make_cube(&[2], &[true]), 0, None));
        q.push(ProofObligation::new(2, make_cube(&[3], &[true]), 0, None));

        // Should pop frame 1 first.
        let first = q.pop(3).unwrap();
        assert_eq!(first.frame, 1);
        let second = q.pop(3).unwrap();
        assert_eq!(second.frame, 2);
        let third = q.pop(3).unwrap();
        assert_eq!(third.frame, 3);
        assert!(q.pop(3).is_none());
    }

    #[test]
    fn test_queue_max_frame_filter() {
        let mut q = ObligationQueue::new();
        q.push(ProofObligation::new(3, make_cube(&[1], &[true]), 0, None));
        q.push(ProofObligation::new(1, make_cube(&[2], &[true]), 0, None));

        // Only pop obligations at frame <= 2.
        let po = q.pop(2).unwrap();
        assert_eq!(po.frame, 1);
        // Frame 3 is above max_frame.
        assert!(q.pop(2).is_none());
    }

    #[test]
    fn test_trace_chain() {
        let inner = ProofObligation::new(1, make_cube(&[1], &[true]), 0, None);
        let outer = ProofObligation::new(2, make_cube(&[2], &[false]), 1, Some(inner));
        assert!(outer.next.is_some());
        assert_eq!(outer.next.as_ref().unwrap().frame, 1);
    }
}
