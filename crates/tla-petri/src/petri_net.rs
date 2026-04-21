// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Petri net data structures for Place/Transition nets.

use serde::{Deserialize, Serialize};

/// Type-safe index into the places vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PlaceIdx(pub u32);

/// Type-safe index into the transitions vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TransitionIdx(pub u32);

/// An arc connecting a place to/from a transition with a weight.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Arc {
    pub place: PlaceIdx,
    pub weight: u64,
}

/// Information about a place in the net.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PlaceInfo {
    pub id: String,
    pub name: Option<String>,
}

/// A transition with its input and output arcs.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct TransitionInfo {
    pub id: String,
    pub name: Option<String>,
    /// Arcs from places to this transition (tokens consumed when firing).
    pub inputs: Vec<Arc>,
    /// Arcs from this transition to places (tokens produced when firing).
    pub outputs: Vec<Arc>,
}

/// A Place/Transition Petri net.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PetriNet {
    pub name: Option<String>,
    pub places: Vec<PlaceInfo>,
    pub transitions: Vec<TransitionInfo>,
    pub initial_marking: Vec<u64>,
}

impl PetriNet {
    /// Returns the number of places.
    #[must_use]
    pub fn num_places(&self) -> usize {
        self.places.len()
    }

    /// Returns the number of transitions.
    #[must_use]
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }

    /// Check if a transition is enabled at the given marking.
    #[must_use]
    pub fn is_enabled(&self, marking: &[u64], trans: TransitionIdx) -> bool {
        let t = &self.transitions[trans.0 as usize];
        t.inputs
            .iter()
            .all(|arc| marking[arc.place.0 as usize] >= arc.weight)
    }

    /// Fire a transition, producing a new marking.
    /// Caller must ensure the transition is enabled.
    #[must_use]
    pub fn fire(&self, marking: &[u64], trans: TransitionIdx) -> Vec<u64> {
        let t = &self.transitions[trans.0 as usize];
        let mut new_marking = marking.to_vec();
        for arc in &t.inputs {
            new_marking[arc.place.0 as usize] -= arc.weight;
        }
        for arc in &t.outputs {
            new_marking[arc.place.0 as usize] += arc.weight;
        }
        new_marking
    }

    /// Fire a transition into a reusable buffer, avoiding allocation.
    ///
    /// The buffer is cleared and filled with the successor marking.
    /// Caller must ensure the transition is enabled.
    pub fn fire_into(&self, marking: &[u64], trans: TransitionIdx, out: &mut Vec<u64>) {
        out.clear();
        out.extend_from_slice(marking);
        let t = &self.transitions[trans.0 as usize];
        for arc in &t.inputs {
            out[arc.place.0 as usize] -= arc.weight;
        }
        for arc in &t.outputs {
            out[arc.place.0 as usize] += arc.weight;
        }
    }

    /// Apply a transition's delta to a marking in place.
    ///
    /// O(arcs) instead of O(places) — avoids copying the entire marking vector.
    /// Use with [`undo_delta`](Self::undo_delta) to restore the marking after
    /// packing/checking the successor. Caller must ensure the transition is enabled.
    pub fn apply_delta(&self, marking: &mut [u64], trans: TransitionIdx) {
        let t = &self.transitions[trans.0 as usize];
        for arc in &t.inputs {
            marking[arc.place.0 as usize] -= arc.weight;
        }
        for arc in &t.outputs {
            marking[arc.place.0 as usize] += arc.weight;
        }
    }

    /// Undo a transition's delta, restoring the original marking.
    ///
    /// Reverses [`apply_delta`](Self::apply_delta). O(arcs).
    pub fn undo_delta(&self, marking: &mut [u64], trans: TransitionIdx) {
        let t = &self.transitions[trans.0 as usize];
        // Reverse: add back inputs, subtract outputs
        for arc in &t.inputs {
            marking[arc.place.0 as usize] += arc.weight;
        }
        for arc in &t.outputs {
            marking[arc.place.0 as usize] -= arc.weight;
        }
    }
}

/// Tracks which places and transitions are relevant to a given property query.
///
/// Used by query slicing and reduction irrelevance analysis to prune structure
/// that cannot affect the query result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct QuerySupport {
    pub(crate) places: Vec<bool>,
    pub(crate) transitions: Vec<bool>,
}

impl QuerySupport {
    #[must_use]
    pub(crate) fn new(num_places: usize, num_transitions: usize) -> Self {
        Self {
            places: vec![false; num_places],
            transitions: vec![false; num_transitions],
        }
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        !self.places.iter().any(|keep| *keep) && !self.transitions.iter().any(|keep| *keep)
    }
}

#[cfg(test)]
mod tests {
    use super::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

    fn arc(place: u32, weight: u64) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight,
        }
    }

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: None,
        }
    }

    fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: None,
            inputs,
            outputs,
        }
    }

    #[test]
    fn test_fire_into_matches_fire() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 1), arc(2, 3)])],
            initial_marking: vec![5, 0, 0],
        };

        let marking = &net.initial_marking;
        let transition = TransitionIdx(0);
        let result_alloc = net.fire(marking, transition);

        let mut buf = Vec::new();
        net.fire_into(marking, transition, &mut buf);

        assert_eq!(result_alloc, buf);
        assert_eq!(buf, vec![3, 1, 3]);
    }

    #[test]
    fn test_fire_into_reuses_buffer() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![3, 0],
        };

        let mut buf = Vec::new();
        net.fire_into(&[3, 0], TransitionIdx(0), &mut buf);
        assert_eq!(buf, vec![2, 1]);

        let prev_ptr = buf.as_ptr();
        net.fire_into(&[2, 1], TransitionIdx(1), &mut buf);
        assert_eq!(buf, vec![3, 0]);
        assert_eq!(buf.as_ptr(), prev_ptr);
    }

    #[test]
    fn test_apply_delta_undo_delta_roundtrip() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 1), arc(2, 3)])],
            initial_marking: vec![5, 0, 0],
        };

        let mut marking = net.initial_marking.clone();
        let original = marking.clone();

        // Apply: [5,0,0] → [3,1,3]
        net.apply_delta(&mut marking, TransitionIdx(0));
        assert_eq!(marking, vec![3, 1, 3]);

        // Undo: [3,1,3] → [5,0,0]
        net.undo_delta(&mut marking, TransitionIdx(0));
        assert_eq!(marking, original);
    }

    #[test]
    fn test_apply_delta_matches_fire() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 1), arc(2, 3)])],
            initial_marking: vec![5, 0, 0],
        };

        let fire_result = net.fire(&net.initial_marking, TransitionIdx(0));
        let mut delta_marking = net.initial_marking.clone();
        net.apply_delta(&mut delta_marking, TransitionIdx(0));
        assert_eq!(fire_result, delta_marking);
    }

    #[test]
    fn test_is_enabled_exact_threshold() {
        // Transition requires exactly 3 tokens from p0
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![trans("t0", vec![arc(0, 3)], vec![arc(1, 1)])],
            initial_marking: vec![3, 0],
        };

        // Exactly enough tokens
        assert!(net.is_enabled(&[3, 0], TransitionIdx(0)));
        // One fewer than required
        assert!(!net.is_enabled(&[2, 0], TransitionIdx(0)));
        // More than required
        assert!(net.is_enabled(&[4, 0], TransitionIdx(0)));
    }

    #[test]
    fn test_is_enabled_multiple_inputs() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1"), place("p2")],
            transitions: vec![trans("t0", vec![arc(0, 2), arc(1, 1)], vec![arc(2, 1)])],
            initial_marking: vec![2, 1, 0],
        };

        // Both inputs satisfied
        assert!(net.is_enabled(&[2, 1, 0], TransitionIdx(0)));
        // First input fails
        assert!(!net.is_enabled(&[1, 1, 0], TransitionIdx(0)));
        // Second input fails
        assert!(!net.is_enabled(&[2, 0, 0], TransitionIdx(0)));
    }
}
