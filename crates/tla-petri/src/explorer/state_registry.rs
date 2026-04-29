// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use rustc_hash::FxHashMap;

use super::fingerprint::fingerprint_marking;

/// Outcome of attempting to admit a packed marking into the graph state registry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum StateAdmission {
    /// The fingerprint already exists; returns the existing state ID.
    Existing(u32),
    /// The fingerprint is new and was inserted; returns the new state info.
    Inserted(NewState),
    /// The registry is at capacity; the state was not inserted.
    LimitReached,
}

/// A newly admitted state with its assigned ID and owned packed bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NewState {
    pub(crate) state_id: u32,
    pub(crate) packed: Box<[u8]>,
}

/// Graph-mode state-ID registry backed by an in-memory `FxHashMap<u128, u32>`.
///
/// Centralizes the admission logic shared by [`super::graph::explore_and_build_graph`]
/// and [`super::graph::explore_full`]: fingerprint → check duplicate → check budget → insert.
pub(crate) struct GraphStateRegistry {
    state_ids: FxHashMap<u128, u32>,
    max_states: usize,
}

impl GraphStateRegistry {
    /// Create a new registry seeded with the initial marking as state ID 0.
    pub(crate) fn with_initial(initial_packed: &[u8], max_states: usize) -> Self {
        let mut state_ids = FxHashMap::default();
        state_ids.insert(fingerprint_marking(initial_packed), 0);
        Self {
            state_ids,
            max_states,
        }
    }

    /// Attempt to admit a packed marking into the registry.
    ///
    /// Returns [`StateAdmission::Existing`] if the fingerprint is already known,
    /// [`StateAdmission::LimitReached`] if the budget would be exceeded,
    /// or [`StateAdmission::Inserted`] with the new state ID and owned packed bytes.
    pub(crate) fn admit_packed(&mut self, packed: &[u8]) -> StateAdmission {
        let fp = fingerprint_marking(packed);
        if let Some(&existing) = self.state_ids.get(&fp) {
            return StateAdmission::Existing(existing);
        }
        if self.state_ids.len() >= self.max_states {
            return StateAdmission::LimitReached;
        }
        let next_id = self.state_ids.len() as u32;
        self.state_ids.insert(fp, next_id);
        StateAdmission::Inserted(NewState {
            state_id: next_id,
            packed: packed.into(),
        })
    }

    /// Number of states currently in the registry.
    pub(crate) fn len(&self) -> u32 {
        self.state_ids.len() as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_graph_state_registry_duplicate_returns_existing_id() {
        let initial = [1u8, 2, 3, 4];
        let mut reg = GraphStateRegistry::with_initial(&initial, 100);
        assert_eq!(reg.len(), 1);

        // Re-admitting the initial marking returns Existing(0)
        let result = reg.admit_packed(&initial);
        assert_eq!(result, StateAdmission::Existing(0));
        assert_eq!(reg.len(), 1);
    }

    #[test]
    fn test_graph_state_registry_new_state_returns_inserted_payload() {
        let initial = [1u8, 2, 3, 4];
        let mut reg = GraphStateRegistry::with_initial(&initial, 100);

        let new_marking = [5u8, 6, 7, 8];
        let result = reg.admit_packed(&new_marking);
        match result {
            StateAdmission::Inserted(ns) => {
                assert_eq!(ns.state_id, 1);
                assert_eq!(&*ns.packed, &new_marking);
            }
            other => panic!("expected Inserted, got {other:?}"),
        }
        assert_eq!(reg.len(), 2);

        // Re-admitting the same new marking returns Existing(1)
        let result2 = reg.admit_packed(&new_marking);
        assert_eq!(result2, StateAdmission::Existing(1));
        assert_eq!(reg.len(), 2);
    }

    #[test]
    fn test_graph_state_registry_limit_reached_blocks_new_state() {
        let initial = [1u8, 2, 3, 4];
        // max_states = 1 means only the initial state fits
        let mut reg = GraphStateRegistry::with_initial(&initial, 1);
        assert_eq!(reg.len(), 1);

        let new_marking = [5u8, 6, 7, 8];
        let result = reg.admit_packed(&new_marking);
        assert_eq!(result, StateAdmission::LimitReached);
        assert_eq!(reg.len(), 1);
    }
}
