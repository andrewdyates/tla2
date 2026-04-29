// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_mc_core::{PorPropertyClass, PorProvider, TransitionSystem};

use crate::explorer::fingerprint::fingerprint_marking;
use crate::marking::{pack_marking_config, unpack_marking_config, PreparedMarking};
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::stubborn::{compute_stubborn_set, DependencyGraph, PorStrategy};

/// Compact packed marking representation used by the generic Petri-net facade.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompactMarking {
    packed: Box<[u8]>,
}

impl CompactMarking {
    #[must_use]
    pub fn from_packed(packed: impl Into<Box<[u8]>>) -> Self {
        Self {
            packed: packed.into(),
        }
    }

    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.packed
    }

    #[must_use]
    pub fn fingerprint(&self) -> u128 {
        fingerprint_marking(&self.packed)
    }
}

/// `tla-mc-core` transition-system adapter for Petri nets.
#[derive(Debug, Clone)]
pub struct PetriNetSystem {
    net: PetriNet,
    prepared_marking: PreparedMarking,
}

impl PetriNetSystem {
    #[must_use]
    pub fn new(net: PetriNet) -> Self {
        let prepared_marking = PreparedMarking::analyze(&net);
        Self {
            net,
            prepared_marking,
        }
    }

    #[must_use]
    pub fn net(&self) -> &PetriNet {
        &self.net
    }

    #[must_use]
    pub fn pack_marking(&self, marking: &[u64]) -> CompactMarking {
        debug_assert_eq!(marking.len(), self.net.num_places());
        let mut packed = Vec::with_capacity(self.prepared_marking.packed_capacity());
        pack_marking_config(marking, &self.prepared_marking.config, &mut packed);
        CompactMarking::from_packed(packed)
    }

    #[must_use]
    pub fn unpack_marking(&self, marking: &CompactMarking) -> Vec<u64> {
        let mut unpacked = Vec::with_capacity(self.net.num_places());
        self.unpack_marking_into(marking, &mut unpacked);
        unpacked
    }

    pub(crate) fn unpack_marking_into(&self, marking: &CompactMarking, unpacked: &mut Vec<u64>) {
        unpack_marking_config(marking.as_bytes(), &self.prepared_marking.config, unpacked);
    }

    #[must_use]
    pub fn enabled_transitions(&self, marking: &CompactMarking) -> Vec<TransitionIdx> {
        let unpacked = self.unpack_marking(marking);
        (0..self.net.num_transitions())
            .map(|index| TransitionIdx(index as u32))
            .filter(|&transition| self.net.is_enabled(&unpacked, transition))
            .collect()
    }

    #[must_use]
    pub fn token_width_bytes(&self) -> usize {
        self.prepared_marking.width.bytes()
    }

    #[must_use]
    pub fn packed_places(&self) -> usize {
        self.prepared_marking.packed_places()
    }
}

impl From<PetriNet> for PetriNetSystem {
    fn from(net: PetriNet) -> Self {
        Self::new(net)
    }
}

impl TransitionSystem for PetriNetSystem {
    type State = CompactMarking;
    type Action = TransitionIdx;
    type Fingerprint = u128;

    fn initial_states(&self) -> Vec<Self::State> {
        vec![self.pack_marking(&self.net.initial_marking)]
    }

    fn successors(&self, state: &Self::State) -> Vec<(Self::Action, Self::State)> {
        let mut current = self.unpack_marking(state);
        let mut pack_buf = Vec::with_capacity(self.prepared_marking.packed_capacity());
        let mut successors = Vec::new();

        for transition in 0..self.net.num_transitions() {
            let transition = TransitionIdx(transition as u32);
            if !self.net.is_enabled(&current, transition) {
                continue;
            }

            self.net.apply_delta(&mut current, transition);
            pack_marking_config(&current, &self.prepared_marking.config, &mut pack_buf);
            successors.push((transition, CompactMarking::from_packed(pack_buf.as_slice())));
            self.net.undo_delta(&mut current, transition);
        }

        successors
    }

    fn fingerprint(&self, state: &Self::State) -> Self::Fingerprint {
        state.fingerprint()
    }
}

/// Stubborn-set POR provider for the generic Petri transition-system facade.
pub struct StubbornPorProvider {
    net: PetriNet,
    prepared_marking: PreparedMarking,
    dependency_graph: DependencyGraph,
    visible_transitions: Vec<TransitionIdx>,
}

impl StubbornPorProvider {
    #[must_use]
    pub fn new(net: PetriNet) -> Self {
        let prepared_marking = PreparedMarking::analyze(&net);
        let dependency_graph = DependencyGraph::build(&net);
        Self {
            net,
            prepared_marking,
            dependency_graph,
            visible_transitions: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_visible_transitions(mut self, visible_transitions: Vec<TransitionIdx>) -> Self {
        self.visible_transitions = visible_transitions;
        self
    }

    fn unpack_marking(&self, state: &CompactMarking) -> Vec<u64> {
        let mut unpacked = Vec::with_capacity(self.net.num_places());
        unpack_marking_config(
            state.as_bytes(),
            &self.prepared_marking.config,
            &mut unpacked,
        );
        unpacked
    }

    fn strategy_for(&self, property: PorPropertyClass) -> PorStrategy {
        match property {
            PorPropertyClass::Deadlock => PorStrategy::DeadlockPreserving,
            PorPropertyClass::Safety if !self.visible_transitions.is_empty() => {
                PorStrategy::SafetyPreserving {
                    visible: self.visible_transitions.clone(),
                }
            }
            _ => PorStrategy::None,
        }
    }
}

impl From<PetriNet> for StubbornPorProvider {
    fn from(net: PetriNet) -> Self {
        Self::new(net)
    }
}

impl PorProvider<PetriNetSystem> for StubbornPorProvider {
    fn reduce(
        &self,
        state: &CompactMarking,
        enabled: &[TransitionIdx],
        property: PorPropertyClass,
    ) -> Vec<TransitionIdx> {
        let strategy = self.strategy_for(property);
        if matches!(strategy, PorStrategy::None) {
            return enabled.to_vec();
        }

        let unpacked = self.unpack_marking(state);
        compute_stubborn_set(&self.net, &unpacked, &self.dependency_graph, &strategy)
            .unwrap_or_else(|| enabled.to_vec())
    }
}

#[cfg(test)]
mod tests {
    use tla_mc_core::{PorPropertyClass, PorProvider, TransitionSystem};

    use super::{PetriNetSystem, StubbornPorProvider};
    use crate::petri_net::{Arc, PetriNet, PlaceIdx, PlaceInfo, TransitionIdx, TransitionInfo};

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: None,
        }
    }

    fn arc(place: u32) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight: 1,
        }
    }

    fn transition(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: None,
            inputs,
            outputs,
        }
    }

    fn independent_choice_net() -> PetriNet {
        PetriNet {
            name: Some("independent".to_string()),
            places: vec![place("p0"), place("p1"), place("p2"), place("p3")],
            transitions: vec![
                transition("t0", vec![arc(0)], vec![arc(2)]),
                transition("t1", vec![arc(1)], vec![arc(3)]),
            ],
            initial_marking: vec![1, 1, 0, 0],
        }
    }

    #[test]
    fn transition_system_uses_compact_markings() {
        let system = PetriNetSystem::new(independent_choice_net());
        let initial = system
            .initial_states()
            .into_iter()
            .next()
            .expect("initial state");

        assert_eq!(system.unpack_marking(&initial), vec![1, 1, 0, 0]);
        assert!(system.token_width_bytes() >= 1);
        assert!(system.packed_places() <= system.net().num_places());
    }

    #[test]
    fn transition_system_successors_match_enabled_transitions() {
        let system = PetriNetSystem::new(independent_choice_net());
        let initial = system.initial_states().pop().expect("initial state");
        let successors = system.successors(&initial);

        assert_eq!(successors.len(), 2);
        let actions: Vec<TransitionIdx> = successors.iter().map(|(action, _)| *action).collect();
        assert_eq!(actions, vec![TransitionIdx(0), TransitionIdx(1)]);
    }

    #[test]
    fn deadlock_por_can_reduce_independent_enabled_transitions() {
        let net = independent_choice_net();
        let system = PetriNetSystem::new(net.clone());
        let provider = StubbornPorProvider::new(net);
        let initial = system.initial_states().pop().expect("initial state");
        let enabled = system.enabled_transitions(&initial);
        let reduced = provider.reduce(&initial, &enabled, PorPropertyClass::Deadlock);

        assert_eq!(enabled.len(), 2);
        assert_eq!(reduced.len(), 1);
    }

    #[test]
    fn unsupported_por_classes_fall_back_to_enabled_set() {
        let net = independent_choice_net();
        let system = PetriNetSystem::new(net.clone());
        let provider = StubbornPorProvider::new(net);
        let initial = system.initial_states().pop().expect("initial state");
        let enabled = system.enabled_transitions(&initial);

        assert_eq!(
            provider.reduce(&initial, &enabled, PorPropertyClass::Liveness),
            enabled
        );
    }
}
