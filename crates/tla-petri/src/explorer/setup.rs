// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::marking::{pack_marking_config, MarkingConfig, PreparedMarking};
use crate::petri_net::PetriNet;

/// Shared explorer-specific preparation used by all execution backends.
pub(crate) struct ExplorationSetup {
    pub(crate) marking_config: MarkingConfig,
    pub(crate) pack_capacity: usize,
    pub(crate) num_places: usize,
    pub(crate) num_transitions: usize,
    pub(crate) initial_packed: Box<[u8]>,
}

impl ExplorationSetup {
    pub(crate) fn analyze(net: &PetriNet) -> Self {
        let prepared = PreparedMarking::analyze(net);
        let pack_capacity = prepared.packed_capacity();
        let marking_config = prepared.config;
        let num_places = marking_config.num_places;
        let num_transitions = net.num_transitions();

        let mut pack_buf = Vec::with_capacity(pack_capacity);
        pack_marking_config(&net.initial_marking, &marking_config, &mut pack_buf);
        let initial_packed: Box<[u8]> = pack_buf.as_slice().into();

        Self {
            marking_config,
            pack_capacity,
            num_places,
            num_transitions,
            initial_packed,
        }
    }
}
