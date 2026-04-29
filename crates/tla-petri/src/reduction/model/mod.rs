// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod reduced_net;
mod types;

pub(crate) use reduced_net::{identity_reduction, ReducedNet};
pub(crate) use types::{
    DuplicateTransitionClass, NeverDisablingArc, NeverDisablingProof, ParallelPlaceMerge,
    PlaceReconstruction, PostAgglomeration, PreAgglomeration, ReductionMode, ReductionReport,
    RuleRAgglomeration, RuleSAgglomeration, SelfLoopArc, SimpleChainPlace, TokenCycleMerge,
    RULE_R_EXPLOSION_LIMITER,
};

// `TransitionProvenance` is defined in `types.rs` for Phase-2 provenance
// tracking (tracking fused Rule R / Rule S transitions through `compose()`).
// Phase-1 synthesizes new transitions without provenance metadata; the type
// is retained in the model for upcoming phases but is not re-exported until
// the provenance plumbing lands.

#[cfg(test)]
mod tests;
