// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod reduced_net;
mod types;

pub(crate) use reduced_net::{identity_reduction, ReducedNet};
pub(crate) use types::{
    DuplicateTransitionClass, NeverDisablingArc, NeverDisablingProof, ParallelPlaceMerge,
    PlaceReconstruction, PostAgglomeration, PreAgglomeration, ReductionReport, SelfLoopArc,
};

#[cfg(test)]
mod tests;
