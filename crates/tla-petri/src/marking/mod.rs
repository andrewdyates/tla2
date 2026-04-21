// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compact marking (state) representation for memory-efficient BFS exploration.

mod codec;
mod layout;
mod width;

pub(crate) use codec::{pack_marking_config, unpack_marking_config};
pub(crate) use layout::{MarkingConfig, PreparedMarking};
pub(crate) use width::TokenWidth;

#[cfg(test)]
pub(crate) use codec::{pack_marking, reconstruct_implied_places, unpack_marking};
#[cfg(test)]
pub(crate) use width::{determine_width, determine_width_with_invariants};

#[cfg(test)]
mod tests;
