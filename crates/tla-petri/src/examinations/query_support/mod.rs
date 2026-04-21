// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query support helpers for determining which places and transitions are
//! relevant to a given property query on a reduced Petri net.

mod closure;
mod collectors;
mod temporal;
mod types;
mod visibility;

pub(crate) use closure::{closure_on_reduced_net, relevance_cone_on_reduced_net};
pub(crate) use collectors::{reachability_support, upper_bounds_support};
pub(crate) use temporal::{ctl_support_with_aliases, ltl_property_support_with_aliases};
pub(crate) use types::QuerySupport;
pub(crate) use visibility::visible_transitions_for_support;

#[cfg(test)]
pub(crate) use temporal::ctl_support;

#[cfg(test)]
mod tests;
