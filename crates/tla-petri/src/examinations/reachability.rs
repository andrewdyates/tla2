// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ReachabilityCardinality and ReachabilityFireability examinations.
//!
//! Both examinations share the same observer: each property is an EF(φ) or
//! AG(φ) formula where φ is a boolean predicate over markings (integer
//! comparisons on token counts) and transition enablement.
//!
//! - EF(φ): TRUE if any reachable state satisfies φ.
//! - AG(φ): TRUE if all reachable states satisfy φ.
//!
//! The observer evaluates all properties simultaneously during a single BFS
//! pass and early-terminates when all properties have definitive answers.
//!
//! Before BFS, bounded model checking (BMC) via z4 is attempted on the
//! original net. BMC can seed witness verdicts (EF=TRUE, AG=FALSE) without
//! full exploration. BFS then handles the remaining unresolved properties.

mod observer;
mod pipeline;
mod reduction;
mod types;

pub(crate) use pipeline::check_reachability_properties_with_aliases;
pub(crate) use pipeline::check_reachability_properties_with_flush;
pub(crate) use types::{resolve_tracker, PropertyTracker, ReachabilityResolutionSource};

#[cfg(test)]
pub(crate) use observer::ReachabilityObserver;
#[cfg(test)]
pub(crate) use pipeline::check_reachability_properties;
#[cfg(test)]
pub(crate) use reduction::protected_places_for_prefire;
#[cfg(test)]
pub(crate) use types::prepare_trackers;

// Test-visible re-exports: the test sidecars use `super::*` and expect items
// that previously lived directly in this file.
#[cfg(test)]
pub(super) use reduction::{explore_reachability_on_reduced_net, reduce_reachability_queries};
#[cfg(test)]
pub(super) use types::assemble_results;

// LP state equation seeding is implemented in reachability_lp module.
// It handles both EF (direct infeasibility) and AG (conjunction decomposition).

#[cfg(test)]
#[path = "reachability_tests/mod.rs"]
mod tests;

#[cfg(test)]
#[path = "reachability_por_tests.rs"]
mod por_tests;
