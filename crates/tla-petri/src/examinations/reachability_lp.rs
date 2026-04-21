// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LP state-equation pre-seeding for reachability properties.
//!
//! Runs between BMC witness seeding and BFS exploration. Uses the LP
//! relaxation of the Petri net state equation to prove *unreachability*:
//!
//! - `EF(φ)`: if LP says `φ` is infeasible → seed `FALSE`
//! - `AG(φ)`: if every LP-checkable conjunct has an LP-infeasible violation
//!   (`lhs > rhs`) → seed `TRUE`
//!
//! Only handles LP-amenable predicates (conjunctions of `IntLe` atoms).
//! Non-amenable formulas (Or, IsFireable, nested Not) are left unresolved
//! for BFS.

use crate::lp_state_equation::{lp_always_true, lp_unreachable};
use crate::petri_net::PetriNet;
use crate::property_xml::PathQuantifier;

use super::reachability::{resolve_tracker, PropertyTracker, ReachabilityResolutionSource};

/// Run LP state-equation seeding on unresolved reachability trackers.
///
/// For each tracker without a verdict:
/// - `EF(φ)`: if `φ` is LP-infeasible, seed `FALSE`
/// - `AG(φ)`: if every violating atom of `φ` is LP-infeasible, seed `TRUE`
pub(crate) fn run_lp_seeding(net: &PetriNet, trackers: &mut [PropertyTracker]) {
    for tracker in trackers.iter_mut() {
        if tracker.verdict.is_some() {
            continue;
        }
        match tracker.quantifier {
            PathQuantifier::EF => {
                // EF(φ): if φ is unreachable, then EF(φ) = FALSE.
                if lp_unreachable(net, &tracker.predicate) {
                    resolve_tracker(tracker, false, ReachabilityResolutionSource::Lp, None);
                }
            }
            PathQuantifier::AG => {
                // AG(φ): true iff no reachable state violates φ.
                if lp_always_true(net, &tracker.predicate) {
                    resolve_tracker(tracker, true, ReachabilityResolutionSource::Lp, None);
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "reachability_lp_tests.rs"]
mod tests;
