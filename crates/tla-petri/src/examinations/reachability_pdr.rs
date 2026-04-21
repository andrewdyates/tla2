// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PDR/IC3 reachability seeding on Petri nets.
//!
//! This phase can resolve both reachability directions:
//! - `AG(phi)` by proving safety of `phi`
//! - `EF(phi)` by disproving safety of `not phi`

use std::time::{Duration, Instant};

use crate::petri_net::PetriNet;
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::ResolvedPredicate;

use super::pdr_encoding::{solve_petri_net_pdr, PdrCheckResult, PdrConfig};
use super::reachability::{resolve_tracker, PropertyTracker, ReachabilityResolutionSource};

const PDR_SEED_TIMEOUT: Duration = Duration::from_secs(5);

pub(crate) fn run_pdr_seeding(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    deadline: Option<Instant>,
) {
    for tracker in trackers
        .iter_mut()
        .filter(|tracker| tracker.verdict.is_none())
    {
        let timeout = deadline
            .map(|limit| PDR_SEED_TIMEOUT.min(limit.saturating_duration_since(Instant::now())))
            .unwrap_or(PDR_SEED_TIMEOUT);
        if timeout.is_zero() {
            break;
        }

        let safety_property = match tracker.quantifier {
            PathQuantifier::AG => tracker.predicate.clone(),
            PathQuantifier::EF => ResolvedPredicate::Not(Box::new(tracker.predicate.clone())),
        };
        let result = solve_petri_net_pdr(
            net,
            &safety_property,
            &PdrConfig {
                time_budget: timeout,
                ..PdrConfig::default()
            },
        );

        match (tracker.quantifier, result) {
            (PathQuantifier::AG, PdrCheckResult::Safe) => {
                resolve_tracker(tracker, true, ReachabilityResolutionSource::Pdr, None)
            }
            (PathQuantifier::AG, PdrCheckResult::Unsafe) => {
                resolve_tracker(tracker, false, ReachabilityResolutionSource::Pdr, None)
            }
            (PathQuantifier::EF, PdrCheckResult::Safe) => {
                resolve_tracker(tracker, false, ReachabilityResolutionSource::Pdr, None)
            }
            (PathQuantifier::EF, PdrCheckResult::Unsafe) => {
                resolve_tracker(tracker, true, ReachabilityResolutionSource::Pdr, None)
            }
            (_, PdrCheckResult::Unknown) => {}
        }
    }
}

#[cfg(test)]
#[path = "reachability_pdr_tests.rs"]
mod tests;
