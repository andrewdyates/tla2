// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AIGER-based reachability seeding via Petri-to-AIGER cross-encoding.
//!
//! For bounded Petri nets, encodes the net as an AIGER circuit and runs the
//! tla-aiger IC3/BMC portfolio. This can resolve both AG and EF properties:
//!
//! - `AG(phi)`: encode `NOT phi` as the bad-state output. Safe => AG=TRUE,
//!   Unsafe => AG=FALSE.
//! - `EF(phi)`: encode `phi` as the bad-state output (negate the safety
//!   encoding). Safe => EF=FALSE, Unsafe => EF=TRUE.
//!
//! The cross-encoding only fires when:
//! 1. All places have finite LP upper bounds
//! 2. Total latch count <= 500 (the `encode_aiger` gating threshold)
//! 3. The property is a pure marking predicate (no IsFireable)
//!
//! This phase runs after LP seeding (which computes the bounds we need) and
//! before PDR seeding (AIGER portfolio is stronger for bounded nets).

use std::collections::HashMap;
use std::time::{Duration, Instant};

use crate::encode_aiger::try_encode_as_aiger;
use crate::lp_state_equation::lp_upper_bound;
use crate::petri_net::{PetriNet, PlaceIdx};
use crate::property_xml::PathQuantifier;
use crate::resolved_predicate::ResolvedPredicate;

use super::reachability::{resolve_tracker, PropertyTracker, ReachabilityResolutionSource};

/// Per-property timeout for AIGER portfolio checking.
const AIGER_SEED_TIMEOUT: Duration = Duration::from_secs(10);

/// Run AIGER-based seeding on unresolved reachability trackers.
///
/// For each unresolved tracker, attempts to:
/// 1. Compute LP upper bounds for all places
/// 2. Encode the net + property as an AIGER circuit
/// 3. Run the tla-aiger portfolio on the circuit
/// 4. Translate the result back to a Petri reachability verdict
pub(crate) fn run_aiger_seeding(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    deadline: Option<Instant>,
) {
    // Pre-compute LP bounds for all places once. If any place lacks a finite
    // bound, the AIGER encoding will reject the net, so we check eagerly.
    let bounds = match compute_all_place_bounds(net) {
        Some(bounds) => bounds,
        None => return, // Unbounded net — AIGER encoding not applicable
    };

    for tracker in trackers
        .iter_mut()
        .filter(|t| t.verdict.is_none())
    {
        let timeout = deadline
            .map(|limit| AIGER_SEED_TIMEOUT.min(limit.saturating_duration_since(Instant::now())))
            .unwrap_or(AIGER_SEED_TIMEOUT);
        if timeout.is_zero() {
            break;
        }

        // For AG(phi): safety property is phi (bad = NOT phi).
        // For EF(phi): safety property is NOT phi (bad = phi).
        //   If SAFE => NOT phi always holds => phi never holds => EF=FALSE.
        //   If UNSAFE => phi is reachable => EF=TRUE.
        let safety_property = match tracker.quantifier {
            PathQuantifier::AG => tracker.predicate.clone(),
            PathQuantifier::EF => ResolvedPredicate::Not(Box::new(tracker.predicate.clone())),
        };

        // Attempt AIGER encoding. Returns None if the property uses IsFireable,
        // latch count exceeds threshold, or bounds are incomplete.
        let encoding = match try_encode_as_aiger(net, &safety_property, &bounds) {
            Some(enc) => enc,
            None => continue,
        };

        eprintln!(
            "AIGER encoding: {} latches, {} transitions for property {}",
            encoding.num_latches, encoding.num_transitions, tracker.id,
        );

        // Run the tla-aiger portfolio on the encoded circuit.
        let results = tla_aiger::check_aiger_sat(&encoding.circuit, Some(timeout));

        // The encoding produces a single bad-state output, so results[0] is
        // the verdict for our property.
        if let Some(result) = results.first() {
            match result {
                tla_aiger::AigerCheckResult::Unsat => {
                    // Safety holds: bad state unreachable.
                    match tracker.quantifier {
                        PathQuantifier::AG => {
                            // AG(phi) + Safe => phi always holds => TRUE
                            resolve_tracker(
                                tracker,
                                true,
                                ReachabilityResolutionSource::Aiger,
                                None,
                            );
                        }
                        PathQuantifier::EF => {
                            // EF(phi) encoded as safety of NOT phi. Safe => NOT phi
                            // always holds => phi never reachable => EF=FALSE.
                            resolve_tracker(
                                tracker,
                                false,
                                ReachabilityResolutionSource::Aiger,
                                None,
                            );
                        }
                    }
                }
                tla_aiger::AigerCheckResult::Sat { .. } => {
                    // Safety violated: bad state reachable.
                    match tracker.quantifier {
                        PathQuantifier::AG => {
                            // AG(phi) + Unsafe => phi violated => FALSE
                            resolve_tracker(
                                tracker,
                                false,
                                ReachabilityResolutionSource::Aiger,
                                None,
                            );
                        }
                        PathQuantifier::EF => {
                            // EF(phi) encoded as safety of NOT phi. Unsafe => NOT phi
                            // violated => phi reachable => EF=TRUE.
                            resolve_tracker(
                                tracker,
                                true,
                                ReachabilityResolutionSource::Aiger,
                                None,
                            );
                        }
                    }
                }
                tla_aiger::AigerCheckResult::Unknown { .. } => {
                    // Inconclusive — fall through to subsequent phases.
                }
            }
        }
    }
}

/// Compute LP upper bounds for every place in the net.
///
/// Returns `None` if any place has an unbounded token count (LP returns
/// `None` for that place), meaning the AIGER encoding is not applicable.
fn compute_all_place_bounds(net: &PetriNet) -> Option<HashMap<PlaceIdx, u64>> {
    let mut bounds = HashMap::with_capacity(net.num_places());
    for p in 0..net.num_places() {
        let place_idx = PlaceIdx(p as u32);
        let bound = lp_upper_bound(net, &[place_idx])?;
        bounds.insert(place_idx, bound);
    }
    Some(bounds)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::examinations::reachability::{PropertyTracker, ReachabilityResolutionSource};
    use crate::petri_net::{Arc, PetriNet, PlaceInfo, TransitionInfo};
    use crate::property_xml::PathQuantifier;
    use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: None,
        }
    }

    fn arc(place: u32, weight: u64) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight,
        }
    }

    fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: None,
            inputs,
            outputs,
        }
    }

    fn make_tracker(id: &str, quantifier: PathQuantifier, predicate: ResolvedPredicate) -> PropertyTracker {
        PropertyTracker {
            id: id.to_string(),
            quantifier,
            predicate,
            verdict: None,
            resolved_by: None,
            flushed: false,
        }
    }

    #[test]
    fn test_aiger_seeding_ag_safe_mutex() {
        // Mutex: free + busy conserved = 1. AG(busy <= 1) should be TRUE.
        let net = PetriNet {
            name: None,
            places: vec![place("free"), place("busy")],
            transitions: vec![
                trans("acquire", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("release", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let predicate = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        );
        let mut trackers = vec![make_tracker("AG-mutex", PathQuantifier::AG, predicate)];

        run_aiger_seeding(&net, &mut trackers, None);

        assert_eq!(trackers[0].verdict, Some(true), "AG(busy<=1) should be TRUE");
        assert_eq!(
            trackers[0].resolved_by.as_ref().map(|r| r.source),
            Some(ReachabilityResolutionSource::Aiger),
        );
    }

    #[test]
    fn test_aiger_seeding_ef_reachable() {
        // Same mutex net. EF(busy >= 1) should be TRUE (acquire fires once).
        let net = PetriNet {
            name: None,
            places: vec![place("free"), place("busy")],
            transitions: vec![
                trans("acquire", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("release", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let predicate = ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        );
        let mut trackers = vec![make_tracker("EF-busy", PathQuantifier::EF, predicate)];

        run_aiger_seeding(&net, &mut trackers, None);

        assert_eq!(trackers[0].verdict, Some(true), "EF(busy>=1) should be TRUE");
        assert_eq!(
            trackers[0].resolved_by.as_ref().map(|r| r.source),
            Some(ReachabilityResolutionSource::Aiger),
        );
    }

    #[test]
    fn test_aiger_seeding_ef_unreachable() {
        // Conserving net: free + busy = 1. EF(busy >= 2) should be FALSE.
        let net = PetriNet {
            name: None,
            places: vec![place("free"), place("busy")],
            transitions: vec![
                trans("acquire", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("release", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let predicate = ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(2),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
        );
        let mut trackers = vec![make_tracker("EF-unreachable", PathQuantifier::EF, predicate)];

        run_aiger_seeding(&net, &mut trackers, None);

        assert_eq!(trackers[0].verdict, Some(false), "EF(busy>=2) should be FALSE");
    }

    #[test]
    fn test_aiger_seeding_skips_unbounded_net() {
        // Unbounded net: transition produces with no input. AIGER should skip.
        let net = PetriNet {
            name: None,
            places: vec![place("p0")],
            transitions: vec![trans("t0", vec![], vec![arc(0, 1)])],
            initial_marking: vec![0],
        };

        let predicate = ResolvedPredicate::IntLe(
            ResolvedIntExpr::Constant(1),
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
        );
        let mut trackers = vec![make_tracker("EF-unbounded", PathQuantifier::EF, predicate)];

        run_aiger_seeding(&net, &mut trackers, None);

        assert_eq!(trackers[0].verdict, None, "Should skip unbounded net");
    }

    #[test]
    fn test_aiger_seeding_skips_already_resolved() {
        let net = PetriNet {
            name: None,
            places: vec![place("free"), place("busy")],
            transitions: vec![
                trans("acquire", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("release", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let predicate = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        );
        let mut trackers = vec![make_tracker("AG-already", PathQuantifier::AG, predicate)];
        // Pre-resolve
        trackers[0].verdict = Some(true);

        run_aiger_seeding(&net, &mut trackers, None);

        // Should remain as-is (no change to resolved_by)
        assert_eq!(trackers[0].resolved_by, None);
    }

    #[test]
    fn test_compute_all_place_bounds_conserving() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
            initial_marking: vec![3, 0],
        };

        let bounds = compute_all_place_bounds(&net);
        assert!(bounds.is_some());
        let bounds = bounds.expect("should have bounds");
        assert_eq!(bounds[&PlaceIdx(0)], 3);
        assert_eq!(bounds[&PlaceIdx(1)], 3);
    }

    #[test]
    fn test_compute_all_place_bounds_unbounded() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0")],
            transitions: vec![trans("t0", vec![], vec![arc(0, 1)])],
            initial_marking: vec![0],
        };

        let bounds = compute_all_place_bounds(&net);
        assert!(bounds.is_none());
    }
}
