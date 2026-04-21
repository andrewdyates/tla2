// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Reduced-net support collectors for reachability and upper-bounds queries.

use crate::petri_net::PlaceIdx;
use crate::reduction::ReducedNet;
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

use crate::examinations::reachability::PropertyTracker;

use super::types::QuerySupport;

pub(crate) fn upper_bounds_support(
    reduced: &ReducedNet,
    tracker_place_sets: &[Vec<PlaceIdx>],
) -> Option<QuerySupport> {
    let mut support = QuerySupport::new(reduced.net.num_places(), reduced.net.num_transitions());
    for place_set in tracker_place_sets {
        for place in place_set {
            match reduced.place_map[place.0 as usize] {
                Some(reduced_place) => {
                    support.places[reduced_place.0 as usize] = true;
                }
                None => {
                    let recon = reduced.reconstructions.iter().find(|r| r.place == *place)?;
                    for &(term_place, _) in &recon.terms {
                        let reduced_term = reduced.place_map[term_place.0 as usize]?;
                        support.places[reduced_term.0 as usize] = true;
                    }
                }
            }
        }
    }
    Some(support)
}

pub(crate) fn reachability_support(
    reduced: &ReducedNet,
    trackers: &[PropertyTracker],
) -> Option<QuerySupport> {
    let mut support = QuerySupport::new(reduced.net.num_places(), reduced.net.num_transitions());
    for tracker in trackers.iter().filter(|tracker| tracker.verdict.is_none()) {
        collect_predicate_support(&tracker.predicate, reduced, &mut support)?;
    }
    Some(support)
}

pub(super) fn collect_predicate_support(
    predicate: &ResolvedPredicate,
    reduced: &ReducedNet,
    support: &mut QuerySupport,
) -> Option<()> {
    match predicate {
        ResolvedPredicate::And(children) | ResolvedPredicate::Or(children) => {
            for child in children {
                collect_predicate_support(child, reduced, support)?;
            }
            Some(())
        }
        ResolvedPredicate::Not(inner) => collect_predicate_support(inner, reduced, support),
        ResolvedPredicate::IntLe(left, right) => {
            collect_int_expr_support(left, reduced, support)?;
            collect_int_expr_support(right, reduced, support)
        }
        ResolvedPredicate::IsFireable(transitions) => {
            for transition in transitions {
                let reduced_transition = reduced.transition_map[transition.0 as usize]?;
                support.transitions[reduced_transition.0 as usize] = true;
            }
            Some(())
        }
        ResolvedPredicate::True | ResolvedPredicate::False => Some(()),
    }
}

fn collect_int_expr_support(
    expression: &ResolvedIntExpr,
    reduced: &ReducedNet,
    support: &mut QuerySupport,
) -> Option<()> {
    match expression {
        ResolvedIntExpr::Constant(_) => Some(()),
        ResolvedIntExpr::TokensCount(places) => {
            for place in places {
                match reduced.place_map[place.0 as usize] {
                    Some(reduced_place) => {
                        support.places[reduced_place.0 as usize] = true;
                    }
                    None => {
                        // Place was removed. If it has a P-invariant reconstruction,
                        // its value depends on the reconstruction terms (which are
                        // in the reduced net). Add those terms to the support so
                        // POR marks transitions affecting them as visible.
                        let recon = reduced.reconstructions.iter().find(|r| r.place == *place)?;
                        for &(term_place, _) in &recon.terms {
                            let reduced_term = reduced.place_map[term_place.0 as usize]?;
                            support.places[reduced_term.0 as usize] = true;
                        }
                    }
                }
            }
            Some(())
        }
    }
}
