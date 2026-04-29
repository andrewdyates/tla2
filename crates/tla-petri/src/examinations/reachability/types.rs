// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared tracker and preparation types for reachability examinations.

use serde::{Deserialize, Serialize};

use crate::examinations::reachability_witness::WitnessValidationTarget;
use crate::model::PropertyAliases;
use crate::output::Verdict;
use crate::property_xml::{Formula, PathQuantifier, Property, ReachabilityFormula};
use crate::resolved_predicate::{
    count_unresolved_with_aliases, resolve_predicate_with_aliases, ResolvedPredicate,
};

/// Which pipeline phase resolved a reachability property.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum ReachabilityResolutionSource {
    Bmc,
    Lp,
    Aiger,
    Pdr,
    Kinduction,
    RandomWalk,
    Heuristic,
    BfsWitness,
    BfsCounterexample,
    ExhaustiveCompletion,
}

/// Attribution record for a resolved reachability verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ReachabilityResolution {
    pub(crate) source: ReachabilityResolutionSource,
    pub(crate) depth: Option<usize>,
}

/// Prepared reachability property: classified before BFS starts.
pub(crate) enum PreparedProperty {
    /// Formula has unresolved names — emit `CANNOT_COMPUTE` without BFS.
    Invalid { id: String },
    /// Formula is valid — participate in BFS at observer slot `slot`.
    Valid { slot: usize },
}

/// Per-property tracking state during BFS.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct PropertyTracker {
    pub(crate) id: String,
    pub(crate) quantifier: PathQuantifier,
    pub(crate) predicate: ResolvedPredicate,
    /// Definitive verdict, if determined (may be pre-seeded by BMC).
    pub(crate) verdict: Option<bool>,
    /// Which pipeline phase resolved this property (first-writer-wins).
    pub(crate) resolved_by: Option<ReachabilityResolution>,
    /// Whether this property's FORMULA line has been printed to stdout already.
    /// Set by [`flush_resolved`] for crash-resilient incremental output.
    pub(crate) flushed: bool,
}

/// Resolve a property tracker's verdict with provenance attribution.
///
/// First-writer-wins: if the tracker already has a verdict, does nothing.
/// When `PNML_REACH_TRACE` is set and the tracker id matches a substring,
/// emits a trace line to stderr.
pub(crate) fn resolve_tracker(
    tracker: &mut PropertyTracker,
    verdict: bool,
    source: ReachabilityResolutionSource,
    depth: Option<usize>,
) {
    if tracker.verdict.is_some() {
        return;
    }
    tracker.verdict = Some(verdict);
    tracker.resolved_by = Some(ReachabilityResolution { source, depth });

    if let Ok(filter) = std::env::var("PNML_REACH_TRACE") {
        if filter.split(',').any(|sub| tracker.id.contains(sub.trim())) {
            eprintln!(
                "REACH-TRACE property={} phase={:?} verdict={} depth={}",
                tracker.id,
                source,
                if verdict { "TRUE" } else { "FALSE" },
                depth.map_or("-".to_string(), |d| d.to_string()),
            );
        }
    }
}

/// Stamp unresolved trackers as `ExhaustiveCompletion` after a completed BFS.
///
/// Call only when BFS exploration is confirmed complete (`result.completed == true`).
pub(crate) fn finalize_exhaustive_completion(trackers: &mut [PropertyTracker]) {
    for tracker in trackers.iter_mut() {
        if tracker.verdict.is_some() {
            continue;
        }
        let verdict = match tracker.quantifier {
            PathQuantifier::EF => false,
            PathQuantifier::AG => true,
        };
        resolve_tracker(
            tracker,
            verdict,
            ReachabilityResolutionSource::ExhaustiveCompletion,
            None,
        );
    }
}

/// Count unresolved names in a reachability formula's state predicate.
fn count_unresolved_reachability(
    formula: &ReachabilityFormula,
    aliases: &PropertyAliases,
) -> (usize, usize) {
    count_unresolved_with_aliases(&formula.predicate, aliases)
}

/// Prepare resolved trackers from properties, classifying as Valid or Invalid.
///
/// Returns `(prepared_order, trackers, validation_targets)` where trackers and
/// validation targets correspond to Valid entries at the same slot.
pub(in crate::examinations) fn prepare_trackers_with_aliases(
    original_properties: &[Property],
    simplified_properties: &[Property],
    aliases: &PropertyAliases,
) -> (
    Vec<PreparedProperty>,
    Vec<PropertyTracker>,
    Vec<WitnessValidationTarget>,
) {
    debug_assert_eq!(original_properties.len(), simplified_properties.len());

    let mut trackers = Vec::new();
    let mut validation_targets = Vec::new();
    let prepared: Vec<PreparedProperty> = original_properties
        .iter()
        .zip(simplified_properties.iter())
        .filter_map(|(original, simplified)| {
            let Formula::Reachability(ref original_rf) = original.formula else {
                return None;
            };
            let Formula::Reachability(ref simplified_rf) = simplified.formula else {
                return None;
            };
            let (total, unresolved) = count_unresolved_reachability(simplified_rf, aliases);
            if unresolved > 0 {
                eprintln!(
                    "Reachability resolution guard: {} has {unresolved}/{total} \
                     unresolved names → CANNOT_COMPUTE",
                    simplified.id
                );
                Some(PreparedProperty::Invalid {
                    id: simplified.id.clone(),
                })
            } else {
                let slot = trackers.len();
                let resolved = resolve_predicate_with_aliases(&simplified_rf.predicate, aliases);
                trackers.push(PropertyTracker {
                    id: simplified.id.clone(),
                    quantifier: simplified_rf.quantifier,
                    predicate: resolved,
                    verdict: None,
                    resolved_by: None,
                    flushed: false,
                });
                validation_targets.push(WitnessValidationTarget {
                    original_predicate: resolve_predicate_with_aliases(
                        &original_rf.predicate,
                        aliases,
                    ),
                });
                Some(PreparedProperty::Valid { slot })
            }
        })
        .collect();

    (prepared, trackers, validation_targets)
}

/// Print FORMULA lines for newly-resolved properties and mark them as flushed.
///
/// Each resolved-but-unflushed tracker gets a FORMULA line printed to stdout
/// immediately, then is marked `flushed = true`. This provides crash-resilient
/// output: if the process is killed mid-pipeline, all previously-flushed
/// results survive on stdout.
///
/// Returns the number of newly flushed properties.
pub(in crate::examinations) fn flush_resolved(trackers: &mut [PropertyTracker]) -> usize {
    let mut count = 0;
    for tracker in trackers.iter_mut() {
        if tracker.verdict.is_some() && !tracker.flushed {
            let verdict = match tracker.verdict {
                Some(true) => Verdict::True,
                Some(false) => Verdict::False,
                None => unreachable!(),
            };
            println!("FORMULA {} {} TECHNIQUES EXPLICIT", tracker.id, verdict);
            tracker.flushed = true;
            count += 1;
        }
    }
    count
}

/// Assemble final ordered results from prepared classification and tracker verdicts.
///
/// When `skip_flushed` is true, properties already printed by [`flush_resolved`]
/// are omitted from the returned vec to prevent duplicate FORMULA lines.
pub(in crate::examinations) fn assemble_results(
    prepared: &[PreparedProperty],
    trackers: &[PropertyTracker],
    completed: bool,
    skip_flushed: bool,
) -> Vec<(String, Verdict)> {
    prepared
        .iter()
        .filter_map(|p| match p {
            PreparedProperty::Invalid { id } => Some((id.clone(), Verdict::CannotCompute)),
            PreparedProperty::Valid { slot } => {
                let tracker = &trackers[*slot];
                if skip_flushed && tracker.flushed {
                    return None;
                }
                let verdict = if completed {
                    match tracker.verdict {
                        Some(true) => Verdict::True,
                        Some(false) => Verdict::False,
                        None => match tracker.quantifier {
                            PathQuantifier::EF => Verdict::False,
                            PathQuantifier::AG => Verdict::True,
                        },
                    }
                } else {
                    match tracker.verdict {
                        Some(true) => Verdict::True,
                        Some(false) => Verdict::False,
                        None => Verdict::CannotCompute,
                    }
                };
                Some((tracker.id.clone(), verdict))
            }
        })
        .collect()
}

#[cfg(test)]
pub(crate) fn prepare_trackers(
    net: &crate::petri_net::PetriNet,
    properties: &[Property],
) -> (Vec<PreparedProperty>, Vec<PropertyTracker>) {
    let aliases = PropertyAliases::identity(net);
    let (prepared, trackers, _) = prepare_trackers_with_aliases(properties, properties, &aliases);
    (prepared, trackers)
}
