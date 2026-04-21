// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pipeline orchestration for reachability examinations.
//!
//! Manages the multi-phase execution: simplification → BMC → LP → AIGER → PDR
//! → k-induction → random walk → heuristic search → structural reduction → BFS.

use std::sync::Arc;

use crate::explorer::{
    explore_checkpointable_observer, explore_observer, CheckpointableObserver, ExplorationConfig,
    ParallelExplorationObserver,
};
use crate::intelligence_bus::{self, IntelligenceBus};
use crate::model::PropertyAliases;
use crate::output::Verdict;
use crate::petri_net::PetriNet;
use crate::property_xml::Property;
use crate::reduction::ReducedNet;

use super::observer::ReachabilityObserver;
use super::reduction::{
    all_predicates_reduction_safe, build_reachability_slice, explore_reachability_on_reduced_net,
    explore_reachability_on_slice, reduce_reachability_queries,
};
use super::types::{
    assemble_results, finalize_exhaustive_completion, flush_resolved, prepare_trackers_with_aliases,
};

use crate::examinations::kinduction;
use crate::examinations::reachability_aiger;
use crate::examinations::reachability_bmc;
use crate::examinations::reachability_heuristic;
use crate::examinations::reachability_lp;
use crate::examinations::reachability_pdr;
use crate::examinations::reachability_por::reachability_por_config;
use crate::examinations::reachability_walk;
use crate::examinations::reachability_witness::WitnessValidationContext;
const CHECKPOINT_MANIFEST_FILE: &str = "checkpoint.json";

fn cannot_compute_results(
    properties: &[Property],
    error: &impl std::fmt::Display,
) -> Vec<(String, Verdict)> {
    eprintln!("Reachability: CANNOT_COMPUTE ({error})");
    properties
        .iter()
        .map(|property| (property.id.clone(), Verdict::CannotCompute))
        .collect()
}

fn incremental_flush_enabled(config: &ExplorationConfig, flush: bool) -> bool {
    flush
        && !config.checkpoint().is_some_and(|checkpoint| {
            checkpoint.resume && checkpoint.dir.join(CHECKPOINT_MANIFEST_FILE).exists()
        })
}

fn explore_with_optional_checkpoint<O>(
    net: &PetriNet,
    config: &ExplorationConfig,
    observer: &mut O,
) -> Result<crate::explorer::ExplorationResult, std::io::Error>
where
    O: ParallelExplorationObserver + CheckpointableObserver + Send,
{
    if config.checkpoint().is_some() {
        explore_checkpointable_observer(net, config, observer)
    } else {
        Ok(explore_observer(net, config, observer))
    }
}

/// Check reachability properties with fail-closed unresolved-name guard.
///
/// Runs BMC on the original net first (witness-only), then BFS on the
/// reduced net for any remaining unresolved properties.
///
/// Safety: returns `CannotCompute` for any formula with unresolved place or
/// transition names. Silent name drops during resolution produce degenerate
/// predicates (`False` for is-fireable, `0` for tokens-count) that corrupt
/// evaluation results.
/// Test entry point: returns all results without incremental stdout flushing.
#[cfg(test)]
pub(crate) fn check_reachability_properties(
    net: &PetriNet,
    properties: &[Property],
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    let aliases = PropertyAliases::identity(net);
    check_reachability_properties_inner(net, properties, &aliases, config, false)
}

/// Collection entry point: returns all results without incremental flushing.
/// Used by `collect_examination_core` and tests that inspect return values.
pub(crate) fn check_reachability_properties_with_aliases(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    check_reachability_properties_inner(net, properties, aliases, config, false)
}

/// MCC binary entry point: prints FORMULA lines incrementally between phases
/// for crash-resilient output, and returns only unflushed (BFS-phase) results.
///
/// Wired into `run_examination_for_model` / `run_examination_with_dir` via
/// `collect_examination_core(flush=true)`.
pub(crate) fn check_reachability_properties_with_flush(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
) -> Vec<(String, Verdict)> {
    check_reachability_properties_inner(net, properties, aliases, config, true)
}

/// Inner pipeline: when `flush` is true, prints resolved FORMULA lines to
/// stdout between phases and omits them from the return value. When false,
/// returns all results in the vec (test mode).
fn check_reachability_properties_inner(
    net: &PetriNet,
    properties: &[Property],
    aliases: &PropertyAliases,
    config: &ExplorationConfig,
    flush: bool,
) -> Vec<(String, Verdict)> {
    let incremental_flush = incremental_flush_enabled(config, flush);

    // Create the intelligence bus for cross-technique cooperation.
    // Seed it with LP bounds and P-invariant constraints so BFS can prune
    // markings that violate proved structural invariants.
    let bus = Arc::new(IntelligenceBus::new());
    intelligence_bus::seed_from_lp(&bus, net);

    // Phase 0: simplify formulas using structural facts and LP proofs.
    let simplified =
        crate::formula_simplify::simplify_properties_with_aliases(net, properties, aliases);
    let simplified_properties = &simplified;

    // Phase 1: classify each property as Valid or Invalid, preserving order.
    let (prepared, mut trackers, validation_targets) =
        prepare_trackers_with_aliases(properties, simplified_properties, aliases);
    let validation = WitnessValidationContext::new(net, &validation_targets);

    // Phase 2: run BMC on the original net to find witnesses.
    // BMC can seed EF(true) and AG(false) verdicts without full exploration.
    // Also returns the max depth where all properties completed (base case for k-induction).
    let max_bmc_depth;
    if !trackers.is_empty() {
        max_bmc_depth = reachability_bmc::run_bmc_seeding(net, &mut trackers, config.deadline());
        let seeded = trackers.iter().filter(|t| t.verdict.is_some()).count();
        if seeded > 0 {
            eprintln!(
                "BMC seeded {seeded}/{} reachability verdicts",
                trackers.len()
            );
        }
        if trackers.iter().all(|t| t.verdict.is_some()) {
            if incremental_flush {
                flush_resolved(&mut trackers);
            }
            return assemble_results(&prepared, &trackers, true, incremental_flush);
        }
    } else {
        max_bmc_depth = None;
    }

    // Flush BMC-resolved verdicts to stdout for crash resilience.
    if incremental_flush {
        flush_resolved(&mut trackers);
    }

    // Phase 2b: LP state equation seeding.
    // LP can prove EF(phi) = FALSE when the state equation + phi is infeasible,
    // and AG(phi) = TRUE when every violating atom is LP-infeasible.
    if !trackers.is_empty() {
        let pre_lp = trackers.iter().filter(|t| t.verdict.is_some()).count();
        reachability_lp::run_lp_seeding(net, &mut trackers);
        let post_lp = trackers.iter().filter(|t| t.verdict.is_some()).count();
        let lp_seeded = post_lp - pre_lp;
        if lp_seeded > 0 {
            eprintln!(
                "LP state equation seeded {lp_seeded}/{} reachability verdicts",
                trackers.len(),
            );
        }
        if trackers.iter().all(|t| t.verdict.is_some()) {
            if incremental_flush {
                flush_resolved(&mut trackers);
            }
            return assemble_results(&prepared, &trackers, true, incremental_flush);
        }
    }

    if incremental_flush {
        flush_resolved(&mut trackers);
    }

    // Phase 2b2: AIGER cross-encoding seeding.
    // For bounded nets, encodes the Petri net as an AIGER circuit and runs
    // the tla-aiger IC3/BMC portfolio. This is the single most impactful
    // technique for bounded safety checking — it leverages the full 60-config
    // hardware model checking portfolio on the encoded circuit.
    if trackers.iter().any(|t| t.verdict.is_none()) {
        let pre_aiger = trackers.iter().filter(|t| t.verdict.is_some()).count();
        reachability_aiger::run_aiger_seeding(net, &mut trackers, config.deadline());
        let post_aiger = trackers.iter().filter(|t| t.verdict.is_some()).count();
        let aiger_seeded = post_aiger - pre_aiger;
        if aiger_seeded > 0 {
            eprintln!(
                "AIGER portfolio seeded {aiger_seeded}/{} reachability verdicts",
                trackers.len(),
            );
        }
        if trackers.iter().all(|t| t.verdict.is_some()) {
            if incremental_flush {
                flush_resolved(&mut trackers);
            }
            return assemble_results(&prepared, &trackers, true, incremental_flush);
        }
    }

    if incremental_flush {
        flush_resolved(&mut trackers);
    }

    // Phase 2c: PDR/IC3 seeding.
    // Resolves AG(φ) as safety on φ and EF(φ) via safety of ¬φ.
    if trackers.iter().any(|t| t.verdict.is_none()) {
        let pre_pdr = trackers.iter().filter(|t| t.verdict.is_some()).count();
        reachability_pdr::run_pdr_seeding(net, &mut trackers, config.deadline());
        let post_pdr = trackers.iter().filter(|t| t.verdict.is_some()).count();
        let pdr_seeded = post_pdr - pre_pdr;
        if pdr_seeded > 0 {
            eprintln!(
                "PDR seeded {pdr_seeded}/{} reachability verdicts",
                trackers.len(),
            );
        }
        if trackers.iter().all(|t| t.verdict.is_some()) {
            if incremental_flush {
                flush_resolved(&mut trackers);
            }
            return assemble_results(&prepared, &trackers, true, incremental_flush);
        }
    }

    if incremental_flush {
        flush_resolved(&mut trackers);
    }

    // Phase 2d: k-induction for remaining proof-side properties.
    // Proves AG(φ) = TRUE by induction, and EF(φ) = FALSE via AG(¬φ) induction.
    if trackers.iter().any(|t| t.verdict.is_none()) {
        let pre_kind = trackers.iter().filter(|t| t.verdict.is_some()).count();
        kinduction::run_kinduction_seeding(net, &mut trackers, config.deadline(), max_bmc_depth);
        let post_kind = trackers.iter().filter(|t| t.verdict.is_some()).count();
        let kind_seeded = post_kind - pre_kind;
        if kind_seeded > 0 {
            eprintln!(
                "k-induction seeded {kind_seeded}/{} reachability verdicts",
                trackers.len(),
            );
        }
        if trackers.iter().all(|t| t.verdict.is_some()) {
            if incremental_flush {
                flush_resolved(&mut trackers);
            }
            return assemble_results(&prepared, &trackers, true, incremental_flush);
        }
    }

    if incremental_flush {
        flush_resolved(&mut trackers);
    }

    // Phase 2e: random walk witness search.
    // Lightweight under-approximation: finds EF(φ)=TRUE and AG(φ)=FALSE witnesses
    // without BFS. Runs on the unreduced net — no hash sets, no memory overhead.
    if trackers.iter().any(|t| t.verdict.is_none()) {
        let pre_walk = trackers.iter().filter(|t| t.verdict.is_some()).count();
        reachability_walk::run_random_walk_seeding(
            net,
            &mut trackers,
            &validation,
            config.deadline(),
        );
        let post_walk = trackers.iter().filter(|t| t.verdict.is_some()).count();
        let walk_seeded = post_walk - pre_walk;
        if walk_seeded > 0 {
            eprintln!(
                "Random walk seeded {walk_seeded}/{} reachability verdicts",
                trackers.len(),
            );
        }
        if trackers.iter().all(|t| t.verdict.is_some()) {
            if incremental_flush {
                flush_resolved(&mut trackers);
            }
            return assemble_results(&prepared, &trackers, true, incremental_flush);
        }
    }

    if incremental_flush {
        flush_resolved(&mut trackers);
    }

    // Phase 2f: heuristic best-first witness search.
    // Guided exploration using LP relaxation heuristic. Memory-bounded via
    // Bloom filter. Only seeds EF(φ)=TRUE / AG(φ)=FALSE witnesses.
    if trackers.iter().any(|t| t.verdict.is_none()) {
        let pre_heur = trackers.iter().filter(|t| t.verdict.is_some()).count();
        reachability_heuristic::run_heuristic_seeding(
            net,
            &mut trackers,
            &validation,
            config.deadline(),
        );
        let post_heur = trackers.iter().filter(|t| t.verdict.is_some()).count();
        let heur_seeded = post_heur - pre_heur;
        if heur_seeded > 0 {
            eprintln!(
                "Heuristic search seeded {heur_seeded}/{} reachability verdicts",
                trackers.len(),
            );
        }
        if trackers.iter().all(|t| t.verdict.is_some()) {
            if incremental_flush {
                flush_resolved(&mut trackers);
            }
            return assemble_results(&prepared, &trackers, true, incremental_flush);
        }
    }

    if incremental_flush {
        flush_resolved(&mut trackers);
    }

    // Phase 3: run BFS on a sliced reduced net when the unresolved queries only
    // touch disconnected components. Fall back to the existing reduced-net path
    // whenever the slice does not shrink or any predicate cannot be remapped.
    let reduced = match reduce_reachability_queries(net, &trackers) {
        Ok(reduced) => reduced,
        Err(error) => return cannot_compute_results(properties, &error),
    };

    // Safety check: verify that all entities referenced by predicates survived
    // the reduction. For IsFireable, checks referenced transitions. For
    // TokensCount, checks all transitions touching referenced places. If any
    // were eliminated, the reduced net may have an incomplete state space,
    // causing unsound AG=TRUE verdicts. Fall back to unreduced BFS.
    if !all_predicates_reduction_safe(net, &reduced, &trackers) {
        eprintln!(
            "Reachability: predicate-referenced transitions eliminated by reduction, \
             falling back to unreduced BFS",
        );
        let por_config = reachability_por_config(&ReducedNet::identity(net), &trackers, config);
        let mut observer =
            ReachabilityObserver::from_trackers(net, trackers).with_bus(Arc::clone(&bus));
        let result = match explore_with_optional_checkpoint(net, &por_config, &mut observer) {
            Ok(result) => result,
            Err(error) => return cannot_compute_results(simplified_properties, &error),
        };
        let mut trackers = observer.into_trackers();
        if result.completed {
            finalize_exhaustive_completion(&mut trackers);
        }
        bus.log_summary();
        return assemble_results(&prepared, &trackers, result.completed, incremental_flush);
    }

    let config = config.refitted_for_net(&reduced.net);
    if let Some((slice, slice_trackers)) = build_reachability_slice(&reduced, &trackers) {
        let (result, mut trackers) =
            match explore_reachability_on_slice(&slice, slice_trackers, &config) {
                Ok(state) => state,
                Err(error) => return cannot_compute_results(simplified_properties, &error),
            };
        if result.completed {
            finalize_exhaustive_completion(&mut trackers);
        }
        bus.log_summary();
        return assemble_results(&prepared, &trackers, result.completed, incremental_flush);
    }

    let (result, mut trackers) =
        match explore_reachability_on_reduced_net(net, &reduced, trackers, &config) {
            Ok(state) => state,
            Err(error) => return cannot_compute_results(simplified_properties, &error),
        };
    if result.completed {
        finalize_exhaustive_completion(&mut trackers);
    }
    bus.log_summary();
    assemble_results(&prepared, &trackers, result.completed, incremental_flush)
}
