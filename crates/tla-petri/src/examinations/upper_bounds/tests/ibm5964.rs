// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bisection tests for IBM5964-PT-none UpperBounds-14 unsound reduction (#1501).
//!
//! Design: `designs/2026-03-22-upperbounds-ibm5964-reduction-unsoundness.md`.

use std::path::PathBuf;

use crate::examinations::query_support::upper_bounds_support;
use crate::explorer::ExplorationConfig;
use crate::model::PropertyAliases;
use crate::parser::parse_pnml_dir;
use crate::petri_net::PlaceIdx;
use crate::property_xml::parse_properties;
use crate::reduction::{
    apply_final_place_gcd_scaling, reduce_iterative_structural_query_with_protected,
    reduce_iterative_structural_with_protected, reduce_query_guarded, ReducedNet,
};

use super::super::model::{prepare_upper_bounds_properties_with_aliases, structural_query_bound};
use super::super::pipeline::{build_upper_bounds_slice, explore_upper_bounds_on_reduced_net};

fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

fn has_benchmark(model: &str) -> bool {
    mcc_input_dir(model).join("model.pnml").exists()
}

/// Prepare trackers with structural + LP bounds seeded (mirrors production pipeline).
fn prepare_ibm5964_trackers() -> Option<(
    crate::petri_net::PetriNet,
    Vec<crate::property_xml::Property>,
    Vec<super::super::model::BoundTracker>,
    usize, // formula_14_slot
)> {
    if !has_benchmark("IBM5964-PT-none") {
        eprintln!("SKIP: IBM5964-PT-none benchmark not available");
        return None;
    }

    let dir = mcc_input_dir("IBM5964-PT-none");
    let net = parse_pnml_dir(&dir).expect("parse PNML");
    let properties = parse_properties(&dir, "UpperBounds").expect("parse properties");
    let aliases = PropertyAliases::identity(&net);
    let (_prepared, mut trackers) =
        prepare_upper_bounds_properties_with_aliases(&properties, &aliases);

    let invariants = crate::invariant::compute_p_invariants(&net);
    for tracker in &mut trackers {
        tracker.structural_bound = structural_query_bound(&invariants, &tracker.place_indices);
        let initial_sum: u64 = tracker
            .place_indices
            .iter()
            .map(|p| net.initial_marking[p.0 as usize])
            .sum();
        tracker.max_bound = initial_sum;
        if let Some(bound) = crate::lp_state_equation::lp_upper_bound(&net, &tracker.place_indices)
        {
            tracker.lp_bound = Some(bound);
        }
    }

    let slot = trackers
        .iter()
        .position(|t| t.id == "IBM5964-PT-none-UpperBounds-14")
        .expect("formula 14 tracker not found");

    Some((net, properties, trackers, slot))
}

/// Config A: Identity net BFS should find bound 3.
#[test]
fn test_ibm5964_config_a_identity_net() {
    let Some((net, _, trackers, slot)) = prepare_ibm5964_trackers() else {
        return;
    };
    let config = ExplorationConfig::new(10_000_000);
    let identity = ReducedNet::identity(&net);
    let (result, out) =
        explore_upper_bounds_on_reduced_net(&identity, trackers, &config).expect("BFS failed");
    eprintln!(
        "Config A: bound={}, completed={}",
        out[slot].max_bound, result.completed
    );
    assert_eq!(out[slot].max_bound, 3, "identity-net BFS must find bound 3");
}

/// Config B: ExactMarking structural reduction + GCD (test fixture path).
///
/// If this returns 3, the bug is specific to QueryRelevantOnly semantics.
#[test]
fn test_ibm5964_config_b_exact_marking_reduction() {
    let Some((net, _, trackers, slot)) = prepare_ibm5964_trackers() else {
        return;
    };
    let config = ExplorationConfig::new(10_000_000);
    let unresolved_place_sets: Vec<Vec<PlaceIdx>> = trackers
        .iter()
        .filter(|t| !t.is_structurally_resolved())
        .map(|t| t.place_indices.clone())
        .collect();
    let initial_protected =
        upper_bounds_support(&ReducedNet::identity(&net), &unresolved_place_sets)
            .map(|s| s.places)
            .unwrap_or_else(|| vec![true; net.num_places()]);

    let reduced = reduce_iterative_structural_with_protected(&net, &initial_protected)
        .expect("reduction failed");
    let mut reduced = reduce_query_guarded(reduced, |r| {
        upper_bounds_support(r, &unresolved_place_sets).map(|s| s.places)
    })
    .expect("query-guarded reduction failed");
    apply_final_place_gcd_scaling(&mut reduced).expect("GCD scaling failed");

    eprintln!(
        "Config B: net={}p/{}t (reduced from {}p/{}t)",
        reduced.net.num_places(),
        reduced.net.transitions.len(),
        net.num_places(),
        net.transitions.len(),
    );

    let cfg = config.refitted_for_net(&reduced.net);
    let (result, out) =
        explore_upper_bounds_on_reduced_net(&reduced, trackers, &cfg).expect("BFS failed");
    eprintln!(
        "Config B: bound={}, completed={}",
        out[slot].max_bound, result.completed
    );
}

/// Config B2: ExactMarking structural reduction WITHOUT GCD or query-guarded.
///
/// Isolates the structural reduction alone.
#[test]
fn test_ibm5964_config_b2_structural_only() {
    let Some((net, _, trackers, slot)) = prepare_ibm5964_trackers() else {
        return;
    };
    let config = ExplorationConfig::new(10_000_000);
    let unresolved_place_sets: Vec<Vec<PlaceIdx>> = trackers
        .iter()
        .filter(|t| !t.is_structurally_resolved())
        .map(|t| t.place_indices.clone())
        .collect();
    let initial_protected =
        upper_bounds_support(&ReducedNet::identity(&net), &unresolved_place_sets)
            .map(|s| s.places)
            .unwrap_or_else(|| vec![true; net.num_places()]);

    let reduced = reduce_iterative_structural_with_protected(&net, &initial_protected)
        .expect("reduction failed");
    // No query_guarded, no GCD — just structural reduction
    eprintln!(
        "Config B2: net={}p/{}t (from {}p/{}t)",
        reduced.net.num_places(),
        reduced.net.transitions.len(),
        net.num_places(),
        net.transitions.len(),
    );
    eprintln!(
        "  report: constant={} source={} dead_t={} isolated={} \
         pre_agg={} post_agg={} dup_t={} self_loop_t={} dom_t={} \
         self_loop_arcs={} never_dis={} tok_elim={} redundant={} \
         parallel={} non_dec={}",
        reduced.report.constant_places.len(),
        reduced.report.source_places.len(),
        reduced.report.dead_transitions.len(),
        reduced.report.isolated_places.len(),
        reduced.report.pre_agglomerations.len(),
        reduced.report.post_agglomerations.len(),
        reduced.report.duplicate_transitions.len(),
        reduced.report.self_loop_transitions.len(),
        reduced.report.dominated_transitions.len(),
        reduced.report.self_loop_arcs.len(),
        reduced.report.never_disabling_arcs.len(),
        reduced.report.token_eliminated_places.len(),
        reduced.report.redundant_places.len(),
        reduced.report.parallel_places.len(),
        reduced.report.non_decreasing_places.len(),
    );

    // Check query place mapping
    let f14 = &trackers[slot];
    for &place in &f14.place_indices {
        let mapped = reduced.place_map[place.0 as usize];
        eprintln!(
            "  query place {} -> {:?} (scale={})",
            place.0, mapped, reduced.place_scales[place.0 as usize]
        );
    }

    // Check constant_values for query place
    for &(p, val) in &reduced.constant_values {
        if f14.place_indices.contains(&p) {
            eprintln!("  ALERT: query place {} has constant_value={}", p.0, val);
        }
    }
    // Check reconstructions for query place
    for recon in &reduced.reconstructions {
        if f14.place_indices.iter().any(|pi| *pi == recon.place) {
            eprintln!(
                "  ALERT: query place {} has P-invariant reconstruction",
                recon.place.0,
            );
        }
    }

    // Trace transitions touching query place in original net
    let query_place = f14.place_indices[0];
    eprintln!("  transitions touching query place {}:", query_place.0);
    for (tidx, t) in net.transitions.iter().enumerate() {
        let is_input = t.inputs.iter().any(|a| a.place == query_place);
        let is_output = t.outputs.iter().any(|a| a.place == query_place);
        if is_input || is_output {
            let survived = reduced.transition_map[tidx].is_some();
            let in_w: u64 = t
                .inputs
                .iter()
                .filter(|a| a.place == query_place)
                .map(|a| a.weight)
                .sum();
            let out_w: u64 = t
                .outputs
                .iter()
                .filter(|a| a.place == query_place)
                .map(|a| a.weight)
                .sum();
            eprintln!(
                "    t{tidx} ({}) in={in_w} out={out_w} net={} survived={survived}",
                t.id,
                out_w as i64 - in_w as i64,
            );
        }
    }

    // Check why t56 was removed
    let t56_dead = reduced.report.dead_transitions.iter().any(|t| t.0 == 56);
    let t56_self_loop = reduced
        .report
        .self_loop_transitions
        .iter()
        .any(|t| t.0 == 56);
    let t56_dominated = reduced
        .report
        .dominated_transitions
        .iter()
        .any(|t| t.0 == 56);
    let t56_duplicate = reduced
        .report
        .duplicate_transitions
        .iter()
        .any(|class| class.duplicates.iter().any(|t| t.0 == 56));
    let t56_pre_agg = reduced
        .report
        .pre_agglomerations
        .iter()
        .any(|a| a.transition.0 == 56);
    let t56_post_agg = reduced
        .report
        .post_agglomerations
        .iter()
        .any(|a| a.transition.0 == 56);
    eprintln!(
        "  t56: dead={t56_dead} self_loop={t56_self_loop} dominated={t56_dominated} \
         duplicate={t56_duplicate} pre_agg={t56_pre_agg} post_agg={t56_post_agg}",
    );

    // Print t56's full arc structure
    let t56 = &net.transitions[56];
    eprintln!("  t56 inputs:");
    for arc in &t56.inputs {
        let pid = &net.places[arc.place.0 as usize].id;
        let survived = reduced.place_map[arc.place.0 as usize].is_some();
        eprintln!(
            "    p{} ({pid}) w={} survived={survived}",
            arc.place.0, arc.weight
        );
    }
    eprintln!("  t56 outputs:");
    for arc in &t56.outputs {
        let pid = &net.places[arc.place.0 as usize].id;
        let survived = reduced.place_map[arc.place.0 as usize].is_some();
        eprintln!(
            "    p{} ({pid}) w={} survived={survived}",
            arc.place.0, arc.weight
        );
    }

    let cfg = config.refitted_for_net(&reduced.net);
    let (result, out) =
        explore_upper_bounds_on_reduced_net(&reduced, trackers, &cfg).expect("BFS failed");
    eprintln!(
        "Config B2 (structural only): bound={}, completed={}",
        out[slot].max_bound, result.completed
    );
}

/// Config C: QueryRelevantOnly structural reduction + GCD (production path, no slicing).
///
/// If this returns 2 while Config B returns 3, token elimination is unsound.
#[test]
fn test_ibm5964_config_c_query_relevant_reduction() {
    let Some((net, _, trackers, slot)) = prepare_ibm5964_trackers() else {
        return;
    };
    let config = ExplorationConfig::new(10_000_000);
    let unresolved_place_sets: Vec<Vec<PlaceIdx>> = trackers
        .iter()
        .filter(|t| !t.is_structurally_resolved())
        .map(|t| t.place_indices.clone())
        .collect();
    let initial_protected =
        upper_bounds_support(&ReducedNet::identity(&net), &unresolved_place_sets)
            .map(|s| s.places)
            .unwrap_or_else(|| vec![true; net.num_places()]);

    let reduced = reduce_iterative_structural_query_with_protected(&net, &initial_protected)
        .expect("reduction failed");
    let mut reduced = reduce_query_guarded(reduced, |r| {
        upper_bounds_support(r, &unresolved_place_sets).map(|s| s.places)
    })
    .expect("query-guarded reduction failed");
    apply_final_place_gcd_scaling(&mut reduced).expect("GCD scaling failed");

    eprintln!(
        "Config C: net={}p/{}t (reduced from {}p/{}t)",
        reduced.net.num_places(),
        reduced.net.transitions.len(),
        net.num_places(),
        net.transitions.len(),
    );

    let cfg = config.refitted_for_net(&reduced.net);
    let (result, out) =
        explore_upper_bounds_on_reduced_net(&reduced, trackers.clone(), &cfg).expect("BFS failed");
    eprintln!(
        "Config C (no slice): bound={}, completed={}",
        out[slot].max_bound, result.completed
    );

    // Also check with slicing (Config D)
    if let Some((slice, unresolved_slots, _slice_trackers)) =
        build_upper_bounds_slice(&reduced, &trackers)
    {
        eprintln!(
            "Config D: slice={}p/{}t",
            slice.net.num_places(),
            slice.net.transitions.len(),
        );
        if let Some(pos) = unresolved_slots.iter().position(|&s| s == slot) {
            eprintln!("Config D: formula 14 in slice at position {pos}",);
        }
    } else {
        eprintln!("Config D: no slice produced");
    }
}
