// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::support::{has_mcc_benchmark, mcc_benchmark_dir};
use crate::examinations::ctl::checker::CtlChecker;
use crate::examinations::ctl::resolve::{resolve_ctl, ResolvedCtl};
use crate::parser::parse_pnml_dir;
use crate::petri_net::PlaceIdx;
use crate::property_xml::{parse_properties, Formula, PathQuantifier};
use crate::resolved_predicate::resolve_predicate;
use std::collections::HashMap;

/// Validate state space correctness by checking ALL Reachability properties
/// against ground truth. Reachability uses only flat EF(predicate) / AG(predicate)
/// — no nested temporal operators. If this is 100% correct, the state space and
/// atom evaluation are validated, and the CTL bug is in nested temporal operators.
#[test]
fn test_validate_reachability_angiogenesis() {
    if !has_mcc_benchmark("Angiogenesis-PT-01") {
        eprintln!("SKIP: Angiogenesis-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("Angiogenesis-PT-01")).expect("parse PNML");
    let config = crate::explorer::ExplorationConfig::default();
    let full = crate::explorer::explore_full(&net, &config);
    assert!(full.graph.completed);

    let place_map: HashMap<&str, PlaceIdx> = net
        .places
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id.as_str(), PlaceIdx(i as u32)))
        .collect();
    let trans_map: HashMap<&str, crate::petri_net::TransitionIdx> = net
        .transitions
        .iter()
        .enumerate()
        .map(|(i, t)| (t.id.as_str(), crate::petri_net::TransitionIdx(i as u32)))
        .collect();

    let checker = CtlChecker::new(&full, &net);

    // ReachabilityFireability ground truth for Angiogenesis-PT-01 (from MCC labels)
    let reach_fire_truth: Vec<bool> = vec![
        true, false, false, true, false, false, false, false, false, false, true, false, true,
        true, true, false,
    ];

    // ReachabilityFireability is parsed from the same XML
    let reach_props = parse_properties(
        &mcc_benchmark_dir("Angiogenesis-PT-01"),
        "ReachabilityFireability",
    )
    .expect("parse ReachabilityFireability");

    let mut wrong = 0;
    for (i, (prop, &expected)) in reach_props.iter().zip(reach_fire_truth.iter()).enumerate() {
        // Reachability formulas are EF(predicate) or AG(predicate)
        // We can evaluate them using the CTL checker
        let formula = match &prop.formula {
            Formula::Reachability(rf) => {
                let pred = resolve_predicate(&rf.predicate, &place_map, &trans_map);
                match rf.quantifier {
                    PathQuantifier::EF => ResolvedCtl::EF(Box::new(ResolvedCtl::Atom(pred))),
                    PathQuantifier::AG => ResolvedCtl::AG(Box::new(ResolvedCtl::Atom(pred))),
                }
            }
            _ => continue,
        };

        let sat = checker.eval(&formula);
        let actual = sat[0];
        if actual != expected {
            wrong += 1;
            eprintln!(
                "REACHABILITY WRONG: ReachabilityFireability-{i:02}: engine={actual}, truth={expected}"
            );
        }
    }

    eprintln!(
        "Angiogenesis ReachabilityFireability: {wrong}/{} wrong",
        reach_fire_truth.len()
    );
    assert_eq!(
        wrong, 0,
        "Reachability should be 100% correct — if wrong, state space or atoms are buggy"
    );
}

/// Detailed atom-level diagnostic: dump fireable state counts for the specific
/// transitions used in the wrong CTL formulas on Angiogenesis.
#[test]
fn test_diagnose_angiogenesis_atom_details() {
    if !has_mcc_benchmark("Angiogenesis-PT-01") {
        eprintln!("SKIP: Angiogenesis-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("Angiogenesis-PT-01")).expect("parse PNML");
    let config = crate::explorer::ExplorationConfig::default();
    let full = crate::explorer::explore_full(&net, &config);
    assert!(full.graph.completed);

    let n = full.graph.num_states as usize;
    assert_eq!(n, 110, "Angiogenesis state count must match MCC");
    eprintln!(
        "Angiogenesis: {n} states, {} transitions",
        net.transitions.len()
    );

    // Dump successor counts per state
    let deadlocks: Vec<usize> = (0..n).filter(|&s| full.graph.adj[s].is_empty()).collect();
    eprintln!("Deadlock states: {:?}", deadlocks);
    let total_edges: usize = full.graph.adj.iter().map(|edges| edges.len()).sum();
    assert_eq!(total_edges, 288, "Angiogenesis edge count must match MCC");

    // For each state, count successors
    for s in 0..n {
        let num_succ = full.graph.adj[s].len();
        if num_succ <= 1 {
            eprintln!(
                "  state {s}: {num_succ} successors ({})",
                if num_succ == 0 {
                    "DEADLOCK"
                } else {
                    "deterministic"
                }
            );
        }
    }

    // Check specific transitions from CTLFireability-14: k24, k10, k51
    let transitions_to_check = ["k24", "k10", "k51"];
    for tid in &transitions_to_check {
        let idx = net
            .transitions
            .iter()
            .position(|t| t.id == *tid)
            .expect("transition not found");
        let trans = crate::petri_net::TransitionIdx(idx as u32);

        let mut fireable_states: Vec<usize> = Vec::new();
        for s in 0..n {
            if net.is_enabled(&full.markings[s], trans) {
                fireable_states.push(s);
            }
        }
        eprintln!(
            "fireable({tid}): {}/{n} states: {:?}",
            fireable_states.len(),
            fireable_states
        );

        // For AX(fireable(k24)): check which states have ALL successors with tid fireable
        let mut ax_states: Vec<usize> = Vec::new();
        for s in 0..n {
            if full.graph.adj[s].is_empty() {
                // Deadlock: AX is vacuously true (no successor can violate φ).
                ax_states.push(s);
            } else {
                let all_succ_fireable = full.graph.adj[s]
                    .iter()
                    .all(|&(succ, _)| fireable_states.contains(&(succ as usize)));
                if all_succ_fireable {
                    ax_states.push(s);
                }
            }
        }
        eprintln!(
            "AX(fireable({tid})): {}/{n} states: {:?}",
            ax_states.len(),
            ax_states
        );
    }

    // Check state 0's successors
    eprintln!("\nState 0 successors:");
    for &(succ, tidx) in &full.graph.adj[0] {
        eprintln!(
            "  -> state {succ} via transition {}",
            net.transitions[tidx as usize].id
        );
    }

    // State 0's successor's successors (2-step reachability)
    eprintln!("\nState 0 two-step reachability:");
    for &(succ1, _) in &full.graph.adj[0] {
        for &(succ2, tidx2) in &full.graph.adj[succ1 as usize] {
            eprintln!(
                "  0 -> {succ1} -> {succ2} via {}",
                net.transitions[tidx2 as usize].id
            );
        }
    }
}

/// Verify atom evaluation by checking raw markings directly against is_enabled.
/// Also verify AX(fireable(k24)) computation step-by-step.
#[test]
fn test_verify_atoms_by_raw_markings_angiogenesis() {
    if !has_mcc_benchmark("Angiogenesis-PT-01") {
        eprintln!("SKIP: Angiogenesis-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("Angiogenesis-PT-01")).expect("parse PNML");
    let config = crate::explorer::ExplorationConfig::default();
    let full = crate::explorer::explore_full(&net, &config);
    assert!(full.graph.completed);

    let n = full.graph.num_states as usize;

    // Verify k24: input = KdStarGStarP3kP3 (weight 1)
    let k24_idx = net.transitions.iter().position(|t| t.id == "k24").unwrap();
    let k24_trans = &net.transitions[k24_idx];
    eprintln!("k24 inputs:");
    for arc in &k24_trans.inputs {
        let place_name = &net.places[arc.place.0 as usize].id;
        eprintln!(
            "  place {} (idx {}) weight {}",
            place_name, arc.place.0, arc.weight
        );
    }

    // Check raw markings for k24's input places
    let mut fireable_k24_raw: Vec<usize> = Vec::new();
    let mut fireable_k24_api: Vec<usize> = Vec::new();
    for s in 0..n {
        // Raw check: all input places have enough tokens
        let raw_enabled = k24_trans
            .inputs
            .iter()
            .all(|arc| full.markings[s][arc.place.0 as usize] >= arc.weight);
        let api_enabled = net.is_enabled(
            &full.markings[s],
            crate::petri_net::TransitionIdx(k24_idx as u32),
        );

        if raw_enabled {
            fireable_k24_raw.push(s);
        }
        if api_enabled {
            fireable_k24_api.push(s);
        }

        assert_eq!(
            raw_enabled, api_enabled,
            "is_enabled mismatch at state {s} for k24: raw={raw_enabled}, api={api_enabled}"
        );
    }
    eprintln!(
        "fireable(k24) raw: {}/{n}: {:?}",
        fireable_k24_raw.len(),
        fireable_k24_raw
    );
    eprintln!(
        "fireable(k24) api: {}/{n}: {:?}",
        fireable_k24_api.len(),
        fireable_k24_api
    );

    // For states where k24 is fireable, dump the input place markings
    for &s in &fireable_k24_raw {
        eprintln!("  state {s}: input place markings:");
        for arc in &k24_trans.inputs {
            let val = full.markings[s][arc.place.0 as usize];
            eprintln!("    {} = {val}", net.places[arc.place.0 as usize].id);
        }
    }

    // Check AX(fireable(k24)) manually: for each state, check ALL successors
    eprintln!("\nChecking AX(fireable(k24)):");
    for s in 0..n {
        if full.graph.adj[s].is_empty() {
            eprintln!("  state {s} (DEADLOCK): AX=true (vacuously true)");
        } else {
            let all_succ = full.graph.adj[s]
                .iter()
                .all(|&(succ, _)| fireable_k24_raw.contains(&(succ as usize)));
            if all_succ {
                eprintln!(
                    "  state {s}: AX=true (all {} successors have k24 fireable)",
                    full.graph.adj[s].len()
                );
            }
            // Also check: does ANY successor have k24 fireable? (for EX)
            let any_succ = full.graph.adj[s]
                .iter()
                .any(|&(succ, _)| fireable_k24_raw.contains(&(succ as usize)));
            if any_succ && !all_succ {
                let fireable_succs: Vec<u32> = full.graph.adj[s]
                    .iter()
                    .filter(|&&(succ, _)| fireable_k24_raw.contains(&(succ as usize)))
                    .map(|&(succ, _)| succ)
                    .collect();
                let total_succs = full.graph.adj[s].len();
                eprintln!("  state {s}: AX=false but EX=true ({}/{total_succs} successors have k24 fireable: {:?})",
                    fireable_succs.len(), fireable_succs);
            }
        }
    }

    // Cross-check k10 and k51
    for tid in &["k10", "k51"] {
        let idx = net.transitions.iter().position(|t| t.id == *tid).unwrap();
        let trans = &net.transitions[idx];
        let mut raw_fireable: Vec<usize> = Vec::new();
        for s in 0..n {
            if trans
                .inputs
                .iter()
                .all(|arc| full.markings[s][arc.place.0 as usize] >= arc.weight)
            {
                raw_fireable.push(s);
            }
        }
        eprintln!(
            "fireable({tid}) raw: {}/{n}: {:?}",
            raw_fireable.len(),
            raw_fireable
        );
    }

    // Key test: is there ANY state where BOTH k10 and k51 are fireable?
    let k10_idx = net.transitions.iter().position(|t| t.id == "k10").unwrap();
    let k51_idx = net.transitions.iter().position(|t| t.id == "k51").unwrap();
    let k10t = crate::petri_net::TransitionIdx(k10_idx as u32);
    let k51t = crate::petri_net::TransitionIdx(k51_idx as u32);

    let mut both_fireable: Vec<usize> = Vec::new();
    for s in 0..n {
        if net.is_enabled(&full.markings[s], k10t) && net.is_enabled(&full.markings[s], k51t) {
            both_fireable.push(s);
        }
    }
    eprintln!(
        "AND(fireable(k10), fireable(k51)): {}/{n}: {:?}",
        both_fireable.len(),
        both_fireable
    );

    // Verify: run the full CTL checker on this formula and compare
    let place_map: HashMap<&str, PlaceIdx> = net
        .places
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id.as_str(), PlaceIdx(i as u32)))
        .collect();
    let trans_map: HashMap<&str, crate::petri_net::TransitionIdx> = net
        .transitions
        .iter()
        .enumerate()
        .map(|(i, t)| (t.id.as_str(), crate::petri_net::TransitionIdx(i as u32)))
        .collect();

    let props = parse_properties(&mcc_benchmark_dir("Angiogenesis-PT-01"), "CTLFireability")
        .expect("parse properties");

    let ctl14 = match &props[14].formula {
        Formula::Ctl(ctl) => ctl,
        _ => panic!("expected CTL"),
    };
    let resolved = resolve_ctl(ctl14, &place_map, &trans_map);

    let checker = CtlChecker::new(&full, &net);
    let result = checker.eval(&resolved);

    eprintln!("\nFull CTL evaluation of property 14:");
    eprintln!("  Result at s0: {}", result[0]);
    eprintln!(
        "  States satisfying: {}/{n}",
        result.iter().filter(|&&v| v).count()
    );

    // 2024 ground truth for property 14 is TRUE
    eprintln!("  Ground truth (2024): true");
    eprintln!("  Match: {}", result[0]);

    // Verify PNML parser: count total arcs
    let total_input_arcs: usize = net.transitions.iter().map(|t| t.inputs.len()).sum();
    let total_output_arcs: usize = net.transitions.iter().map(|t| t.outputs.len()).sum();
    eprintln!("\nPNML parser verification:");
    eprintln!("  Places: {} (expect 39)", net.places.len());
    eprintln!("  Transitions: {} (expect 64)", net.transitions.len());
    eprintln!(
        "  Total arcs: {} (input) + {} (output) = {} (expect 185 total from PNML)",
        total_input_arcs,
        total_output_arcs,
        total_input_arcs + total_output_arcs
    );

    // CRITICAL: verify edge count matches MCC state-space-2024.csv
    // MCC says: 110 states, 288 edges
    let total_edges: usize = full.graph.adj.iter().map(|edges| edges.len()).sum();
    eprintln!("\nEdge count verification:");
    eprintln!("  States: {} (MCC says 110)", n);
    eprintln!("  Edges: {} (MCC says 288)", total_edges);
    assert_eq!(n, 110, "state count mismatch with MCC");
    assert_eq!(
        total_edges, 288,
        "EDGE COUNT MISMATCH with MCC — graph structure is wrong!"
    );
}

/// Verify edge counts for both models against MCC state-space-2024.csv.
#[test]
fn test_verify_edge_counts_against_mcc() {
    if !mcc_benchmark_dir("Angiogenesis-PT-01")
        .join("model.pnml")
        .exists()
    {
        eprintln!("SKIP: Angiogenesis-PT-01 benchmark not downloaded");
        return;
    }
    if !mcc_benchmark_dir("AirplaneLD-PT-0010")
        .join("model.pnml")
        .exists()
    {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }

    let config = crate::explorer::ExplorationConfig::default();

    // Angiogenesis: MCC says 110 states, 288 edges
    {
        let net = parse_pnml_dir(&mcc_benchmark_dir("Angiogenesis-PT-01")).unwrap();
        let full = crate::explorer::explore_full(&net, &config);
        let n = full.graph.num_states as usize;
        let total_edges: usize = full.graph.adj.iter().map(|edges| edges.len()).sum();
        let deadlocks: Vec<usize> = (0..n).filter(|&s| full.graph.adj[s].is_empty()).collect();
        eprintln!(
            "Angiogenesis: {} states, {} edges, {} deadlocks: {:?}",
            n,
            total_edges,
            deadlocks.len(),
            deadlocks
        );
        assert_eq!(n, 110, "Angiogenesis state count");
        assert_eq!(total_edges, 288, "Angiogenesis edge count (MCC says 288)");
    }

    // AirplaneLD: MCC says 43463 states, 183664 edges
    {
        let net = parse_pnml_dir(&mcc_benchmark_dir("AirplaneLD-PT-0010")).unwrap();
        let full = crate::explorer::explore_full(&net, &config);
        let n = full.graph.num_states as usize;
        let total_edges: usize = full.graph.adj.iter().map(|edges| edges.len()).sum();
        let deadlocks: Vec<usize> = (0..n).filter(|&s| full.graph.adj[s].is_empty()).collect();
        eprintln!(
            "AirplaneLD: {} states, {} edges, {} deadlocks",
            n,
            total_edges,
            deadlocks.len()
        );
        assert_eq!(n, 43463, "AirplaneLD state count");
        assert_eq!(
            total_edges, 183664,
            "AirplaneLD edge count (MCC says 183664)"
        );
    }
}
