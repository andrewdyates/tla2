// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::support::{has_mcc_benchmark, mcc_benchmark_dir, trace_eval};
use crate::examinations::ctl::checker::CtlChecker;
use crate::examinations::ctl::resolve::resolve_ctl;
use crate::parser::parse_pnml_dir;
use crate::petri_net::PlaceIdx;
use crate::property_xml::{parse_properties, Formula};
use std::collections::HashMap;

/// Validate ReachabilityFireability on AirplaneLD against 2024 ground truth.
/// Reachability uses flat EF(atom)/AG(atom) — if atoms are correct, this is 100%.
/// If this has wrong answers, atoms are wrong and CTL errors follow from that.
#[test]
fn test_validate_reachability_fireability_airplaneld() {
    if !has_mcc_benchmark("AirplaneLD-PT-0010") {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("AirplaneLD-PT-0010")).expect("parse PNML");
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
    let _n = full.graph.num_states as usize;

    // ReachabilityFireability ground truth (2024):
    // EF(is-fireable(...)) for each property
    let ground_truth = [
        true, true, false, false, false, true, false, true, true, false, true, false, true, true,
        true, false,
    ];

    let props = parse_properties(
        &mcc_benchmark_dir("AirplaneLD-PT-0010"),
        "ReachabilityFireability",
    )
    .expect("parse properties");

    let mut wrong_count = 0;
    for (i, (prop, &expected)) in props.iter().zip(ground_truth.iter()).enumerate() {
        let formula = match &prop.formula {
            Formula::Ctl(ctl) => resolve_ctl(ctl, &place_map, &trans_map),
            _ => continue,
        };
        let sat = checker.eval(&formula);
        let actual = sat[0];
        if actual != expected {
            wrong_count += 1;
            eprintln!(
                "WRONG: ReachabilityFireability-{i:02} ({}): engine={actual}, truth={expected}",
                prop.id
            );
            // Dump atom details
            eprintln!("  Formula trace:");
            trace_eval(&checker, &formula, 2);
        }
    }

    eprintln!(
        "AirplaneLD ReachabilityFireability: {wrong_count}/{} wrong",
        props.len()
    );
    assert_eq!(
        wrong_count, 0,
        "ReachabilityFireability should be 100% correct if atoms are correct"
    );
}

/// Deep diagnostic: manually trace CTL operator results for Angiogenesis property 14.
/// Checks each intermediate bitvector against independent manual computation.
#[test]
fn test_deep_trace_angiogenesis_property_14() {
    if !has_mcc_benchmark("Angiogenesis-PT-01") {
        eprintln!("SKIP: Angiogenesis-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("Angiogenesis-PT-01")).expect("parse PNML");
    let config = crate::explorer::ExplorationConfig::default();
    let full = crate::explorer::explore_full(&net, &config);
    assert!(full.graph.completed);

    let n = full.graph.num_states as usize;
    let checker = CtlChecker::new(&full, &net);
    let deadlocks: Vec<usize> = (0..n).filter(|&s| full.graph.adj[s].is_empty()).collect();
    eprintln!("States: {n}, Deadlocks: {:?}", deadlocks);

    // Build transition map
    let trans_map: HashMap<&str, crate::petri_net::TransitionIdx> = net
        .transitions
        .iter()
        .enumerate()
        .map(|(i, t)| (t.id.as_str(), crate::petri_net::TransitionIdx(i as u32)))
        .collect();

    // Compute fireable(k24) manually
    let k24_idx = trans_map["k24"];
    let k24_fireable: Vec<bool> = (0..n)
        .map(|s| net.is_enabled(&full.markings[s], k24_idx))
        .collect();
    let k24_states: Vec<usize> = (0..n).filter(|&s| k24_fireable[s]).collect();
    eprintln!("fireable(k24): {}/{n}: {:?}", k24_states.len(), k24_states);

    // Compute AX(fireable(k24)) manually — MCC semantics: deadlock → vacuously TRUE
    let ax_k24_manual: Vec<bool> = (0..n)
        .map(|s| {
            if full.graph.adj[s].is_empty() {
                true // Deadlock: AX is vacuously true (no successor to violate)
            } else {
                full.graph.adj[s]
                    .iter()
                    .all(|&(succ, _)| k24_fireable[succ as usize])
            }
        })
        .collect();
    let ax_k24_manual_states: Vec<usize> = (0..n).filter(|&s| ax_k24_manual[s]).collect();
    eprintln!(
        "AX(k24) manual: {}/{n}: {:?}",
        ax_k24_manual_states.len(),
        ax_k24_manual_states
    );

    // Compute AX(k24) via checker
    let ax_k24_checker = checker.pre_a(&k24_fireable);
    let ax_k24_checker_states: Vec<usize> = (0..n).filter(|&s| ax_k24_checker[s]).collect();
    eprintln!(
        "AX(k24) checker: {}/{n}: {:?}",
        ax_k24_checker_states.len(),
        ax_k24_checker_states
    );
    assert_eq!(
        ax_k24_manual, ax_k24_checker,
        "AX manual vs checker disagree!"
    );

    // For each state with EX(k24), show all successors — MCC: deadlock → FALSE
    let ex_k24: Vec<bool> = (0..n)
        .map(|s| {
            if full.graph.adj[s].is_empty() {
                false // Deadlock: EX = false (no successor)
            } else {
                full.graph.adj[s]
                    .iter()
                    .any(|&(succ, _)| k24_fireable[succ as usize])
            }
        })
        .collect();
    let ex_k24_states: Vec<usize> = (0..n).filter(|&s| ex_k24[s]).collect();
    eprintln!("\nStates with EX(k24)=true: {:?}", ex_k24_states);
    for &s in &ex_k24_states {
        let succs: Vec<u32> = full.graph.adj[s].iter().map(|&(succ, _)| succ).collect();
        let k24_succs: Vec<u32> = succs
            .iter()
            .filter(|&&succ| k24_fireable[succ as usize])
            .copied()
            .collect();
        eprintln!(
            "  state {s}: {} successors {:?}, k24 at {:?} -> AX={}",
            succs.len(),
            succs,
            k24_succs,
            succs.iter().all(|&succ| k24_fireable[succ as usize])
        );
    }

    // Also check k24-fireable states' successors (do they lead to k24?)
    eprintln!("\nk24-fireable states' successors:");
    for &s in &k24_states {
        let succs: Vec<u32> = full.graph.adj[s].iter().map(|&(succ, _)| succ).collect();
        let k24_succs: Vec<u32> = succs
            .iter()
            .filter(|&&succ| k24_fireable[succ as usize])
            .copied()
            .collect();
        eprintln!(
            "  state {s}: {} successors {:?}, k24 at {:?}",
            succs.len(),
            succs,
            k24_succs
        );
    }

    // Compute EF(AX(k24))
    let ef_ax_k24 = checker.lfp_ef(&ax_k24_checker);
    let ef_ax_k24_count = ef_ax_k24.iter().filter(|&&v| v).count();
    eprintln!("\nEF(AX(k24)): {ef_ax_k24_count}/{n}");

    // Check k10 and k51
    let k10_idx = trans_map["k10"];
    let k51_idx = trans_map["k51"];
    let k10_fireable: Vec<bool> = (0..n)
        .map(|s| net.is_enabled(&full.markings[s], k10_idx))
        .collect();
    let k51_fireable: Vec<bool> = (0..n)
        .map(|s| net.is_enabled(&full.markings[s], k51_idx))
        .collect();
    let and_k10_k51: Vec<bool> = (0..n).map(|s| k10_fireable[s] && k51_fireable[s]).collect();
    let and_count = and_k10_k51.iter().filter(|&&v| v).count();
    eprintln!("AND(k10,k51): {and_count}/{n}");

    // OR(EF(AX(k24)), AND(k10,k51))
    let or_result: Vec<bool> = (0..n).map(|s| ef_ax_k24[s] || and_k10_k51[s]).collect();
    let or_count = or_result.iter().filter(|&&v| v).count();
    eprintln!("OR(EF(AX(k24)), AND(k10,k51)): {or_count}/{n}");

    // Full formula eval via checker
    let place_map: HashMap<&str, PlaceIdx> = net
        .places
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id.as_str(), PlaceIdx(i as u32)))
        .collect();
    let props = parse_properties(&mcc_benchmark_dir("Angiogenesis-PT-01"), "CTLFireability")
        .expect("parse properties");
    let ctl14 = match &props[14].formula {
        Formula::Ctl(ctl) => ctl,
        _ => panic!("expected CTL"),
    };
    let resolved = resolve_ctl(ctl14, &place_map, &trans_map);
    let full_result = checker.eval(&resolved);
    eprintln!(
        "\nFull CTL result at s0: {} (ground truth: true)",
        full_result[0]
    );
    assert!(
        full_result[0],
        "CTLFireability-14 must be TRUE per MCC ground truth (deadlock fix corrects this)"
    );
}
