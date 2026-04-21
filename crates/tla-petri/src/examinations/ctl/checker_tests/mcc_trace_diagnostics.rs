// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::support::{has_mcc_benchmark, mcc_benchmark_dir, trace_eval};
use crate::examinations::ctl::checker::CtlChecker;
use crate::examinations::ctl::resolve::{resolve_ctl, ResolvedCtl};
use crate::parser::parse_pnml_dir;
use crate::petri_net::PlaceIdx;
use crate::property_xml::{parse_properties, Formula};
use std::collections::HashMap;

/// Diagnostic: evaluate ALL CTLCardinality and CTLFireability properties on
/// AirplaneLD, comparing each with ground truth.
#[test]
fn test_diagnose_airplaneld_ctl_all_properties() {
    if !has_mcc_benchmark("AirplaneLD-PT-0010") {
        eprintln!("SKIP: AirplaneLD-PT-0010 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("AirplaneLD-PT-0010")).expect("parse PNML");
    let config = crate::explorer::ExplorationConfig::default();
    let full = crate::explorer::explore_full(&net, &config);
    assert!(
        full.graph.completed,
        "state space exploration did not complete"
    );

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

    eprintln!(
        "AirplaneLD-PT-0010: {} states, {} places, {} transitions",
        full.graph.num_states,
        net.places.len(),
        net.transitions.len()
    );

    // Count deadlock states
    let deadlocks = full
        .graph
        .adj
        .iter()
        .filter(|edges| edges.is_empty())
        .count();
    eprintln!("Deadlock states: {deadlocks}");

    // Ground truth from registry/mcc-labels/
    let card_truth: Vec<bool> = vec![
        true, false, true, false, false, true, true, true, true, true, false, false, false, true,
        false, false,
    ];
    let fire_truth: Vec<bool> = vec![
        true, false, true, true, false, true, true, false, false, false, true, true, true, false,
        true, false,
    ];

    let examinations = [
        ("CTLCardinality", &card_truth),
        ("CTLFireability", &fire_truth),
    ];

    let mut wrong_count = 0;
    for (exam, truth) in &examinations {
        let props = parse_properties(&mcc_benchmark_dir("AirplaneLD-PT-0010"), exam)
            .expect("parse properties");

        for (i, (prop, &expected)) in props.iter().zip(truth.iter()).enumerate() {
            let formula = match &prop.formula {
                Formula::Ctl(ctl) => resolve_ctl(ctl, &place_map, &trans_map),
                _ => continue,
            };

            let sat = checker.eval(&formula);
            let actual = sat[0];

            if actual != expected {
                wrong_count += 1;
                eprintln!(
                    "\nWRONG: {exam}-{i:02} ({}): engine={actual}, truth={expected}",
                    prop.id
                );
                eprintln!("Formula tree:");
                trace_eval(&checker, &formula, 1);
            }
        }
    }

    eprintln!("\nTotal wrong answers: {wrong_count}");
    assert_eq!(
        wrong_count, 0,
        "all AirplaneLD CTL properties should match ground truth after deadlock fix"
    );
}

/// Diagnostic: evaluate Angiogenesis CTLFireability-14 with trace.
#[test]
fn test_diagnose_angiogenesis_ctl_fireability_14() {
    if !has_mcc_benchmark("Angiogenesis-PT-01") {
        eprintln!("SKIP: Angiogenesis-PT-01 benchmark not downloaded");
        return;
    }

    let net = parse_pnml_dir(&mcc_benchmark_dir("Angiogenesis-PT-01")).expect("parse PNML");
    let config = crate::explorer::ExplorationConfig::default();
    let full = crate::explorer::explore_full(&net, &config);
    assert!(
        full.graph.completed,
        "state space exploration did not complete"
    );

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

    eprintln!(
        "Angiogenesis-PT-01: {} states, {} places, {} transitions",
        full.graph.num_states,
        net.places.len(),
        net.transitions.len()
    );

    let deadlocks = full
        .graph
        .adj
        .iter()
        .filter(|edges| edges.is_empty())
        .count();
    eprintln!("Deadlock states: {deadlocks}");

    // Ground truth from registry: property 14 = true
    let props = parse_properties(&mcc_benchmark_dir("Angiogenesis-PT-01"), "CTLFireability")
        .expect("parse properties");

    // From registry/mcc-labels/c-t-l-fireability-2024.csv
    let fire_truth: Vec<bool> = vec![
        false, false, true, true, true, false, true, true, false, false, true, true, true, true,
        true, false,
    ];

    let mut wrong_count = 0;
    for (i, (prop, &expected)) in props.iter().zip(fire_truth.iter()).enumerate() {
        let formula = match &prop.formula {
            Formula::Ctl(ctl) => resolve_ctl(ctl, &place_map, &trans_map),
            _ => continue,
        };

        let sat = checker.eval(&formula);
        let actual = sat[0];

        if actual != expected {
            wrong_count += 1;
            eprintln!(
                "\nWRONG: CTLFireability-{i:02} ({}): engine={actual}, truth={expected}",
                prop.id
            );
            eprintln!("Formula tree:");
            trace_eval(&checker, &formula, 1);
        }
    }

    eprintln!("\nAngiogenesis total wrong: {wrong_count}");
    assert_eq!(
        wrong_count, 0,
        "all Angiogenesis CTLFireability properties should match ground truth after deadlock fix"
    );
}

/// Compare AU algebraic rewrite vs direct fixpoint on the real AirplaneLD model.
/// If they disagree, the bug is in the AU rewrite. If they agree, the bug is
/// in a different operator.
#[test]
fn test_diagnose_au_algebraic_vs_fixpoint_airplaneld() {
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
    let n = full.graph.num_states as usize;

    /// Reference AU using direct least fixpoint with MCC maximal-path deadlock
    /// correction: A[φ U ψ] = μZ. ψ ∨ (HAS_SUCCESSORS ∧ φ ∧ AX(Z)).
    ///
    /// Under MCC maximal-path semantics, A[φ U ψ] at a deadlock state = ψ(s),
    /// because the only maximal path [s] requires ψ to eventually hold (at s).
    /// The uncorrected fixpoint gives ψ ∨ (φ ∧ TRUE) = ψ ∨ φ at deadlocks,
    /// which is wrong when ψ=false and φ=true.
    fn reference_lfp_au(checker: &CtlChecker, sat_phi: &[bool], sat_psi: &[bool]) -> Vec<bool> {
        let n = sat_phi.len();
        let mut z = vec![false; n];
        loop {
            let ax_z = checker.pre_a(&z);
            let new_z: Vec<bool> = (0..n)
                .map(|i| {
                    let has_succs = !checker.full.graph.adj[i].is_empty();
                    sat_psi[i] || (has_succs && sat_phi[i] && ax_z[i])
                })
                .collect();
            if new_z == z {
                break;
            }
            z = new_z;
        }
        z
    }

    /// Algebraic AU: A[φ U ψ] = ¬(E[¬ψ U (¬φ ∧ ¬ψ)] ∨ EG(¬ψ)).
    fn algebraic_au(checker: &CtlChecker, sat_phi: &[bool], sat_psi: &[bool]) -> Vec<bool> {
        let n = sat_phi.len();
        let not_phi: Vec<bool> = sat_phi.iter().map(|&v| !v).collect();
        let not_psi: Vec<bool> = sat_psi.iter().map(|&v| !v).collect();
        let not_phi_and_not_psi: Vec<bool> = (0..n).map(|i| not_phi[i] && not_psi[i]).collect();
        let eu = checker.lfp_eu(&not_psi, &not_phi_and_not_psi);
        let eg = checker.gfp_eg(&not_psi);
        (0..n).map(|i| !(eu[i] || eg[i])).collect()
    }

    /// Reference AF using direct least fixpoint with MCC maximal-path deadlock
    /// correction: AF(φ) = μZ. φ ∨ (HAS_SUCCESSORS ∧ AX(Z)).
    ///
    /// Standard fixpoint AF(φ) = μZ. φ ∨ AX(Z) assumes infinite paths (Kripke
    /// structure semantics). Under MCC maximal-path semantics, deadlock states
    /// have the single maximal path [s], so AF(φ) at a deadlock = φ(s).
    /// The uncorrected fixpoint gives AF(φ) = TRUE at all deadlocks because
    /// AX is vacuously true, which is wrong when φ is false.
    fn reference_lfp_af(checker: &CtlChecker, sat_phi: &[bool]) -> Vec<bool> {
        let n = sat_phi.len();
        let mut z = vec![false; n];
        loop {
            let ax_z = checker.pre_a(&z);
            let new_z: Vec<bool> = (0..n)
                .map(|i| {
                    let has_succs = !checker.full.graph.adj[i].is_empty();
                    sat_phi[i] || (has_succs && ax_z[i])
                })
                .collect();
            if new_z == z {
                break;
            }
            z = new_z;
        }
        z
    }

    // Check CTLFireability-13 which uses AU:
    // EG(EF(EX(NOT(fireable("SampleLW_on") OR AU(fireable("getAlt_3"), fireable("getAlt_16"))))))
    // Extract the AU subformula and compare algebraic vs fixpoint
    let props = parse_properties(&mcc_benchmark_dir("AirplaneLD-PT-0010"), "CTLFireability")
        .expect("parse properties");

    // Property 13 contains AU
    let ctl = match &props[13].formula {
        Formula::Ctl(ctl) => ctl,
        _ => panic!("expected CTL formula"),
    };
    let resolved = resolve_ctl(ctl, &place_map, &trans_map);

    // Walk the formula tree to find AU subformulas and test them
    fn find_and_test_au(checker: &CtlChecker, formula: &ResolvedCtl, n: usize) {
        match formula {
            ResolvedCtl::AU(phi, psi) => {
                let sat_phi = checker.eval(phi);
                let sat_psi = checker.eval(psi);
                let alg = algebraic_au(checker, &sat_phi, &sat_psi);
                let fix = reference_lfp_au(checker, &sat_phi, &sat_psi);
                let agree = alg == fix;
                let alg_s0 = alg[0];
                let fix_s0 = fix[0];
                let alg_count = alg.iter().filter(|&&v| v).count();
                let fix_count = fix.iter().filter(|&&v| v).count();
                eprintln!(
                    "AU subformula: algebraic={alg_count}/{n} s0={alg_s0}, \
                     fixpoint={fix_count}/{n} s0={fix_s0}, agree={agree}"
                );
                assert!(
                    agree,
                    "AU algebraic and fixpoint must agree on all {n} states"
                );
            }
            ResolvedCtl::Not(inner)
            | ResolvedCtl::EX(inner)
            | ResolvedCtl::AX(inner)
            | ResolvedCtl::EF(inner)
            | ResolvedCtl::AF(inner)
            | ResolvedCtl::EG(inner)
            | ResolvedCtl::AG(inner) => {
                find_and_test_au(checker, inner, n);
            }
            ResolvedCtl::And(children) | ResolvedCtl::Or(children) => {
                for child in children {
                    find_and_test_au(checker, child, n);
                }
            }
            ResolvedCtl::EU(phi, psi) => {
                find_and_test_au(checker, phi, n);
                find_and_test_au(checker, psi, n);
            }
            ResolvedCtl::Atom(_) => {}
        }
    }

    eprintln!("\n=== AU algebraic vs fixpoint on CTLFireability-13 ===");
    find_and_test_au(&checker, &resolved, n);

    // Also test CTLCardinality-07 which uses EU
    let card_props = parse_properties(&mcc_benchmark_dir("AirplaneLD-PT-0010"), "CTLCardinality")
        .expect("parse properties");
    let ctl07 = match &card_props[7].formula {
        Formula::Ctl(ctl) => ctl,
        _ => panic!("expected CTL formula"),
    };
    let resolved07 = resolve_ctl(ctl07, &place_map, &trans_map);
    eprintln!("\n=== AU algebraic vs fixpoint on CTLCardinality-07 ===");
    find_and_test_au(&checker, &resolved07, n);

    // Check AF duality on the real graph
    // AF(phi) = NOT(EG(NOT(phi))) vs mu Z. phi OR AX(Z)
    // Extract AF subformulas from CTLFireability-09
    let ctl09 = match &props[9].formula {
        Formula::Ctl(ctl) => ctl,
        _ => panic!("expected CTL formula"),
    };
    let resolved09 = resolve_ctl(ctl09, &place_map, &trans_map);

    fn find_and_test_af(checker: &CtlChecker, formula: &ResolvedCtl, n: usize) {
        match formula {
            ResolvedCtl::AF(inner) => {
                let sat_phi = checker.eval(inner);
                let not_phi: Vec<bool> = sat_phi.iter().map(|&v| !v).collect();
                let eg_not = checker.gfp_eg(&not_phi);
                let af_duality: Vec<bool> = eg_not.into_iter().map(|v| !v).collect();
                let af_fixpoint = reference_lfp_af(checker, &sat_phi);
                let agree = af_duality == af_fixpoint;
                let dual_count = af_duality.iter().filter(|&&v| v).count();
                let fix_count = af_fixpoint.iter().filter(|&&v| v).count();
                eprintln!(
                    "AF subformula: duality={dual_count}/{n} s0={}, \
                     fixpoint={fix_count}/{n} s0={}, agree={agree}",
                    af_duality[0], af_fixpoint[0]
                );
                assert!(
                    agree,
                    "AF duality and fixpoint must agree on all {n} states"
                );
                find_and_test_af(checker, inner, n);
            }
            ResolvedCtl::Not(inner)
            | ResolvedCtl::EX(inner)
            | ResolvedCtl::AX(inner)
            | ResolvedCtl::EF(inner)
            | ResolvedCtl::EG(inner)
            | ResolvedCtl::AG(inner) => {
                find_and_test_af(checker, inner, n);
            }
            ResolvedCtl::And(children) | ResolvedCtl::Or(children) => {
                for child in children {
                    find_and_test_af(checker, child, n);
                }
            }
            ResolvedCtl::EU(phi, psi) | ResolvedCtl::AU(phi, psi) => {
                find_and_test_af(checker, phi, n);
                find_and_test_af(checker, psi, n);
            }
            ResolvedCtl::Atom(_) => {}
        }
    }

    eprintln!("\n=== AF duality vs fixpoint on CTLFireability-09 ===");
    find_and_test_af(&checker, &resolved09, n);
}
