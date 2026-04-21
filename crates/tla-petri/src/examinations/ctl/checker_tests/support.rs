// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::examinations::ctl::checker::CtlChecker;
use crate::examinations::ctl::resolve::ResolvedCtl;
use crate::explorer::{FullReachabilityGraph, ReachabilityGraph};
use crate::petri_net::{PetriNet, PlaceIdx, PlaceInfo};
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};
use std::path::PathBuf;

pub(super) fn test_net(num_places: usize) -> PetriNet {
    PetriNet {
        name: Some("ctl-test".to_string()),
        places: (0..num_places)
            .map(|index| PlaceInfo {
                id: format!("p{index}"),
                name: None,
            })
            .collect(),
        transitions: Vec::new(),
        initial_marking: vec![0; num_places],
    }
}

pub(super) fn full_graph(adj: Vec<Vec<u32>>, markings: Vec<Vec<u64>>) -> FullReachabilityGraph {
    FullReachabilityGraph {
        graph: ReachabilityGraph {
            num_states: adj.len() as u32,
            adj: adj
                .into_iter()
                .map(|successors| successors.into_iter().map(|succ| (succ, 0)).collect())
                .collect(),
            completed: true,
        },
        markings,
    }
}

pub(super) fn atom_at_least(place: u32, value: u64) -> ResolvedCtl {
    ResolvedCtl::Atom(ResolvedPredicate::IntLe(
        ResolvedIntExpr::Constant(value),
        ResolvedIntExpr::TokensCount(vec![PlaceIdx(place)]),
    ))
}

pub(super) fn mcc_benchmark_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

pub(super) fn has_mcc_benchmark(model: &str) -> bool {
    mcc_benchmark_dir(model).join("model.pnml").exists()
}

/// Recursive formula tracer: prints sat-set size and initial-state value for
/// every subformula in the evaluation tree.
pub(super) fn trace_eval(checker: &CtlChecker, formula: &ResolvedCtl, depth: usize) -> Vec<bool> {
    let indent = "  ".repeat(depth);
    let sat = checker.eval(formula);
    let count = sat.iter().filter(|&&v| v).count();
    let s0 = sat[0];

    let label = match formula {
        ResolvedCtl::Atom(_) => "Atom".to_string(),
        ResolvedCtl::Not(_) => "NOT".to_string(),
        ResolvedCtl::And(c) => format!("AND({})", c.len()),
        ResolvedCtl::Or(c) => format!("OR({})", c.len()),
        ResolvedCtl::EX(_) => "EX".to_string(),
        ResolvedCtl::AX(_) => "AX".to_string(),
        ResolvedCtl::EF(_) => "EF".to_string(),
        ResolvedCtl::AF(_) => "AF".to_string(),
        ResolvedCtl::EG(_) => "EG".to_string(),
        ResolvedCtl::AG(_) => "AG".to_string(),
        ResolvedCtl::EU(_, _) => "EU".to_string(),
        ResolvedCtl::AU(_, _) => "AU".to_string(),
    };

    eprintln!("{indent}{label}: {count}/{} states, s0={s0}", sat.len());

    // Recurse into children for detail
    match formula {
        ResolvedCtl::Atom(_) => {}
        ResolvedCtl::Not(inner)
        | ResolvedCtl::EX(inner)
        | ResolvedCtl::AX(inner)
        | ResolvedCtl::EF(inner)
        | ResolvedCtl::AF(inner)
        | ResolvedCtl::EG(inner)
        | ResolvedCtl::AG(inner) => {
            trace_eval(checker, inner, depth + 1);
        }
        ResolvedCtl::And(children) | ResolvedCtl::Or(children) => {
            for child in children {
                trace_eval(checker, child, depth + 1);
            }
        }
        ResolvedCtl::EU(phi, psi) | ResolvedCtl::AU(phi, psi) => {
            trace_eval(checker, phi, depth + 1);
            trace_eval(checker, psi, depth + 1);
        }
    }

    sat
}
