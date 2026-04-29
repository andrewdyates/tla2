// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::examinations::ctl::resolve::ResolvedCtl;
use crate::explorer::FullReachabilityGraph;
use crate::petri_net::PetriNet;
use crate::resolved_predicate::eval_predicate;

/// Independent CTL evaluator using ONLY naive fixpoint iteration.
/// No backward BFS, no duality, no algebraic rewrites.
/// If this agrees with the existing checker on wrong answers, the bug isn't in operators.
/// If it disagrees, we can find the differing operator.
pub(super) fn naive_ctl_eval(
    formula: &ResolvedCtl,
    full: &FullReachabilityGraph,
    net: &PetriNet,
) -> Vec<bool> {
    let n = full.graph.num_states as usize;
    match formula {
        ResolvedCtl::Atom(pred) => (0..n)
            .map(|s| eval_predicate(pred, &full.markings[s], net))
            .collect(),
        ResolvedCtl::Not(inner) => naive_ctl_eval(inner, full, net)
            .into_iter()
            .map(|v| !v)
            .collect(),
        ResolvedCtl::And(children) => {
            let mut result = vec![true; n];
            for child in children {
                let sat = naive_ctl_eval(child, full, net);
                for i in 0..n {
                    result[i] = result[i] && sat[i];
                }
            }
            result
        }
        ResolvedCtl::Or(children) => {
            let mut result = vec![false; n];
            for child in children {
                let sat = naive_ctl_eval(child, full, net);
                for i in 0..n {
                    result[i] = result[i] || sat[i];
                }
            }
            result
        }
        ResolvedCtl::EX(inner) => {
            let sat = naive_ctl_eval(inner, full, net);
            naive_pre_e(&sat, full)
        }
        ResolvedCtl::AX(inner) => {
            let sat = naive_ctl_eval(inner, full, net);
            naive_pre_a(&sat, full)
        }
        ResolvedCtl::EF(inner) => {
            // μZ. φ ∨ EX(Z)
            let phi = naive_ctl_eval(inner, full, net);
            let mut z = phi.clone();
            loop {
                let ex_z = naive_pre_e(&z, full);
                let next: Vec<bool> = (0..n).map(|i| phi[i] || ex_z[i]).collect();
                if next == z {
                    break;
                }
                z = next;
            }
            z
        }
        ResolvedCtl::AF(inner) => {
            // μZ. φ ∨ AX(Z) — direct fixpoint, NOT via ¬EG(¬φ)
            let phi = naive_ctl_eval(inner, full, net);
            let mut z = vec![false; n]; // least fixpoint starts empty
            loop {
                let ax_z = naive_pre_a(&z, full);
                let next: Vec<bool> = (0..n).map(|i| phi[i] || ax_z[i]).collect();
                if next == z {
                    break;
                }
                z = next;
            }
            z
        }
        ResolvedCtl::EG(inner) => {
            // νZ. φ ∧ EX(Z) — greatest fixpoint starts from φ
            let phi = naive_ctl_eval(inner, full, net);
            let mut z = phi.clone();
            loop {
                let ex_z = naive_pre_e(&z, full);
                let next: Vec<bool> = (0..n).map(|i| phi[i] && ex_z[i]).collect();
                if next == z {
                    break;
                }
                z = next;
            }
            z
        }
        ResolvedCtl::AG(inner) => {
            // νZ. φ ∧ AX(Z) — greatest fixpoint starts from φ
            let phi = naive_ctl_eval(inner, full, net);
            let mut z = phi.clone();
            loop {
                let ax_z = naive_pre_a(&z, full);
                let next: Vec<bool> = (0..n).map(|i| phi[i] && ax_z[i]).collect();
                if next == z {
                    break;
                }
                z = next;
            }
            z
        }
        ResolvedCtl::EU(phi_f, psi_f) => {
            // μZ. ψ ∨ (φ ∧ EX(Z))
            let phi = naive_ctl_eval(phi_f, full, net);
            let psi = naive_ctl_eval(psi_f, full, net);
            let mut z = vec![false; n];
            loop {
                let ex_z = naive_pre_e(&z, full);
                let next: Vec<bool> = (0..n).map(|i| psi[i] || (phi[i] && ex_z[i])).collect();
                if next == z {
                    break;
                }
                z = next;
            }
            z
        }
        ResolvedCtl::AU(phi_f, psi_f) => {
            // μZ. ψ ∨ (φ ∧ AX(Z)) — direct fixpoint, NOT via algebraic identity
            let phi = naive_ctl_eval(phi_f, full, net);
            let psi = naive_ctl_eval(psi_f, full, net);
            let mut z = vec![false; n];
            loop {
                let ax_z = naive_pre_a(&z, full);
                let next: Vec<bool> = (0..n).map(|i| psi[i] || (phi[i] && ax_z[i])).collect();
                if next == z {
                    break;
                }
                z = next;
            }
            z
        }
    }
}

pub(super) fn naive_pre_e(sat: &[bool], full: &FullReachabilityGraph) -> Vec<bool> {
    let n = sat.len();
    (0..n)
        .map(|s| {
            if full.graph.adj[s].is_empty() {
                false // MCC semantics: no successor exists
            } else {
                full.graph.adj[s]
                    .iter()
                    .any(|&(succ, _)| sat[succ as usize])
            }
        })
        .collect()
}

pub(super) fn naive_pre_a(sat: &[bool], full: &FullReachabilityGraph) -> Vec<bool> {
    let n = sat.len();
    (0..n)
        .map(|s| {
            if full.graph.adj[s].is_empty() {
                true // MCC semantics: vacuously true
            } else {
                full.graph.adj[s]
                    .iter()
                    .all(|&(succ, _)| sat[succ as usize])
            }
        })
        .collect()
}
