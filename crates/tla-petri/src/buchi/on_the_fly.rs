// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! On-the-fly product emptiness checking: system × GBA.
//!
//! Unlike [`super::product`] which requires a pre-built [`FullReachabilityGraph`],
//! this module computes system successors lazily by firing transitions on the
//! Petri net. Benefits:
//!
//! 1. **No full-graph memory cost.** The system reachability graph is never
//!    materialized — only the product graph is stored.
//! 2. **POR-compatible.** Stubborn set reduction can filter successors at
//!    each product state (Phase 3).
//! 3. **Early termination potential.** Future DFS-based emptiness can stop
//!    as soon as an accepting cycle is found.

use std::collections::VecDeque;
use std::time::Instant;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::error::PnmlError;
use crate::explorer::ExplorationSetup;
use crate::marking::{pack_marking_config, unpack_marking_config};
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::reduction::ReducedNet;
use crate::resolved_predicate::{eval_predicate, ResolvedPredicate};
use crate::scc::tarjan_scc_generic;
use crate::stubborn::{compute_stubborn_set, DependencyGraph, PorStrategy};

use super::gba::{Gba, GbaStateId, GbaTransition};

const PRODUCT_STATE_LIMIT: usize = 50_000_000;

/// Pre-computed POR context for on-the-fly product exploration.
///
/// When present, the successor generation loop at each product state
/// calls [`compute_stubborn_set`] to fire only a subset of enabled
/// transitions, reducing the explored product graph while preserving
/// stutter-equivalent traces.
pub(crate) struct PorContext {
    pub(crate) dep: DependencyGraph,
    pub(crate) visible: Vec<TransitionIdx>,
}

/// Check guard satisfaction by evaluating atoms directly against a marking.
///
/// This replaces the precomputed `atom_sat` table in [`super::atoms::LtlContext`]
/// with per-state evaluation, trading CPU for memory.
fn guard_satisfied_at_marking(
    trans: &GbaTransition,
    atoms: &[ResolvedPredicate],
    marking: &[u64],
    net: &PetriNet,
) -> bool {
    trans
        .pos_atoms
        .iter()
        .all(|&a| eval_predicate(&atoms[a], marking, net))
        && trans
            .neg_atoms
            .iter()
            .all(|&a| !eval_predicate(&atoms[a], marking, net))
}

/// On-the-fly product emptiness: system × GBA accepting cycle detection.
///
/// Builds the product graph lazily — system successors are computed by firing
/// transitions on the reduced `net`, then expanded to original-net space via
/// `reduced` for atom evaluation against `original_net`.
///
/// Returns `Some(true)` if an accepting cycle exists (formula is violated),
/// `Some(false)` if no accepting cycle (formula holds), or `None` if the
/// system-marking or product-state budget was exceeded.
pub(super) fn on_the_fly_product_emptiness(
    gba: &Gba,
    net: &PetriNet,
    reduced: &ReducedNet,
    original_net: &PetriNet,
    atoms: &[ResolvedPredicate],
    por: Option<&PorContext>,
    max_system_states: usize,
    deadline: Option<Instant>,
) -> Result<Option<bool>, PnmlError> {
    on_the_fly_impl(
        gba,
        net,
        reduced,
        original_net,
        atoms,
        por,
        max_system_states,
        PRODUCT_STATE_LIMIT,
        deadline,
    )
}

#[cfg(test)]
pub(super) fn on_the_fly_product_emptiness_with_limit(
    gba: &Gba,
    net: &PetriNet,
    reduced: &ReducedNet,
    original_net: &PetriNet,
    atoms: &[ResolvedPredicate],
    max_system_states: usize,
    product_state_limit: usize,
    deadline: Option<Instant>,
) -> Result<Option<bool>, PnmlError> {
    on_the_fly_impl(
        gba,
        net,
        reduced,
        original_net,
        atoms,
        None,
        max_system_states,
        product_state_limit,
        deadline,
    )
}

/// Collect all enabled transitions at a marking (fallback when POR is off or gives no reduction).
fn all_enabled(net: &PetriNet, marking: &[u64], num_transitions: usize) -> Vec<TransitionIdx> {
    (0..num_transitions)
        .map(|i| TransitionIdx(i as u32))
        .filter(|&t| net.is_enabled(marking, t))
        .collect()
}

fn record_system_marking(
    seen_markings: &mut FxHashSet<Box<[u8]>>,
    packed_marking: &[u8],
    max_system_states: usize,
) -> bool {
    if !seen_markings.insert(Box::from(packed_marking)) {
        return true;
    }
    seen_markings.len() <= max_system_states
}

fn on_the_fly_impl(
    gba: &Gba,
    net: &PetriNet,
    reduced: &ReducedNet,
    original_net: &PetriNet,
    atoms: &[ResolvedPredicate],
    por: Option<&PorContext>,
    max_system_states: usize,
    product_state_limit: usize,
    deadline: Option<Instant>,
) -> Result<Option<bool>, PnmlError> {
    if gba.num_states == 0 {
        return Ok(Some(false));
    }

    let num_accept = gba.acceptance.len();
    let setup = ExplorationSetup::analyze(net);

    // Product state = (packed_system_marking, gba_state).
    // Integer IDs assigned for SCC algorithm.
    let mut product_ids: FxHashMap<(Box<[u8]>, GbaStateId), u32> = FxHashMap::default();
    let mut product_adj: Vec<Vec<u32>> = Vec::new();
    let mut product_accept: Vec<Vec<bool>> = Vec::new();
    let mut product_edge_accept: Vec<Vec<(u32, Vec<bool>)>> = Vec::new();
    let mut queue: VecDeque<u32> = VecDeque::new();

    // Per-product-state data for lazy successor computation.
    let mut product_packed: Vec<Box<[u8]>> = Vec::new();
    let mut product_gba_state: Vec<GbaStateId> = Vec::new();
    let mut seen_system_markings: FxHashSet<Box<[u8]>> = FxHashSet::default();

    // Reusable buffers.
    let mut tokens_buf = Vec::with_capacity(setup.num_places);
    let mut pack_buf = Vec::with_capacity(setup.pack_capacity);
    let mut expanded_buf = Vec::new();

    if !record_system_marking(
        &mut seen_system_markings,
        &setup.initial_packed,
        max_system_states,
    ) {
        return Ok(None);
    }

    // Evaluate initial GBA transitions against initial system state.
    // The initial marking is already in original-net space for the reduced net's
    // initial marking, but we need the ORIGINAL net's initial marking for atoms.
    let initial_expanded = reduced.expand_marking(&net.initial_marking)?;

    for init_trans in &gba.initial_transitions {
        if guard_satisfied_at_marking(init_trans, atoms, &initial_expanded, original_net) {
            let key = (setup.initial_packed.clone(), init_trans.successor);
            if product_ids.contains_key(&key) {
                continue;
            }
            let pid = product_ids.len() as u32;
            product_ids.insert(key, pid);
            product_adj.push(Vec::new());
            product_edge_accept.push(Vec::new());
            product_packed.push(setup.initial_packed.clone());
            product_gba_state.push(init_trans.successor);
            let accepts: Vec<bool> = (0..num_accept)
                .map(|i| gba.acceptance[i].contains(&init_trans.successor))
                .collect();
            product_accept.push(accepts);
            queue.push_back(pid);
        }
    }

    // BFS to build product graph with lazy system successors.
    while let Some(pid) = queue.pop_front() {
        if (pid as usize & 0x0FFF) == 0 && deadline.is_some_and(|dl| Instant::now() >= dl) {
            return Ok(None);
        }

        let packed = &product_packed[pid as usize];
        let gba_state = product_gba_state[pid as usize];

        // Unpack to get reduced-net tokens.
        unpack_marking_config(packed, &setup.marking_config, &mut tokens_buf);

        // Compute system successors by firing transitions on the reduced net.
        // When POR is active, only fire the stubborn subset of enabled transitions.
        let mut sys_succs: Vec<Box<[u8]>> = Vec::new();

        let to_fire = if let Some(por) = por {
            let strategy = PorStrategy::SafetyPreserving {
                visible: por.visible.clone(),
            };
            match compute_stubborn_set(net, &tokens_buf, &por.dep, &strategy) {
                Some(stubborn) => stubborn,
                None => all_enabled(net, &tokens_buf, setup.num_transitions),
            }
        } else {
            all_enabled(net, &tokens_buf, setup.num_transitions)
        };

        for &trans in &to_fire {
            net.apply_delta(&mut tokens_buf, trans);
            pack_marking_config(&tokens_buf, &setup.marking_config, &mut pack_buf);
            sys_succs.push(pack_buf.as_slice().into());
            net.undo_delta(&mut tokens_buf, trans);
        }

        if to_fire.is_empty() {
            // Deadlock: self-loop with current marking.
            sys_succs.push(packed.clone());
        }

        let mut successors = Vec::new();
        let mut edge_accepts = Vec::new();

        for succ_packed in &sys_succs {
            if !record_system_marking(&mut seen_system_markings, succ_packed, max_system_states) {
                return Ok(None);
            }

            // Expand successor marking for atom evaluation.
            // Unpack the reduced-net marking, then expand to original-net space.
            unpack_marking_config(succ_packed, &setup.marking_config, &mut tokens_buf);
            reduced.expand_marking_into(&tokens_buf, &mut expanded_buf)?;

            // GBA guards are evaluated against the SUCCESSOR system state.
            // See product.rs comments for the GPVW construction semantics.
            for trans in &gba.transitions[gba_state as usize] {
                if guard_satisfied_at_marking(trans, atoms, &expanded_buf, original_net) {
                    let key = (succ_packed.clone(), trans.successor);
                    let succ_pid = if let Some(&existing) = product_ids.get(&key) {
                        existing
                    } else {
                        let new_pid = product_ids.len() as u32;
                        product_ids.insert(key, new_pid);
                        product_adj.push(Vec::new());
                        product_edge_accept.push(Vec::new());
                        product_packed.push(succ_packed.clone());
                        product_gba_state.push(trans.successor);
                        let accepts: Vec<bool> = (0..num_accept)
                            .map(|i| gba.acceptance[i].contains(&trans.successor))
                            .collect();
                        product_accept.push(accepts);
                        queue.push_back(new_pid);
                        new_pid
                    };
                    successors.push(succ_pid);
                    edge_accepts.push((succ_pid, trans.edge_accept.clone()));
                }
            }
        }

        successors.sort_unstable();
        successors.dedup();
        product_adj[pid as usize] = successors;
        product_edge_accept[pid as usize] = edge_accepts;

        if product_ids.len() > product_state_limit {
            return Ok(None);
        }
    }

    // SCC-based accepting cycle detection (same logic as product.rs).
    let product_n = product_adj.len();
    if product_n == 0 {
        return Ok(Some(false));
    }

    let sccs = tarjan_scc_generic(&product_adj, |&w| w);

    for scc in &sccs {
        // Non-trivial: has a cycle (size > 1, or size 1 with self-loop).
        let is_nontrivial = if scc.len() > 1 {
            true
        } else {
            let s = scc[0];
            product_adj[s as usize].contains(&s)
        };
        if !is_nontrivial {
            continue;
        }

        if num_accept == 0 {
            return Ok(Some(true));
        }

        let scc_set: FxHashSet<u32> = scc.iter().copied().collect();

        let all_accepted = (0..num_accept).all(|i| {
            // State-based acceptance.
            let state_accepted = scc
                .iter()
                .any(|&s| product_accept[s as usize].get(i).copied().unwrap_or(false));
            if state_accepted {
                return true;
            }
            // Edge-based acceptance: both source and target in the SCC.
            scc.iter().any(|&s| {
                product_edge_accept[s as usize]
                    .iter()
                    .any(|(succ, ea)| scc_set.contains(succ) && ea.get(i).copied().unwrap_or(false))
            })
        });
        if all_accepted {
            return Ok(Some(true));
        }
    }

    Ok(Some(false))
}

#[cfg(test)]
#[path = "on_the_fly_tests.rs"]
mod tests;
