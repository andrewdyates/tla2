// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Product graph emptiness checking: system × GBA accepting cycle detection.
//!
//! Uses both state-based and edge-based acceptance to correctly handle
//! `G(X(F(...)))` patterns where the `Release` operator re-introduces
//! `Until` obligations at every step.

use rustc_hash::FxHashMap;

use super::atoms::LtlContext;
use super::gba::{Gba, GbaStateId};
use crate::scc::tarjan_scc_generic;

const PRODUCT_STATE_LIMIT: usize = 50_000_000;

/// Check if the product of system × GBA has an accepting cycle reachable from
/// the initial system state.
///
/// Returns `Some(true)` if an accepting cycle exists, `Some(false)` if none,
/// or `None` if the product graph exceeded the size limit.
pub(super) fn product_has_accepting_cycle(gba: &Gba, ctx: &LtlContext<'_>) -> Option<bool> {
    product_has_accepting_cycle_impl(gba, ctx, PRODUCT_STATE_LIMIT)
}

#[cfg(test)]
pub(super) fn product_has_accepting_cycle_with_limit(
    gba: &Gba,
    ctx: &LtlContext<'_>,
    product_state_limit: usize,
) -> Option<bool> {
    product_has_accepting_cycle_impl(gba, ctx, product_state_limit)
}

fn product_has_accepting_cycle_impl(
    gba: &Gba,
    ctx: &LtlContext<'_>,
    product_state_limit: usize,
) -> Option<bool> {
    if gba.num_states == 0 || ctx.full.graph.num_states == 0 {
        return Some(false);
    }

    // No acceptance sets means any cycle is accepting.
    let num_accept = gba.acceptance.len();

    // Build the product graph on-the-fly and check for accepting SCCs.
    // Product state = (system_state, gba_state).
    let mut product_ids: FxHashMap<(u32, GbaStateId), u32> = FxHashMap::default();
    let mut product_adj: Vec<Vec<u32>> = Vec::new();
    let mut product_accept: Vec<Vec<bool>> = Vec::new(); // [product_state][accept_set_idx]
                                                         // Edge-based acceptance: for each product state, the outgoing edges
                                                         // with their successor and edge_accept flags.
    let mut product_edge_accept: Vec<Vec<(u32, Vec<bool>)>> = Vec::new();
    let mut queue: std::collections::VecDeque<u32> = std::collections::VecDeque::new();

    // Initial product states: check each initial GBA transition's guard
    // against system state 0. Only add product states where guard is satisfied.
    for init_trans in &gba.initial_transitions {
        if init_trans.guard_satisfied(ctx, 0) {
            let gba_state = init_trans.successor;
            let product_key = (0u32, gba_state);
            if product_ids.contains_key(&product_key) {
                continue; // Already added
            }
            let pid = product_ids.len() as u32;
            product_ids.insert(product_key, pid);
            product_adj.push(Vec::new());
            product_edge_accept.push(Vec::new());
            let accepts: Vec<bool> = (0..num_accept)
                .map(|i| gba.acceptance[i].contains(&gba_state))
                .collect();
            product_accept.push(accepts);
            queue.push_back(pid);
        }
    }

    // Reverse lookup: product_id → (sys_state, gba_state)
    let mut product_keys: Vec<(u32, GbaStateId)> = vec![(0, 0); product_ids.len()];
    for (&key, &pid) in &product_ids {
        product_keys[pid as usize] = key;
    }

    // BFS to build product graph
    while let Some(pid) = queue.pop_front() {
        let (sys, gba_state) = product_keys[pid as usize];

        let mut successors = Vec::new();
        let mut edge_accepts = Vec::new();

        // For each system transition from sys
        let sys_succs: Vec<u32> = if ctx.full.graph.adj[sys as usize].is_empty() {
            vec![sys] // Deadlock self-loop
        } else {
            ctx.full.graph.adj[sys as usize]
                .iter()
                .map(|&(s, _)| s)
                .collect()
        };

        // GBA guards are evaluated against the SUCCESSOR system state.
        //
        // In the GPVW on-the-fly construction, the initial expansion
        // "reads" the first letter (L(s0)), so GBA state obligations
        // are one step ahead of the product state's system position.
        // Product state (si, qi) pairs system state si with GBA state qi
        // whose obligations correspond to step i+1. When qi transitions,
        // the guard describes what must hold at step i+1 = L(si+1).
        //
        // Historical note: #1246 changed this from sys_succ to sys,
        // which fixed 5 wrong answers that were actually caused by the
        // XML parser bug (first_element → only_element_child). Reverting
        // to sys_succ with the parser fix resolves all 9 properties.
        for &sys_succ in &sys_succs {
            for trans in &gba.transitions[gba_state as usize] {
                if trans.guard_satisfied(ctx, sys_succ) {
                    let product_key = (sys_succ, trans.successor);
                    let succ_pid = if let Some(&existing) = product_ids.get(&product_key) {
                        existing
                    } else {
                        let new_pid = product_ids.len() as u32;
                        product_ids.insert(product_key, new_pid);
                        product_adj.push(Vec::new());
                        product_edge_accept.push(Vec::new());
                        product_keys.push(product_key);
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

        // Safety: limit product size
        if product_ids.len() > product_state_limit {
            // Product too large — inconclusive
            return None;
        }
    }

    // Find accepting SCCs in the product graph.
    // An SCC is accepting if it's non-trivial AND for each acceptance set,
    // at least one state in the SCC is state-accepting for that set, OR
    // at least one edge within the SCC is edge-accepting for that set.
    let product_n = product_adj.len();
    if product_n == 0 {
        return Some(false);
    }

    let sccs = tarjan_product(&product_adj);

    for scc in &sccs {
        // Non-trivial: has a cycle (size > 1, or size 1 with self-loop)
        let is_nontrivial = if scc.len() > 1 {
            true
        } else {
            let s = scc[0];
            product_adj[s as usize].contains(&s)
        };
        if !is_nontrivial {
            continue;
        }

        // Check all acceptance conditions
        if num_accept == 0 {
            return Some(true); // Any non-trivial cycle is accepting
        }

        // Build set of SCC members for fast lookup
        let scc_set: rustc_hash::FxHashSet<u32> = scc.iter().copied().collect();

        let all_accepted = (0..num_accept).all(|i| {
            // State-based acceptance: some state in SCC is accepting
            let state_accepted = scc
                .iter()
                .any(|&s| product_accept[s as usize].get(i).copied().unwrap_or(false));
            if state_accepted {
                return true;
            }
            // Edge-based acceptance: some edge WITHIN the SCC is accepting
            // (both source and target must be in the SCC)
            scc.iter().any(|&s| {
                product_edge_accept[s as usize]
                    .iter()
                    .any(|(succ, ea)| scc_set.contains(succ) && ea.get(i).copied().unwrap_or(false))
            })
        });
        if all_accepted {
            return Some(true);
        }
    }

    Some(false)
}

/// Tarjan's SCC for the product graph (plain `u32` successor edges).
fn tarjan_product(adj: &[Vec<u32>]) -> Vec<Vec<u32>> {
    tarjan_scc_generic(adj, |&w| w)
}

#[cfg(test)]
#[path = "product_tests.rs"]
mod product_tests;
