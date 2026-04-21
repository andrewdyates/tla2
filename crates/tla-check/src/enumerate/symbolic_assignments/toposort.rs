// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Topological sorting of symbolic assignments.
//!
//! Sorts primed-variable assignments so that definitions come before references,
//! e.g. `count' = count + 1` before `announced' = (count' >= VT)`.

use rustc_hash::FxHashSet;
use std::sync::Arc;

use crate::eval::EvalCtx;

use super::super::{
    debug_toposort, get_primed_var_refs, get_primed_var_refs_with_ctx, SymbolicAssignment,
};

/// Extract primed variable references from a symbolic assignment.
/// Part of #1564: shared by topo sort n=2 fast-path and main loop.
fn get_symbolic_primed_refs(ctx: Option<&EvalCtx>, sym: &SymbolicAssignment) -> FxHashSet<Arc<str>> {
    match sym {
        SymbolicAssignment::Expr(_, expr, _) | SymbolicAssignment::InSet(_, expr, _) => {
            if let Some(c) = ctx {
                get_primed_var_refs_with_ctx(c, &expr.node)
            } else {
                get_primed_var_refs(&expr.node)
            }
        }
        SymbolicAssignment::Value(_, _) | SymbolicAssignment::Unchanged(_) => FxHashSet::default(),
    }
}

/// Topologically sort symbolic assignments so that assignments defining x' come before
/// assignments that reference x'. This ensures proper evaluation order when computing
/// expressions like `announced' = (count' >= VT)` which depends on `count' = count + 1`.
///
/// When `ctx` is provided, operator references are followed to find hidden dependencies
/// (e.g., `IF ActionX THEN 5 ELSE y` where ActionX contains `x'`).
pub(in crate::enumerate) fn topological_sort_assignments(
    ctx: Option<&EvalCtx>,
    symbolic: &[SymbolicAssignment],
) -> Vec<SymbolicAssignment> {
    let debug = debug_toposort();

    if symbolic.is_empty() {
        return Vec::new();
    }

    let n = symbolic.len();

    // Fast path: single assignment has no dependencies to sort.
    if n == 1 {
        return symbolic.to_vec();
    }

    // Fast path: two assignments — check single dependency direction without
    // allocating FxHashMap, BinaryHeap, adjacency lists, or in_degree vectors.
    // Most specs have 2-4 state variables, so n=2 is the most common case
    // after n=1. Part of #1564.
    if n == 2 {
        let name_0 = symbolic[0].var_name();
        let name_1 = symbolic[1].var_name();

        let refs_0 = get_symbolic_primed_refs(ctx, &symbolic[0]);
        let refs_1 = get_symbolic_primed_refs(ctx, &symbolic[1]);

        let dep_0_on_1 = refs_0.contains(name_1);
        let dep_1_on_0 = refs_1.contains(name_0);

        if debug {
            eprintln!(
                "[TOPOSORT] n=2 fast path: {}'→{}'={}, {}'→{}'={}",
                name_0, name_1, dep_0_on_1, name_1, name_0, dep_1_on_0
            );
        }

        return if dep_0_on_1 && !dep_1_on_0 {
            // Assignment 0 depends on 1: must swap order
            vec![symbolic[1].clone(), symbolic[0].clone()]
        } else {
            // No deps, both independent, or mutual cycle — keep original order
            symbolic.to_vec()
        };
    }

    // For n <= 16 (covers >99% of real specs), use bitmask-based topo sort
    // with zero heap allocation for the sort bookkeeping itself. Each node's
    // dependencies are a u16 bitmask — eliminating FxHashMap, Vec<Vec>, and
    // BinaryHeap allocations that the general case requires. Part of #1564.
    if n <= 16 {
        return topological_sort_bitmask(ctx, symbolic, n, debug);
    }

    // n > 16: fall through to allocation-heavy general case (extremely rare).
    topological_sort_general(ctx, symbolic, n, debug)
}

/// Bitmask-based topological sort for n <= 16. Zero heap allocation for sort
/// bookkeeping — all state fits in stack-allocated `[u16; 16]` arrays.
/// Kahn's algorithm uses linear scan (O(n^2) total, but n <= 16 so max 256 ops).
fn topological_sort_bitmask(
    ctx: Option<&EvalCtx>,
    symbolic: &[SymbolicAssignment],
    n: usize,
    debug: bool,
) -> Vec<SymbolicAssignment> {
    debug_assert!((3..=16).contains(&n));

    // dep_mask[i] has bit j set if assignment i depends on assignment j.
    let mut dep_mask = [0u16; 16];

    for (i, sym) in symbolic.iter().enumerate() {
        let refs = get_symbolic_primed_refs(ctx, sym);
        if refs.is_empty() {
            continue;
        }
        // Find the first defining assignment for each referenced primed variable.
        // Must match FxHashMap::entry(name).or_insert(idx) semantics: the first
        // definer wins, and self-references (def_idx == i) are not dependencies.
        // Linear scan is faster than FxHashMap for n <= 16 (cache-friendly, no alloc).
        for ref_name in &refs {
            // Find the first assignment (any index) that defines ref_name.
            let first_def = symbolic[..n]
                .iter()
                .position(|s| s.var_name().as_ref() == ref_name.as_ref());
            if let Some(def_idx) = first_def {
                if def_idx != i {
                    dep_mask[i] |= 1u16 << def_idx;
                }
            }
        }
        if debug {
            let dep_indices: Vec<usize> =
                (0..n).filter(|&j| dep_mask[i] & (1u16 << j) != 0).collect();
            eprintln!(
                "[TOPOSORT] Assignment {} references primed vars: {:?}, deps: {:?}",
                i,
                refs.iter()
                    .map(std::convert::AsRef::as_ref)
                    .collect::<Vec<_>>(),
                dep_indices
            );
        }
    }

    // Fast path: if all dependencies point to earlier indices, already in topo order.
    let already_sorted = (0..n).all(|i| dep_mask[i] & !((1u16 << i).wrapping_sub(1)) == 0);
    if already_sorted {
        if debug {
            eprintln!("[TOPOSORT] Already in topological order, skipping Kahn's");
        }
        return symbolic.to_vec();
    }

    // Kahn's algorithm: process nodes with no remaining deps, smallest index first.
    // Maintain dep_mask copy — clear bits as nodes are processed.
    let mut remaining = dep_mask;
    let mut processed = 0u16;
    let mut order = [0u8; 16];
    let mut order_len = 0usize;

    for _ in 0..n {
        // Find smallest unprocessed node with no remaining dependencies.
        let next = remaining[..n]
            .iter()
            .enumerate()
            .find(|&(k, &deps)| processed & (1u16 << k) == 0 && deps == 0)
            .map(|(k, _)| k);
        let Some(i) = next else {
            // Cycle detected — fall back to original order.
            if debug {
                eprintln!("[TOPOSORT] Cycle detected, falling back to original order");
            }
            return symbolic.to_vec();
        };
        order[order_len] = i as u8;
        order_len += 1;
        processed |= 1u16 << i;

        // Clear bit i from all remaining dependency masks.
        let clear = !(1u16 << i);
        for slot in &mut remaining[..n] {
            *slot &= clear;
        }
    }

    if debug {
        eprintln!("[TOPOSORT] Sorted order:");
        for (out_i, &in_i) in order[..order_len].iter().enumerate() {
            eprintln!(
                "[TOPOSORT]   {}: {}'",
                out_i,
                symbolic[in_i as usize].var_name()
            );
        }
    }

    order[..order_len]
        .iter()
        .map(|&i| symbolic[i as usize].clone())
        .collect()
}

/// General topological sort for n > 16 using heap-allocated collections.
/// This path is extremely rare — most TLA+ specs have fewer than 16 state variables.
fn topological_sort_general(
    ctx: Option<&EvalCtx>,
    symbolic: &[SymbolicAssignment],
    n: usize,
    debug: bool,
) -> Vec<SymbolicAssignment> {
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;
    use rustc_hash::FxHashMap;

    // Capture defined variable per assignment in stable, input order.
    let mut defined_vars: Vec<Arc<str>> = Vec::with_capacity(n);
    for (i, sym) in symbolic.iter().enumerate() {
        let name = sym.var_name().clone();
        if debug {
            eprintln!("[TOPOSORT] Assignment {}: {}' = {:?}", i, name, sym);
        }
        defined_vars.push(name);
    }

    // Map variable name -> defining assignment index.
    //
    // If a variable is assigned more than once, pick the FIRST occurrence to keep the
    // result deterministic and consistent with extraction order.
    let mut var_to_idx: FxHashMap<Arc<str>, usize> = FxHashMap::default();
    for (i, name) in defined_vars.iter().enumerate() {
        var_to_idx.entry(name.clone()).or_insert(i);
    }

    // deps[i] = indices that must come before i
    let mut deps: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, sym) in symbolic.iter().enumerate() {
        let refs = get_symbolic_primed_refs(ctx, sym);

        for var_name in &refs {
            if let Some(&def_idx) = var_to_idx.get(var_name) {
                if def_idx != i {
                    deps[i].push(def_idx);
                }
            }
        }

        deps[i].sort_unstable();
        deps[i].dedup();

        if debug && !refs.is_empty() {
            eprintln!(
                "[TOPOSORT] Assignment {} references primed vars: {:?}, deps: {:?}",
                i,
                refs.iter()
                    .map(std::convert::AsRef::as_ref)
                    .collect::<Vec<_>>(),
                deps[i]
            );
        }
    }

    // Fast path: if all dependencies point to earlier indices, the input is
    // already in valid topological order. Skip adjacency + Kahn's. Part of #1564.
    let already_sorted = deps
        .iter()
        .enumerate()
        .all(|(i, dep_list)| dep_list.iter().all(|&dep_idx| dep_idx < i));
    if already_sorted {
        if debug {
            eprintln!("[TOPOSORT] Already in topological order, skipping Kahn's");
        }
        return symbolic.to_vec();
    }

    // adjacency[dep] = assignments that depend on dep
    let mut adjacency: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, dep_list) in deps.iter().enumerate() {
        for &dep in dep_list {
            adjacency[dep].push(i);
        }
    }
    for out in &mut adjacency {
        out.sort_unstable();
        out.dedup();
    }

    // Kahn's algorithm with deterministic tie-breaker (smallest input index first).
    let mut in_degree: Vec<usize> = deps.iter().map(std::vec::Vec::len).collect();
    let mut ready: BinaryHeap<Reverse<usize>> = BinaryHeap::new();
    for (i, &deg) in in_degree.iter().enumerate() {
        if deg == 0 {
            ready.push(Reverse(i));
        }
    }

    let mut order: Vec<usize> = Vec::with_capacity(n);
    while let Some(Reverse(i)) = ready.pop() {
        order.push(i);
        for &j in &adjacency[i] {
            let deg = &mut in_degree[j];
            debug_assert!(*deg > 0, "in_degree underflow for node {j} (from {i})");
            *deg -= 1;
            if *deg == 0 {
                ready.push(Reverse(j));
            }
        }
    }

    // If we couldn't sort all (cycle detected), fall back to original order
    if order.len() != symbolic.len() {
        if debug {
            eprintln!("[TOPOSORT] Cycle detected, falling back to original order");
        }
        return symbolic.to_vec();
    }

    if debug {
        eprintln!("[TOPOSORT] Sorted order:");
        for (out_i, &in_i) in order.iter().enumerate() {
            eprintln!("[TOPOSORT]   {}: {}'", out_i, defined_vars[in_i].as_ref());
        }
    }

    order.into_iter().map(|i| symbolic[i].clone()).collect()
}
