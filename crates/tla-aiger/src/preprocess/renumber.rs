// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable renumbering for preprocessed transition systems.
//!
//! After preprocessing removes variables, the remaining variable IDs may have
//! large gaps. This pass compacts all referenced variables into a dense range
//! `[1..=N]`, preserving `Var(0)` as the constant variable.
//!
//! Unlike simple gap-filling, this module performs *topological* renumbering:
//! variables are ordered by dependency depth in the AND gate graph. Variables
//! that depend on each other get adjacent indices, improving CPU cache locality
//! during SAT solver watcher list traversal.
//!
//! The ordering prioritizes (matching rIC3's `rearrange()`):
//! 1. Latch variables (most important for IC3 cubes)
//! 2. Input variables
//! 3. Bad/constraint variables
//! 4. AND gate outputs in topological (dependency-depth) order
//!
//! Reference: rIC3 `src/transys/simp.rs:75-112` — `rearrange()`.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::sat_types::{Clause, Lit, Var};
use crate::transys::Transys;

/// Compute dependency depth for each AND gate output variable.
///
/// Depth is defined as the length of the longest path from any primary input
/// (input or latch variable) to the gate output through the AND gate graph.
/// Primary inputs have depth 0.
///
/// Variables not in `and_defs` (inputs, latches) get depth 0.
fn compute_depths(ts: &Transys) -> FxHashMap<Var, u32> {
    let mut depths: FxHashMap<Var, u32> = FxHashMap::default();

    // Primary inputs and latches have depth 0.
    for &var in &ts.latch_vars {
        depths.insert(var, 0);
    }
    for &var in &ts.input_vars {
        depths.insert(var, 0);
    }

    // Compute depths for AND gate outputs via memoized DFS.
    fn depth_of(
        var: Var,
        and_defs: &FxHashMap<Var, (Lit, Lit)>,
        depths: &mut FxHashMap<Var, u32>,
        visiting: &mut FxHashSet<Var>,
    ) -> u32 {
        if let Some(&d) = depths.get(&var) {
            return d;
        }
        // Cycle detection: if we're already visiting this var, return 0.
        if !visiting.insert(var) {
            return 0;
        }
        let d = if let Some(&(rhs0, rhs1)) = and_defs.get(&var) {
            let d0 = depth_of(rhs0.var(), and_defs, depths, visiting);
            let d1 = depth_of(rhs1.var(), and_defs, depths, visiting);
            d0.max(d1).saturating_add(1)
        } else {
            0
        };
        visiting.remove(&var);
        depths.insert(var, d);
        d
    }

    let mut visiting = FxHashSet::default();
    let gate_vars: Vec<Var> = ts.and_defs.keys().copied().collect();
    for var in gate_vars {
        depth_of(var, &ts.and_defs, &mut depths, &mut visiting);
    }

    depths
}

fn collect_used_vars(ts: &Transys) -> FxHashSet<Var> {
    let mut used = FxHashSet::default();
    used.insert(Var::CONST);

    for &var in &ts.latch_vars {
        used.insert(var);
    }
    for &var in &ts.input_vars {
        used.insert(var);
    }
    for (&var, &(rhs0, rhs1)) in &ts.and_defs {
        used.insert(var);
        used.insert(rhs0.var());
        used.insert(rhs1.var());
    }
    for &lit in &ts.bad_lits {
        used.insert(lit.var());
    }
    for &lit in &ts.constraint_lits {
        used.insert(lit.var());
    }
    for clause in &ts.init_clauses {
        for &lit in &clause.lits {
            used.insert(lit.var());
        }
    }
    for clause in &ts.trans_clauses {
        for &lit in &clause.lits {
            used.insert(lit.var());
        }
    }
    for (&var, &lit) in &ts.next_state {
        used.insert(var);
        used.insert(lit.var());
    }
    for &var in &ts.internal_signals {
        used.insert(var);
    }

    used
}

#[inline]
fn remap_var(var: Var, var_map: &FxHashMap<Var, Var>) -> Var {
    if var == Var::CONST {
        return Var::CONST;
    }

    if let Some(mapped) = var_map.get(&var).copied() {
        mapped
    } else {
        debug_assert!(false, "missing renumbering for variable {:?}", var);
        var
    }
}

#[inline]
fn remap_lit(lit: Lit, var_map: &FxHashMap<Var, Var>) -> Lit {
    let remapped_var = remap_var(lit.var(), var_map);
    if lit.is_negated() {
        Lit::neg(remapped_var)
    } else {
        Lit::pos(remapped_var)
    }
}

fn remap_clause(clause: &Clause, var_map: &FxHashMap<Var, Var>) -> Clause {
    Clause::new(
        clause
            .lits
            .iter()
            .map(|&lit| remap_lit(lit, var_map))
            .collect(),
    )
}

/// Renumber all variables in the transition system into a dense range,
/// ordered by topological dependency depth for better cache locality.
///
/// The ordering assigns the lowest variable IDs to the most "important"
/// variables for IC3 (latches first, then inputs, then bad/constraint refs),
/// followed by AND gate outputs sorted by dependency depth. This matches
/// rIC3's `rearrange()` approach where dependent variables get adjacent
/// indices, improving SAT solver watcher list cache behavior.
///
/// Returns the renumbered transition system and the number of eliminated gaps,
/// computed as `old_max_var - new_max_var`.
pub(crate) fn renumber_variables(ts: &Transys) -> (Transys, usize) {
    let used_vars = collect_used_vars(ts);
    let new_max_var = used_vars.len().saturating_sub(1) as u32;
    let compacted = ts.max_var.saturating_sub(new_max_var) as usize;

    if compacted == 0 {
        return (ts.clone(), 0);
    }

    let depths = compute_depths(ts);

    // Build priority-ordered variable list (matching rIC3 rearrange):
    // 1. Var::CONST (always index 0)
    // 2. Latch variables (most important for IC3 cubes)
    // 3. Input variables
    // 4. Variables referenced by bad/constraint lits (not already placed)
    // 5. AND gate outputs sorted by dependency depth (shallow first)
    // 6. Any remaining used variables
    let mut ordered_vars: Vec<Var> = Vec::with_capacity(used_vars.len());
    let mut placed = FxHashSet::default();

    // Var(0) always maps to itself.
    ordered_vars.push(Var::CONST);
    placed.insert(Var::CONST);

    // Latches first.
    for &var in &ts.latch_vars {
        if used_vars.contains(&var) && placed.insert(var) {
            ordered_vars.push(var);
        }
    }

    // Inputs next.
    for &var in &ts.input_vars {
        if used_vars.contains(&var) && placed.insert(var) {
            ordered_vars.push(var);
        }
    }

    // Bad/constraint referenced variables.
    for &lit in &ts.bad_lits {
        let var = lit.var();
        if used_vars.contains(&var) && placed.insert(var) {
            ordered_vars.push(var);
        }
    }
    for &lit in &ts.constraint_lits {
        let var = lit.var();
        if used_vars.contains(&var) && placed.insert(var) {
            ordered_vars.push(var);
        }
    }

    // AND gate outputs sorted by dependency depth (shallow gates first).
    // This groups dependent variables together for cache locality.
    let mut gate_vars: Vec<(Var, u32)> = ts
        .and_defs
        .keys()
        .filter(|v| used_vars.contains(v) && !placed.contains(v))
        .map(|&v| (v, depths.get(&v).copied().unwrap_or(0)))
        .collect();
    gate_vars.sort_unstable_by_key(|&(v, depth)| (depth, v.0));
    for (var, _) in gate_vars {
        if placed.insert(var) {
            ordered_vars.push(var);
        }
    }

    // Any remaining used variables not yet placed.
    let mut remaining: Vec<Var> = used_vars
        .iter()
        .copied()
        .filter(|v| !placed.contains(v))
        .collect();
    remaining.sort_unstable_by_key(|v| v.0);
    for var in remaining {
        placed.insert(var);
        ordered_vars.push(var);
    }

    debug_assert_eq!(ordered_vars.len(), used_vars.len());

    // Build the old-to-new variable mapping.
    let mut var_map = FxHashMap::default();
    for (new_idx, &old_var) in ordered_vars.iter().enumerate() {
        var_map.insert(old_var, Var(new_idx as u32));
    }

    let latch_vars: Vec<Var> = ts
        .latch_vars
        .iter()
        .map(|&var| remap_var(var, &var_map))
        .collect();
    let input_vars: Vec<Var> = ts
        .input_vars
        .iter()
        .map(|&var| remap_var(var, &var_map))
        .collect();
    let next_state: FxHashMap<Var, Lit> = ts
        .next_state
        .iter()
        .map(|(&var, &lit)| (remap_var(var, &var_map), remap_lit(lit, &var_map)))
        .collect();
    let init_clauses: Vec<Clause> = ts
        .init_clauses
        .iter()
        .map(|clause| remap_clause(clause, &var_map))
        .collect();
    let trans_clauses: Vec<Clause> = ts
        .trans_clauses
        .iter()
        .map(|clause| remap_clause(clause, &var_map))
        .collect();
    let bad_lits: Vec<Lit> = ts
        .bad_lits
        .iter()
        .map(|&lit| remap_lit(lit, &var_map))
        .collect();
    let constraint_lits: Vec<Lit> = ts
        .constraint_lits
        .iter()
        .map(|&lit| remap_lit(lit, &var_map))
        .collect();
    let and_defs: FxHashMap<Var, (Lit, Lit)> = ts
        .and_defs
        .iter()
        .map(|(&var, &(rhs0, rhs1))| {
            (
                remap_var(var, &var_map),
                (remap_lit(rhs0, &var_map), remap_lit(rhs1, &var_map)),
            )
        })
        .collect();
    let internal_signals: Vec<Var> = ts
        .internal_signals
        .iter()
        .map(|&var| remap_var(var, &var_map))
        .collect();

    (
        Transys {
            max_var: new_max_var,
            num_latches: latch_vars.len(),
            num_inputs: input_vars.len(),
            latch_vars,
            input_vars,
            next_state,
            init_clauses,
            trans_clauses,
            bad_lits,
            constraint_lits,
            and_defs,
            internal_signals,
        },
        compacted,
    )
}
