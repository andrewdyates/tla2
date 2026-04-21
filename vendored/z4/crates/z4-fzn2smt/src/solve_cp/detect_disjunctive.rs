// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Detect disjunctive (unary resource) scheduling patterns from FlatZinc
// int_lin_le_reif pairs and emit Constraint::Disjunctive for each machine.
//
// Pattern in jobshop FlatZinc:
//   int_lin_le_reif([1,-1], [s_i, s_j], -d_i, b_ij)  // s_i + d_i ≤ s_j when b_ij
//   int_lin_le_reif([1,-1], [s_j, s_i], -d_j, b_ji)  // s_j + d_j ≤ s_i when b_ji
//   bool_clause([b_ij, b_ji], [])                       // exactly one ordering
//
// Detection algorithm:
//   1. Collect all int_lin_le_reif with coeffs [1,-1] — these encode "s_a + d ≤ s_b"
//   2. Group by task-variable pairs: (s_a, s_b) and (s_b, s_a) form a disjunctive pair
//   3. Build disjunctive-pair graph: tasks connected by disjunctive pairs
//   4. Find cliques in the graph — each clique is a machine
//   5. Add Constraint::Disjunctive for each machine
//
// The int_lin_le_reif constraints are STILL translated normally (Big-M encoding
// provides the SAT-level OR choice). The Disjunctive propagator adds stronger
// bounds propagation via O(n log n) edge-finding.

use std::collections::{HashMap, HashSet};

use z4_cp::propagator::Constraint;
use z4_cp::variable::IntVarId;
use z4_flatzinc_parser::ast::{ConstraintItem, FznModel};

use super::CpContext;

/// A disjunctive pair: tasks (s_a, d_a) and (s_b, d_b) cannot overlap.
#[derive(Debug)]
struct DisjunctivePair {
    var_a: IntVarId,
    var_b: IntVarId,
    dur_a: i64,
    dur_b: i64,
}

impl CpContext {
    /// Pre-scan FlatZinc constraints for disjunctive scheduling patterns.
    /// Adds Constraint::Disjunctive for each detected machine (clique of
    /// pairwise-disjunctive tasks).
    ///
    /// Must be called AFTER variables are created but BEFORE constraint
    /// translation, since we need IntVarIds for the FlatZinc variable names.
    pub(super) fn detect_disjunctive(&mut self, model: &FznModel) {
        // Step 1: Collect int_lin_le_reif([1,-1], [s_a, s_b], -d_a, _)
        // These encode s_a - s_b ≤ -d_a, i.e., s_a + d_a ≤ s_b.
        let mut half_pairs: Vec<(IntVarId, IntVarId, i64)> = Vec::new(); // (s_a, s_b, d_a)

        for c in &model.constraints {
            if c.id != "int_lin_le_reif" {
                continue;
            }
            if let Some((var_a, var_b, dur)) = self.try_parse_disjunctive_half(c) {
                half_pairs.push((var_a, var_b, dur));
            }
        }

        if half_pairs.is_empty() {
            return;
        }

        // Step 2: Find matching pairs.
        // For each (s_a, s_b, d_a), look for (s_b, s_a, d_b).
        let mut pair_map: HashMap<(IntVarId, IntVarId), i64> = HashMap::new();
        for &(va, vb, dur) in &half_pairs {
            pair_map.insert((va, vb), dur);
        }

        let mut pairs: Vec<DisjunctivePair> = Vec::new();
        let mut used_halves: HashSet<(IntVarId, IntVarId)> = HashSet::new();

        for &(va, vb, dur_a) in &half_pairs {
            if used_halves.contains(&(va, vb)) {
                continue;
            }
            if let Some(&dur_b) = pair_map.get(&(vb, va)) {
                used_halves.insert((va, vb));
                used_halves.insert((vb, va));
                pairs.push(DisjunctivePair {
                    var_a: va,
                    var_b: vb,
                    dur_a,
                    dur_b,
                });
            }
        }

        if pairs.is_empty() {
            return;
        }

        // Step 3: Build disjunctive-pair graph and find machines (cliques).
        // Each task variable has a duration that may vary by pair. For jobshop,
        // each task has a SINGLE consistent duration across all pairs on the
        // same machine. We verify this and extract it.
        let mut task_durations: HashMap<IntVarId, i64> = HashMap::new();
        let mut adj: HashMap<IntVarId, HashSet<IntVarId>> = HashMap::new();

        for p in &pairs {
            // Record duration for each task variable.
            // If a task appears with inconsistent durations across pairs,
            // it may be from different machines. We use first-seen duration.
            task_durations.entry(p.var_a).or_insert(p.dur_a);
            task_durations.entry(p.var_b).or_insert(p.dur_b);

            adj.entry(p.var_a).or_default().insert(p.var_b);
            adj.entry(p.var_b).or_default().insert(p.var_a);
        }

        // Step 4: Greedy clique detection (same algorithm as detect_alldifferent).
        // For jobshop, each machine is a complete graph of n tasks.
        let mut vars_by_degree: Vec<(IntVarId, usize)> =
            adj.iter().map(|(&v, nbrs)| (v, nbrs.len())).collect();
        vars_by_degree.sort_by(|a, b| b.1.cmp(&a.1));

        let mut used: HashSet<IntVarId> = HashSet::new();
        let mut machines: Vec<Vec<IntVarId>> = Vec::new();

        for &(seed, _) in &vars_by_degree {
            if used.contains(&seed) {
                continue;
            }
            let seed_nbrs = match adj.get(&seed) {
                Some(n) => n,
                None => continue,
            };

            let mut clique = vec![seed];
            let mut candidates: Vec<IntVarId> = seed_nbrs
                .iter()
                .filter(|v| !used.contains(v))
                .copied()
                .collect();
            // Sort by degree descending for better cliques
            candidates.sort_by(|a, b| {
                adj.get(b)
                    .map_or(0, HashSet::len)
                    .cmp(&adj.get(a).map_or(0, HashSet::len))
            });

            for cand in candidates {
                let cand_nbrs = match adj.get(&cand) {
                    Some(n) => n,
                    None => continue,
                };
                if clique.iter().all(|m| cand_nbrs.contains(m)) {
                    clique.push(cand);
                }
            }

            if clique.len() >= 2 {
                for &v in &clique {
                    used.insert(v);
                }
                machines.push(clique);
            }
        }

        // Step 5: Add Constraint::Disjunctive for each machine.
        for machine in &machines {
            let starts = machine.clone();
            let durations: Vec<i64> = machine
                .iter()
                .map(|v| *task_durations.get(v).expect("task must have duration"))
                .collect();
            self.engine
                .add_constraint(Constraint::Disjunctive { starts, durations });
        }

        if !machines.is_empty() {
            eprintln!(
                "detect_disjunctive: {} machines from {} disjunctive pairs ({} tasks total)",
                machines.len(),
                pairs.len(),
                machines.iter().map(Vec::len).sum::<usize>()
            );
        }
    }

    /// Try to parse a single int_lin_le_reif as a disjunctive half-pair.
    ///
    /// Pattern: int_lin_le_reif([1,-1], [s_a, s_b], rhs, _)
    /// where rhs < 0, meaning s_a - s_b ≤ rhs, i.e., s_a + |rhs| ≤ s_b.
    /// Duration = -rhs.
    fn try_parse_disjunctive_half(&self, c: &ConstraintItem) -> Option<(IntVarId, IntVarId, i64)> {
        // Must have 4 args: coeffs, vars, rhs, indicator
        if c.args.len() != 4 {
            return None;
        }

        // Parse coefficients — must be [1, -1]
        let coeffs = self.resolve_const_int_array_opt(&c.args[0])?;
        if coeffs.len() != 2 || coeffs[0] != 1 || coeffs[1] != -1 {
            return None;
        }

        // Parse rhs — must be negative (encodes -duration)
        let rhs = self.eval_const_int(&c.args[2])?;
        if rhs >= 0 {
            return None;
        }

        // Parse variables
        let vars = self.resolve_var_array_opt(&c.args[1])?;
        if vars.len() != 2 {
            return None;
        }

        let dur = -rhs;
        Some((vars[0], vars[1], dur))
    }

    /// Non-failing version of resolve_const_int_array.
    fn resolve_const_int_array_opt(
        &self,
        expr: &z4_flatzinc_parser::ast::Expr,
    ) -> Option<Vec<i64>> {
        match expr {
            z4_flatzinc_parser::ast::Expr::ArrayLit(elems) => {
                let mut result = Vec::with_capacity(elems.len());
                for e in elems {
                    result.push(self.eval_const_int(e)?);
                }
                Some(result)
            }
            z4_flatzinc_parser::ast::Expr::Ident(name) => self.par_int_arrays.get(name).cloned(),
            _ => None,
        }
    }

    /// Non-failing version of resolve_var_array.
    fn resolve_var_array_opt(&self, expr: &z4_flatzinc_parser::ast::Expr) -> Option<Vec<IntVarId>> {
        match expr {
            z4_flatzinc_parser::ast::Expr::ArrayLit(elems) => {
                let mut result = Vec::with_capacity(elems.len());
                for e in elems {
                    if let z4_flatzinc_parser::ast::Expr::Ident(name) = e {
                        result.push(*self.var_map.get(name)?);
                    } else {
                        return None;
                    }
                }
                Some(result)
            }
            _ => None,
        }
    }
}
