// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AIG synthesis preprocessing: iterative balance + rewrite.
//!
//! This module implements ABC-style AIG synthesis as a preprocessing pass
//! for hardware model checking. ABC's standard synthesis script `resyn2`
//! runs `balance; rewrite; refactor; balance; rewrite; rewrite -z; balance;
//! refactor -z; rewrite -z; balance`.
//!
//! We implement a simplified version: `balance; rewrite; strash` iterated
//! to fixpoint (or a maximum number of rounds). This captures the two most
//! impactful transformations:
//! - **Balance**: reduces AND-tree depth (critical for SAT solver performance)
//! - **Rewrite**: local gate simplification (idempotent merge, associativity)
//! - **Strash**: structural hashing to merge duplicates after rewrite
//!
//! super-prove (#4 HWMCC'25, 255/330) achieves 30-60% circuit shrinkage
//! via this pattern before running IC3/PDR. The shrinkage primarily benefits
//! circuits with deep sequential logic (shift registers, counters, ALUs).
//!
//! Reference: ABC synthesis scripts in `src/base/abc/abcDar.c`.

use crate::transys::Transys;

use super::balance::balance;
use super::dag_rewrite::dag_rewrite;
use super::rewrite::local_rewrite;
use super::strash::structural_hash;

/// Maximum number of synthesis iterations (balance + rewrite + strash).
/// Used by the default [`aig_synthesis`] wrapper (test-only).
#[cfg(test)]
const MAX_SYNTHESIS_ROUNDS: usize = 4;

/// Minimum gate count to attempt synthesis (tiny circuits not worth it).
const MIN_GATES_FOR_SYNTHESIS: usize = 10;

/// Statistics from the synthesis pass.
#[derive(Debug, Clone, Default)]
pub(crate) struct SynthesisStats {
    pub rounds: usize,
    pub balance_reductions: usize,
    pub rewrite_eliminations: usize,
    pub dag_rewrite_eliminations: usize,
    pub strash_merges: usize,
    pub orig_gates: usize,
    pub final_gates: usize,
    pub orig_depth: usize,
    pub final_depth: usize,
}

impl std::fmt::Display for SynthesisStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "synthesis: {} rounds, gates {}->{}({:+}), depth {}->{}, \
             balance={} rewrite={} dag_rewrite={} strash={}",
            self.rounds,
            self.orig_gates,
            self.final_gates,
            self.final_gates as isize - self.orig_gates as isize,
            self.orig_depth,
            self.final_depth,
            self.balance_reductions,
            self.rewrite_eliminations,
            self.dag_rewrite_eliminations,
            self.strash_merges,
        )
    }
}

/// Compute the maximum AND-gate depth of a transition system.
fn max_depth(ts: &Transys) -> usize {
    use rustc_hash::FxHashMap;
    use crate::sat_types::{Lit, Var};

    let mut depths: FxHashMap<Var, usize> = FxHashMap::default();

    fn depth_of(
        lit: Lit,
        and_defs: &FxHashMap<Var, (Lit, Lit)>,
        depths: &mut FxHashMap<Var, usize>,
    ) -> usize {
        if lit == Lit::FALSE || lit == Lit::TRUE {
            return 0;
        }
        if let Some(&d) = depths.get(&lit.var()) {
            return d;
        }
        if let Some(&(rhs0, rhs1)) = and_defs.get(&lit.var()) {
            let d0 = depth_of(rhs0, and_defs, depths);
            let d1 = depth_of(rhs1, and_defs, depths);
            let d = d0.max(d1) + 1;
            depths.insert(lit.var(), d);
            d
        } else {
            depths.insert(lit.var(), 0);
            0
        }
    }

    let mut max_d = 0;
    for &lit in &ts.bad_lits {
        let d = depth_of(lit, &ts.and_defs, &mut depths);
        max_d = max_d.max(d);
    }
    for &lit in &ts.constraint_lits {
        let d = depth_of(lit, &ts.and_defs, &mut depths);
        max_d = max_d.max(d);
    }
    for &next_lit in ts.next_state.values() {
        let d = depth_of(next_lit, &ts.and_defs, &mut depths);
        max_d = max_d.max(d);
    }

    max_d
}

/// Run iterative AIG synthesis (balance + rewrite + strash) to fixpoint.
///
/// Returns the optimized transition system and synthesis statistics.
/// Uses the default [`MAX_SYNTHESIS_ROUNDS`] limit. Used by tests.
#[cfg(test)]
pub(crate) fn aig_synthesis(ts: &Transys) -> (Transys, SynthesisStats) {
    aig_synthesis_configurable(ts, MAX_SYNTHESIS_ROUNDS)
}

/// Run iterative AIG synthesis with a configurable round limit.
///
/// Like [`aig_synthesis`] but allows overriding the maximum number of
/// synthesis rounds. Portfolio configs can use more rounds for aggressive
/// preprocessing.
pub(crate) fn aig_synthesis_configurable(
    ts: &Transys,
    max_rounds: usize,
) -> (Transys, SynthesisStats) {
    let orig_gates = ts.and_defs.len();
    let orig_depth = max_depth(ts);

    if orig_gates < MIN_GATES_FOR_SYNTHESIS {
        return (
            ts.clone(),
            SynthesisStats {
                orig_gates,
                final_gates: orig_gates,
                orig_depth,
                final_depth: orig_depth,
                ..Default::default()
            },
        );
    }

    let mut stats = SynthesisStats {
        orig_gates,
        orig_depth,
        ..Default::default()
    };

    let mut current = ts.clone();
    let mut prev_gates = orig_gates;

    for round in 0..max_rounds {
        // Phase 1: Balance (reduce depth).
        let (after_balance, bal_red) = balance(&current);
        stats.balance_reductions += bal_red;

        // Phase 2: Local rewrite (eliminate redundant gates).
        let (after_rewrite, rw_elim) = if after_balance.and_defs.len() >= 10 {
            local_rewrite(&after_balance)
        } else {
            (after_balance, 0)
        };
        stats.rewrite_eliminations += rw_elim;

        // Phase 3: DAG-aware rewrite (cut-based multi-gate optimization).
        // More powerful than local rewrite — enumerates 4-input cuts and
        // replaces suboptimal sub-graphs with optimal implementations.
        let (after_dag_rw, dag_rw_elim) = if after_rewrite.and_defs.len() >= 4 {
            dag_rewrite(&after_rewrite)
        } else {
            (after_rewrite, 0)
        };
        stats.dag_rewrite_eliminations += dag_rw_elim;

        // Phase 4: Structural hashing (merge duplicates).
        let after_strash = if bal_red > 0 || rw_elim > 0 || dag_rw_elim > 0 {
            let before_strash = after_dag_rw.and_defs.len();
            let result = structural_hash(&after_dag_rw);
            let merged = before_strash.saturating_sub(result.and_defs.len());
            stats.strash_merges += merged;
            result
        } else {
            after_dag_rw
        };

        let new_gates = after_strash.and_defs.len();
        stats.rounds = round + 1;

        // Check for convergence: no progress = stop.
        if new_gates >= prev_gates {
            current = after_strash;
            break;
        }

        prev_gates = new_gates;
        current = after_strash;
    }

    stats.final_gates = current.and_defs.len();
    stats.final_depth = max_depth(&current);

    (current, stats)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::preprocess::substitution::rebuild_trans_clauses;
    use crate::sat_types::{Clause, Lit, Var};
    use rustc_hash::FxHashMap;

    fn build_ts(
        max_var: u32,
        latch_vars: Vec<Var>,
        input_vars: Vec<Var>,
        next_state: FxHashMap<Var, Lit>,
        init_clauses: Vec<Clause>,
        bad_lits: Vec<Lit>,
        constraint_lits: Vec<Lit>,
        and_defs: FxHashMap<Var, (Lit, Lit)>,
    ) -> Transys {
        Transys {
            max_var,
            num_latches: latch_vars.len(),
            num_inputs: input_vars.len(),
            latch_vars,
            input_vars,
            next_state,
            init_clauses,
            trans_clauses: rebuild_trans_clauses(&and_defs),
            bad_lits,
            constraint_lits,
            and_defs,
            internal_signals: Vec::new(),
        }
    }

    #[test]
    fn test_synthesis_noop_small_circuit() {
        let a = Var(1);
        let b = Var(2);
        let g = Var(3);

        let mut and_defs = FxHashMap::default();
        and_defs.insert(g, (Lit::pos(a), Lit::pos(b)));

        let ts = build_ts(
            3,
            Vec::new(),
            vec![a, b],
            FxHashMap::default(),
            Vec::new(),
            vec![Lit::pos(g)],
            Vec::new(),
            and_defs,
        );

        let (result, stats) = aig_synthesis(&ts);
        assert_eq!(stats.rounds, 0);
        assert_eq!(result.and_defs.len(), 1);
    }

    #[test]
    fn test_synthesis_reduces_deep_chain() {
        // Build a deep linear AND chain (depth = 11) with 12 inputs.
        let inputs: Vec<Var> = (1..=12).map(Var).collect();
        let mut and_defs = FxHashMap::default();
        let mut prev_lit = Lit::pos(inputs[0]);
        let mut max_var = 12u32;

        for &inp in &inputs[1..] {
            max_var += 1;
            let gate = Var(max_var);
            and_defs.insert(gate, (prev_lit, Lit::pos(inp)));
            prev_lit = Lit::pos(gate);
        }

        let ts = build_ts(
            max_var,
            Vec::new(),
            inputs,
            FxHashMap::default(),
            Vec::new(),
            vec![prev_lit],
            Vec::new(),
            and_defs,
        );

        let orig_depth = max_depth(&ts);
        assert_eq!(orig_depth, 11);

        let (result, stats) = aig_synthesis(&ts);
        assert!(
            stats.rounds >= 1,
            "should run at least 1 round"
        );
        let new_depth = max_depth(&result);
        assert!(
            new_depth < orig_depth,
            "should reduce depth: {} -> {}",
            orig_depth,
            new_depth
        );
        // balanced depth of 12 inputs = ceil(log2(12)) = 4
        assert!(
            new_depth <= 4,
            "balanced depth should be <= 4, got {}",
            new_depth
        );
    }

    #[test]
    fn test_synthesis_with_duplicates() {
        // Build a circuit with duplicate gates that rewrite+strash can merge.
        let inputs: Vec<Var> = (1..=5).map(Var).collect();
        let mut and_defs = FxHashMap::default();
        let mut max_var = 5u32;

        // Create 10 duplicate gates (all AND(in1, in2)).
        for _ in 0..10 {
            max_var += 1;
            let gate = Var(max_var);
            and_defs.insert(gate, (Lit::pos(inputs[0]), Lit::pos(inputs[1])));
        }
        // One unique gate.
        max_var += 1;
        let unique_gate = Var(max_var);
        and_defs.insert(unique_gate, (Lit::pos(inputs[2]), Lit::pos(inputs[3])));

        let bad_lits: Vec<Lit> = (6..=max_var).map(|v| Lit::pos(Var(v))).collect();

        let ts = build_ts(
            max_var,
            Vec::new(),
            inputs,
            FxHashMap::default(),
            Vec::new(),
            bad_lits,
            Vec::new(),
            and_defs,
        );

        let (result, stats) = aig_synthesis(&ts);
        // Strash should merge the 10 duplicates into 1.
        assert!(
            result.and_defs.len() <= 2,
            "should have at most 2 unique gates, got {}",
            result.and_defs.len()
        );
        assert!(
            stats.strash_merges > 0 || stats.rewrite_eliminations > 0,
            "should merge or eliminate duplicates"
        );
    }

    #[test]
    fn test_synthesis_stats_display() {
        let stats = SynthesisStats {
            rounds: 2,
            balance_reductions: 3,
            rewrite_eliminations: 5,
            dag_rewrite_eliminations: 1,
            strash_merges: 2,
            orig_gates: 100,
            final_gates: 90,
            orig_depth: 15,
            final_depth: 8,
        };
        let s = format!("{stats}");
        assert!(s.contains("synthesis:"));
        assert!(s.contains("gates 100->90(-10)"));
        assert!(s.contains("depth 15->8"));
    }
}
