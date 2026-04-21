// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCC-based Equivalent Literal Substitution (Decompose)
//!
//! Builds the binary implication graph from binary clauses, runs Tarjan's
//! iterative SCC algorithm, and substitutes equivalent literals throughout
//! the clause database. This is CaDiCaL's `decompose.cpp`.
//!
//! If literal `a` and literal `b` are in the same SCC, they are logically
//! equivalent: all occurrences of `b` can be replaced with `a` (choosing
//! the representative with the smallest variable index).
//!
//! If literal `a` and `¬a` are in the same SCC, the formula is UNSAT.
//!
//! Reference: CaDiCaL `decompose.cpp:130-730`

mod rewrite;
mod scc;
#[cfg(test)]
mod tests;

pub(crate) use rewrite::{rewrite_clauses, ClauseMutation};

use crate::literal::Literal;
use crate::watched::WatchedLists;

/// Maximum number of decompose rounds per invocation.
const MAX_ROUNDS: usize = 2;

/// Sentinel value: SCC fully processed, do not revisit.
const TRAVERSED: u32 = u32::MAX;

/// Per-literal DFS state for Tarjan's algorithm.
#[derive(Clone, Copy, Default)]
struct DfsEntry {
    /// DFS index (0 = unvisited, TRAVERSED = done).
    idx: u32,
    /// Minimum reachable DFS index in this SCC.
    min: u32,
}

/// LRAT equivalence chains for a substituted literal.
///
/// For substituted literal `lit` with representative `repr`:
/// - `repr_to_lit`: ClauseRef.0 values along the implication path repr -> lit
///   (used as LRAT hints for proving `(lit | ~repr)`)
/// - `lit_to_repr`: ClauseRef.0 values along the implication path lit -> repr
///   (used as LRAT hints for proving `(repr | ~lit)`)
///
/// Both paths exist because lit and repr are in the same SCC.
/// Reference: CaDiCaL decompose.cpp:266-356 (parent pointer BFS + chain walk).
#[derive(Debug, Clone, Default)]
pub(crate) struct EquivChain {
    pub repr_to_lit: Vec<u32>,
    pub lit_to_repr: Vec<u32>,
}

/// Result of one decompose round.
#[derive(Debug, Default)]
pub(crate) struct DecomposeResult {
    /// Number of variables whose literals were substituted.
    pub substituted: u32,
    /// Number of new units discovered.
    pub new_units: u32,
    /// Whether a new binary clause was created by clause rewriting.
    pub new_binary: bool,
    /// Whether the formula was found to be unsatisfiable.
    pub unsat: bool,
    /// Literals to propagate as units at level 0.
    pub units: Vec<Literal>,
    /// Representative mapping: `reprs[lit.index()]` is the canonical literal
    /// for `lit`. If `reprs[lit.index()] == lit`, the literal is its own
    /// representative (no substitution needed).
    pub reprs: Vec<Literal>,
    /// LRAT equivalence chains for substituted literals.
    /// Indexed by `lit.index()`. Non-empty only for substituted literals.
    pub equiv_chains: Vec<EquivChain>,
}

/// Decompose engine.
pub(crate) struct Decompose {
    /// Per-literal DFS entries, indexed by `lit.index()`.
    dfs: Vec<DfsEntry>,
    /// DFS traversal work stack: `(literal, next_child_position)`.
    work: Vec<(u32, usize)>,
    /// SCC collection stack (literal indices).
    scc_stack: Vec<u32>,
    /// Representative mapping, indexed by `lit.index()`.
    reprs: Vec<Literal>,
    /// Statistics.
    pub stats: DecomposeStats,
}

/// Statistics for SCC decomposition.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct DecomposeStats {
    /// Number of decompose rounds run.
    pub rounds: u64,
    /// Total number of variables substituted by their SCC representative.
    pub substituted: u64,
    /// Number of unit literals discovered during decomposition.
    pub units: u64,
}

impl Decompose {
    pub(crate) fn new(num_vars: usize) -> Self {
        let num_lits = num_vars * 2;
        Self {
            dfs: vec![DfsEntry::default(); num_lits],
            work: Vec::new(),
            scc_stack: Vec::new(),
            reprs: (0..num_lits as u32).map(Literal).collect(),
            stats: DecomposeStats::default(),
        }
    }

    /// Restore previously saved statistics (e.g., after compaction recreates
    /// the engine via `Decompose::new()`). Without this, stats are zeroed.
    pub(crate) fn restore_stats(&mut self, stats: DecomposeStats) {
        self.stats = stats;
    }

    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let num_lits = num_vars * 2;
        if self.dfs.len() < num_lits {
            self.dfs.resize(num_lits, DfsEntry::default());
            let old_len = self.reprs.len();
            self.reprs.resize(num_lits, Literal(0));
            for i in old_len..num_lits {
                self.reprs[i] = Literal(i as u32);
            }
        }
    }

    /// Run up to `MAX_ROUNDS` of SCC decomposition.
    ///
    /// Returns a `DecomposeResult` describing the substitutions found.
    /// The caller is responsible for rewriting clauses and propagating units.
    pub(crate) fn run(
        &mut self,
        watches: &WatchedLists,
        num_vars: usize,
        vals: &[i8],
        frozen: &[u32],
        var_states: &[crate::solver::lifecycle::VarState],
    ) -> DecomposeResult {
        self.run_inner(watches, num_vars, vals, frozen, var_states, true)
    }

    fn run_inner(
        &mut self,
        watches: &WatchedLists,
        num_vars: usize,
        vals: &[i8],
        frozen: &[u32],
        var_states: &[crate::solver::lifecycle::VarState],
        need_chains: bool,
    ) -> DecomposeResult {
        let num_lits = num_vars * 2;
        // CaDiCaL decompose.cpp:139: must have sufficient buffer capacity
        debug_assert!(
            self.dfs.len() >= num_lits,
            "BUG: decompose dfs buffer too small ({} < {num_lits})",
            self.dfs.len(),
        );
        debug_assert!(
            self.reprs.len() >= num_lits,
            "BUG: decompose reprs buffer too small ({} < {num_lits})",
            self.reprs.len(),
        );
        // Reset DFS state.
        for e in self.dfs[..num_lits].iter_mut() {
            *e = DfsEntry::default();
        }
        // Reset representatives to identity.
        for i in 0..num_lits {
            self.reprs[i] = Literal(i as u32);
        }

        let mut combined = DecomposeResult {
            reprs: self.reprs[..num_lits].to_vec(),
            equiv_chains: if need_chains {
                vec![EquivChain::default(); num_lits]
            } else {
                Vec::new()
            },
            ..DecomposeResult::default()
        };

        for _round in 0..MAX_ROUNDS {
            let result = self.run_round(watches, num_vars, vals, frozen, var_states, need_chains);
            self.stats.rounds += 1;
            self.stats.substituted += u64::from(result.substituted);
            self.stats.units += u64::from(result.new_units);

            if result.unsat {
                combined.unsat = true;
                combined.units.extend(result.units);
                combined.reprs = self.reprs[..num_lits].to_vec();
                return combined;
            }

            combined.substituted += result.substituted;
            combined.new_units += result.new_units;
            combined.new_binary |= result.new_binary;
            combined.units.extend(result.units);

            // Merge equiv_chains from this round.
            for (i, chain) in result.equiv_chains.into_iter().enumerate() {
                if (!chain.repr_to_lit.is_empty() || !chain.lit_to_repr.is_empty())
                    && i < combined.equiv_chains.len()
                {
                    combined.equiv_chains[i] = chain;
                }
            }

            if result.substituted == 0 || (!result.new_binary && result.new_units == 0) {
                break;
            }

            // Reset DFS for next round (representatives carry over).
            for e in self.dfs[..num_lits].iter_mut() {
                *e = DfsEntry::default();
            }
        }

        combined.reprs = self.reprs[..num_lits].to_vec();
        combined
    }
}
