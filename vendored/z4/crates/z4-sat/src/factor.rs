// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause factorization: introduce extension variables to compress clause structure.
//!
//! Factoring identifies groups of clauses that share all literals except one
//! (the "factor"). A fresh extension variable compresses N clauses into fewer:
//!
//! Given clauses that form a `factors × quotients` matrix (each clause is
//! Q_i ∨ f_j for quotient Q_i and factor f_j), we replace them with:
//!
//! - Binary "divider" clauses: `(fresh ∨ f_j)` for each factor
//! - "Quotient" clauses: `(¬fresh ∨ Q_i)` for each quotient
//!
//! Net effect: `factors * quotients` clauses become `factors + quotients` clauses.
//! Reduction: `factors * quotients - factors - quotients`.
//!
//! Reference: CaDiCaL `factor.cpp` (Biere et al.)

mod chain;
#[cfg(test)]
mod tests;

use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};
use crate::occ_list::OccList;

use chain::{find_best_quotient, find_complementary_factors, flush_unmatched_clauses};

/// Maximum clause size eligible for factorization.
/// CaDiCaL: `factorsize = 5` (options.hpp:124). Larger clauses rarely
/// factor productively and waste effort scanning occurrence lists.
pub(crate) const FACTOR_SIZE_LIMIT: usize = 5;

/// Minimum factor count for a factoring candidate to be considered.
const MIN_FACTOR_MATCHES: usize = 2;

/// One factorization application with full proof structure.
///
/// Each application introduces one extension variable and rewrites a
/// `factors × quotients` clause matrix into `factors + quotients` clauses.
/// The `blocked_clause` is a proof-only artifact needed for DRAT checking
/// (see CaDiCaL `factor.cpp:606-623`).
#[derive(Debug, Clone)]
pub(crate) struct FactorApplication {
    /// The fresh extension variable introduced.
    pub fresh_var: Variable,
    /// Factor literals that were compressed.
    pub factors: Vec<Literal>,
    /// Binary divider clauses: `(fresh ∨ f_j)` for each factor.
    pub divider_clauses: Vec<Vec<Literal>>,
    /// Quotient clauses: `(¬fresh ∨ Q_i)` for each quotient.
    pub quotient_clauses: Vec<Vec<Literal>>,
    /// Proof-only blocked clause: `(¬fresh ∨ ¬f_1 ∨ ¬f_2 ∨ ...)`.
    /// RAT on `¬fresh`. Never added to the clause database.
    pub blocked_clause: Vec<Literal>,
    /// All original clause indices to delete.
    pub to_delete: Vec<usize>,
}

/// Self-subsuming factor application: no extension variable needed.
///
/// When two factors in the quotient chain are complementary (f and ~f),
/// resolving their respective clauses directly produces shorter resolvents
/// (quotient literals only, with the factor literal removed entirely).
///
/// Reference: CaDiCaL `factor.cpp:506-591`.
#[derive(Debug, Clone)]
pub(crate) struct SelfSubsumingApplication {
    /// Resolvent clauses: quotient literals only (factor removed).
    pub resolvents: Vec<Vec<Literal>>,
    /// Original clause indices to delete.
    pub to_delete: Vec<usize>,
    /// Pairs (ci_a, ci_b) of clause indices that produced each resolvent.
    pub proof_pairs: Vec<(usize, usize)>,
}

/// Result of one factorization pass.
#[derive(Debug, Default)]
pub(crate) struct FactorResult {
    /// New clauses to add: each is a list of literals.
    pub new_clauses: Vec<Vec<Literal>>,
    /// Clause indices to delete from clause_db.
    pub to_delete: Vec<usize>,
    /// Number of extension variables introduced.
    pub extension_vars_needed: usize,
    /// Number of factoring applications.
    pub factored_count: usize,
    /// Per-application structured data for proof emission.
    pub applications: Vec<FactorApplication>,
    /// Self-subsuming applications (complementary factor pairs).
    pub self_subsuming: Vec<SelfSubsumingApplication>,
    /// Factor candidates consumed from the schedule in this run.
    pub consumed_candidates: Vec<Literal>,
    /// Whether the candidate schedule was fully processed.
    pub completed: bool,
    /// Ticks consumed during this run (for effort budget tracking).
    pub ticks_consumed: u64,
}

/// Control parameters for a factorization run.
pub(crate) struct FactorConfig {
    /// The next variable index for extension variables.
    pub next_var_id: usize,
    /// Effort limit in ticks for this run.
    pub effort_limit: u64,
    /// Current BVE elimination bound (CaDiCaL factor.cpp:118,888).
    /// Factoring only fires when clause reduction exceeds this bound.
    pub elim_bound: i64,
}

/// Factorization engine.
///
/// Ported from CaDiCaL `factor.cpp`. The algorithm:
/// 1. Schedule candidate literals by occurrence count.
/// 2. For each candidate `first`, build a quotient chain:
///    - Level 0: all clauses containing `first` (these share factor `first`)
///    - Level k: intersect with clauses containing factor `next_k`
/// 3. Find the best depth where `factors * quotients - factors - quotients > 0`.
/// 4. Apply factoring: create extension variable, add divider + quotient clauses.
#[derive(Debug, Clone)]
pub(crate) struct Factor {
    num_vars: usize,
    /// Per-literal marks for factor/quotient identification.
    marks: Vec<u8>,
    /// Reusable counts buffer for `find_next_factor` (avoids per-call allocation).
    counts: Vec<u32>,
}

const MARK_FACTOR: u8 = 1;
const MARK_QUOTIENT: u8 = 2;
/// Candidate already counted for the current source clause scan in
/// `find_next_factor` (CaDiCaL's NOUNTED mark).
const MARK_NOUNTED: u8 = 4;

impl Factor {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            marks: vec![0; num_vars * 2],
            counts: vec![0; num_vars * 2],
        }
    }

    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if num_vars > self.num_vars {
            self.num_vars = num_vars;
            self.marks.resize(num_vars * 2, 0);
            self.counts.resize(num_vars * 2, 0);
        }
    }

    fn mark(&mut self, lit: Literal, flag: u8) {
        let idx = lit.index();
        if idx < self.marks.len() {
            self.marks[idx] |= flag;
        }
    }

    fn unmark(&mut self, lit: Literal, flag: u8) {
        let idx = lit.index();
        if idx < self.marks.len() {
            self.marks[idx] &= !flag;
        }
    }

    fn is_marked(&self, lit: Literal, flag: u8) -> bool {
        let idx = lit.index();
        idx < self.marks.len() && (self.marks[idx] & flag) != 0
    }

    /// Check if a literal is satisfied under the current vals[] assignment.
    /// vals[lit.index()] > 0 means the literal is true.
    #[inline]
    fn lit_satisfied(lit: Literal, vals: &[i8]) -> bool {
        let idx = lit.index();
        idx < vals.len() && vals[idx] > 0
    }

    #[inline]
    fn clause_satisfied(lits: &[Literal], vals: &[i8]) -> bool {
        lits.iter().any(|&lit| Self::lit_satisfied(lit, vals))
    }

    /// Run factorization on the clause database.
    ///
    /// `occ`: pre-built occurrence list for irredundant clauses.
    /// `vals`: literal-indexed i8 array (vals[var*2]==0 means unassigned).
    /// `var_states`: per-variable state (active, eliminated, etc.).
    /// `config`: control parameters (next_var_id, effort_limit, elim_bound).
    pub(crate) fn run(
        &mut self,
        clause_db: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
        config: &FactorConfig,
    ) -> FactorResult {
        // CaDiCaL factor.cpp:960: vals must cover all variables (2 entries per var)
        debug_assert!(
            vals.len() >= self.num_vars * 2,
            "BUG: factor vals.len()={} < num_vars*2={}",
            vals.len(),
            self.num_vars * 2,
        );
        // CaDiCaL factor.cpp: var_states mask must cover all variables
        debug_assert!(
            var_states.len() >= self.num_vars,
            "BUG: factor var_states.len()={} < num_vars={}",
            var_states.len(),
            self.num_vars,
        );
        let mut result = FactorResult {
            completed: true,
            ..FactorResult::default()
        };
        let mut ticks: u64 = 0;
        let mut next_var = config.next_var_id;

        // Build candidate schedule: literals sorted by occurrence count (descending).
        let mut candidates: Vec<(Literal, usize)> = Vec::new();
        for var_idx in 0..self.num_vars {
            if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
                continue;
            }
            if var_idx < var_states.len() && var_states[var_idx].is_removed() {
                continue;
            }
            for positive in [true, false] {
                let lit = if positive {
                    Literal::positive(Variable(var_idx as u32))
                } else {
                    Literal::negative(Variable(var_idx as u32))
                };
                let count = occ.count(lit);
                if count >= MIN_FACTOR_MATCHES {
                    candidates.push((lit, count));
                }
            }
        }
        // Sort by occurrence count descending (CaDiCaL uses a priority queue).
        candidates.sort_by(|a, b| b.1.cmp(&a.1));

        // Already-deleted clauses tracked to avoid double-deletion.
        let mut deleted: Vec<bool> = vec![false; clause_db.len()];

        for &(first_lit, _) in &candidates {
            if ticks > config.effort_limit {
                result.completed = false;
                break;
            }
            result.consumed_candidates.push(first_lit);
            if self.is_marked(first_lit, MARK_FACTOR) {
                continue; // Already used as a factor in a previous application.
            }

            // Collect eligible clauses containing first_lit.
            let first_occs = occ.get(first_lit);
            let mut eligible: Vec<usize> = Vec::new();
            for &ci in first_occs {
                ticks += 1;
                if deleted[ci] {
                    continue;
                }
                if clause_db.is_empty_clause(ci) || clause_db.is_learned(ci) {
                    continue;
                }
                if Self::clause_satisfied(clause_db.literals(ci), vals) {
                    continue;
                }
                let len = clause_db.len_of(ci);
                if !(2..=FACTOR_SIZE_LIMIT).contains(&len) {
                    continue;
                }
                eligible.push(ci);
            }
            if eligible.len() < MIN_FACTOR_MATCHES {
                continue;
            }

            // Build quotient chain (CaDiCaL: first_factor + next_factor loop).
            let mut chain = self.build_quotient_chain(
                clause_db,
                occ,
                vals,
                first_lit,
                &eligible,
                &deleted,
                &mut ticks,
                config.effort_limit,
            );

            if chain.is_empty() {
                continue;
            }

            // Find best quotient level for factoring.
            if let Some((best_idx, reduction)) = find_best_quotient(&chain) {
                // CaDiCaL factor.cpp:888: only factor when clause reduction
                // exceeds the current BVE elimination bound. This creates a
                // dual guard: factoring requires `F*Q - F - Q > elimbound`,
                // while BVE rejects elimination when `F*Q > F + Q + elimbound`.
                // These are the same condition, so BVE can never profitably
                // undo a factoring that passed this guard.
                if reduction <= config.elim_bound {
                    continue;
                }
                // Flush unmatched clauses so all levels have identical entry counts.
                // CaDiCaL: apply_factoring calls flush for each level (factor.cpp:711-712).
                for level in (1..=best_idx).rev() {
                    flush_unmatched_clauses(&mut chain, level);
                }

                // Apply factoring: create extension variable and rewrite clauses.
                let factors: Vec<Literal> = chain[..=best_idx].iter().map(|q| q.factor).collect();
                let num_quotients = chain[best_idx].clause_indices.len();

                // Self-subsuming check: if two factors are complementary (f, ~f),
                // resolve directly without creating an extension variable.
                // Reference: CaDiCaL factor.cpp:506-591.
                if let Some((comp_a, comp_b)) = find_complementary_factors(&factors) {
                    let f_a = factors[comp_a];
                    let mut app = SelfSubsumingApplication {
                        resolvents: Vec::new(),
                        to_delete: Vec::new(),
                        proof_pairs: Vec::new(),
                    };
                    // Build resolvents: clause_a minus its factor literal.
                    for i in 0..num_quotients {
                        let ci_a = chain[comp_a].clause_indices[i];
                        let ci_b = chain[comp_b].clause_indices[i];
                        if deleted[ci_a] || deleted[ci_b] {
                            continue;
                        }
                        let lits = clause_db.literals(ci_a);
                        let resolvent: Vec<Literal> =
                            lits.iter().filter(|&&l| l != f_a).copied().collect();
                        result.new_clauses.push(resolvent.clone());
                        app.resolvents.push(resolvent);
                        app.proof_pairs.push((ci_a, ci_b));
                    }
                    // Delete ALL original clauses across ALL factor levels.
                    for level in &chain[..=best_idx] {
                        for &ci in &level.clause_indices[..num_quotients] {
                            if !deleted[ci] {
                                deleted[ci] = true;
                                result.to_delete.push(ci);
                                app.to_delete.push(ci);
                            }
                        }
                    }
                    result.self_subsuming.push(app);
                    result.factored_count += 1;
                    continue;
                }

                let quotient_clauses: &[usize] = &chain[best_idx].clause_indices;

                // Delete original clauses in the factored matrix.
                let mut to_delete_set: Vec<usize> = Vec::new();

                // Mark all factor literals.
                for &f in &factors {
                    self.mark(f, MARK_FACTOR);
                }

                // For each quotient clause at the best level, find all matching
                // original clauses (one per factor).
                for &qi in quotient_clauses {
                    let lits = clause_db.literals(qi);
                    let quotient: Vec<Literal> = lits
                        .iter()
                        .filter(|l| !self.is_marked(**l, MARK_FACTOR))
                        .copied()
                        .collect();

                    // Mark quotient literals.
                    for &ql in &quotient {
                        self.mark(ql, MARK_QUOTIENT);
                    }

                    // For each factor, find a clause that is (factor ∨ quotient).
                    for &f in &factors {
                        // Search occ list of rarest quotient literal.
                        let rarest = quotient.iter().min_by_key(|&&l| occ.count(l)).copied();
                        if let Some(r) = rarest {
                            for &ci in occ.get(r) {
                                if deleted[ci] || to_delete_set.contains(&ci) {
                                    continue;
                                }
                                if clause_db.is_empty_clause(ci) || clause_db.is_learned(ci) {
                                    continue;
                                }
                                if Self::clause_satisfied(clause_db.literals(ci), vals) {
                                    continue;
                                }
                                if clause_db.len_of(ci) != quotient.len() + 1 {
                                    continue;
                                }
                                let c_lits = clause_db.literals(ci);
                                // Check: clause = quotient ∪ {f}.
                                let mut has_factor = false;
                                let mut all_quotient = true;
                                for &lit in c_lits {
                                    if lit == f {
                                        has_factor = true;
                                    } else if !self.is_marked(lit, MARK_QUOTIENT) {
                                        all_quotient = false;
                                        break;
                                    }
                                }
                                if has_factor && all_quotient {
                                    to_delete_set.push(ci);
                                    break;
                                }
                            }
                        }
                    }

                    // Clear quotient marks.
                    for &ql in &quotient {
                        self.unmark(ql, MARK_QUOTIENT);
                    }
                }

                // Clear factor marks.
                for &f in &factors {
                    self.unmark(f, MARK_FACTOR);
                }

                // Require a complete factors × quotients matrix. A partial rewrite
                // can delete clauses that are not fully represented by the new
                // divider/quotient set, which breaks model soundness.
                let expected_delete = factors.len() * quotient_clauses.len();
                if to_delete_set.len() != expected_delete {
                    continue;
                }

                let fresh_var = Variable(next_var as u32);
                let fresh_pos = Literal::positive(fresh_var);
                let fresh_neg = Literal::negative(fresh_var);
                next_var += 1;
                result.extension_vars_needed += 1;

                // Build per-application proof structure alongside flattened result.
                let mut app_dividers = Vec::with_capacity(factors.len());
                let mut app_quotients = Vec::with_capacity(quotient_clauses.len());

                // Binary divider clauses: (fresh ∨ f_i) for each factor.
                for &factor in &factors {
                    let divider = vec![fresh_pos, factor];
                    result.new_clauses.push(divider.clone());
                    app_dividers.push(divider);
                }

                // Quotient clauses: (¬fresh ∨ Q_lits) for each quotient clause.
                for &qi in quotient_clauses {
                    let lits = clause_db.literals(qi);
                    let mut q_clause = vec![fresh_neg];
                    for &lit in lits {
                        // Remove all factor literals from the quotient.
                        if !factors.contains(&lit) {
                            q_clause.push(lit);
                        }
                    }
                    result.new_clauses.push(q_clause.clone());
                    app_quotients.push(q_clause);
                }

                // Proof-only blocked clause: (¬fresh ∨ ¬f_1 ∨ ¬f_2 ∨ ...).
                // RAT on ¬fresh. See CaDiCaL factor.cpp:606-623.
                let mut blocked = Vec::with_capacity(1 + factors.len());
                blocked.push(fresh_neg);
                for &f in &factors {
                    blocked.push(f.negated());
                }

                let mut app_to_delete = Vec::with_capacity(to_delete_set.len());
                for &ci in &to_delete_set {
                    if !deleted[ci] {
                        deleted[ci] = true;
                        result.to_delete.push(ci);
                        app_to_delete.push(ci);
                    }
                }

                result.applications.push(FactorApplication {
                    fresh_var,
                    factors: factors.clone(),
                    divider_clauses: app_dividers,
                    quotient_clauses: app_quotients,
                    blocked_clause: blocked,
                    to_delete: app_to_delete,
                });
                result.factored_count += 1;
            }
        }

        result.ticks_consumed = ticks;

        // Validate structured application data against flattened result.
        assert_eq!(
            result.applications.len() + result.self_subsuming.len(),
            result.factored_count
        );
        for app in &result.applications {
            assert_eq!(app.blocked_clause.len(), 1 + app.factors.len());
            assert_eq!(app.divider_clauses.len(), app.factors.len());
            assert!(app.fresh_var.index() < next_var);
            assert_eq!(
                app.to_delete.len(),
                app.factors.len() * app.quotient_clauses.len()
            );
        }

        result
    }
}
