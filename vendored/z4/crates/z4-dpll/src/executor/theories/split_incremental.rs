// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental split-loop helpers for DPLL(T) theory solving.
//!
//! Extracted from `solve_harness.rs` to keep that file under 500 lines.
//! These functions are used by `solve_incremental_split_loop_pipeline!` to:
//! - Encode split atom pairs via Tseitin into a persistent SAT solver
//! - Map theory conflicts to SAT blocking clauses
//!
//! Part of #3536 (solve-harness-refactor).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_rational::BigRational;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{
    BoundRefinementRequest, TermId, TermStore, TheoryConflict, TheoryLit, Tseitin, TseitinResult,
};
use z4_sat::{Literal as SatLiteral, Solver as SatSolver, Variable as SatVariable};

use crate::incremental_proof_cache::IncrementalNegationCache;

use super::freeze_var_if_needed;

/// Stable key for deduplicating incremental split clauses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::executor) struct SplitClauseKey {
    left_atom: TermId,
    right_atom: TermId,
    pub(crate) disequality_guard: Option<(TermId, bool)>,
}

/// Stable key for deduplicating replayed bound-refinement implication clauses.
///
/// This key is computed from the request itself so duplicate replays can be
/// detected before materializing a fresh bound atom into the term store.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct BoundRefinementReplayKey {
    variable: TermId,
    rhs_term: Option<TermId>,
    normalized_bound: BigRational,
    is_upper: bool,
    is_integer: bool,
    reason_lits: Vec<(TermId, bool)>,
}

impl BoundRefinementReplayKey {
    pub(crate) fn new(request: &BoundRefinementRequest) -> Self {
        let mut reason_lits: Vec<(TermId, bool)> = request
            .reason
            .iter()
            .map(|lit| (lit.term, lit.value))
            .collect();
        reason_lits.sort_unstable();
        reason_lits.dedup();
        let normalized_bound = if request.is_integer {
            let int_bound = if request.is_upper {
                request.bound_value.floor().to_integer()
            } else {
                request.bound_value.ceil().to_integer()
            };
            BigRational::from_integer(int_bound)
        } else {
            request.bound_value.clone()
        };
        Self {
            variable: request.variable,
            rhs_term: request.rhs_term,
            normalized_bound,
            is_upper: request.is_upper,
            is_integer: request.is_integer,
            reason_lits,
        }
    }
}

/// Encode a split-atom pair into the incremental SAT solver and return the
/// 0-indexed SAT variables for `(left_atom, right_atom)`.
pub(in crate::executor) fn encode_split_pair_incremental(
    terms: &TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    split_pair: (TermId, TermId),
) -> Option<(SatVariable, SatVariable)> {
    let (left_atom, right_atom) = split_pair;

    fn reuse_encoded_atom(
        solver: &mut SatSolver,
        local_term_to_var: &HashMap<TermId, u32>,
        atom: TermId,
    ) -> Option<SatVariable> {
        let var = SatVariable::new(*local_term_to_var.get(&atom)?);
        freeze_var_if_needed(solver, var);
        Some(var)
    }

    fn encode_new_atom(
        terms: &TermStore,
        solver: &mut SatSolver,
        local_term_to_var: &mut HashMap<TermId, u32>,
        local_var_to_term: &mut HashMap<u32, TermId>,
        local_next_var: &mut u32,
        negations: &mut IncrementalNegationCache,
        atom: TermId,
    ) -> Option<SatVariable> {
        let tseitin = Tseitin::new(terms);
        let result = tseitin.transform_all(&[atom]);
        let offset = *local_next_var;

        for (&term, &var) in &result.term_to_var {
            let sat_var = (var - 1) + offset;
            let is_new = local_term_to_var.insert(term, sat_var).is_none();
            local_var_to_term.insert(sat_var, term);
            if is_new {
                negations.note_fresh_term(term);
            }
        }
        *local_next_var += result.num_vars;

        solver.ensure_num_vars(*local_next_var as usize);
        add_split_def_clauses(solver, &result, offset);

        let atom_var = *local_term_to_var.get(&atom)?;
        let atom_var = SatVariable::new(atom_var);
        freeze_var_if_needed(solver, atom_var);
        Some(atom_var)
    }

    // Repeated disequality/expression split requests can target the same atoms
    // across split-loop iterations. Reusing the original SAT vars keeps the
    // persistent SAT state aligned with the theory term mapping.
    let left_var = reuse_encoded_atom(solver, local_term_to_var, left_atom).or_else(|| {
        encode_new_atom(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            left_atom,
        )
    })?;
    let right_var = reuse_encoded_atom(solver, local_term_to_var, right_atom).or_else(|| {
        encode_new_atom(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            right_atom,
        )
    })?;

    Some((left_var, right_var))
}

/// Add split-atom Tseitin clauses, skipping the root-asserting unit clause.
fn add_split_def_clauses(solver: &mut SatSolver, result: &TseitinResult, offset: u32) {
    for clause in &result.clauses {
        // Skip unit clauses that assert the root -- we add the split
        // disjunction separately.
        if clause.literals().len() == 1 && clause.literals()[0] == result.root {
            continue;
        }
        let lits: Vec<SatLiteral> = clause
            .literals()
            .iter()
            .map(|&lit| {
                if lit > 0 {
                    let var = SatVariable::new((lit - 1) as u32 + offset);
                    SatLiteral::positive(var)
                } else {
                    let var = SatVariable::new((-lit - 1) as u32 + offset);
                    SatLiteral::negative(var)
                }
            })
            .collect();
        solver.add_clause(lits);
    }
}

/// Ensure an atom is Tseitin-encoded into the incremental SAT solver.
pub(in crate::executor) fn ensure_incremental_atom_encoded(
    terms: &TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    atom: TermId,
) -> SatVariable {
    if let Some(&var) = local_term_to_var.get(&atom) {
        let sat_var = SatVariable::new(var);
        freeze_var_if_needed(solver, sat_var);
        return sat_var;
    }

    let tseitin = Tseitin::new(terms);
    let result = tseitin.transform_all(&[atom]);
    let offset = *local_next_var;

    for (&term, &var) in &result.term_to_var {
        let sat_var = (var - 1) + offset;
        let is_new = local_term_to_var.insert(term, sat_var).is_none();
        local_var_to_term.insert(sat_var, term);
        if is_new {
            negations.note_fresh_term(term);
        }
    }
    *local_next_var += result.num_vars;

    solver.ensure_num_vars(*local_next_var as usize);
    add_split_def_clauses(solver, &result, offset);

    // Boolean constants (true/false) are encoded by Tseitin as fresh variables
    // forced by unit clauses, but NOT added to term_to_var. When a string lemma
    // clause contains a bare `true` atom (e.g., a tautological guard), we must
    // manually record the mapping so subsequent lookups succeed.
    if !local_term_to_var.contains_key(&atom)
        && result.num_vars > 0
        && result.term_to_var.is_empty()
    {
        let root_var = result.root.unsigned_abs();
        let sat_var = (root_var - 1) + offset;
        local_term_to_var.insert(atom, sat_var);
        local_var_to_term.insert(sat_var, atom);
        negations.note_fresh_term(atom);
    }

    let atom_var = local_term_to_var
        .get(&atom)
        .copied()
        .expect("Tseitin should always map incremental refinement atoms");
    let atom_var = SatVariable::new(atom_var);
    freeze_var_if_needed(solver, atom_var);
    atom_var
}

/// Replay pending bound refinements into the persistent incremental SAT solver.
///
/// Returns `false` if a reason literal is unmapped; duplicate clauses are skipped.
#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn replay_incremental_bound_refinements(
    terms: &mut TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    pending_refinements: &[BoundRefinementRequest],
    added_refinement_clauses: &mut HashSet<BoundRefinementReplayKey>,
) -> bool {
    for request in pending_refinements {
        let key = BoundRefinementReplayKey::new(request);
        if !added_refinement_clauses.insert(key) {
            continue;
        }
        let atom = crate::bound_refinement::materialize_bound_refinement_atom_term(terms, request);
        let bound_var = ensure_incremental_atom_encoded(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            atom,
        );

        let mut clause = Vec::with_capacity(request.reason.len() + 1);
        for reason_lit in &request.reason {
            let Some(&var) = local_term_to_var.get(&reason_lit.term) else {
                return false;
            };
            clause.push(if reason_lit.value {
                SatLiteral::negative(SatVariable::new(var))
            } else {
                SatLiteral::positive(SatVariable::new(var))
            });
        }
        clause.push(SatLiteral::positive(bound_var));
        solver.add_clause(clause);
    }

    true
}

/// Result of mapping a theory conflict to a SAT blocking clause.
pub(in crate::executor) enum BlockingClauseResult {
    /// Primary clause was added to the SAT solver, plus all mappable
    /// extra_conflicts. Continue the SAT loop.
    Added,
    /// The conflict mapped to an empty clause, meaning unconditional UNSAT.
    /// The caller should pop the SAT scope and return `SolveResult::Unsat`.
    Unsat,
    /// Some conflict terms failed to map through `local_term_to_var`.
    /// The blocking clause would be STRONGER than what the theory proved,
    /// so the caller should return `SolveResult::Unknown` (#5117).
    Unmapped,
}

/// Map theory conflict literals to SAT literals for a blocking clause.
///
/// Each `TheoryLit { term, value }` is negated (value=true → negative literal,
/// value=false → positive literal) so the clause blocks the conflicting assignment.
///
/// Returns `BlockingClauseResult::Unmapped` if any conflict term fails to map.
/// Returns the clause via `BlockingClauseResult` for the caller to log/add.
///
/// Deduplicates the conflict-term-mapping pattern that appeared twice in
/// `solve_lia_incremental` (for `TheoryResult::Unsat` and `UnsatWithFarkas`).
fn map_conflict_lits(
    conflict_lits: &[TheoryLit],
    local_term_to_var: &HashMap<TermId, u32>,
) -> Result<Vec<SatLiteral>, (usize, usize)> {
    let mut dropped = 0usize;
    let clause: Vec<SatLiteral> = conflict_lits
        .iter()
        .filter_map(|t| {
            local_term_to_var
                .get(&t.term)
                .map(|&var| {
                    if t.value {
                        SatLiteral::negative(SatVariable::new(var))
                    } else {
                        SatLiteral::positive(SatVariable::new(var))
                    }
                })
                .or_else(|| {
                    dropped += 1;
                    None
                })
        })
        .collect();

    if dropped > 0 {
        Err((dropped, conflict_lits.len()))
    } else {
        Ok(clause)
    }
}

/// Map theory conflict literals to a SAT blocking clause and add it to the solver.
///
/// Each `TheoryLit { term, value }` is negated (value=true → negative literal,
/// value=false → positive literal) so the clause blocks the conflicting assignment.
///
/// This function also processes `extra_conflicts` (batch-collected bound conflicts
/// from `collect_all_bound_conflicts`), adding each as a blocking clause. Extra
/// conflicts with unmapped terms are silently skipped (partial mapping is unsound).
///
/// Deduplicates the conflict-to-blocking-clause pattern that appeared twice in
/// `solve_lia_incremental` (for `TheoryResult::Unsat` and `UnsatWithFarkas`).
pub(in crate::executor) fn map_conflict_to_blocking_clause(
    solver: &mut SatSolver,
    conflict_lits: &[TheoryLit],
    extra_conflicts: &[TheoryConflict],
    local_term_to_var: &HashMap<TermId, u32>,
) -> BlockingClauseResult {
    let clause = match map_conflict_lits(conflict_lits, local_term_to_var) {
        Ok(c) => c,
        Err(_) => {
            return BlockingClauseResult::Unmapped;
        }
    };

    if clause.is_empty() {
        debug_assert!(
            conflict_lits.is_empty(),
            "BUG(#3820): conflict terms all failed to map: {conflict_lits:?}"
        );
        return BlockingClauseResult::Unsat;
    }

    solver.add_clause(clause);

    // Add blocking clauses for remaining batch-collected bound conflicts (#5117).
    // Skip any extra clause where a conflict term fails to map — a partial
    // clause is stronger than what the theory proved and could cause false UNSAT.
    add_extra_blocking_clauses(solver, extra_conflicts, local_term_to_var);

    BlockingClauseResult::Added
}

/// Encode a split pair into the incremental SAT solver, build a disjunctive
/// clause (optionally with a disequality guard literal), and add it.
///
/// Returns the SAT variables for `(left_atom, right_atom)`.
///
/// This deduplicates the encode → clause → add_clause pattern that appeared in
/// `NeedSplit`, `NeedDisequalitySplit`, and `NeedExpressionSplit` handlers of
/// `solve_incremental_split_loop_pipeline!` (#6321).
#[allow(clippy::too_many_arguments)]
pub(in crate::executor) fn encode_and_add_split_clause(
    terms: &TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    left_atom: TermId,
    right_atom: TermId,
    disequality_guard: Option<(TermId, bool)>,
    added_split_clauses: &mut HashSet<SplitClauseKey>,
) -> (SatVariable, SatVariable) {
    let (left_var, right_var) = encode_split_pair_incremental(
        terms,
        solver,
        local_term_to_var,
        local_var_to_term,
        local_next_var,
        negations,
        (left_atom, right_atom),
    )
    .expect("Tseitin should always map split atoms");

    let key = SplitClauseKey {
        left_atom,
        right_atom,
        disequality_guard,
    };
    if !added_split_clauses.insert(key) {
        return (left_var, right_var);
    }

    let mut clause = vec![
        SatLiteral::positive(left_var),
        SatLiteral::positive(right_var),
    ];
    if let Some((diseq_term, is_distinct)) = disequality_guard {
        if let Some(&diseq_var) = local_term_to_var.get(&diseq_term) {
            if is_distinct {
                clause.push(SatLiteral::negative(SatVariable::new(diseq_var)));
            } else {
                clause.push(SatLiteral::positive(SatVariable::new(diseq_var)));
            }
        }
    }
    solver.add_clause(clause);

    (left_var, right_var)
}

/// Bias a disjunctive split pair toward prompt SAT decisions.
///
/// Disequality and expression splits encode `(left_var ∨ right_var)` without a
/// "closer branch" preference. Seed both disjuncts with positive polarity and
/// bump both vars so the persistent SAT loop actually decides the new split.
pub(in crate::executor) fn bias_positive_split_clause_vars(
    solver: &mut SatSolver,
    left_var: SatVariable,
    right_var: SatVariable,
) {
    solver.set_var_phase(left_var, true);
    solver.set_var_phase(right_var, true);
    solver.bump_variable_activity(left_var);
    solver.bump_variable_activity(right_var);
}

pub(in crate::executor) mod lemmas;
pub(in crate::executor) use lemmas::apply_string_lemma_incremental;
pub(in crate::executor) use lemmas::apply_theory_lemma_incremental;
pub(in crate::executor) use lemmas::apply_theory_lemma_incremental_persistent;

#[cfg(test)]
mod tests;

/// Add blocking clauses for batch-collected extra bound conflicts (#5117).
///
/// Each extra conflict is mapped through `local_term_to_var` independently.
/// Conflicts with any unmapped terms are silently skipped (partial mapping
/// is unsound — a partial clause is stronger than what the theory proved).
pub(in crate::executor) fn add_extra_blocking_clauses(
    solver: &mut SatSolver,
    extra_conflicts: &[TheoryConflict],
    local_term_to_var: &HashMap<TermId, u32>,
) {
    for extra in extra_conflicts {
        if let Ok(extra_clause) = map_conflict_lits(&extra.literals, local_term_to_var) {
            if !extra_clause.is_empty() {
                solver.add_clause(extra_clause);
            }
        }
        // Err = some terms unmapped → skip this clause (partial mapping is unsound)
    }
}
