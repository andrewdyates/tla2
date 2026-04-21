// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Apply a permanent theory lemma clause to the incremental SAT solver.
///
/// Used by the lazy incremental split-loop to keep theory lemmas SAT-visible
/// across split iterations without rebuilding from scratch.
pub(in crate::executor) fn apply_theory_lemma_incremental(
    terms: &z4_core::TermStore,
    solver: &mut z4_sat::Solver,
    local_term_to_var: &mut super::HashMap<z4_core::TermId, u32>,
    local_var_to_term: &mut super::HashMap<u32, z4_core::TermId>,
    local_next_var: &mut u32,
    negations: &mut crate::incremental_proof_cache::IncrementalNegationCache,
    clause: &[z4_core::TheoryLit],
) {
    use z4_sat::Literal as SatLiteral;
    let lits: Vec<SatLiteral> = clause
        .iter()
        .map(|lit| {
            let var = super::ensure_incremental_atom_encoded(
                terms,
                solver,
                local_term_to_var,
                local_var_to_term,
                local_next_var,
                negations,
                lit.term,
            );
            if lit.value {
                SatLiteral::positive(var)
            } else {
                SatLiteral::negative(var)
            }
        })
        .collect();
    solver.add_clause(lits);
}

/// Apply a theory lemma clause to the persistent no-split incremental SAT solver.
///
/// No-split incremental lemmas must survive repeated `check-sat` calls while
/// the current SAT scope is active, but they must still disappear on `pop()`.
/// Returns `true` when SAT normalization kept the clause in the original-clause
/// ledger rather than discarding it as tautological.
pub(in crate::executor) fn apply_theory_lemma_incremental_persistent(
    solver: &mut z4_sat::Solver,
    term_to_var: &mut super::HashMap<z4_core::TermId, u32>,
    var_to_term: &mut super::HashMap<u32, z4_core::TermId>,
    negations: &mut crate::incremental_proof_cache::IncrementalNegationCache,
    clause: &[z4_core::TheoryLit],
) -> bool {
    use z4_sat::{Literal as SatLiteral, Variable as SatVariable};

    let mut lits: Vec<SatLiteral> = clause
        .iter()
        .map(|lit| {
            let var = *term_to_var.entry(lit.term).or_insert_with(|| {
                let next = solver.total_num_vars() as u32;
                solver.ensure_num_vars((next + 1) as usize);
                var_to_term.insert(next, lit.term);
                negations.note_fresh_term(lit.term);
                next
            });
            if lit.value {
                SatLiteral::positive(SatVariable::new(var))
            } else {
                SatLiteral::negative(SatVariable::new(var))
            }
        })
        .collect();

    if lits.is_empty() {
        solver.add_clause(lits);
        return false;
    }

    lits.sort_by_key(|lit| lit.raw());
    lits.dedup();
    let recorded = !lits
        .windows(2)
        .any(|pair| pair[0].variable() == pair[1].variable());
    solver.add_clause(lits);
    recorded
}

/// Apply a string lemma clause to the incremental SAT solver.
///
/// String lemmas use TermId atoms (possibly NOT-wrapped), unlike theory
/// lemmas which use TheoryLit. This handles polarity unwrapping and
/// incremental variable encoding.
pub(in crate::executor) fn apply_string_lemma_incremental(
    terms: &z4_core::TermStore,
    solver: &mut z4_sat::Solver,
    local_term_to_var: &mut super::HashMap<z4_core::TermId, u32>,
    local_var_to_term: &mut super::HashMap<u32, z4_core::TermId>,
    local_next_var: &mut u32,
    negations: &mut crate::incremental_proof_cache::IncrementalNegationCache,
    atoms: &[z4_core::TermId],
) {
    use z4_sat::Literal as SatLiteral;
    let mut lowered_atoms = Vec::with_capacity(atoms.len());
    let mut pending: Vec<z4_core::TermId> = atoms.iter().rev().copied().collect();
    while let Some(atom) = pending.pop() {
        match terms.get(atom) {
            z4_core::term::TermData::App(z4_core::Symbol::Named(name), args)
                if name == "or" && !args.is_empty() =>
            {
                pending.extend(args.iter().rev().copied());
            }
            _ => lowered_atoms.push(atom),
        }
    }

    let lits: Vec<SatLiteral> = lowered_atoms
        .iter()
        .map(|&atom| {
            let (base_atom, positive) = match terms.get(atom) {
                z4_core::term::TermData::Not(inner) => (*inner, false),
                _ => (atom, true),
            };
            let var = super::ensure_incremental_atom_encoded(
                terms,
                solver,
                local_term_to_var,
                local_var_to_term,
                local_next_var,
                negations,
                base_atom,
            );
            if positive {
                SatLiteral::positive(var)
            } else {
                SatLiteral::negative(var)
            }
        })
        .collect();

    // Polarity hint for LengthSplit tautologies [eq, NOT(eq)]
    if lits.len() == 2
        && lits[0].variable() == lits[1].variable()
        && lits[0].is_positive() != lits[1].is_positive()
    {
        let pos_var = if lits[0].is_positive() {
            lits[0].variable()
        } else {
            lits[1].variable()
        };
        solver.set_var_phase(pos_var, true);
        for _ in 0..20 {
            solver.bump_variable_activity(pos_var);
        }
    } else if lits.len() == 2
        && lits[0].variable() != lits[1].variable()
        && lits[0].is_positive()
        && lits[1].is_positive()
    {
        let empty_idx = lowered_atoms.iter().position(|&atom| {
            if let z4_core::term::TermData::App(z4_core::Symbol::Named(name), args) =
                terms.get(atom)
            {
                name == "="
                    && args.len() == 2
                    && (matches!(
                        terms.get(args[0]),
                        z4_core::term::TermData::Const(z4_core::Constant::String(s)) if s.is_empty()
                    ) || matches!(
                        terms.get(args[1]),
                        z4_core::term::TermData::Const(z4_core::Constant::String(s)) if s.is_empty()
                    ))
            } else {
                false
            }
        });
        if let Some(ei) = empty_idx {
            let decomp_idx = 1 - ei;
            solver.set_var_phase(lits[decomp_idx].variable(), true);
            solver.set_var_phase(lits[ei].variable(), false);
            for _ in 0..10 {
                solver.bump_variable_activity(lits[decomp_idx].variable());
            }
        }
    } else if lits.len() == 3 {
        let len_eq_idx = lowered_atoms.iter().position(|&atom| {
            if let z4_core::term::TermData::App(z4_core::Symbol::Named(name), args) =
                terms.get(atom)
            {
                if name == "=" && args.len() == 2 {
                    let l_is_len = matches!(
                        terms.get(args[0]),
                        z4_core::term::TermData::App(z4_core::Symbol::Named(n), _) if n == "str.len"
                    );
                    let r_is_len = matches!(
                        terms.get(args[1]),
                        z4_core::term::TermData::App(z4_core::Symbol::Named(n), _) if n == "str.len"
                    );
                    l_is_len && r_is_len
                } else {
                    false
                }
            } else {
                false
            }
        });
        if let Some(lei) = len_eq_idx {
            solver.set_var_phase(lits[lei].variable(), true);
            for _ in 0..10 {
                solver.bump_variable_activity(lits[lei].variable());
            }
        }
    }

    // Keep fresh string-lemma atoms decision-relevant even when SAT
    // normalizes the clause away to a weak tautology.
    let mut bumped = hashbrown::HashSet::new();
    for lit in &lits {
        if bumped.insert(lit.variable()) {
            solver.bump_variable_activity(lit.variable());
        }
    }

    solver.add_clause(lits);
}
