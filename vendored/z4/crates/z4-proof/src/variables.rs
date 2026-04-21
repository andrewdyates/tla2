// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof variable and declaration collection.
//!
//! Walks proof structures to discover referenced variables, filter auxiliary
//! declarations, and collect free variables with proper binding-scope tracking.

use std::collections::{BTreeMap, HashSet};
use z4_core::{Proof, ProofStep, Sort, TermData, TermId, TermStore};

/// Collect all variables referenced in proof terms, sorted by name.
///
/// Walks all terms in the proof recursively to find `Var` nodes,
/// including Skolem variables introduced by theory solvers (e.g.,
/// `_mod_q_*`, `_div_r_*`) that are not registered in `TermStore::names`.
pub(crate) fn collect_proof_variables(proof: &Proof, terms: &TermStore) -> Vec<(String, Sort)> {
    let mut vars: BTreeMap<String, Sort> = BTreeMap::new();
    let mut visited: HashSet<TermId> = HashSet::new();

    for step in &proof.steps {
        match step {
            ProofStep::Assume(t) => collect_term_vars(*t, terms, &mut vars, &mut visited),
            ProofStep::Resolution { clause, pivot, .. } => {
                for t in clause {
                    collect_term_vars(*t, terms, &mut vars, &mut visited);
                }
                collect_term_vars(*pivot, terms, &mut vars, &mut visited);
            }
            ProofStep::TheoryLemma { clause, .. } => {
                for t in clause {
                    collect_term_vars(*t, terms, &mut vars, &mut visited);
                }
            }
            ProofStep::Step { clause, args, .. } => {
                for t in clause {
                    collect_term_vars(*t, terms, &mut vars, &mut visited);
                }
                for t in args {
                    collect_term_vars(*t, terms, &mut vars, &mut visited);
                }
            }
            ProofStep::Anchor { .. } => {}
            _ => unreachable!("unexpected ProofStep variant"),
        }
    }

    vars.into_iter().collect()
}

/// Recursively collect variable names and sorts from a term.
fn collect_term_vars(
    term_id: TermId,
    terms: &TermStore,
    vars: &mut BTreeMap<String, Sort>,
    visited: &mut HashSet<TermId>,
) {
    if !visited.insert(term_id) {
        return;
    }
    let term = terms.get(term_id);
    match term {
        TermData::Var(name, _) => {
            vars.entry(name.clone())
                .or_insert_with(|| terms.sort(term_id).clone());
        }
        TermData::Const(_) => {}
        TermData::Not(t) => collect_term_vars(*t, terms, vars, visited),
        TermData::Ite(c, t, e) => {
            collect_term_vars(*c, terms, vars, visited);
            collect_term_vars(*t, terms, vars, visited);
            collect_term_vars(*e, terms, vars, visited);
        }
        TermData::App(_, args) => {
            for a in args {
                collect_term_vars(*a, terms, vars, visited);
            }
        }
        TermData::Let(bindings, body) => {
            for (_, t) in bindings {
                collect_term_vars(*t, terms, vars, visited);
            }
            collect_term_vars(*body, terms, vars, visited);
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            collect_term_vars(*body, terms, vars, visited);
            for trigger_set in triggers {
                for t in trigger_set {
                    collect_term_vars(*t, terms, vars, visited);
                }
            }
        }
        _ => unreachable!("unexpected TermData variant"),
    }
}

/// Collect auxiliary proof declarations that are not in the problem scope.
pub(crate) fn collect_auxiliary_proof_declarations(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> Vec<(String, Sort)> {
    let proof_free_vars = collect_free_vars_from_roots(terms, collect_proof_term_roots(proof));
    let problem_free_vars = collect_free_vars_from_roots(terms, problem_assertions.iter().copied());

    proof_free_vars
        .into_iter()
        .filter(|(name, _)| {
            !problem_free_vars.contains_key(name) && is_auxiliary_proof_symbol(name)
        })
        .collect()
}

fn collect_proof_term_roots(proof: &Proof) -> Vec<TermId> {
    let mut roots = Vec::new();
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => roots.push(*term),
            ProofStep::Resolution { clause, pivot, .. } => {
                roots.extend(clause.iter().copied());
                roots.push(*pivot);
            }
            ProofStep::TheoryLemma { clause, .. } => roots.extend(clause.iter().copied()),
            ProofStep::Step { clause, args, .. } => {
                roots.extend(clause.iter().copied());
                roots.extend(args.iter().copied());
            }
            ProofStep::Anchor { .. } => {}
            _ => unreachable!("unexpected ProofStep variant"),
        }
    }
    roots
}

fn collect_free_vars_from_roots(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> BTreeMap<String, Sort> {
    let mut free_vars = BTreeMap::new();
    let mut bound_names = Vec::new();
    for root in roots {
        collect_free_vars_in_term(terms, root, &mut bound_names, &mut free_vars);
    }
    free_vars
}

fn collect_free_vars_in_term(
    terms: &TermStore,
    term_id: TermId,
    bound_names: &mut Vec<String>,
    free_vars: &mut BTreeMap<String, Sort>,
) {
    match terms.get(term_id) {
        TermData::Var(name, _) => {
            if !bound_names.iter().any(|bound| bound == name) {
                let sort = terms.sort(term_id).clone();
                if let Some(existing_sort) = free_vars.get(name) {
                    debug_assert_eq!(
                        existing_sort, &sort,
                        "BUG: variable {name} collected with multiple sorts"
                    );
                } else {
                    free_vars.insert(name.clone(), sort);
                }
            }
        }
        TermData::Const(_) => {}
        TermData::Not(inner) => collect_free_vars_in_term(terms, *inner, bound_names, free_vars),
        TermData::Ite(cond, then_term, else_term) => {
            collect_free_vars_in_term(terms, *cond, bound_names, free_vars);
            collect_free_vars_in_term(terms, *then_term, bound_names, free_vars);
            collect_free_vars_in_term(terms, *else_term, bound_names, free_vars);
        }
        TermData::App(_, args) => {
            for &arg in args {
                collect_free_vars_in_term(terms, arg, bound_names, free_vars);
            }
        }
        TermData::Let(bindings, body) => {
            for (_, binding_value) in bindings {
                collect_free_vars_in_term(terms, *binding_value, bound_names, free_vars);
            }
            let bound_base = bound_names.len();
            for (name, _) in bindings {
                bound_names.push(name.clone());
            }
            collect_free_vars_in_term(terms, *body, bound_names, free_vars);
            bound_names.truncate(bound_base);
        }
        TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
            let bound_base = bound_names.len();
            for (name, _) in vars {
                bound_names.push(name.clone());
            }
            collect_free_vars_in_term(terms, *body, bound_names, free_vars);
            for trigger_set in triggers {
                for &trigger_term in trigger_set {
                    collect_free_vars_in_term(terms, trigger_term, bound_names, free_vars);
                }
            }
            bound_names.truncate(bound_base);
        }
        _ => unreachable!("unexpected TermData variant"),
    }
}

fn is_auxiliary_proof_symbol(name: &str) -> bool {
    const AUX_PREFIXES: &[&str] = &[
        "_mod_",
        "_div_",
        "__z4_",
        "__ext_diff",
        "_sk_",
        "sk_",
        "skolem",
    ];
    AUX_PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}
