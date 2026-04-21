// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Free helper functions for assertion flattening, store-flat substitution,
//! and proof source tracking used by `solve_harness.rs`.
//!
//! Split from `solve_harness.rs` for code health (#7006, #5970).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermId, TermStore};

use crate::preprocess::VariableSubstitution;

pub(super) fn flatten_assertions_with_sources(
    terms: &TermStore,
    assertions: &[TermId],
) -> Vec<(TermId, Vec<TermId>)> {
    let mut flattened = Vec::new();
    for &assertion in assertions {
        flatten_assertion_with_source(terms, assertion, &[assertion], &mut flattened);
    }
    flattened
}

pub(super) fn flatten_assertions_with_optional_sources(
    terms: &TermStore,
    assertions: &[TermId],
    source_sets: &[Option<Vec<Vec<TermId>>>],
) -> Vec<(TermId, Option<Vec<Vec<TermId>>>)> {
    let mut flattened = Vec::new();
    for (&assertion, maybe_sources) in assertions.iter().zip(source_sets.iter()) {
        flatten_assertion_with_optional_sources(
            terms,
            assertion,
            maybe_sources.clone(),
            &mut flattened,
        );
    }
    flattened
}

pub(super) fn flatten_assertion_with_source(
    terms: &TermStore,
    assertion: TermId,
    source_set: &[TermId],
    flattened: &mut Vec<(TermId, Vec<TermId>)>,
) {
    if let TermData::App(Symbol::Named(name), args) = terms.get(assertion) {
        if name == "and" {
            for &arg in args {
                flatten_assertion_with_source(terms, arg, source_set, flattened);
            }
            return;
        }
    }
    flattened.push((assertion, source_set.to_vec()));
}

fn flatten_assertion_with_optional_sources(
    terms: &TermStore,
    assertion: TermId,
    source_sets: Option<Vec<Vec<TermId>>>,
    flattened: &mut Vec<(TermId, Option<Vec<Vec<TermId>>>)>,
) {
    if let TermData::App(Symbol::Named(name), args) = terms.get(assertion) {
        if name == "and" {
            for &arg in args {
                flatten_assertion_with_optional_sources(terms, arg, source_sets.clone(), flattened);
            }
            return;
        }
    }
    flattened.push((assertion, source_sets));
}

/// Substitute store-flat array equalities in AUFLIA preprocessing (#6820).
///
/// Store-flat benchmarks encode array chains as:
///   `(= a_N (store a_{N-1} idx val))`
/// where each `a_N` is a named Array-sorted variable. This function finds such
/// equalities and substitutes each `a_N` with its store expression throughout
/// all assertions. This converts `(select a_N k)` into
/// `(select (store a_{N-1} idx val) k)`, which directly triggers ROW axioms
/// without needing equality-chain reasoning.
///
/// Unlike `VariableSubstitution` (which excludes Array sorts to avoid regressions
/// in other paths), this is only called in the AUFLIA/ArrayEUF preprocessing pipeline.
pub(super) fn substitute_store_flat_equalities(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
) {
    // Phase 1: Collect var -> store_expr substitutions from equalities.
    // First pass: count how many store equalities target each variable.
    // Variables with multiple store equalities (e.g., b = store(a,x,v) AND
    // b = store(a,y,w)) must NOT be substituted — replacing b destroys the
    // "two stores to same target" pattern that check_disjunctive_store_target_equalities
    // needs to detect UNSAT (#6885).
    let mut store_eq_count: HashMap<TermId, usize> = HashMap::new();
    for &assertion in assertions.iter() {
        if let TermData::App(ref sym, ref args) = terms.get(assertion).clone() {
            if sym.name() == "=" && args.len() == 2 {
                let (lhs, rhs) = (args[0], args[1]);
                if matches!(terms.get(lhs), TermData::Var(_, _))
                    && matches!(terms.sort(lhs), Sort::Array(_))
                    && is_store_term(terms, rhs)
                {
                    *store_eq_count.entry(lhs).or_insert(0) += 1;
                } else if matches!(terms.get(rhs), TermData::Var(_, _))
                    && matches!(terms.sort(rhs), Sort::Array(_))
                    && is_store_term(terms, lhs)
                {
                    *store_eq_count.entry(rhs).or_insert(0) += 1;
                }
            }
        }
    }

    let mut subst_map: HashMap<TermId, TermId> = HashMap::new();

    for &assertion in assertions.iter() {
        let candidate = match terms.get(assertion).clone() {
            TermData::App(ref sym, ref args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                if matches!(terms.get(lhs), TermData::Var(_, _))
                    && matches!(terms.sort(lhs), Sort::Array(_))
                    && is_store_term(terms, rhs)
                {
                    Some((lhs, rhs))
                } else if matches!(terms.get(rhs), TermData::Var(_, _))
                    && matches!(terms.sort(rhs), Sort::Array(_))
                    && is_store_term(terms, lhs)
                {
                    Some((rhs, lhs))
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some((var, store_expr)) = candidate {
            // Skip variables that are the target of multiple store equalities.
            if store_eq_count.get(&var).copied().unwrap_or(0) > 1 {
                continue;
            }
            // Only take the first substitution for each variable, and do an
            // occurs check to prevent cycles.
            if !subst_map.contains_key(&var) && !term_contains(terms, store_expr, var) {
                subst_map.insert(var, store_expr);
            }
        }
    }

    if subst_map.is_empty() {
        return;
    }

    // Phase 2: Apply substitutions to all assertions.
    // After substitution, defining equalities like (= a_N (store ...)) become
    // tautological (mk_eq simplifies (= X X) to true). Remove them to avoid
    // the axiom fixpoint generating spurious ROW axioms from dead terms.
    let true_term = terms.true_term();
    let mut cache: HashMap<TermId, TermId> = HashMap::new();
    let mut new_assertions = Vec::with_capacity(assertions.len());
    for &assertion in assertions.iter() {
        let substituted = apply_store_flat_subst(terms, assertion, &subst_map, &mut cache);
        if substituted != true_term {
            new_assertions.push(substituted);
        }
    }
    *assertions = new_assertions;
}

/// Check if a term is a `store` application.
fn is_store_term(terms: &TermStore, term: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3
    )
}

/// Check if `term` contains `target` (occurs check for cycle prevention).
fn term_contains(terms: &TermStore, term: TermId, target: TermId) -> bool {
    if term == target {
        return true;
    }
    match terms.get(term) {
        TermData::Const(_) | TermData::Var(_, _) => false,
        TermData::App(_, args) => args.iter().any(|&a| term_contains(terms, a, target)),
        TermData::Not(inner) => term_contains(terms, *inner, target),
        TermData::Ite(c, t, e) => {
            term_contains(terms, *c, target)
                || term_contains(terms, *t, target)
                || term_contains(terms, *e, target)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, t)| term_contains(terms, *t, target))
                || term_contains(terms, *body, target)
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            term_contains(terms, *body, target)
                || triggers
                    .iter()
                    .flatten()
                    .any(|&t| term_contains(terms, t, target))
        }
        other => unreachable!("unhandled TermData variant in term_contains(): {other:?}"),
    }
}

/// Recursively apply store-flat substitutions with caching.
fn apply_store_flat_subst(
    terms: &mut TermStore,
    term: TermId,
    subst_map: &HashMap<TermId, TermId>,
    cache: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }

    // If this term is a variable in the substitution map, replace it
    // (and recursively substitute in the replacement).
    if let Some(&replacement) = subst_map.get(&term) {
        let result = apply_store_flat_subst(terms, replacement, subst_map, cache);
        cache.insert(term, result);
        return result;
    }

    let result = match terms.get(term).clone() {
        TermData::Const(_) | TermData::Var(_, _) => term,

        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&a| apply_store_flat_subst(terms, a, subst_map, cache))
                .collect();
            if new_args == args {
                term
            } else {
                // Use canonical constructors for known operators.
                match sym.name() {
                    "=" if new_args.len() == 2 => terms.mk_eq(new_args[0], new_args[1]),
                    "select" if new_args.len() == 2 => terms.mk_select(new_args[0], new_args[1]),
                    "store" if new_args.len() == 3 => {
                        terms.mk_store(new_args[0], new_args[1], new_args[2])
                    }
                    _ => {
                        let sort = terms.sort(term).clone();
                        terms.mk_app(sym.clone(), new_args, sort)
                    }
                }
            }
        }

        TermData::Not(inner) => {
            let new_inner = apply_store_flat_subst(terms, inner, subst_map, cache);
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }

        TermData::Ite(c, t, e) => {
            let new_c = apply_store_flat_subst(terms, c, subst_map, cache);
            let new_t = apply_store_flat_subst(terms, t, subst_map, cache);
            let new_e = apply_store_flat_subst(terms, e, subst_map, cache);
            if new_c == c && new_t == t && new_e == e {
                term
            } else {
                terms.mk_ite(new_c, new_t, new_e)
            }
        }

        TermData::Let(bindings, body) => {
            let new_bindings: Vec<(String, TermId)> = bindings
                .iter()
                .map(|(name, t)| {
                    (
                        name.clone(),
                        apply_store_flat_subst(terms, *t, subst_map, cache),
                    )
                })
                .collect();
            let new_body = apply_store_flat_subst(terms, body, subst_map, cache);
            let changed = new_body != body
                || new_bindings
                    .iter()
                    .zip(bindings.iter())
                    .any(|((_, a), (_, b))| a != b);
            if changed {
                terms.mk_let(new_bindings, new_body)
            } else {
                term
            }
        }

        TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
            // Quantifiers are uncommon in QF_AUFLIA; skip substitution inside them.
            term
        }

        other => unreachable!("unhandled TermData variant in apply_store_flat_subst(): {other:?}"),
    };

    cache.insert(term, result);
    result
}

pub(super) fn push_assertion_source_set(
    assertion_sources: &mut HashMap<TermId, Vec<Vec<TermId>>>,
    assertion: TermId,
    mut source_set: Vec<TermId>,
) {
    source_set.sort_by_key(|term| term.index());
    source_set.dedup();
    let entry = assertion_sources.entry(assertion).or_default();
    if !entry.contains(&source_set) {
        entry.push(source_set);
    }
}

pub(super) fn augment_lia_source_sets_with_substitutions(
    terms: &TermStore,
    original_assertions: &[TermId],
    source_sets: &mut [Vec<TermId>],
    var_subst: &VariableSubstitution,
) {
    for (assertion, source_set) in original_assertions
        .iter()
        .copied()
        .zip(source_sets.iter_mut())
    {
        let mut extra_sources = HashSet::new();
        let mut visited_vars = HashSet::new();
        collect_lia_substitution_sources_for_term(
            terms,
            assertion,
            var_subst,
            &mut visited_vars,
            &mut extra_sources,
        );
        for source in extra_sources {
            if !source_set.contains(&source) {
                source_set.push(source);
            }
        }
    }
}

fn collect_lia_substitution_sources_for_term(
    terms: &TermStore,
    term: TermId,
    var_subst: &VariableSubstitution,
    visited_vars: &mut HashSet<TermId>,
    sources: &mut HashSet<TermId>,
) {
    match terms.get(term) {
        TermData::Const(_) => {}
        TermData::Var(_, _) => {
            if !visited_vars.insert(term) {
                return;
            }
            if let Some(&source_assertion) = var_subst.substitution_sources().get(&term) {
                sources.insert(source_assertion);
            }
            if let Some(&replacement) = var_subst.substitutions().get(&term) {
                collect_lia_substitution_sources_for_term(
                    terms,
                    replacement,
                    var_subst,
                    visited_vars,
                    sources,
                );
            }
        }
        TermData::App(_, args) => {
            for &arg in args {
                collect_lia_substitution_sources_for_term(
                    terms,
                    arg,
                    var_subst,
                    visited_vars,
                    sources,
                );
            }
        }
        TermData::Not(inner) => collect_lia_substitution_sources_for_term(
            terms,
            *inner,
            var_subst,
            visited_vars,
            sources,
        ),
        TermData::Ite(cond, then_term, else_term) => {
            collect_lia_substitution_sources_for_term(
                terms,
                *cond,
                var_subst,
                visited_vars,
                sources,
            );
            collect_lia_substitution_sources_for_term(
                terms,
                *then_term,
                var_subst,
                visited_vars,
                sources,
            );
            collect_lia_substitution_sources_for_term(
                terms,
                *else_term,
                var_subst,
                visited_vars,
                sources,
            );
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                collect_lia_substitution_sources_for_term(
                    terms,
                    *value,
                    var_subst,
                    visited_vars,
                    sources,
                );
            }
            collect_lia_substitution_sources_for_term(
                terms,
                *body,
                var_subst,
                visited_vars,
                sources,
            );
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            collect_lia_substitution_sources_for_term(
                terms,
                *body,
                var_subst,
                visited_vars,
                sources,
            );
            for &trigger_term in triggers.iter().flatten() {
                collect_lia_substitution_sources_for_term(
                    terms,
                    trigger_term,
                    var_subst,
                    visited_vars,
                    sources,
                );
            }
        }
        other => unreachable!(
            "unhandled TermData variant in collect_lia_substitution_sources_for_term(): {other:?}"
        ),
    }
}
