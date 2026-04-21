// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable substitution preprocessing pass
//!
//! Extracts equalities from assertions and substitutes variables with
//! their equivalent terms. This is critical for BV soundness (#1708, #1720):
//!
//! When `(= mode_1 mode_2)` is asserted, predicates `(= mode_1 c)` and
//! `(= mode_2 c)` must become the same SAT variable. Without substitution,
//! they are encoded as different variables with no semantic link.
//!
//! # Algorithm
//!
//! 1. Extract equalities `(= var term)` from top-level assertions
//! 2. Build substitution map: var -> term
//! 3. Apply substitutions to all assertions
//!
//! # Reference
//! - `reference/bitwuzla/src/preprocess/pass/variable_substitution.cpp`
//! - `designs/2026-02-01-bv-preprocessing-framework.md`

use super::PreprocessingPass;
#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::TermData;
use z4_core::{Sort, TermId, TermStore};

/// Variable substitution preprocessing pass.
///
/// Scope (per #1782, extended #2767):
/// - Direct equalities `(= var term)` only
/// - Direct substitution (no transitive chains initially)
/// - Bool, BV, Int, and Real sorts
pub(crate) struct VariableSubstitution {
    /// Substitution map: variable TermId -> replacement TermId
    substitutions: HashMap<TermId, TermId>,
    /// Source equality assertion that introduced each substitution.
    substitution_sources: HashMap<TermId, TermId>,
    /// Cache for substituted terms to avoid redundant work
    subst_cache: HashMap<TermId, TermId>,
}

impl VariableSubstitution {
    /// Create a new VariableSubstitution pass.
    pub(crate) fn new() -> Self {
        Self {
            substitutions: HashMap::new(),
            substitution_sources: HashMap::new(),
            subst_cache: HashMap::new(),
        }
    }

    /// Get the substitution map (from -> to).
    ///
    /// This can be used after preprocessing to recover original variable values
    /// from the preprocessed model: if `from -> to` is in the map, then the
    /// original variable `from` has the same value as `to` in any model.
    pub(crate) fn substitutions(&self) -> &HashMap<TermId, TermId> {
        &self.substitutions
    }

    /// Get the equality assertion that introduced each substitution variable.
    pub(crate) fn substitution_sources(&self) -> &HashMap<TermId, TermId> {
        &self.substitution_sources
    }

    /// Check if a term is a variable (not a constant, not a compound term).
    fn is_variable(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::Var(_, _))
    }

    /// Check if `term` contains `var` (for cycle detection).
    fn contains_var(terms: &TermStore, term: TermId, var: TermId) -> bool {
        if term == var {
            return true;
        }

        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => false,
            TermData::App(_, args) => args.iter().any(|&arg| Self::contains_var(terms, arg, var)),
            TermData::Not(inner) => Self::contains_var(terms, *inner, var),
            TermData::Ite(c, t, e) => {
                Self::contains_var(terms, *c, var)
                    || Self::contains_var(terms, *t, var)
                    || Self::contains_var(terms, *e, var)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, t)| Self::contains_var(terms, *t, var))
                    || Self::contains_var(terms, *body, var)
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                Self::contains_var(terms, *body, var)
                    || triggers
                        .iter()
                        .flatten()
                        .any(|&t| Self::contains_var(terms, t, var))
            }
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in contains_var(): {other:?}"),
        }
    }

    /// Check whether `var -> replacement` is a cycle-safe substitution
    /// given the existing and pending substitutions.
    ///
    /// We require:
    /// - `replacement` does not contain `var` (occurs check).
    /// - Adding `var -> replacement` does not create a cycle through existing
    ///   substitutions (e.g., `a -> b+2` and `b -> a` would cycle).
    fn is_cycle_safe_substitution(
        terms: &TermStore,
        var: TermId,
        replacement: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        pending_vars: &HashSet<TermId>,
    ) -> bool {
        // Occurs check: replacement must not contain var directly
        if Self::contains_var(terms, replacement, var) {
            return false;
        }

        // Collect all variables in the replacement expression
        let mut vars_in_replacement = Vec::new();
        Self::collect_vars(terms, replacement, &mut vars_in_replacement);

        // Check: would any variable in replacement transitively reach var
        // through the existing + pending substitution chain?
        for &v in &vars_in_replacement {
            if Self::reaches_var_through_substs(terms, v, var, existing_substs, pending_vars) {
                return false;
            }
        }

        true
    }

    /// Collect all variable TermIds appearing in `term`.
    fn collect_vars(terms: &TermStore, term: TermId, out: &mut Vec<TermId>) {
        match terms.get(term) {
            TermData::Var(_, _) => out.push(term),
            TermData::Const(_) => {}
            TermData::App(_, args) => {
                for &arg in args {
                    Self::collect_vars(terms, arg, out);
                }
            }
            TermData::Not(inner) => Self::collect_vars(terms, *inner, out),
            TermData::Ite(c, t, e) => {
                Self::collect_vars(terms, *c, out);
                Self::collect_vars(terms, *t, out);
                Self::collect_vars(terms, *e, out);
            }
            TermData::Let(bindings, body) => {
                for (_, t) in bindings {
                    Self::collect_vars(terms, *t, out);
                }
                Self::collect_vars(terms, *body, out);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                Self::collect_vars(terms, *body, out);
                for &t in triggers.iter().flatten() {
                    Self::collect_vars(terms, t, out);
                }
            }
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in collect_vars(): {other:?}"),
        }
    }

    /// Check if variable `start` can reach `target` by following the substitution
    /// chain transitively.
    ///
    /// Follows the chain: if `start` is substituted with an expression, collect
    /// all variables in that expression. If any of them is `target`, return true.
    /// Otherwise, recursively check each of those variables.
    fn reaches_var_through_substs(
        terms: &TermStore,
        start: TermId,
        target: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        _pending_vars: &HashSet<TermId>,
    ) -> bool {
        let mut visited = HashSet::new();
        let mut worklist = vec![start];

        while let Some(current) = worklist.pop() {
            if !visited.insert(current) {
                continue;
            }
            if let Some(&replacement) = existing_substs.get(&current) {
                if Self::contains_var(terms, replacement, target) {
                    return true;
                }
                // Follow chain: collect variables in the replacement and
                // check them too
                let mut vars = Vec::new();
                Self::collect_vars(terms, replacement, &mut vars);
                for v in vars {
                    if !visited.contains(&v) {
                        worklist.push(v);
                    }
                }
            }
        }
        false
    }

    /// Try to extract a substitution from an equality assertion.
    ///
    /// Returns `Some((var, term))` if the assertion is `(= var term)` or
    /// `(= term var)` where var is a variable and term doesn't contain var.
    ///
    /// `existing_substs` and `pending_vars` are used for graph-based cycle
    /// detection, replacing the overly strict TermId-ordering that blocked
    /// substitutions like `a -> (+ b 2)` when `b > a` (#2830).
    fn find_substitution(
        terms: &TermStore,
        assertion: TermId,
        existing_substs: &HashMap<TermId, TermId>,
        pending_vars: &HashSet<TermId>,
    ) -> Option<(TermId, TermId)> {
        match terms.get(assertion) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);

                // Prefer substituting sort-compatible variables
                let lhs_sort = terms.sort(lhs);
                let rhs_sort = terms.sort(rhs);

                // Substitute Bool, BV, Int, and Real sorts.
                // Int/Real enables elimination of equality chains like
                // result_a = self_a + 1 that the LRA simplex can't resolve (#2767).
                let is_substitutable_sort =
                    |s: &Sort| matches!(s, Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Real);

                if !is_substitutable_sort(lhs_sort) && !is_substitutable_sort(rhs_sort) {
                    return None;
                }

                // If both sides are variables, orient substitution by TermId to avoid cycles.
                if Self::is_variable(terms, lhs) && Self::is_variable(terms, rhs) {
                    if lhs == rhs {
                        return None;
                    }
                    let (var, replacement) = if lhs > rhs { (lhs, rhs) } else { (rhs, lhs) };
                    if Self::is_cycle_safe_substitution(
                        terms,
                        var,
                        replacement,
                        existing_substs,
                        pending_vars,
                    ) {
                        return Some((var, replacement));
                    }
                    return None;
                }

                // Try lhs -> rhs
                if Self::is_variable(terms, lhs)
                    && Self::is_cycle_safe_substitution(
                        terms,
                        lhs,
                        rhs,
                        existing_substs,
                        pending_vars,
                    )
                {
                    return Some((lhs, rhs));
                }

                // Try rhs -> lhs
                if Self::is_variable(terms, rhs)
                    && Self::is_cycle_safe_substitution(
                        terms,
                        rhs,
                        lhs,
                        existing_substs,
                        pending_vars,
                    )
                {
                    return Some((rhs, lhs));
                }

                None
            }
            // Bool equality is encoded as ite(a, b, not(b)) by mk_eq (#3421).
            // Recognize this pattern for variable substitution.
            TermData::Ite(cond, then_br, else_br)
                if *terms.sort(*cond) == Sort::Bool
                    && *terms.sort(*then_br) == Sort::Bool
                    && matches!(terms.get(*else_br), TermData::Not(inner) if *inner == *then_br) =>
            {
                let (lhs, rhs) = (*cond, *then_br);

                if Self::is_variable(terms, lhs) && Self::is_variable(terms, rhs) {
                    if lhs == rhs {
                        return None;
                    }
                    let (var, replacement) = if lhs > rhs { (lhs, rhs) } else { (rhs, lhs) };
                    if Self::is_cycle_safe_substitution(
                        terms,
                        var,
                        replacement,
                        existing_substs,
                        pending_vars,
                    ) {
                        return Some((var, replacement));
                    }
                    return None;
                }

                if Self::is_variable(terms, lhs)
                    && Self::is_cycle_safe_substitution(
                        terms,
                        lhs,
                        rhs,
                        existing_substs,
                        pending_vars,
                    )
                {
                    return Some((lhs, rhs));
                }

                if Self::is_variable(terms, rhs)
                    && Self::is_cycle_safe_substitution(
                        terms,
                        rhs,
                        lhs,
                        existing_substs,
                        pending_vars,
                    )
                {
                    return Some((rhs, lhs));
                }

                None
            }
            _ => None,
        }
    }
}

impl Default for VariableSubstitution {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for VariableSubstitution {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let debug = std::env::var("Z4_DEBUG_VAR_SUBST").is_ok();

        // Phase 1: Extract all substitutions from assertions
        let mut new_substitutions: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut substituted_vars: HashSet<TermId> = HashSet::new();

        if debug {
            safe_eprintln!("[var_subst] Scanning {} assertions", assertions.len());
        }

        // Build combined substitution map for cycle detection: includes both
        // previously-committed and newly-found substitutions. This allows
        // graph-based cycle checks that are less restrictive than TermId ordering (#2830).
        let mut combined_substs = self.substitutions.clone();

        for &assertion in assertions.iter() {
            if let Some((var, replacement)) =
                Self::find_substitution(terms, assertion, &combined_substs, &substituted_vars)
            {
                // Don't substitute a variable twice (within this pass, or across fixed-point rounds).
                if self.substitutions.contains_key(&var) || substituted_vars.contains(&var) {
                    if debug {
                        safe_eprintln!("[var_subst] Skip: {:?} already substituted", var);
                    }
                    continue;
                }
                if debug {
                    let var_name = if let TermData::Var(n, _) = terms.get(var) {
                        n.clone()
                    } else {
                        format!("{var:?}")
                    };
                    let rep_name = if let TermData::Var(n, _) = terms.get(replacement) {
                        n.clone()
                    } else {
                        format!("{replacement:?}")
                    };
                    safe_eprintln!(
                        "[var_subst] Found: {} ({:?}) -> {} ({:?})",
                        var_name,
                        var,
                        rep_name,
                        replacement
                    );
                }
                new_substitutions.push((var, replacement, assertion));
                substituted_vars.insert(var);
                // Add to combined map so future assertions see this substitution
                // for cycle detection purposes
                combined_substs.insert(var, replacement);
            }
        }

        // If no new substitutions, nothing to do
        if new_substitutions.is_empty() {
            return false;
        }

        // Add new substitutions to the map
        for (var, replacement, assertion) in new_substitutions {
            self.substitutions.insert(var, replacement);
            self.substitution_sources.insert(var, assertion);
        }

        // Phase 2: Apply substitutions to all assertions
        let mut modified = false;
        for assertion in assertions.iter_mut() {
            let new_assertion = self.substitute_term(terms, *assertion);
            if new_assertion != *assertion {
                *assertion = new_assertion;
                modified = true;
            }
        }

        modified
    }

    fn reset(&mut self) {
        // Clear caches but preserve substitutions for fixed-point iteration
        self.subst_cache.clear();
    }
}

mod apply;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
