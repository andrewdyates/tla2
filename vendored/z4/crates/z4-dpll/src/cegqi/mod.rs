// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counter-Example Guided Quantifier Instantiation (CEGQI)
//!
//! This module implements CEGQI for quantified arithmetic formulas that E-matching
//! cannot handle (formulas without ground terms to match against).
//!
//! # Algorithm
//!
//! From Reynolds et al. "Solving Linear Arithmetic Using Counterexample-Guided
//! Instantiation" (FMSD 2017):
//!
//! 1. **Negate the quantifier body**: For `forall x. phi(x)`, create `~phi(e)`
//!    where `e` is a fresh constant ("counterexample variable")
//! 2. **Check satisfiability**: If `~phi(e)` is UNSAT, the quantifier is valid
//! 3. **Extract model**: If SAT, get model `M` with assignment `e = v`
//! 4. **Compute selection term**: Find `t` such that `phi(t)` is implied
//! 5. **Add instantiation**: Assert `phi(t)` and repeat
//!
//! # Architecture
//!
//! - `CegqiInstantiator`: Main orchestrator for CEGQI
//! - `ArithInstantiator`: Theory-specific instantiation for LIA/LRA
//!
//! # Usage
//!
//! CEGQI is invoked after E-matching fails to fully instantiate quantified formulas.
//! It complements E-matching rather than replacing it.

pub(crate) mod arith;

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermId, TermStore};

/// Main orchestrator for CEGQI
///
/// Handles:
/// - Counterexample lemma creation (negating quantifier body)
/// - Variable ordering for elimination
/// - Solved form tracking (var -> substitution term)
/// - Instantiation construction
pub(crate) struct CegqiInstantiator {
    /// The quantified formula being processed
    quantifier: TermId,
    /// Mapping from bound variable name to CE variable
    bound_to_ce: HashMap<String, TermId>,
    /// True if this is a forall quantifier, false if exists
    is_forall: bool,
}

impl CegqiInstantiator {
    /// Create a new CEGQI instantiator for a quantified formula
    ///
    /// # Arguments
    /// * `quantifier` - Term ID of a forall/exists formula
    /// * `terms` - Term store for creating new terms
    ///
    /// # Returns
    /// A new instantiator, or None if the term is not a quantified formula
    pub(crate) fn new(quantifier: TermId, terms: &mut TermStore) -> Option<Self> {
        // Check that this is a quantified formula
        // TermData::Forall and Exists are tuple variants: (Vec<(String, Sort)>, TermId)
        let data = terms.get(quantifier);
        let (vars, is_forall) = match data {
            TermData::Forall(vars, _body, _) => (vars.clone(), true),
            TermData::Exists(vars, _body, _) => (vars.clone(), false),
            _ => return None,
        };

        // Create counterexample variables for each bound variable
        let mut bound_to_ce = HashMap::new();

        for (name, sort) in &vars {
            // Create a fresh CE constant for this bound variable
            let ce_name = format!("__ce_{name}");
            let ce_var = terms.mk_var(&ce_name, sort.clone());
            bound_to_ce.insert(name.clone(), ce_var);
        }

        Some(Self {
            quantifier,
            bound_to_ce,
            is_forall,
        })
    }

    /// Create the counterexample lemma for CEGQI
    ///
    /// For `forall x. phi(x)`: creates `~phi(e)` where `e` is the CE variable.
    /// If this is SAT, we get a counterexample to guide instantiation.
    ///
    /// For `exists x. phi(x)`: creates `phi(e)` (no negation).
    /// If this is SAT, we found a witness for the existential.
    ///
    /// # Returns
    /// Term ID of the CE lemma, or None if construction fails
    pub(crate) fn create_ce_lemma(&self, terms: &mut TermStore) -> Option<TermId> {
        // Get quantifier body and determine if it's forall or exists
        let data = terms.get(self.quantifier);
        let (body, is_forall) = match data {
            TermData::Forall(_, body, _) => (*body, true),
            TermData::Exists(_, body, _) => (*body, false),
            _ => return None,
        };

        // Substitute bound variables with CE variables
        let substituted = self.substitute_vars(body, terms)?;

        // For forall: negate to find counterexamples
        // For exists: keep as-is to find witnesses
        if is_forall {
            Some(terms.mk_not(substituted))
        } else {
            Some(substituted)
        }
    }

    /// Substitute bound variables with counterexample variables
    fn substitute_vars(&self, term: TermId, terms: &mut TermStore) -> Option<TermId> {
        let data = terms.get(term).clone();

        match &data {
            TermData::Var(name, _) => {
                // If this is a bound variable, substitute with CE var
                if let Some(&ce_var) = self.bound_to_ce.get(name) {
                    Some(ce_var)
                } else {
                    Some(term)
                }
            }
            TermData::Const(_) => {
                // Constants don't need substitution
                Some(term)
            }
            TermData::Not(inner) => {
                let subst_inner = self.substitute_vars(*inner, terms)?;
                Some(terms.mk_not(subst_inner))
            }
            TermData::Ite(c, t, e) => {
                let subst_c = self.substitute_vars(*c, terms)?;
                let subst_t = self.substitute_vars(*t, terms)?;
                let subst_e = self.substitute_vars(*e, terms)?;
                Some(terms.mk_ite(subst_c, subst_t, subst_e))
            }
            TermData::App(sym, args) => {
                let subst_args: Option<Vec<_>> = args
                    .iter()
                    .map(|&a| self.substitute_vars(a, terms))
                    .collect();
                // Preserve the original term's sort
                let original_sort = terms.sort(term).clone();
                Some(terms.mk_app(sym.clone(), subst_args?, original_sort))
            }
            TermData::Let(bindings, body) => {
                // Let bindings need capture-avoiding substitution:
                // 1. Substitute in binding expressions (they use outer scope)
                // 2. Track let-bound names as shadowed when processing body
                let substituted_bindings: Option<Vec<_>> = bindings
                    .iter()
                    .map(|(name, expr)| {
                        self.substitute_vars(*expr, terms)
                            .map(|e| (name.clone(), e))
                    })
                    .collect();
                let substituted_bindings = substituted_bindings?;

                // Get names that are shadowed in the body
                let shadowed: Vec<_> = bindings.iter().map(|(n, _)| n.clone()).collect();
                let subst_body = self.substitute_vars_filtered(*body, terms, &shadowed)?;

                Some(terms.mk_let(substituted_bindings, subst_body))
            }
            // Nested quantifiers: don't substitute their bound vars (shadowing)
            TermData::Forall(vars, body, _) => {
                // Filter out shadowed variables
                let shadowed: Vec<_> = vars.iter().map(|(n, _)| n.clone()).collect();
                let subst_body = self.substitute_vars_filtered(*body, terms, &shadowed)?;
                Some(terms.mk_forall(vars.clone(), subst_body))
            }
            TermData::Exists(vars, body, _) => {
                let shadowed: Vec<_> = vars.iter().map(|(n, _)| n.clone()).collect();
                let subst_body = self.substitute_vars_filtered(*body, terms, &shadowed)?;
                Some(terms.mk_exists(vars.clone(), subst_body))
            }
            // Future TermData variants: return term unchanged (identity substitution).
            _ => Some(term),
        }
    }

    /// Substitute vars but skip shadowed names
    fn substitute_vars_filtered(
        &self,
        term: TermId,
        terms: &mut TermStore,
        shadowed: &[String],
    ) -> Option<TermId> {
        let data = terms.get(term).clone();

        match &data {
            TermData::Var(name, _) => {
                // Skip if shadowed, otherwise check for substitution
                if shadowed.contains(name) {
                    Some(term)
                } else if let Some(&ce_var) = self.bound_to_ce.get(name) {
                    Some(ce_var)
                } else {
                    Some(term)
                }
            }
            TermData::Const(_) => Some(term),
            TermData::Not(inner) => {
                let subst = self.substitute_vars_filtered(*inner, terms, shadowed)?;
                Some(terms.mk_not(subst))
            }
            TermData::Ite(c, t, e) => {
                let sc = self.substitute_vars_filtered(*c, terms, shadowed)?;
                let st = self.substitute_vars_filtered(*t, terms, shadowed)?;
                let se = self.substitute_vars_filtered(*e, terms, shadowed)?;
                Some(terms.mk_ite(sc, st, se))
            }
            TermData::App(sym, args) => {
                let subst_args: Option<Vec<_>> = args
                    .iter()
                    .map(|&a| self.substitute_vars_filtered(a, terms, shadowed))
                    .collect();
                // Preserve the original term's sort
                let original_sort = terms.sort(term).clone();
                Some(terms.mk_app(sym.clone(), subst_args?, original_sort))
            }
            TermData::Let(bindings, body) => {
                // Capture-avoiding substitution for let:
                // 1. Substitute in binding expressions with current shadowed set
                // 2. Add let-bound names to shadowed set for body
                let substituted_bindings: Option<Vec<_>> = bindings
                    .iter()
                    .map(|(name, expr)| {
                        self.substitute_vars_filtered(*expr, terms, shadowed)
                            .map(|e| (name.clone(), e))
                    })
                    .collect();
                let substituted_bindings = substituted_bindings?;

                // Add let-bound names to shadowed set for body
                let mut new_shadowed = shadowed.to_vec();
                new_shadowed.extend(bindings.iter().map(|(n, _)| n.clone()));
                let subst_body = self.substitute_vars_filtered(*body, terms, &new_shadowed)?;

                Some(terms.mk_let(substituted_bindings, subst_body))
            }
            TermData::Forall(vars, body, _) => {
                // Add more shadowed names
                let mut new_shadowed = shadowed.to_vec();
                new_shadowed.extend(vars.iter().map(|(n, _)| n.clone()));
                let subst_body = self.substitute_vars_filtered(*body, terms, &new_shadowed)?;
                Some(terms.mk_forall(vars.clone(), subst_body))
            }
            TermData::Exists(vars, body, _) => {
                let mut new_shadowed = shadowed.to_vec();
                new_shadowed.extend(vars.iter().map(|(n, _)| n.clone()));
                let subst_body = self.substitute_vars_filtered(*body, terms, &new_shadowed)?;
                Some(terms.mk_exists(vars.clone(), subst_body))
            }
            // Future TermData variants: return term unchanged (identity substitution).
            _ => Some(term),
        }
    }

    /// Returns true if this is a forall quantifier, false for exists
    ///
    /// This is used by the executor to correctly map CE lemma results:
    /// - forall: UNSAT on CE lemma → SAT (quantifier holds)
    /// - exists: SAT on CE lemma → SAT (witness found)
    pub(crate) fn is_forall(&self) -> bool {
        self.is_forall
    }

    /// Returns the mapping from bound variable names to CE variables
    ///
    /// Used by the executor to extract CE variable model values after solving.
    pub(crate) fn _ce_variables(&self) -> &HashMap<String, TermId> {
        &self.bound_to_ce
    }

    /// Create a ground instantiation of the quantifier body using an explicit
    /// substitution map (bound variable name -> ground term).
    ///
    /// This is the CEGQI refinement step: after solving with a CE lemma yields
    /// SAT (counterexample found), the executor extracts model values for CE
    /// variables and passes them as ground terms here. The result `phi(t)` is
    /// added to assertions before re-solving.
    pub(crate) fn _create_model_instantiation(
        &self,
        terms: &mut TermStore,
        var_values: &HashMap<String, TermId>,
    ) -> Option<TermId> {
        let body = match terms.get(self.quantifier) {
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => *body,
            _ => return None,
        };

        // Reuse the existing substitution walker by creating a temporary
        // instantiator whose bound_to_ce maps to value terms instead of CE vars.
        let temp = Self {
            quantifier: self.quantifier,
            bound_to_ce: var_values.clone(),
            is_forall: self.is_forall,
        };
        temp.substitute_vars(body, terms)
    }
}

/// Check if a term is a good candidate for CEGQI
///
/// Returns true if:
/// 1. It's a quantified formula (forall/exists)
/// 2. Every bound variable has arithmetic sort (Int/Real)
/// 3. The body involves arithmetic (LIA/LRA) without patterns for E-matching
///
/// # Arguments
/// * `terms` - Term store
/// * `term` - Term to check
pub(crate) fn is_cegqi_candidate(terms: &TermStore, term: TermId) -> bool {
    let data = terms.get(term);

    match data {
        TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
            // Arithmetic CEGQI only supports quantifiers whose binders are all
            // arithmetic-sorted. If any bound variable has a non-arithmetic
            // sort (Seq, Array, Datatype, UF sort, ...), refinement cannot
            // extract model values or compute selection terms soundly for the
            // full quantified body, and CE lemmas can over-constrain the
            // problem (#7883/#7885/#7886/#7887).
            has_only_arithmetic_bound_vars(vars) && involves_arithmetic(terms, *body)
        }
        _ => false,
    }
}

fn has_only_arithmetic_bound_vars(vars: &[(String, Sort)]) -> bool {
    vars.iter()
        .all(|(_, sort)| matches!(sort, Sort::Int | Sort::Real))
}

/// Check if a term involves arithmetic operations (LIA/LRA)
fn involves_arithmetic(terms: &TermStore, term: TermId) -> bool {
    let data = terms.get(term);

    match data {
        TermData::Const(c) => {
            use z4_core::term::Constant;
            matches!(c, Constant::Int(_) | Constant::Rational(_))
        }
        // Bare variables do not make a formula arithmetic. CEGQI only handles
        // variables when they appear inside arithmetic operators/comparisons
        // or arithmetic equalities.
        TermData::Var(_, _) => false,
        TermData::App(Symbol::Named(name), args) => {
            // Check for arithmetic operators
            let is_arith_op = matches!(
                name.as_str(),
                "+" | "-" | "*" | "/" | "div" | "mod" | "<" | "<=" | ">" | ">="
            );
            if is_arith_op {
                return true;
            }
            // Equality over arithmetic-sorted terms is part of the supported
            // arithmetic CEGQI fragment, including pure UF equalities such as
            // f(x) = x with x:Int.
            if name == "="
                && args.len() == 2
                && args
                    .iter()
                    .any(|&arg| matches!(terms.sort(arg), Sort::Int | Sort::Real))
            {
                return true;
            }
            // Recurse into arguments
            args.iter().any(|&a| involves_arithmetic(terms, a))
        }
        TermData::App(_, args) => args.iter().any(|&a| involves_arithmetic(terms, a)),
        TermData::Not(inner) => involves_arithmetic(terms, *inner),
        TermData::Ite(c, t, e) => {
            involves_arithmetic(terms, *c)
                || involves_arithmetic(terms, *t)
                || involves_arithmetic(terms, *e)
        }
        TermData::Let(bindings, body) => {
            bindings.iter().any(|(_, t)| involves_arithmetic(terms, *t))
                || involves_arithmetic(terms, *body)
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            involves_arithmetic(terms, *body)
        }
        // Future TermData variants: conservatively not arithmetic.
        _ => false,
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
