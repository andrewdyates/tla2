// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Substitution application: applying discovered substitutions to terms.
//!
//! Handles quantifier scoping (shadow/restore), let-bindings, and
//! recursive term rewriting. Extracted from `mod.rs` to keep each file
//! under 500 lines.

use super::VariableSubstitution;
use z4_core::term::TermData;
use z4_core::{Sort, TermId, TermStore};

impl VariableSubstitution {
    /// Shadow substitutions for bound variables when entering a quantifier scope.
    ///
    /// Clears `subst_cache` when any substitution is shadowed because compound
    /// terms containing the bound variable retain stale cache entries from the
    /// outer scope. Due to hash-consing, inner `(+ x y)` shares the same TermId
    /// as outer `(+ x y)`, so the cache would return wrong results (#5731).
    fn shadow_bound_vars(
        &mut self,
        terms: &mut TermStore,
        bound_vars: &[(String, Sort)],
    ) -> Vec<(TermId, Option<TermId>)> {
        let mut shadowed = Vec::new();
        let mut any_shadowed = false;
        for (name, sort) in bound_vars {
            let var_id = terms.mk_var(name.clone(), sort.clone());
            let old = self.substitutions.remove(&var_id);
            if old.is_some() {
                any_shadowed = true;
            }
            shadowed.push((var_id, old));
        }
        if any_shadowed {
            self.subst_cache.clear();
        }
        shadowed
    }

    /// Restore previously-shadowed substitutions when leaving a quantifier scope.
    fn restore_shadowed(&mut self, shadowed: Vec<(TermId, Option<TermId>)>) {
        let mut any_restored = false;
        for (var_id, old_subst) in shadowed {
            if let Some(replacement) = old_subst {
                self.substitutions.insert(var_id, replacement);
                any_restored = true;
            }
        }
        if any_restored {
            self.subst_cache.clear();
        }
    }

    /// Apply existing substitutions to a single term without discovering new substitutions.
    ///
    /// Used by the LIA assumption preprocessing path (#6728) to apply assertion-derived
    /// substitutions to assumption terms while preserving original assumption identity.
    pub(crate) fn apply_to_term(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        self.substitute_term(terms, term)
    }

    /// Substitute inside a quantifier body, shadowing bound variables (#5731).
    ///
    /// Returns `Some(new_term)` if the body or triggers changed, `None` otherwise.
    fn substitute_quantifier(
        &mut self,
        terms: &mut TermStore,
        vars: &[(String, Sort)],
        body: TermId,
        triggers: &[Vec<TermId>],
        is_forall: bool,
    ) -> Option<TermId> {
        let shadowed = self.shadow_bound_vars(terms, vars);
        let new_body = self.substitute_term(terms, body);
        let new_triggers: Vec<Vec<TermId>> = triggers
            .iter()
            .map(|trig| {
                trig.iter()
                    .map(|&t| self.substitute_term(terms, t))
                    .collect()
            })
            .collect();
        self.restore_shadowed(shadowed);
        if new_body == body && new_triggers == triggers {
            return None;
        }
        Some(if is_forall {
            terms.mk_forall_with_triggers(vars.to_vec(), new_body, new_triggers)
        } else {
            terms.mk_exists_with_triggers(vars.to_vec(), new_body, new_triggers)
        })
    }

    /// Substitute inside a let-binding, recursing into values and body.
    ///
    /// Let-bound variables shadow outer substitutions in the body (#5731 variant).
    fn substitute_let(
        &mut self,
        terms: &mut TermStore,
        bindings: &[(String, TermId)],
        body: TermId,
        term: TermId,
    ) -> TermId {
        // Substitute in binding values (outer scope — no shadowing yet)
        let new_bindings: Vec<(String, TermId)> = bindings
            .iter()
            .map(|(name, val)| (name.clone(), self.substitute_term(terms, *val)))
            .collect();
        // Shadow let-bound names before substituting in body
        let bound_vars: Vec<(String, Sort)> = bindings
            .iter()
            .map(|(name, val)| (name.clone(), terms.sort(*val).clone()))
            .collect();
        let shadowed = self.shadow_bound_vars(terms, &bound_vars);
        let new_body = self.substitute_term(terms, body);
        self.restore_shadowed(shadowed);
        if new_bindings
            .iter()
            .zip(bindings.iter())
            .all(|((_, nv), (_, ov))| nv == ov)
            && new_body == body
        {
            term
        } else {
            terms.mk_let(new_bindings, new_body)
        }
    }

    /// Apply substitutions to a term, returning the substituted term.
    pub(super) fn substitute_term(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        // Check cache first
        if let Some(&cached) = self.subst_cache.get(&term) {
            return cached;
        }

        // Check if this term is a variable that should be substituted
        if let Some(&replacement) = self.substitutions.get(&term) {
            // Recursively substitute in the replacement (for transitive chains)
            let result = self.substitute_term(terms, replacement);
            self.subst_cache.insert(term, result);
            return result;
        }

        // Recursively substitute in subterms
        let result = match terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,

            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| self.substitute_term(terms, arg))
                    .collect();

                if new_args == args {
                    term
                } else {
                    // Dispatch to canonical constructors for special operators.
                    // This ensures flattening and constant folding (#1708, #2767).
                    match sym.name() {
                        "=" if new_args.len() == 2 => terms.mk_eq(new_args[0], new_args[1]),
                        "+" => terms.mk_add(new_args),
                        "-" => terms.mk_sub(new_args),
                        "*" => terms.mk_mul(new_args),
                        _ => {
                            let sort = terms.sort(term).clone();
                            terms.mk_app(sym.clone(), new_args, sort)
                        }
                    }
                }
            }

            TermData::Not(inner) => {
                let new_inner = self.substitute_term(terms, inner);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }

            TermData::Ite(c, t, e) => {
                let new_c = self.substitute_term(terms, c);
                let new_t = self.substitute_term(terms, t);
                let new_e = self.substitute_term(terms, e);
                if new_c == c && new_t == t && new_e == e {
                    term
                } else {
                    if std::env::var("Z4_DEBUG_VAR_SUBST").is_ok() && new_c != c {
                        safe_eprintln!("[var_subst] ITE cond {:?} -> {:?}", c, new_c);
                    }
                    terms.mk_ite(new_c, new_t, new_e)
                }
            }

            TermData::Let(bindings, body) => self.substitute_let(terms, &bindings, body, term),
            TermData::Forall(v, b, t) => self
                .substitute_quantifier(terms, &v, b, &t, true)
                .unwrap_or(term),
            TermData::Exists(v, b, t) => self
                .substitute_quantifier(terms, &v, b, &t, false)
                .unwrap_or(term),
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in substitute_term(): {other:?}"),
        };

        self.subst_cache.insert(term, result);
        result
    }
}
