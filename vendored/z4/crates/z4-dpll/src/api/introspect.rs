// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term introspection for the Z4 Solver API.
//!
//! Provides methods to decompose terms back into their operator and arguments.
//! Used by the Z3-compatible FFI layer for `Z3_get_app_num_args`, etc.

use z4_core::term::{Symbol, TermData};
use z4_core::Sort;

use super::types::Term;
use super::Solver;

/// Describes the kind of a term node.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TermKind {
    /// Function application (named or indexed operator)
    App {
        /// Operator name (e.g. "+", "and", "f")
        name: String,
        /// Number of arguments
        num_args: usize,
    },
    /// Variable reference
    Var {
        /// Variable name
        name: String,
    },
    /// Constant value (numeral, boolean, bitvector literal)
    Const,
    /// Negation (single child)
    Not,
    /// If-then-else (3 children: cond, then, else)
    Ite,
    /// Universal quantifier
    Forall,
    /// Existential quantifier
    Exists,
    /// Let binding
    Let,
}

impl Solver {
    /// Get the kind of a term, including operator info for applications.
    #[must_use]
    pub fn term_kind(&self, term: Term) -> TermKind {
        match self.terms().get(term.0) {
            TermData::App(sym, args) => {
                let name = match sym {
                    Symbol::Named(n) => n.clone(),
                    Symbol::Indexed(n, indices) => {
                        format!(
                            "(_ {n} {})",
                            indices
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(" ")
                        )
                    }
                    // All current Symbol variants handled above (#5692).
                    other => unreachable!("unhandled Symbol variant in term_kind(): {other:?}"),
                };
                TermKind::App {
                    name,
                    num_args: args.len(),
                }
            }
            TermData::Var(name, _) => TermKind::Var { name: name.clone() },
            TermData::Const(_) => TermKind::Const,
            TermData::Not(_) => TermKind::Not,
            TermData::Ite(_, _, _) => TermKind::Ite,
            TermData::Forall(_, _, _) => TermKind::Forall,
            TermData::Exists(_, _, _) => TermKind::Exists,
            TermData::Let(_, _) => TermKind::Let,
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in term_kind(): {other:?}"),
        }
    }

    /// Get the children (arguments) of a term.
    ///
    /// - `App(f, [a, b])` → `[a, b]`
    /// - `Not(x)` → `[x]`
    /// - `Ite(c, t, e)` → `[c, t, e]`
    /// - `Var`, `Const` → `[]`
    #[must_use]
    pub fn term_children(&self, term: Term) -> Vec<Term> {
        self.terms()
            .children(term.0)
            .into_iter()
            .map(Term)
            .collect()
    }

    /// Get the sort of a term.
    #[must_use]
    pub fn term_sort(&self, term: Term) -> Sort {
        self.terms().sort(term.0).clone()
    }

    /// Get bound variable names and sorts from a quantifier term.
    ///
    /// Returns `None` if the term is not a quantifier.
    #[must_use]
    pub fn quantifier_bound_vars(&self, term: Term) -> Option<Vec<(String, Sort)>> {
        match self.terms().get(term.0) {
            TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => Some(vars.clone()),
            _ => None,
        }
    }

    /// Get trigger patterns from a quantifier term.
    ///
    /// Returns `None` if the term is not a quantifier.
    /// Each inner `Vec<Term>` is a multi-pattern (conjunction).
    /// The outer `Vec` contains alternative trigger sets (disjunction).
    #[must_use]
    pub fn quantifier_triggers(&self, term: Term) -> Option<Vec<Vec<Term>>> {
        match self.terms().get(term.0) {
            TermData::Forall(_, _, triggers) | TermData::Exists(_, _, triggers) => Some(
                triggers
                    .iter()
                    .map(|ts| ts.iter().map(|&t| Term(t)).collect())
                    .collect(),
            ),
            _ => None,
        }
    }
}
