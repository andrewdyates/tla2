// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constraint types and utilities for Init predicate constraint extraction.
//!
//! This module defines the Constraint enum which represents variable constraints
//! extracted from Init predicates, along with utility functions for working with
//! constraint sets.

use crate::error::EvalError;
use crate::eval::{eval_iter_set_tlc_normalized, EvalCtx};
use crate::Value;
use std::collections::BTreeSet;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

/// A constraint extracted from a predicate.
///
/// Constraints are extracted from Init predicates to efficiently enumerate
/// all satisfying initial states.
#[derive(Debug, Clone)]
pub enum InitDomain {
    /// Eagerly materialized domain values.
    Concrete(Vec<Value>),
    /// A finite enumerable value kept lazy until enumeration time.
    Enumerable(Value),
}

impl InitDomain {
    fn materialize(&self, ctx: Option<&EvalCtx>) -> Result<Option<Vec<Value>>, EvalError> {
        match self {
            Self::Concrete(values) => Ok(Some(values.clone())),
            Self::Enumerable(value) => {
                let Some(ctx) = ctx else {
                    return Ok(None);
                };
                Ok(Some(
                    eval_iter_set_tlc_normalized(ctx, value, None)?.collect(),
                ))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Constraint {
    /// Variable equals a concrete value: x = v
    Eq(String, Value),
    /// Variable is in a set: x \in S
    In(String, InitDomain),
    /// Variable is not equal to a value: x /= v or x # v
    /// Note: NotEq alone cannot define a domain; it must be combined with
    /// other constraints that establish the domain.
    NotEq(String, Value),
    /// Variable equals an expression that depends on other variables.
    /// The expression will be evaluated after binding other variables.
    /// This handles patterns like: <code>state = \[n \\in Node |-> IF initiator\[n\] THEN "cand" ELSE "lost"\]</code>
    /// where state depends on initiator.
    Deferred(String, Box<Spanned<Expr>>),
    /// Variable is in a set expression that depends on other variables.
    /// The set expression will be evaluated after binding other variables.
    /// This handles patterns like: terminationDetected \in {FALSE, terminated}
    /// where terminated depends on active.
    DeferredIn(String, Box<Spanned<Expr>>),
    /// A boolean filter expression that must evaluate to TRUE.
    /// This handles constraints like in.ack = in.rdy that compare record fields
    /// or other expressions that don't directly enumerate variable values.
    /// The expression is evaluated after all variables have been bound from
    /// other constraints, and states that don't satisfy the filter are discarded.
    Filter(Box<Spanned<Expr>>),
}

/// Check which variables have no positive constraints (Eq, In, Deferred, or DeferredIn) in any branch.
/// Returns a list of variable names that are missing positive constraints.
/// Note: NotEq alone cannot define a domain, so it doesn't count as a "defining" constraint.
///
/// Part of #1564: O(vars + total_constraints) via HashSet instead of
/// O(vars * branches * constraints_per_branch) nested scan.
pub fn find_unconstrained_vars(vars: &[Arc<str>], branches: &[Vec<Constraint>]) -> Vec<String> {
    // Collect all variable names that have a positive constraint in any branch.
    let mut positively_constrained: std::collections::HashSet<&str> =
        std::collections::HashSet::new();
    for branch in branches {
        for c in branch {
            match c {
                Constraint::Eq(name, _)
                | Constraint::In(name, _)
                | Constraint::Deferred(name, _)
                | Constraint::DeferredIn(name, _) => {
                    positively_constrained.insert(name.as_str());
                }
                Constraint::NotEq(_, _) | Constraint::Filter(_) => {}
            }
        }
    }
    vars.iter()
        .filter(|v| !positively_constrained.contains(v.as_ref()))
        .map(std::string::ToString::to_string)
        .collect()
}

/// Find all possible values for a variable from a set of constraints.
///
/// Combines positive constraints (Eq, In) via intersection and excludes
/// values from NotEq constraints.
///
/// Returns Some(values) with the enumerable domain for the variable (may be empty),
/// or None if no positive constraints define a domain for this variable.
// Allow mutable_key_type: Value has interior mutability for lazy evaluation memoization,
// but Ord/Eq implementations don't depend on the mutable state
#[allow(clippy::mutable_key_type)]
pub fn find_values_for_var(
    ctx: Option<&EvalCtx>,
    var: &Arc<str>,
    constraints: &[Constraint],
) -> Result<Option<Vec<Value>>, EvalError> {
    let mut domain: Option<BTreeSet<Value>> = None;
    let mut excluded: Vec<Value> = Vec::new();

    // First pass: Build domain from positive constraints (Eq, In)
    // and collect excluded values from NotEq
    for constraint in constraints {
        match constraint {
            Constraint::Eq(name, value) if name == var.as_ref() => {
                let mut set = BTreeSet::new();
                set.insert(value.clone());
                domain = Some(match domain {
                    None => set,
                    Some(existing) => existing.intersection(&set).cloned().collect(),
                });
            }
            Constraint::In(name, init_domain) if name == var.as_ref() => {
                let Some(values) = init_domain.materialize(ctx)? else {
                    return Ok(None);
                };
                let set: BTreeSet<Value> = values.into_iter().collect();
                domain = Some(match domain {
                    None => set,
                    Some(existing) => existing.intersection(&set).cloned().collect(),
                });
            }
            Constraint::NotEq(name, value) if name == var.as_ref() => {
                excluded.push(value.clone());
            }
            _ => {}
        }

        // Early exit if domain becomes empty
        if matches!(domain, Some(ref d) if d.is_empty()) {
            return Ok(Some(Vec::new()));
        }
    }

    // Second pass: Remove excluded values from domain
    if let Some(mut d) = domain {
        for excl in &excluded {
            d.remove(excl);
        }
        Ok(Some(d.into_iter().collect()))
    } else if !excluded.is_empty() {
        // NotEq constraints exist but no positive constraints define a domain
        // Cannot enumerate without a bounded domain
        Ok(None)
    } else {
        // No constraints at all for this variable
        Ok(None)
    }
}
