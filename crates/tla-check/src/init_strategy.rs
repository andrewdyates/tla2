// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Init Enumeration Strategy Selection
//!
//! This module determines whether to use brute-force constraint extraction
//! or SMT-based enumeration (via z4) for Init state generation.
//!
//! # Background (Part of #251)
//!
//! Some TLA+ specs have Init predicates too complex for direct enumeration:
//! - Einstein: Permutation(S) creates 120! combinations
//! - MCConsensus/MCVoting: ISpec pattern where Init is actually an invariant
//! - Specs with unconstrained function variables
//!
//! For these specs, SMT-based enumeration via z4's ALL-SAT solver is more
//! efficient than brute-force enumeration.
//!
//! # Strategy Selection
//!
//! The heuristic analyzes Init predicate structure to classify:
//! - **BruteForce**: Simple equality/membership constraints, small domains
//! - **Z4Smt**: Complex constraints, function domains, permutations
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::complexity_visitor::ComplexityVisitor;

/// Strategy for Init state enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum InitStrategy {
    /// Direct constraint extraction and enumeration (current approach)
    /// Suitable for simple Init predicates with bounded domains
    BruteForce,

    /// SMT-based enumeration using z4 ALL-SAT solver
    /// Suitable for complex predicates, permutations, function constraints
    Z4Smt,
}

impl std::fmt::Display for InitStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InitStrategy::BruteForce => write!(f, "brute-force"),
            InitStrategy::Z4Smt => write!(f, "z4-smt"),
        }
    }
}

/// Reasons why Z4Smt strategy was selected
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum Z4Reason {
    /// Init contains function set membership: x \in [S -> T]
    FunctionSetMembership { variable: String },
    /// Init contains permutation-like constraint
    PermutationPattern { description: String },
    /// Variables have no direct constraints (likely ISpec pattern)
    UnconstrainedVariables { variables: Vec<String> },
    /// Init contains set filter with complex predicate
    ComplexSetFilter { description: String },
    /// Init references operators that suggest complex constraints
    ComplexOperatorReference { operator: String },
    /// Constraint extraction returned None (unsupported expressions)
    ConstraintExtractionFailed,
    /// Init contains nested SUBSET(SUBSET ...) producing doubly-exponential state space.
    /// The z4 NestedPowersetEncoder can handle this with Boolean SAT variables.
    /// Part of #3826.
    NestedSubsetPattern { description: String },
}

impl std::fmt::Display for Z4Reason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Z4Reason::FunctionSetMembership { variable } => {
                write!(f, "function set membership for '{}'", variable)
            }
            Z4Reason::PermutationPattern { description } => {
                write!(f, "permutation pattern: {}", description)
            }
            Z4Reason::UnconstrainedVariables { variables } => {
                write!(f, "unconstrained variables: {}", variables.join(", "))
            }
            Z4Reason::ComplexSetFilter { description } => {
                write!(f, "complex set filter: {}", description)
            }
            Z4Reason::ComplexOperatorReference { operator } => {
                write!(f, "complex operator reference: {}", operator)
            }
            Z4Reason::ConstraintExtractionFailed => {
                write!(f, "constraint extraction failed")
            }
            Z4Reason::NestedSubsetPattern { description } => {
                write!(f, "nested SUBSET pattern: {}", description)
            }
        }
    }
}

/// Result of analyzing Init predicate for strategy selection
#[derive(Debug, Clone)]
pub struct InitAnalysis {
    /// Recommended strategy
    pub strategy: InitStrategy,
    /// Reasons for Z4Smt (empty if BruteForce)
    pub reasons: Vec<Z4Reason>,
    /// Complexity score (higher = more complex)
    pub complexity_score: u32,
}

impl InitAnalysis {
    /// Create analysis recommending brute-force
    pub fn brute_force() -> Self {
        InitAnalysis {
            strategy: InitStrategy::BruteForce,
            reasons: Vec::new(),
            complexity_score: 0,
        }
    }

    /// Create analysis recommending z4-smt with reasons
    pub fn z4_smt(reasons: Vec<Z4Reason>, complexity_score: u32) -> Self {
        InitAnalysis {
            strategy: InitStrategy::Z4Smt,
            reasons,
            complexity_score,
        }
    }

    /// Check if z4 strategy is recommended
    pub fn needs_z4(&self) -> bool {
        self.strategy == InitStrategy::Z4Smt
    }
}

/// Analyze Init predicate to determine enumeration strategy.
///
/// This is the main entry point for strategy selection. It examines the
/// structure of the Init predicate to determine whether brute-force
/// enumeration will work or if z4 SMT-based enumeration is needed.
///
/// # Arguments
/// * `init_expr` - The Init predicate expression
/// * `vars` - State variables that need to be constrained
/// * `constraint_extraction_succeeded` - Whether extract_init_constraints returned Some
/// * `unconstrained_vars` - Variables without constraints (from find_unconstrained_vars)
///
/// # Returns
/// Analysis result with recommended strategy and reasons
pub fn analyze_init_predicate(
    init_expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    constraint_extraction_succeeded: bool,
    unconstrained_vars: &[String],
) -> InitAnalysis {
    let mut reasons = Vec::new();
    let mut complexity_score = 0;

    // Reason 1: Constraint extraction failed
    if !constraint_extraction_succeeded {
        reasons.push(Z4Reason::ConstraintExtractionFailed);
        complexity_score += 50;
    }

    // Reason 2: Unconstrained variables (ISpec pattern, complex Init)
    if !unconstrained_vars.is_empty() {
        reasons.push(Z4Reason::UnconstrainedVariables {
            variables: unconstrained_vars.to_vec(),
        });
        complexity_score += 30 * unconstrained_vars.len() as u32;
    }

    // Reason 3-5: Analyze Init expression structure
    let mut visitor = ComplexityVisitor::new(vars);
    visitor.visit_expr(&init_expr.node);

    for reason in visitor.reasons {
        complexity_score += match &reason {
            Z4Reason::FunctionSetMembership { .. } => 40,
            Z4Reason::PermutationPattern { .. } => 60,
            Z4Reason::ComplexSetFilter { .. } => 30,
            Z4Reason::ComplexOperatorReference { .. } => 20,
            Z4Reason::NestedSubsetPattern { .. } => 80, // Part of #3826: highest priority
            _ => 10,
        };
        reasons.push(reason);
    }

    // Decision threshold: z4 if any reasons found or high complexity
    if reasons.is_empty() {
        InitAnalysis::brute_force()
    } else {
        InitAnalysis::z4_smt(reasons, complexity_score)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::{FileId, Span};

    fn spanned<T>(node: T) -> Spanned<T> {
        Spanned {
            node,
            span: Span::new(FileId(0), 0, 0),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_simple_init_brute_force() {
        // Simple Init: x = 0 /\ y = 1
        let init = spanned(Expr::And(
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(0.into()))),
            ))),
            Box::new(spanned(Expr::Eq(
                Box::new(spanned(Expr::Ident(
                    "y".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(1.into()))),
            ))),
        ));

        let vars: Vec<Arc<str>> = vec!["x".into(), "y".into()];
        let analysis = analyze_init_predicate(&init, &vars, true, &[]);

        assert_eq!(analysis.strategy, InitStrategy::BruteForce);
        assert!(analysis.reasons.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_unconstrained_vars_needs_z4() {
        let init = spanned(Expr::Bool(true));
        let vars: Vec<Arc<str>> = vec!["x".into(), "y".into()];
        let unconstrained = vec!["x".to_string(), "y".to_string()];

        let analysis = analyze_init_predicate(&init, &vars, true, &unconstrained);

        assert_eq!(analysis.strategy, InitStrategy::Z4Smt);
        assert!(analysis.reasons.iter().any(|r| matches!(
            r,
            Z4Reason::UnconstrainedVariables { variables } if variables.len() == 2
        )));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_function_set_membership_needs_z4() {
        // x \in [S -> T]
        let init = spanned(Expr::In(
            Box::new(spanned(Expr::Ident(
                "votes".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::FuncSet(
                Box::new(spanned(Expr::Ident(
                    "Acceptors".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Ident(
                    "Values".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
            ))),
        ));

        let vars: Vec<Arc<str>> = vec!["votes".into()];
        let analysis = analyze_init_predicate(&init, &vars, true, &[]);

        assert_eq!(analysis.strategy, InitStrategy::Z4Smt);
        assert!(analysis.reasons.iter().any(
            |r| matches!(r, Z4Reason::FunctionSetMembership { variable } if variable == "votes")
        ));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_constraint_extraction_failed_needs_z4() {
        let init = spanned(Expr::Bool(true));
        let vars: Vec<Arc<str>> = vec!["x".into()];

        let analysis = analyze_init_predicate(&init, &vars, false, &[]);

        assert_eq!(analysis.strategy, InitStrategy::Z4Smt);
        assert!(analysis
            .reasons
            .iter()
            .any(|r| matches!(r, Z4Reason::ConstraintExtractionFailed)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_permutation_operator_needs_z4() {
        // nationality \in Permutation(S)
        let init = spanned(Expr::In(
            Box::new(spanned(Expr::Ident(
                "nationality".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Apply(
                Box::new(spanned(Expr::Ident(
                    "Permutation".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                vec![spanned(Expr::Ident(
                    "Nationalities".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))],
            ))),
        ));

        let vars: Vec<Arc<str>> = vec!["nationality".into()];
        let analysis = analyze_init_predicate(&init, &vars, true, &[]);

        assert_eq!(analysis.strategy, InitStrategy::Z4Smt);
        assert!(analysis.reasons.iter().any(
            |r| matches!(r, Z4Reason::ComplexOperatorReference { operator } if operator == "Permutation")
        ));
    }
}
