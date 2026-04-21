// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QBF formula representation
//!
//! Represents quantified boolean formulas in prenex normal form:
//! Q₁x₁...Qₙxₙ. φ(x₁,...,xₙ)
//!
//! Where each Qᵢ is either ∃ (existential) or ∀ (universal),
//! and φ is a propositional formula in CNF.

use z4_sat::Literal;

/// Quantifier type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    /// Existential quantifier (∃)
    Exists,
    /// Universal quantifier (∀)
    Forall,
}

impl std::fmt::Display for Quantifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Exists => write!(f, "∃"),
            Self::Forall => write!(f, "∀"),
        }
    }
}

/// A quantifier block (quantifier + variables)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierBlock {
    /// The quantifier type
    pub quantifier: Quantifier,
    /// Variables in this block (1-indexed)
    pub variables: Vec<u32>,
}

impl QuantifierBlock {
    /// Create a new quantifier block
    pub fn new(quantifier: Quantifier, variables: Vec<u32>) -> Self {
        Self {
            quantifier,
            variables,
        }
    }

    /// Create an existential block
    pub fn exists(variables: Vec<u32>) -> Self {
        Self::new(Quantifier::Exists, variables)
    }

    /// Create a universal block
    pub fn forall(variables: Vec<u32>) -> Self {
        Self::new(Quantifier::Forall, variables)
    }
}

/// A QBF formula in prenex CNF form
///
/// The quantifier prefix is a sequence of quantifier blocks,
/// followed by a CNF matrix (list of clauses).
#[derive(Debug, Clone)]
pub struct QbfFormula {
    /// Number of variables
    pub num_vars: usize,
    /// Quantifier prefix (ordered from outermost to innermost)
    pub prefix: Vec<QuantifierBlock>,
    /// CNF matrix (clauses as lists of literals)
    pub clauses: Vec<Vec<Literal>>,
    /// Quantifier level for each variable (0-indexed by var-1)
    /// Level 0 is outermost, higher levels are more inner
    var_levels: Vec<u32>,
    /// Quantifier type for each variable (0-indexed by var-1)
    var_quantifiers: Vec<Quantifier>,
}

impl QbfFormula {
    /// Create a new QBF formula
    pub fn new(num_vars: usize, prefix: Vec<QuantifierBlock>, clauses: Vec<Vec<Literal>>) -> Self {
        // Build variable info from prefix
        let mut var_levels = vec![0u32; num_vars];
        let mut var_quantifiers = vec![Quantifier::Exists; num_vars]; // Default to existential

        for (level, block) in prefix.iter().enumerate() {
            for &var in &block.variables {
                if var > 0 && (var as usize) <= num_vars {
                    var_levels[var as usize - 1] = level as u32;
                    var_quantifiers[var as usize - 1] = block.quantifier;
                }
            }
        }

        Self {
            num_vars,
            prefix,
            clauses,
            var_levels,
            var_quantifiers,
        }
    }

    /// Get the quantifier level of a variable (1-indexed)
    pub fn var_level(&self, var: u32) -> u32 {
        if var > 0 && (var as usize) <= self.num_vars {
            self.var_levels[var as usize - 1]
        } else {
            0
        }
    }

    /// Get the quantifier type of a variable (1-indexed)
    pub fn var_quantifier(&self, var: u32) -> Quantifier {
        if var > 0 && (var as usize) <= self.num_vars {
            self.var_quantifiers[var as usize - 1]
        } else {
            Quantifier::Exists // Unquantified variables are existential
        }
    }

    /// Check if a variable is existential
    pub fn is_existential(&self, var: u32) -> bool {
        self.var_quantifier(var) == Quantifier::Exists
    }

    /// Check if a variable is universal
    pub fn is_universal(&self, var: u32) -> bool {
        self.var_quantifier(var) == Quantifier::Forall
    }

    /// Get the quantifier level of a literal
    pub fn lit_level(&self, lit: Literal) -> u32 {
        self.var_level(lit.variable().id())
    }

    /// Check if a literal is existential
    pub fn lit_is_existential(&self, lit: Literal) -> bool {
        self.is_existential(lit.variable().id())
    }

    /// Check if a literal is universal
    pub fn lit_is_universal(&self, lit: Literal) -> bool {
        self.is_universal(lit.variable().id())
    }

    /// Get the maximum quantifier level of any existential literal in a clause
    pub fn max_existential_level(&self, clause: &[Literal]) -> Option<u32> {
        clause
            .iter()
            .filter(|lit| self.lit_is_existential(**lit))
            .map(|lit| self.lit_level(*lit))
            .max()
    }

    /// Apply universal reduction to a clause
    ///
    /// Removes universal literals whose level is >= the maximum existential level.
    /// These literals cannot affect satisfiability because they can always be
    /// set to satisfy the clause after all existential decisions are made.
    pub fn universal_reduce(&self, clause: &[Literal]) -> Vec<Literal> {
        let max_exist_level = self.max_existential_level(clause);

        match max_exist_level {
            Some(max_level) => {
                clause
                    .iter()
                    .filter(|lit| {
                        // Keep existential literals and universal literals with level < max_exist
                        self.lit_is_existential(**lit) || self.lit_level(**lit) < max_level
                    })
                    .copied()
                    .collect()
            }
            None => {
                // No existential literals - this is unusual but keep universals
                clause.to_vec()
            }
        }
    }
}

#[cfg(test)]
#[path = "formula_tests.rs"]
mod tests;
