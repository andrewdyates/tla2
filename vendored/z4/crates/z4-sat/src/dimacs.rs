// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DIMACS CNF parser
//!
//! Parses the standard DIMACS CNF format used in SAT competitions.
//! Delegates tokenization to [`crate::dimacs_core`] and converts raw
//! i32 literals to 0-indexed [`Literal`]/[`Variable`] values.

use crate::dimacs_core::{self, DimacsCoreError, DimacsRecord};
use crate::literal::{Literal, Variable};
use crate::solver::Solver;
use crate::{SolverVariant, VariantInput};
use std::io::Read;

/// Error type for DIMACS parsing
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DimacsError {
    /// Missing problem line (p cnf ...)
    MissingProblemLine,
    /// Invalid problem line format
    InvalidProblemLine {
        /// The invalid line content.
        line_content: String,
        /// 1-based line number (0 if unknown).
        line_number: usize,
    },
    /// Invalid literal in clause
    InvalidLiteral {
        /// The invalid token.
        token: String,
        /// 1-based line number (0 if unknown).
        line_number: usize,
    },
    /// I/O error description
    IoError(String),
    /// More clauses than declared
    TooManyClauses {
        /// Expected number of clauses
        expected: usize,
        /// Actual number of clauses
        got: usize,
    },
    /// Literal variable exceeds declared variable count
    VariableOutOfRange {
        /// The variable that was out of range
        var: u32,
        /// Maximum allowed variable
        max: u32,
        /// 1-based line number (0 if unknown).
        line_number: usize,
    },
}

impl std::fmt::Display for DimacsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingProblemLine => {
                write!(f, "missing problem line, expected \"p cnf <num_vars> <num_clauses>\"")
            }
            Self::InvalidProblemLine { line_content, line_number } if *line_number > 0 => {
                write!(f, "line {line_number}: invalid problem line: {line_content} (expected \"p cnf <num_vars> <num_clauses>\")")
            }
            Self::InvalidProblemLine { line_content, .. } => {
                write!(f, "invalid problem line: {line_content} (expected \"p cnf <num_vars> <num_clauses>\")")
            }
            Self::InvalidLiteral { token, line_number } if *line_number > 0 => {
                write!(f, "line {line_number}: invalid literal \"{token}\", expected integer")
            }
            Self::InvalidLiteral { token, .. } => {
                write!(f, "invalid literal \"{token}\", expected integer")
            }
            Self::IoError(s) => write!(f, "I/O error: {s}"),
            Self::TooManyClauses { expected, got } => {
                write!(f, "too many clauses: expected {expected}, got {got}")
            }
            Self::VariableOutOfRange { var, max, line_number } if *line_number > 0 => {
                write!(f, "line {line_number}: variable {var} out of range (declared max {max} in header)")
            }
            Self::VariableOutOfRange { var, max, .. } => {
                write!(f, "variable {var} out of range (declared max {max} in header)")
            }
        }
    }
}

impl std::error::Error for DimacsError {}

impl From<DimacsCoreError> for DimacsError {
    fn from(e: DimacsCoreError) -> Self {
        match e {
            DimacsCoreError::MissingHeader => Self::MissingProblemLine,
            DimacsCoreError::InvalidHeader { line_content, line_number } => {
                Self::InvalidProblemLine { line_content, line_number }
            }
            DimacsCoreError::InvalidLiteral { token, line_number } => {
                Self::InvalidLiteral { token, line_number }
            }
            DimacsCoreError::IoError(s) => Self::IoError(s),
            DimacsCoreError::VariableOutOfRange { var, max, line_number } => {
                Self::VariableOutOfRange { var, max, line_number }
            }
        }
    }
}

/// Result of parsing a DIMACS file
#[derive(Debug)]
pub struct DimacsFormula {
    /// Number of variables
    pub num_vars: usize,
    /// Number of clauses (declared)
    pub num_clauses: usize,
    /// The clauses
    pub clauses: Vec<Vec<Literal>>,
}

impl DimacsFormula {
    /// Create a solver from this formula.
    ///
    /// Enables BVE and congruence closure for pure SAT mode.
    /// BVE is safe here because DIMACS has no theory variables to protect.
    /// Default `Solver::new()` disables these for DPLL(T) safety (#3329).
    /// CaDiCaL eliminates ~18% of vars via congruence+SCC+BVE on BMC
    /// formulas (#3366). Subsumption re-enabled (#4872): CaDiCaL-style
    /// one-watch forward subsumption replaces the 150x-slower backward engine.
    /// Factorization stays enabled: on structured DIMACS formulas such as
    /// clique encodings it creates the extension-variable scaffolding that
    /// fastelim/BVE relies on for profitable preprocessing cascades.
    pub fn into_solver(self) -> Solver {
        self.into_solver_with_variant(SolverVariant::Default)
    }

    /// Create a solver using a named SAT-COMP variant preset.
    ///
    /// Applies feature-driven adaptive adjustments after the variant preset.
    /// See [`crate::adaptive::adjust_features_for_instance`] for the threshold
    /// rules applied.
    pub fn into_solver_with_variant(self, variant: SolverVariant) -> Solver {
        let mut solver = Solver::new(self.num_vars);
        let mut config = variant.config(VariantInput::new(
            self.num_vars,
            self.num_clauses,
            false,
            false,
        ));

        // Extract features and apply adaptive adjustments before applying
        // the config to the solver. This allows instance-specific overrides
        // to take effect during the initial variant application.
        let features =
            crate::features::SatFeatures::extract(self.num_vars, &self.clauses);
        let class = crate::features::InstanceClass::classify(&features);
        let _ = crate::adaptive::adjust_features_for_instance(&features, &class, &mut config.features);
        config.apply_to_solver(&mut solver);

        // Reorder toggle lives outside InprocessingFeatureProfile.
        if crate::adaptive::should_disable_reorder(&features, &class) {
            solver.set_reorder_enabled(false);
        }

        for clause in self.clauses {
            solver.add_clause(clause);
        }
        solver
    }
}

/// Convert a raw i32 DIMACS literal to a 0-indexed Literal.
///
/// DIMACS variables are 1-indexed; we use 0-indexed internally.
fn dimacs_lit_to_literal(lit: i32) -> Literal {
    let var = lit.unsigned_abs();
    let variable = Variable(var - 1);
    if lit > 0 {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    }
}

/// Parse a DIMACS CNF formula from a reader
pub(crate) fn parse<R: Read>(reader: R) -> Result<DimacsFormula, DimacsError> {
    let (header, records) = dimacs_core::parse_dimacs_records(reader)?;

    let mut clauses: Vec<Vec<Literal>> = Vec::with_capacity(header.num_clauses);
    for record in records {
        match record {
            DimacsRecord::Clause(raw) => {
                let clause: Vec<Literal> = raw.iter().map(|&l| dimacs_lit_to_literal(l)).collect();
                clauses.push(clause);
            }
            DimacsRecord::Tagged { tag, .. } => {
                return Err(DimacsError::InvalidLiteral {
                    token: format!("unexpected tagged line '{tag}' in CNF input"),
                    line_number: 0,
                });
            }
        }
    }

    Ok(DimacsFormula {
        num_vars: header.num_vars,
        num_clauses: header.num_clauses,
        clauses,
    })
}

/// Parse a DIMACS CNF formula from a string
pub fn parse_str(input: &str) -> Result<DimacsFormula, DimacsError> {
    parse(input.as_bytes())
}

#[cfg(test)]
/// Write a CNF formula in DIMACS format
pub(crate) fn write_dimacs<W: std::io::Write>(
    writer: &mut W,
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> std::io::Result<()> {
    writeln!(writer, "p cnf {} {}", num_vars, clauses.len())?;
    for clause in clauses {
        for lit in clause {
            write!(writer, "{} ", lit.to_dimacs())?;
        }
        writeln!(writer, "0")?;
    }
    Ok(())
}

#[cfg(test)]
#[path = "dimacs_tests.rs"]
mod tests;
