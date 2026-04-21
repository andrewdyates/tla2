// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QDIMACS parser
//!
//! Parses QBF formulas in QDIMACS format (standard format for QBF benchmarks).
//! Delegates tokenization to [`z4_sat::dimacs_core`] and handles quantifier
//! blocks (`e`/`a`) locally.
//!
//! ## Format
//! ```text
//! c comment line
//! p cnf <num_vars> <num_clauses>
//! e <var1> <var2> ... 0    // existential block
//! a <var1> <var2> ... 0    // universal block
//! <lit1> <lit2> ... 0      // clause
//! ...
//! ```
//!
//! Variables are 1-indexed positive integers.
//! Literals are signed integers (positive = true, negative = false).
//! Each line ends with 0.

use crate::formula::{QbfFormula, Quantifier, QuantifierBlock};
use z4_sat::dimacs_core::{self, DimacsCoreError, DimacsRecord};
use z4_sat::{Literal, Variable};

/// Error type for QDIMACS parsing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QdimacsError {
    /// Missing problem line (p cnf ...)
    MissingProblemLine,
    /// Invalid problem line format
    InvalidProblemLine(String),
    /// Invalid quantifier line
    InvalidQuantifierLine(String),
    /// Invalid clause format
    InvalidClause(String),
    /// Variable out of range
    VariableOutOfRange(u32, usize),
}

impl std::fmt::Display for QdimacsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingProblemLine => write!(f, "missing problem line"),
            Self::InvalidProblemLine(s) => write!(f, "invalid problem line: {s}"),
            Self::InvalidQuantifierLine(s) => write!(f, "invalid quantifier line: {s}"),
            Self::InvalidClause(s) => write!(f, "invalid clause: {s}"),
            Self::VariableOutOfRange(v, n) => {
                write!(f, "variable {v} out of range (max {n})")
            }
        }
    }
}

impl std::error::Error for QdimacsError {}

impl From<DimacsCoreError> for QdimacsError {
    fn from(e: DimacsCoreError) -> Self {
        match e {
            DimacsCoreError::MissingHeader => Self::MissingProblemLine,
            DimacsCoreError::InvalidHeader { line_content, .. } => {
                Self::InvalidProblemLine(line_content)
            }
            DimacsCoreError::InvalidLiteral { token, .. } => Self::InvalidClause(token),
            DimacsCoreError::IoError(s) => Self::InvalidClause(format!("I/O error: {s}")),
            DimacsCoreError::VariableOutOfRange { var, max, .. } => {
                Self::VariableOutOfRange(var, max as usize)
            }
            _ => Self::InvalidClause(format!("{e}")),
        }
    }
}

/// Parse a QDIMACS string into a QBF formula
pub fn parse_qdimacs(input: &str) -> Result<QbfFormula, QdimacsError> {
    let (header, records) = dimacs_core::parse_dimacs_records_str(input)?;
    let num_vars = header.num_vars;

    let mut prefix = Vec::new();
    let mut clauses = Vec::with_capacity(header.num_clauses);

    for record in records {
        match record {
            DimacsRecord::Tagged {
                tag: tag @ ('e' | 'a'),
                values,
            } => {
                let quantifier = if tag == 'e' {
                    Quantifier::Exists
                } else {
                    Quantifier::Forall
                };

                let mut variables = Vec::new();
                for &val in &values {
                    if val <= 0 {
                        return Err(QdimacsError::InvalidQuantifierLine(format!(
                            "non-positive variable {val} in quantifier block"
                        )));
                    }
                    let var = val as u32;
                    if var > num_vars as u32 {
                        return Err(QdimacsError::VariableOutOfRange(var, num_vars));
                    }
                    variables.push(var);
                }

                if !variables.is_empty() {
                    prefix.push(QuantifierBlock::new(quantifier, variables));
                }
            }
            DimacsRecord::Clause(raw) => {
                // QBF uses 1-indexed variables directly (no -1 adjustment)
                let clause: Vec<Literal> = raw
                    .iter()
                    .map(|&l| {
                        let var = l.unsigned_abs();
                        if l > 0 {
                            Literal::positive(Variable::new(var))
                        } else {
                            Literal::negative(Variable::new(var))
                        }
                    })
                    .collect();
                if !clause.is_empty() {
                    clauses.push(clause);
                }
            }
            DimacsRecord::Tagged { tag, .. } => {
                return Err(QdimacsError::InvalidQuantifierLine(format!(
                    "unexpected tagged line '{tag}' in QDIMACS input"
                )));
            }
            _ => {
                return Err(QdimacsError::InvalidClause(
                    "unexpected record type in QDIMACS input".to_string(),
                ));
            }
        }
    }

    Ok(QbfFormula::new(num_vars, prefix, clauses))
}

#[cfg(test)]
#[path = "parser_tests.rs"]
mod tests;
