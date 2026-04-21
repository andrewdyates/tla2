// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared DIMACS-family parser core.
//!
//! Handles header parsing, comment/blank-line skipping, `%` termination,
//! clause tokenization with multiline accumulation, and tagged-line records
//! (`x` for XOR, `e`/`a` for QBF quantifiers). Crate-specific semantics
//! (variable indexing, quantifier interpretation) live in thin adapters.

use std::io::{BufRead, BufReader, Read};

/// Parsed DIMACS `p cnf` header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DimacsHeader {
    /// Number of variables declared.
    pub num_vars: usize,
    /// Number of clauses declared.
    pub num_clauses: usize,
}

/// Error from the core DIMACS parser.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DimacsCoreError {
    /// No `p cnf` header found before clause data.
    MissingHeader,
    /// Invalid `p cnf` header format.
    InvalidHeader {
        /// The invalid header line content.
        line_content: String,
        /// 1-based line number where the error occurred.
        line_number: usize,
    },
    /// Non-numeric token in a clause line.
    InvalidLiteral {
        /// The invalid token.
        token: String,
        /// 1-based line number where the error occurred.
        line_number: usize,
    },
    /// I/O error (stringified).
    IoError(String),
    /// Literal variable exceeds declared `num_vars`.
    VariableOutOfRange {
        /// The out-of-range variable.
        var: u32,
        /// Maximum allowed variable from header.
        max: u32,
        /// 1-based line number where the error occurred.
        line_number: usize,
    },
}

impl std::fmt::Display for DimacsCoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingHeader => write!(f, "missing problem line (p cnf ...), expected \"p cnf <num_vars> <num_clauses>\""),
            Self::InvalidHeader { line_content, line_number } => {
                write!(f, "line {line_number}: invalid problem line: {line_content} (expected \"p cnf <num_vars> <num_clauses>\")")
            }
            Self::InvalidLiteral { token, line_number } => {
                write!(f, "line {line_number}: invalid literal \"{token}\", expected integer")
            }
            Self::IoError(s) => write!(f, "I/O error: {s}"),
            Self::VariableOutOfRange { var, max, line_number } => {
                write!(f, "line {line_number}: variable {var} out of range (declared max {max} in header)")
            }
        }
    }
}

impl std::error::Error for DimacsCoreError {}

/// A parsed DIMACS record (clause or tagged line).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DimacsRecord {
    /// Clause: raw signed literals (positive = true, negative = false).
    /// Empty vec represents the empty clause (signals UNSAT).
    Clause(Vec<i32>),
    /// Tagged line: single-character prefix followed by integer values.
    /// Used for XOR (`x`), existential (`e`), and universal (`a`) quantifiers.
    Tagged {
        /// The tag character (e.g., 'x', 'e', 'a').
        tag: char,
        /// Raw integer values after the tag, before the terminating 0.
        values: Vec<i32>,
    },
}

/// Parse a DIMACS-family input into a header and sequence of records.
///
/// Handles:
/// - Comment lines (`c ...`)
/// - Blank lines
/// - `%` end-of-file marker (terminates parsing)
/// - `p cnf <vars> <clauses>` header
/// - Multiline clause accumulation (tokens split by whitespace, 0 terminates)
/// - Tagged lines (first non-whitespace is a letter other than `c`/`p`):
///   single-line, values parsed until 0 or end-of-line
///
/// Variable range checking is applied to clause literals only. Tagged-line
/// values are passed through without validation (adapters validate them).
pub fn parse_dimacs_records<R: Read>(
    reader: R,
) -> Result<(DimacsHeader, Vec<DimacsRecord>), DimacsCoreError> {
    let reader = BufReader::new(reader);
    let mut header: Option<DimacsHeader> = None;
    let mut records: Vec<DimacsRecord> = Vec::new();
    let mut current_clause: Vec<i32> = Vec::new();
    let mut line_number: usize = 0;

    for line in reader.lines() {
        let line = line.map_err(|e| DimacsCoreError::IoError(e.to_string()))?;
        line_number += 1;
        let line = line.trim();

        // Skip empty lines and comments
        if line.is_empty() || line.starts_with('c') {
            continue;
        }

        // `%` is an end-of-file marker in SAT competition DIMACS files
        if line.starts_with('%') {
            break;
        }

        // Problem header line
        if line.starts_with('p') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() < 4 || parts[1] != "cnf" {
                return Err(DimacsCoreError::InvalidHeader {
                    line_content: line.to_string(),
                    line_number,
                });
            }
            let num_vars: usize = parts[2].parse().map_err(|_| {
                DimacsCoreError::InvalidHeader {
                    line_content: line.to_string(),
                    line_number,
                }
            })?;
            let num_clauses: usize = parts[3].parse().map_err(|_| {
                DimacsCoreError::InvalidHeader {
                    line_content: line.to_string(),
                    line_number,
                }
            })?;
            header = Some(DimacsHeader {
                num_vars,
                num_clauses,
            });
            continue;
        }

        let max_var = header.ok_or(DimacsCoreError::MissingHeader)?.num_vars as u32;

        // Tagged line: first non-whitespace char is a letter
        let first_char = line.as_bytes()[0] as char; // line is non-empty (checked above)
        if first_char.is_ascii_alphabetic() {
            // Strip the tag character; remainder may start with a digit or space
            let content = &line[first_char.len_utf8()..];
            let mut values = Vec::new();
            for token in content.split_whitespace() {
                let val: i32 = token.parse().map_err(|_| DimacsCoreError::InvalidLiteral {
                    token: token.to_string(),
                    line_number,
                })?;
                if val == 0 {
                    break;
                }
                values.push(val);
            }
            records.push(DimacsRecord::Tagged {
                tag: first_char,
                values,
            });
            continue;
        }

        // Clause line: parse i32 tokens, accumulate across lines until 0
        for token in line.split_whitespace() {
            let lit_val: i32 = token.parse().map_err(|_| DimacsCoreError::InvalidLiteral {
                token: token.to_string(),
                line_number,
            })?;

            if lit_val == 0 {
                // Flush accumulated clause (empty clauses are preserved)
                records.push(DimacsRecord::Clause(std::mem::take(&mut current_clause)));
            } else {
                // Validate variable range
                let var = lit_val.unsigned_abs();
                if var > max_var {
                    return Err(DimacsCoreError::VariableOutOfRange {
                        var,
                        max: max_var,
                        line_number,
                    });
                }
                current_clause.push(lit_val);
            }
        }
    }

    // Handle final clause not terminated by 0
    if !current_clause.is_empty() {
        records.push(DimacsRecord::Clause(current_clause));
    }

    let header = header.ok_or(DimacsCoreError::MissingHeader)?;
    Ok((header, records))
}

/// Parse DIMACS-family records from a string (convenience wrapper).
pub fn parse_dimacs_records_str(
    input: &str,
) -> Result<(DimacsHeader, Vec<DimacsRecord>), DimacsCoreError> {
    parse_dimacs_records(input.as_bytes())
}

#[cfg(test)]
#[path = "dimacs_core_tests.rs"]
mod tests;
