// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended DIMACS parser with XOR support.
//!
//! Delegates header/comment/clause tokenization to [`z4_sat::dimacs_core`]
//! and handles XOR-tagged lines (`x...`) locally.

use crate::{XorConstraint, XorExtension};
use z4_sat::dimacs_core::{self, DimacsCoreError, DimacsRecord};
use z4_sat::{Literal, Variable};

// ============================================================================
// Extended DIMACS Parser with XOR Support
// ============================================================================

/// Error type for extended DIMACS parsing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtDimacsError {
    /// Missing problem line (p cnf ...)
    MissingProblemLine,
    /// Invalid problem line format
    InvalidProblemLine(String),
    /// Invalid literal in clause
    InvalidLiteral(String),
    /// Invalid XOR constraint
    InvalidXor(String),
    /// I/O error description
    IoError(String),
    /// Variable exceeds declared count
    VariableOutOfRange {
        /// The variable that was out of range
        var: u32,
        /// Maximum allowed variable
        max: u32,
    },
}

impl std::fmt::Display for ExtDimacsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingProblemLine => write!(f, "Missing problem line (p cnf ...)"),
            Self::InvalidProblemLine(s) => write!(f, "Invalid problem line: {s}"),
            Self::InvalidLiteral(s) => write!(f, "Invalid literal: {s}"),
            Self::InvalidXor(s) => write!(f, "Invalid XOR constraint: {s}"),
            Self::IoError(s) => write!(f, "I/O error: {s}"),
            Self::VariableOutOfRange { var, max } => {
                write!(f, "Variable {var} out of range (max {max})")
            }
        }
    }
}

impl std::error::Error for ExtDimacsError {}

impl From<DimacsCoreError> for ExtDimacsError {
    fn from(e: DimacsCoreError) -> Self {
        match e {
            DimacsCoreError::MissingHeader => Self::MissingProblemLine,
            DimacsCoreError::InvalidHeader { line_content, .. } => {
                Self::InvalidProblemLine(line_content)
            }
            DimacsCoreError::InvalidLiteral { token, .. } => Self::InvalidLiteral(token),
            DimacsCoreError::IoError(s) => Self::IoError(s),
            DimacsCoreError::VariableOutOfRange { var, max, .. } => {
                Self::VariableOutOfRange { var, max }
            }
            _ => Self::IoError(format!("{e}")),
        }
    }
}

/// Result of parsing an extended DIMACS file with XOR constraints.
///
/// The extended DIMACS format used by CryptoMiniSat adds XOR constraints
/// with the syntax `x<lit> <lit> ... 0` where:
/// - `x` prefix indicates an XOR line
/// - Positive literals contribute their variable to the XOR
/// - Negative literals contribute their variable AND flip the RHS
///
/// For example:
/// - `x1 2 3 0` means x1 XOR x2 XOR x3 = 1 (odd parity)
/// - `x-1 0` means x1 = 0 (negation of x1, so rhs flips)
/// - `x1 -2 0` means x1 XOR x2 = 0 (one negation flips rhs from default 1 to 0)
#[derive(Debug)]
pub struct ExtDimacsFormula {
    /// Number of variables declared
    pub num_vars: usize,
    /// Number of clauses declared (CNF only, not XOR)
    pub num_clauses: usize,
    /// The CNF clauses
    pub clauses: Vec<Vec<Literal>>,
    /// The XOR constraints
    pub xors: Vec<XorConstraint>,
}

impl ExtDimacsFormula {
    /// Create a solver with XOR extension from this formula.
    ///
    /// Applies adaptive inprocessing gating based on syntactic features
    /// of the CNF portion. This matches the adaptive gating applied by
    /// the DIMACS entry point in `z4-sat`.
    ///
    /// Returns the solver and optionally an XOR extension if there are XOR constraints.
    pub fn into_solver_with_xor(self) -> (z4_sat::Solver, Option<XorExtension>) {
        // Extract features before moving clauses into the solver.
        let features =
            z4_sat::SatFeatures::extract(self.num_vars, &self.clauses);
        let class = z4_sat::InstanceClass::classify(&features);

        let mut solver = z4_sat::Solver::new(self.num_vars);

        // Apply adaptive inprocessing adjustments.
        let mut profile = solver.inprocessing_feature_profile();
        if z4_sat::adjust_features_for_instance(&features, &class, &mut profile) {
            solver.set_condition_enabled(profile.condition);
            solver.set_symmetry_enabled(profile.symmetry);
            solver.set_bce_enabled(profile.bce);
        }
        if z4_sat::should_disable_reorder(&features, &class) {
            solver.set_reorder_enabled(false);
        }

        for clause in self.clauses {
            solver.add_clause(clause);
        }

        let xor_ext = if self.xors.is_empty() {
            None
        } else {
            Some(XorExtension::new(self.xors))
        };

        (solver, xor_ext)
    }

    /// Solve this formula using XOR-aware solving.
    pub fn solve(self) -> z4_sat::VerifiedSatResult {
        let (mut solver, xor_ext) = self.into_solver_with_xor();

        match xor_ext {
            Some(mut ext) => solver.solve_with_extension(&mut ext),
            None => solver.solve(),
        }
    }
}

/// Convert a raw i32 DIMACS literal to a 0-indexed Literal.
fn dimacs_lit_to_literal(lit: i32) -> Literal {
    let var = lit.unsigned_abs();
    let variable = Variable::new(var - 1);
    if lit > 0 {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    }
}

/// Convert raw i32 XOR values to an XorConstraint.
///
/// Each value is a signed literal: positive contributes its variable,
/// negative contributes its variable AND flips the RHS.
/// Variables are converted from 1-indexed DIMACS to 0-indexed.
fn xor_values_to_constraint(values: &[i32], max_var: u32) -> Result<XorConstraint, ExtDimacsError> {
    let mut vars = Vec::new();
    let mut rhs = true; // Default: odd parity (XOR = 1)

    for &lit_val in values {
        let var = lit_val.unsigned_abs();
        if var > max_var {
            return Err(ExtDimacsError::VariableOutOfRange { var, max: max_var });
        }
        // DIMACS is 1-indexed
        vars.push(var - 1);
        // Negative literal flips the RHS
        if lit_val < 0 {
            rhs = !rhs;
        }
    }

    if vars.is_empty() {
        return Err(ExtDimacsError::InvalidXor(
            "empty XOR constraint".to_string(),
        ));
    }

    Ok(XorConstraint::new(vars, rhs))
}

/// Parse an extended DIMACS file with XOR support.
///
/// This parser handles both standard DIMACS CNF and CryptoMiniSat's XOR extension.
///
/// # XOR Syntax
///
/// XOR lines start with `x` followed by literals and terminated by `0`:
/// - `x1 2 3 0` - means x1 XOR x2 XOR x3 = 1 (default: odd parity required)
/// - `x-1 0` - means x1 = 0 (single negated var means var must be false)
/// - `x1 -2 3 0` - means x1 XOR x2 XOR x3 = 0 (one negation flips the parity)
///
/// The RHS is computed as: start with 1 (odd parity), flip for each negative literal.
///
/// # Example
///
/// ```
/// use z4_xor::parse_ext_dimacs_str;
///
/// let input = r"
/// p cnf 3 0
/// x1 2 0
/// x2 3 0
/// ";
///
/// let formula = parse_ext_dimacs_str(input).unwrap();
/// assert_eq!(formula.xors.len(), 2);
/// assert!(formula.clauses.is_empty());
/// ```
pub fn parse_ext_dimacs<R: std::io::Read>(reader: R) -> Result<ExtDimacsFormula, ExtDimacsError> {
    let (header, records) = dimacs_core::parse_dimacs_records(reader)?;
    let max_var = header.num_vars as u32;

    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    let mut xors: Vec<XorConstraint> = Vec::new();

    for record in records {
        match record {
            DimacsRecord::Clause(raw) => {
                if !raw.is_empty() {
                    let clause: Vec<Literal> =
                        raw.iter().map(|&l| dimacs_lit_to_literal(l)).collect();
                    clauses.push(clause);
                }
            }
            DimacsRecord::Tagged { tag: 'x', values } => {
                let xor = xor_values_to_constraint(&values, max_var)?;
                xors.push(xor);
            }
            DimacsRecord::Tagged { tag, .. } => {
                return Err(ExtDimacsError::InvalidLiteral(format!(
                    "unexpected tagged line '{tag}' in extended DIMACS input"
                )));
            }
            _ => {
                return Err(ExtDimacsError::InvalidLiteral(
                    "unexpected record type in extended DIMACS input".to_string(),
                ));
            }
        }
    }

    Ok(ExtDimacsFormula {
        num_vars: header.num_vars,
        num_clauses: header.num_clauses,
        clauses,
        xors,
    })
}

/// Parse an extended DIMACS formula from a string.
///
/// See `parse_ext_dimacs` for format details.
pub fn parse_ext_dimacs_str(input: &str) -> Result<ExtDimacsFormula, ExtDimacsError> {
    parse_ext_dimacs(input.as_bytes())
}

/// Write an extended DIMACS formula with XOR constraints.
///
/// Outputs both CNF clauses and XOR constraints in CryptoMiniSat format.
pub fn write_ext_dimacs<W: std::io::Write>(
    writer: &mut W,
    num_vars: usize,
    clauses: &[Vec<Literal>],
    xors: &[XorConstraint],
) -> std::io::Result<()> {
    // Note: num_clauses in header is CNF only (XORs are extensions)
    writeln!(writer, "p cnf {} {}", num_vars, clauses.len())?;

    // Write CNF clauses
    for clause in clauses {
        for lit in clause {
            // Convert back to 1-indexed DIMACS format
            let var = lit.variable().id() as i32 + 1;
            let dimacs_lit = if lit.is_positive() { var } else { -var };
            write!(writer, "{dimacs_lit} ")?;
        }
        writeln!(writer, "0")?;
    }

    // Write XOR constraints
    for xor in xors {
        write!(writer, "x")?;
        // First variable determines base polarity
        // If rhs=true (odd parity), first var is positive
        // If rhs=false (even parity), first var is negative
        let mut first = true;
        for &var in &xor.vars {
            // Convert to 1-indexed
            let dimacs_var = var as i32 + 1;
            if first && !xor.rhs {
                // First variable negative to indicate even parity
                write!(writer, "-{dimacs_var} ")?;
            } else {
                write!(writer, "{dimacs_var} ")?;
            }
            first = false;
        }
        writeln!(writer, "0")?;
    }

    Ok(())
}

/// Solve an extended DIMACS file with XOR constraints.
///
/// Convenience function to parse and solve in one step.
pub fn solve_ext_dimacs<R: std::io::Read>(
    reader: R,
) -> Result<z4_sat::VerifiedSatResult, ExtDimacsError> {
    let formula = parse_ext_dimacs(reader)?;
    Ok(formula.solve())
}

/// Solve an extended DIMACS formula from a string.
pub fn solve_ext_dimacs_str(input: &str) -> Result<z4_sat::VerifiedSatResult, ExtDimacsError> {
    solve_ext_dimacs(input.as_bytes())
}
