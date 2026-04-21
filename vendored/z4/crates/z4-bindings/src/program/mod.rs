// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Z4 Program - container for verification constraints.
//!
//! A Z4Program represents a complete verification problem that can be
//! serialized to SMT-LIB2 format and solved by Z4 or other SMT solvers.
//!
//! ## Usage
//!
//! ```rust
//! use z4_bindings::{Expr, Sort, Z4Program};
//!
//! let mut program = Z4Program::qf_bv();
//!
//! // Declare variables
//! let x = program.declare_const("x", Sort::bv32());
//! let y = program.declare_const("y", Sort::bv32());
//!
//! // Add constraint: x + y == 10
//! let sum = x.bvadd(y);
//! let ten = Expr::bitvec_const(10i32, 32);
//! program.assert(sum.eq(ten));
//!
//! // Check satisfiability
//! program.check_sat();
//!
//! // Serialize to SMT-LIB2
//! let _smt2 = program.to_string();
//! ```

mod builder;
mod commands;
mod constructors;
mod declarations;
mod horn;
mod reset;

#[cfg(test)]
mod tests;

pub use builder::ProgramBuilder;

use crate::constraint::Constraint;
use crate::sort::{DatatypeSort, Sort};
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

/// A Z4 verification program.
///
/// Contains all declarations, assertions, and commands needed for verification.
#[derive(Debug, Clone)]
pub struct Z4Program {
    /// The SMT-LIB2 logic to use.
    pub(crate) logic: Option<String>,

    /// Solver options.
    pub(crate) options: Vec<(String, String)>,

    /// The sequence of commands/constraints.
    pub(crate) commands: Vec<Constraint>,

    /// Variable declarations (for tracking declared names).
    pub(crate) declared_vars: HashMap<String, Sort>,

    /// Function declarations (for restoration after clear_commands).
    pub(crate) declared_funs: Vec<(String, Vec<Sort>, Sort)>,

    /// Declared datatype definitions (full definitions for restoration, keyed by name).
    pub(crate) declared_datatypes: HashMap<String, DatatypeSort>,

    /// Declared CHC relations (for restoration after clear_commands).
    pub(crate) declared_rels: Vec<(String, Vec<Sort>)>,

    /// Declared CHC variables (for restoration after clear_commands).
    pub(crate) declared_chc_vars: Vec<(String, Sort)>,

    /// Current context level (for push/pop tracking).
    pub(crate) context_level: u32,
}

impl Default for Z4Program {
    fn default() -> Self {
        Self::new()
    }
}

impl Display for Z4Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Write options first
        for (name, value) in &self.options {
            writeln!(f, "(set-option :{name} {value})")?;
        }

        // Write logic if set
        if let Some(ref logic) = self.logic {
            writeln!(f, "(set-logic {logic})")?;
        }

        // Write all commands
        for cmd in &self.commands {
            writeln!(f, "{cmd}")?;
        }

        Ok(())
    }
}
