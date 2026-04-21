// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 parsing bridge.

use z4_frontend::Command;

use crate::api::types::{SolverError, Term};
use crate::api::Solver;

impl Solver {
    /// Parse an SMT-LIB2 string, executing declarations and assertions.
    ///
    /// Processes `declare-fun`, `declare-const`, `define-fun`, `assert`, `push`,
    /// `pop`, and `set-logic` commands. Skips `check-sat`, `get-model`, and
    /// other query commands.
    ///
    /// Returns the assertions added during parsing as `Vec<Term>`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::ParseError`] if parsing fails, or other errors
    /// if command execution fails.
    pub fn parse_smtlib2(&mut self, input: &str) -> Result<Vec<Term>, SolverError> {
        let commands = z4_frontend::parse(input).map_err(|e| SolverError::InvalidArgument {
            operation: "parse_smtlib2",
            message: format!("{e}"),
        })?;

        let before = self.executor.context().assertions.len();

        for cmd in &commands {
            match cmd {
                // Skip query commands — only process declarations and assertions
                Command::CheckSat
                | Command::CheckSatAssuming(_)
                | Command::GetModel
                | Command::GetValue(_)
                | Command::GetUnsatCore
                | Command::GetUnsatAssumptions
                | Command::GetProof
                | Command::GetAssertions
                | Command::GetAssignment
                | Command::GetInfo(_)
                | Command::GetOption(_)
                | Command::GetObjectives
                | Command::Echo(_)
                | Command::Exit => continue,
                _ => {
                    self.executor.execute(cmd)?;
                }
            }
        }

        let after = self.executor.context().assertions.len();
        let new_assertions: Vec<Term> = self.executor.context().assertions[before..after]
            .iter()
            .map(|tid| Term(*tid))
            .collect();

        Ok(new_assertions)
    }
}
