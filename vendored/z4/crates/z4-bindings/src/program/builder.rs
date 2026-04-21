// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! ProgramBuilder — fluent API for constructing Z4 programs.

use super::Z4Program;

/// Builder for creating Z4 programs with a fluent API.
#[derive(Debug)]
pub struct ProgramBuilder {
    program: Z4Program,
}

impl ProgramBuilder {
    /// Create a new program builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            program: Z4Program::new(),
        }
    }

    /// Set the logic.
    #[must_use = "builders return the modified builder"]
    pub fn logic(mut self, logic: impl Into<String>) -> Self {
        self.program.set_logic(logic);
        self
    }

    /// Set an option.
    #[must_use = "builders return the modified builder"]
    pub fn option(mut self, name: impl Into<String>, value: impl Into<String>) -> Self {
        self.program.set_option(name, value);
        self
    }

    /// Enable model production.
    #[must_use = "builders return the modified builder"]
    pub fn with_models(mut self) -> Self {
        self.program.produce_models();
        self
    }

    /// Enable unsat core production.
    #[must_use = "builders return the modified builder"]
    pub fn with_unsat_cores(mut self) -> Self {
        self.program.produce_unsat_cores();
        self
    }

    /// Build the program.
    #[must_use]
    pub fn build(self) -> Z4Program {
        self.program
    }
}

impl Default for ProgramBuilder {
    fn default() -> Self {
        Self::new()
    }
}
