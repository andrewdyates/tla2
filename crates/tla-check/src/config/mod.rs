// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC Configuration file (.cfg) parser
//!
//! TLC uses configuration files to specify:
//! - INIT: The initial state predicate
//! - NEXT: The next-state relation
//! - INVARIANT: Safety properties to check
//! - PROPERTY: Temporal properties to check
//! - CONSTANT: Constant assignments and model values
//! - SYMMETRY: Symmetry sets for state reduction
//! - CONSTRAINT: State constraints (limits search space)
//! - ACTION_CONSTRAINT: Action constraints
//! - VIEW: Expression to use for state fingerprinting (reduces state space)
//!
//! # Example .cfg file
//!
//! ```text
//! INIT Init
//! NEXT Next
//! INVARIANT TypeOK
//! INVARIANT Safety
//! PROPERTY Liveness
//! CONSTANT N = 3
//! CONSTANT Procs = {p1, p2, p3}
//! CONSTANT Procs <- [ model value ]
//! ```

mod constants;
mod init_mode;
mod parse;
mod policy;
mod serialize;
mod types;

#[cfg(test)]
mod tests;

pub use init_mode::InitMode;
pub(crate) use types::ConfigValidationIssue;
pub use types::{Config, ConfigError, ConstantValue, LivenessExecutionMode, TerminalSpec};
