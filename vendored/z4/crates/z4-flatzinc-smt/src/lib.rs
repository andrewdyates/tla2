// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc to SMT-LIB2 translation crate for MiniZinc Challenge entry

// deny rather than forbid: solver.rs:poll_readable needs libc::poll (#6231).
#![deny(unsafe_code)]

pub mod branching;
mod builtins;
mod builtins_extra;
pub mod error;
mod globals;
mod globals_count;
mod globals_extra;
mod globals_regular;
pub mod output;
mod resolve;
pub mod search;
mod set_constraints;
mod set_constraints_reif;
pub mod solver;
pub(crate) mod translate;

pub use branching::solve_branching;
pub use error::TranslateError;
pub use output::format_dzn_solution;
pub use search::{
    flatten_search_vars, parse_search_annotations, SearchAnnotation, SearchStrategy, ValChoice,
    VarChoice,
};
pub use solver::{solve, SolverConfig, SolverError};
pub use translate::{translate, ObjectiveInfo, OutputVarInfo, TranslationResult, VarDomain};

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_error;
#[cfg(test)]
mod tests_extended;
#[cfg(test)]
mod tests_globals;
#[cfg(test)]
mod tests_globals_extra;
#[cfg(test)]
mod tests_set_constraints;
#[cfg(test)]
mod z4_library_bench;
