// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z4-backed Init state enumeration using ALL-SAT with blocking clauses.
//!
//! Supports finite membership domains, arithmetic constraints, and quantified
//! finite domains that benefit from symbolic solving over brute-force search.
//! Part of #251.

use std::sync::Arc;

mod model;
mod type_inference;
mod value_convert;

#[cfg(feature = "z4")]
mod enumerate;

#[cfg(feature = "z4")]
pub(crate) use enumerate::enumerate_init_states_z4;

#[cfg(all(test, feature = "z4"))]
use self::type_inference::{infer_sort_from_expr, infer_sort_from_set};

pub(crate) use value_convert::extract_var_name;

/// Result type for z4 enumeration operations
pub(crate) type Z4EnumResult<T> = Result<T, Z4EnumError>;

/// Errors that can occur during z4-based enumeration
#[derive(Debug)]
pub(crate) enum Z4EnumError {
    /// Failed to translate Init predicate to z4
    TranslationFailed(String),
    /// z4 solver returned unknown (unclassified or incomplete)
    SolverUnknown,
    /// z4 solver timed out (Part of #2826)
    SolverTimeout,
    /// z4 solver panicked or produced a typed failure (Part of #2826)
    SolverFailed(String),
    /// Exceeded maximum number of solutions
    MaxSolutionsExceeded(usize),
    /// Variable type not supported for z4 translation
    UnsupportedVarType { var: String, reason: String },
    /// z4 returned invalid model
    InvalidModel(String),
}

impl std::fmt::Display for Z4EnumError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Z4EnumError::TranslationFailed(msg) => {
                write!(f, "failed to translate Init to z4: {}", msg)
            }
            Z4EnumError::SolverUnknown => write!(f, "z4 solver returned unknown"),
            Z4EnumError::SolverTimeout => write!(f, "z4 solver timed out"),
            Z4EnumError::SolverFailed(msg) => {
                write!(f, "z4 solver failed: {}", msg)
            }
            Z4EnumError::MaxSolutionsExceeded(n) => {
                write!(f, "exceeded maximum solutions limit ({})", n)
            }
            Z4EnumError::UnsupportedVarType { var, reason } => {
                write!(f, "variable '{}' not supported for z4: {}", var, reason)
            }
            Z4EnumError::InvalidModel(msg) => write!(f, "invalid z4 model: {}", msg),
        }
    }
}

impl std::error::Error for Z4EnumError {}

/// Configuration for z4-based Init enumeration
#[derive(Debug, Clone)]
pub(crate) struct Z4EnumConfig {
    /// Maximum number of solutions to enumerate (default: 1_000_000)
    pub(crate) max_solutions: usize,
    /// Timeout for each solver `check_sat` call (Part of #2826).
    /// `None` means no timeout (default).
    pub(crate) solve_timeout: Option<std::time::Duration>,
    /// Enable debug output
    pub(crate) debug: bool,
}

impl Default for Z4EnumConfig {
    fn default() -> Self {
        Z4EnumConfig {
            max_solutions: 1_000_000,
            solve_timeout: None,
            debug: debug_z4_enabled(),
        }
    }
}

debug_flag!(debug_z4_enabled, "TLA2_DEBUG_Z4");

/// Information about a state variable for z4 translation
#[derive(Debug, Clone)]
pub(crate) struct VarInfo {
    /// Variable name
    pub(crate) name: Arc<str>,
    /// Inferred sort (Int, Bool, or Function)
    pub(crate) sort: VarSort,
    /// For function types: domain elements as strings
    pub(crate) domain_keys: Option<Vec<String>>,
}

/// Variable sort for z4 translation
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VarSort {
    /// Boolean variable
    Bool,
    /// Integer variable
    Int,
    /// String variable with finite domain
    String {
        /// Finite domain of string values
        domain: Vec<String>,
    },
    /// Function with finite domain
    Function {
        /// Domain element keys
        domain_keys: Vec<String>,
        /// Range sort
        range: Box<VarSort>,
    },
    /// Tuple with fixed element sorts (1-indexed)
    Tuple {
        /// Sort of each element (index 0 = element 1, etc.)
        element_sorts: Vec<VarSort>,
    },
    /// Heterogeneous set - cannot be represented in z4
    /// This is set when SetEnum contains mixed types (e.g., {1, "a"})
    /// Part of #523: soundness fix for heterogeneous SetEnum
    Heterogeneous {
        /// Description of why this is heterogeneous
        reason: String,
    },
}

/// Check if z4 enumeration is available (feature enabled)
pub(crate) fn z4_available() -> bool {
    cfg!(feature = "z4")
}

#[cfg(test)]
#[cfg(feature = "z4")]
mod tests;
