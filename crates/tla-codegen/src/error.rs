// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed error types for the TLA+ code generator.

use crate::types::TypeInferError;

/// Errors produced during TLA+ to Rust code generation.
#[derive(Debug, thiserror::Error)]
pub enum CodegenError {
    /// Type inference failed with one or more errors.
    #[error("type inference errors:\n{}", .0.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n"))]
    TypeInference(Vec<TypeInferError>),

    /// Invalid combination of code generation options.
    #[error("checker_map requires generate_checker")]
    CheckerMapRequiresChecker,

    /// Checker map module name does not match the module being generated.
    #[error("checker map module mismatch: config spec.module={config_module:?}, generating module {actual_module:?}")]
    CheckerMapModuleMismatch {
        config_module: String,
        actual_module: String,
    },

    /// Checker map has no `[[impls]]` entries.
    #[error("checker map has no [[impls]] entries")]
    CheckerMapNoImpls,

    /// Checker map has a duplicate field mapping.
    #[error("checker map impls[{index}] duplicate mapping for state field {field:?}: {prev:?} vs {current:?}")]
    CheckerMapDuplicateField {
        index: usize,
        field: String,
        prev: String,
        current: String,
    },

    /// Checker map references unknown state field(s).
    #[error("checker map impls[{index}] has unknown state field(s): {unknown} (expected keys: {expected})")]
    CheckerMapUnknownFields {
        index: usize,
        unknown: String,
        expected: String,
    },

    /// Checker map is missing a required field mapping.
    #[error("checker map impls[{index}] missing mapping for state field {field:?}")]
    CheckerMapMissingField { index: usize, field: String },

    /// Input validation failure for user-supplied Rust fragments (injection prevention).
    #[error("{context}: {reason}")]
    InvalidRustFragment { context: String, reason: String },
}
