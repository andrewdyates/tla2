// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error types for tla-core

use crate::span::Span;
use thiserror::Error;

/// Result type for tla-core operations
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during parsing or analysis
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Error {
    #[error("Syntax error: {message}")]
    Syntax { message: String, span: Span },

    #[error("Undefined name: {name}")]
    UndefinedName { name: String, span: Span },

    #[error("Duplicate definition: {name}")]
    DuplicateDefinition {
        name: String,
        original: Span,
        duplicate: Span,
    },

    #[error("Type error: {message}")]
    Type { message: String, span: Span },

    #[error("Arity mismatch: expected {expected} arguments, got {got}")]
    ArityMismatch {
        expected: usize,
        got: usize,
        span: Span,
    },

    #[error("Module not found: {name}")]
    ModuleNotFound { name: String, span: Span },

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}
