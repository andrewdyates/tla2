// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error types for name resolution.

use super::types::SymbolKind;
use crate::span::Span;

/// Error during name resolution
#[derive(Debug, Clone)]
pub struct ResolveError {
    /// Error kind
    pub kind: ResolveErrorKind,
    /// Span where error occurred
    pub span: Span,
}

/// Kinds of resolution errors
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ResolveErrorKind {
    /// Reference to undefined identifier
    Undefined { name: String },
    /// Duplicate definition in same scope
    Duplicate { name: String, first_def: Span },
    /// Conflicting operator arity between imported definitions.
    ///
    /// TLC treats same-kind duplicate symbols as a warning only if their arity matches; otherwise,
    /// it is an error.
    ImportedOperatorArityConflict {
        name: String,
        first_def: Span,
        first_arity: usize,
        second_arity: usize,
    },
    /// Wrong arity in operator application
    ArityMismatch {
        name: String,
        expected: usize,
        got: usize,
    },
    /// Using variable where operator expected (or vice versa)
    KindMismatch {
        name: String,
        expected: SymbolKind,
        got: SymbolKind,
    },
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ResolveErrorKind::Undefined { name } => {
                write!(f, "undefined identifier `{name}`")
            }
            ResolveErrorKind::Duplicate { name, .. } => {
                write!(f, "duplicate definition of `{name}`")
            }
            ResolveErrorKind::ImportedOperatorArityConflict {
                name,
                first_arity,
                second_arity,
                ..
            } => {
                write!(
                    f,
                    "conflicting definitions of operator `{name}` (arity {first_arity} vs {second_arity})"
                )
            }
            ResolveErrorKind::ArityMismatch {
                name,
                expected,
                got,
            } => {
                write!(
                    f,
                    "operator `{name}` expects {expected} arguments, got {got}"
                )
            }
            ResolveErrorKind::KindMismatch {
                name,
                expected,
                got,
            } => {
                write!(f, "`{name}` is a {got:?}, expected {expected:?}")
            }
        }
    }
}

impl std::error::Error for ResolveError {}
