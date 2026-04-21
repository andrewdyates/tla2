// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::span::Span;

use super::types::Diagnostic;

/// Create a diagnostic from a parse error
pub fn parse_error_diagnostic(file_path: &str, message: &str, start: u32, end: u32) -> Diagnostic {
    Diagnostic::error(format!("syntax error: {message}")).with_span_label(
        file_path,
        start as usize,
        end as usize,
        "here",
    )
}

/// Create a diagnostic from a lower error
pub fn lower_error_diagnostic(file_path: &str, message: &str, span: Span) -> Diagnostic {
    Diagnostic::error(format!("semantic error: {message}")).with_span_label(
        file_path,
        span.start as usize,
        span.end as usize,
        "here",
    )
}

/// Create a diagnostic from an undefined name error
pub(crate) fn undefined_name_diagnostic(file_path: &str, name: &str, span: Span) -> Diagnostic {
    Diagnostic::error(format!("undefined name: {name}"))
        .with_span_label(
            file_path,
            span.start as usize,
            span.end as usize,
            format!("'{name}' is not defined"),
        )
        .with_help("Check the spelling, or add a definition for this name")
}

/// Create a diagnostic from a duplicate definition error
pub(crate) fn duplicate_definition_diagnostic(
    file_path: &str,
    name: &str,
    original: Span,
    duplicate: Span,
) -> Diagnostic {
    Diagnostic::error(format!("duplicate definition: {name}"))
        .with_span_label(
            file_path,
            duplicate.start as usize,
            duplicate.end as usize,
            format!("'{name}' defined again here"),
        )
        .with_label(
            file_path,
            original.start as usize,
            original.end as usize,
            "first definition here",
        )
        .with_help("Remove one of the definitions or rename one")
}

/// Create a diagnostic from an arity mismatch error
pub(crate) fn arity_mismatch_diagnostic(
    file_path: &str,
    expected: usize,
    got: usize,
    span: Span,
) -> Diagnostic {
    let message = if expected == 1 {
        format!("expected {expected} argument, found {got}")
    } else {
        format!("expected {expected} arguments, found {got}")
    };

    Diagnostic::error(format!("arity mismatch: {message}"))
        .with_span_label(file_path, span.start as usize, span.end as usize, message)
        .with_help("Check the operator definition for the correct number of arguments")
}

/// Create a diagnostic from a type error
pub(crate) fn type_error_diagnostic(file_path: &str, message: &str, span: Span) -> Diagnostic {
    Diagnostic::error(format!("type error: {message}")).with_span_label(
        file_path,
        span.start as usize,
        span.end as usize,
        "type mismatch here",
    )
}

/// Create a diagnostic from a module not found error
pub(crate) fn module_not_found_diagnostic(
    file_path: &str,
    module_name: &str,
    span: Span,
) -> Diagnostic {
    Diagnostic::error(format!("module not found: {module_name}"))
        .with_span_label(
            file_path,
            span.start as usize,
            span.end as usize,
            format!("cannot find module '{module_name}'"),
        )
        .with_help("Check the module name and ensure the file exists")
}

/// Convert a core Error to a Diagnostic
impl crate::Error {
    /// Convert this error to a diagnostic
    pub(crate) fn to_diagnostic(&self, file_path: &str) -> Diagnostic {
        match self {
            crate::Error::Syntax { message, span } => {
                parse_error_diagnostic(file_path, message, span.start, span.end)
            }
            crate::Error::UndefinedName { name, span } => {
                undefined_name_diagnostic(file_path, name, *span)
            }
            crate::Error::DuplicateDefinition {
                name,
                original,
                duplicate,
            } => duplicate_definition_diagnostic(file_path, name, *original, *duplicate),
            crate::Error::Type { message, span } => {
                type_error_diagnostic(file_path, message, *span)
            }
            crate::Error::ArityMismatch {
                expected,
                got,
                span,
            } => arity_mismatch_diagnostic(file_path, *expected, *got, *span),
            crate::Error::ModuleNotFound { name, span } => {
                module_not_found_diagnostic(file_path, name, *span)
            }
            crate::Error::Io(err) => Diagnostic::error(format!("I/O error: {err}")),
        }
    }
}
