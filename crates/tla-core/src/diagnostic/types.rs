// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

/// A diagnostic that can be rendered with ariadne
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// The severity of this diagnostic
    pub severity: Severity,
    /// The main error message
    pub message: String,
    /// The primary span (highlighted in red)
    pub span: Option<DiagnosticSpan>,
    /// Additional labels (notes, hints, related locations)
    pub labels: Vec<DiagnosticLabel>,
    /// Help text shown at the bottom
    pub help: Option<String>,
    /// Note text shown at the bottom
    pub note: Option<String>,
}

/// Diagnostic severity
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Info,
}

/// A span for diagnostic display
#[derive(Debug, Clone)]
pub struct DiagnosticSpan {
    /// File path
    pub file: String,
    /// Start byte offset
    pub start: usize,
    /// End byte offset
    pub end: usize,
    /// Optional label text
    pub label: Option<String>,
}

/// An additional label on a diagnostic
#[derive(Debug, Clone)]
pub struct DiagnosticLabel {
    /// File path
    pub file: String,
    /// Start byte offset
    pub start: usize,
    /// End byte offset
    pub end: usize,
    /// Label text
    pub text: String,
    /// Label color
    pub color: LabelColor,
}

/// Color for a diagnostic label
#[derive(Debug, Clone, Copy)]
pub enum LabelColor {
    Primary,
    Secondary,
    Info,
}

impl Diagnostic {
    /// Create a new error diagnostic
    pub(crate) fn error(message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            message: message.into(),
            span: None,
            labels: Vec::new(),
            help: None,
            note: None,
        }
    }

    /// Set the primary span
    pub(crate) fn with_span(mut self, file: impl Into<String>, start: usize, end: usize) -> Self {
        self.span = Some(DiagnosticSpan {
            file: file.into(),
            start,
            end,
            label: None,
        });
        self
    }

    /// Set the primary span with a label
    pub(crate) fn with_span_label(
        mut self,
        file: impl Into<String>,
        start: usize,
        end: usize,
        label: impl Into<String>,
    ) -> Self {
        self.span = Some(DiagnosticSpan {
            file: file.into(),
            start,
            end,
            label: Some(label.into()),
        });
        self
    }

    /// Add a secondary label
    pub(crate) fn with_label(
        mut self,
        file: impl Into<String>,
        start: usize,
        end: usize,
        text: impl Into<String>,
    ) -> Self {
        self.labels.push(DiagnosticLabel {
            file: file.into(),
            start,
            end,
            text: text.into(),
            color: LabelColor::Secondary,
        });
        self
    }

    /// Add help text
    pub(crate) fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    /// Add a note
    pub(crate) fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }
}
