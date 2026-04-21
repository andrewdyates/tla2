// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;
use std::io::Write;

use ariadne::{Color, ColorGenerator, Label, Report, ReportKind, Source};

use super::types::{Diagnostic, LabelColor, Severity};

/// A source file cache for ariadne rendering
pub(crate) struct SourceCache {
    /// Map from file path to source content
    files: HashMap<String, Source<String>>,
}

impl SourceCache {
    /// Create a new empty source cache
    pub(crate) fn new() -> Self {
        Self {
            files: HashMap::new(),
        }
    }

    /// Add a source file to the cache
    pub(crate) fn add(&mut self, path: impl Into<String>, source: impl Into<String>) {
        let path = path.into();
        let source = source.into();
        self.files.insert(path, Source::from(source));
    }

    /// Get a source from the cache
    pub(crate) fn get(&self, path: &str) -> Option<&Source<String>> {
        self.files.get(path)
    }
}

impl Default for SourceCache {
    fn default() -> Self {
        Self::new()
    }
}

impl Diagnostic {
    /// Render this diagnostic to a writer
    pub(crate) fn render(
        &self,
        file_path: &str,
        source: &str,
        writer: &mut impl Write,
    ) -> std::io::Result<()> {
        let kind = match self.severity {
            Severity::Error => ReportKind::Error,
            Severity::Warning => ReportKind::Warning,
            Severity::Info => ReportKind::Advice,
        };

        let primary_offset = self.span.as_ref().map_or(0, |s| s.start);

        let mut builder =
            Report::build(kind, file_path, primary_offset).with_message(&self.message);

        let mut colors = ColorGenerator::new();

        // Add the primary span label
        if let Some(ref span) = self.span {
            let label = Label::new((file_path, span.start..span.end))
                .with_color(Color::Red)
                .with_order(0);
            let label = if let Some(ref text) = span.label {
                label.with_message(text)
            } else {
                label
            };
            builder = builder.with_label(label);
        }

        // Add secondary labels
        for (i, lab) in self.labels.iter().enumerate() {
            let color = match lab.color {
                LabelColor::Primary => Color::Red,
                LabelColor::Secondary => colors.next(),
                LabelColor::Info => Color::Cyan,
            };
            builder = builder.with_label(
                Label::new((file_path, lab.start..lab.end))
                    .with_color(color)
                    .with_message(&lab.text)
                    .with_order((i + 1) as i32),
            );
        }

        // Add help text
        if let Some(ref help) = self.help {
            builder = builder.with_help(help);
        }

        // Add note
        if let Some(ref note) = self.note {
            builder = builder.with_note(note);
        }

        let report = builder.finish();

        // Write with the source
        report.write((file_path, Source::from(source)), writer)
    }

    /// Render this diagnostic to stderr
    pub fn eprint(&self, file_path: &str, source: &str) {
        let mut buf = Vec::new();
        let _ = self.render(file_path, source, &mut buf);
        let _ = std::io::stderr().write_all(&buf);
    }
}
