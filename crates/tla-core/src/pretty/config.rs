// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Configuration for the TLA+ pretty printer / formatter.

/// Configuration controlling TLA+ formatting output.
#[derive(Debug, Clone)]
pub struct FormatConfig {
    /// Number of spaces per indentation level (default: 2).
    pub indent_width: usize,
    /// Target maximum line width before breaking expressions (default: 80).
    pub max_width: usize,
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self {
            indent_width: 2,
            max_width: 80,
        }
    }
}

impl FormatConfig {
    /// Create a config with the given indent width.
    #[must_use]
    pub fn with_indent_width(mut self, width: usize) -> Self {
        self.indent_width = width;
        self
    }

    /// Create a config with the given max line width.
    #[must_use]
    pub fn with_max_width(mut self, width: usize) -> Self {
        self.max_width = width;
        self
    }

    /// Return a string of spaces for one indentation level.
    pub(super) fn indent_str(&self) -> String {
        " ".repeat(self.indent_width)
    }
}
