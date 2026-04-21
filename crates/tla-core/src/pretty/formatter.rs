// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Width-aware TLA+ formatter.
//!
//! This module provides `TlaFormatter`, which produces well-formatted TLA+
//! output from an AST, handling:
//! - Configurable indentation (2 or 4 spaces)
//! - Aligned conjunction (`/\`) and disjunction (`\/`) lists
//! - Multi-line CASE expressions with aligned arms
//! - Proper LET/IN block indentation
//! - Width-aware line breaking for long expressions

use super::config::FormatConfig;
use super::PrettyPrinter;
use crate::ast::{Expr, Module};

/// A width-aware TLA+ formatter that produces idiomatic TLA+ output.
pub struct TlaFormatter {
    config: FormatConfig,
}

impl Default for TlaFormatter {
    fn default() -> Self {
        Self::new(FormatConfig::default())
    }
}

impl TlaFormatter {
    /// Create a new formatter with the given configuration.
    pub fn new(config: FormatConfig) -> Self {
        Self { config }
    }

    /// Format a module to a string.
    pub fn format_module(&self, module: &Module) -> String {
        let mut pp = FormattingPrinter::new(&self.config);
        pp.print_module(module);
        pp.finish()
    }

    /// Format a single expression to a string.
    pub fn format_expr(&self, expr: &Expr) -> String {
        let mut pp = FormattingPrinter::new(&self.config);
        pp.print_expr(expr);
        pp.finish()
    }
}

/// Internal printer state that tracks column position for width-aware breaking.
pub(super) struct FormattingPrinter<'c> {
    config: &'c FormatConfig,
    output: String,
    indent: usize,
    /// Current column position (0-based) for width-aware line breaking.
    col: usize,
}

impl<'c> FormattingPrinter<'c> {
    pub(super) fn new(config: &'c FormatConfig) -> Self {
        Self {
            config,
            output: String::new(),
            indent: 0,
            col: 0,
        }
    }

    pub(super) fn finish(self) -> String {
        self.output
    }

    pub(super) fn write(&mut self, s: &str) {
        self.output.push_str(s);
        // Track column: only count characters after last newline
        if let Some(pos) = s.rfind('\n') {
            self.col = s.len() - pos - 1;
        } else {
            self.col += s.len();
        }
    }

    pub(super) fn newline(&mut self) {
        self.output.push('\n');
        self.col = 0;
    }

    pub(super) fn write_indent(&mut self) {
        let indent_str = self.config.indent_str();
        for _ in 0..self.indent {
            self.output.push_str(&indent_str);
        }
        self.col = self.indent * self.config.indent_width;
    }

    /// Write N spaces (for custom alignment).
    pub(super) fn write_spaces(&mut self, n: usize) {
        for _ in 0..n {
            self.output.push(' ');
        }
        self.col += n;
    }

    pub(super) fn indent(&mut self) {
        self.indent += 1;
    }

    pub(super) fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    pub(super) fn push_char(&mut self, c: char) {
        self.output.push(c);
        if c == '\n' {
            self.col = 0;
        } else {
            self.col += 1;
        }
    }

    /// Returns the current column position.
    pub(super) fn current_col(&self) -> usize {
        self.col
    }

    /// Returns the configured max width.
    pub(super) fn max_width(&self) -> usize {
        self.config.max_width
    }

    /// Estimate the width of an expression when printed on a single line.
    /// Used to decide whether to break to multi-line.
    pub(super) fn estimate_expr_width(expr: &Expr) -> usize {
        // Use the basic PrettyPrinter to get single-line width
        let mut pp = PrettyPrinter::new();
        pp.print_expr(expr);
        pp.finish().len()
    }
}
