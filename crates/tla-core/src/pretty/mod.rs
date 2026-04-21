// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pretty printer for TLA+ AST
//!
//! Converts AST back to TLA+ source code. Used for:
//! - Roundtrip testing (parse -> AST -> pretty print -> compare)
//! - Code generation
//! - Error message context
//!
//! Two printer modes are available:
//! - **`PrettyPrinter`** — compact single-line output (used for error messages,
//!   internal AST dumps). Accessed via `pretty_module()` / `pretty_expr()`.
//! - **`TlaFormatter`** — width-aware formatter that produces idiomatic TLA+
//!   with aligned conjunction/disjunction lists, multi-line CASE expressions,
//!   proper LET/IN indentation, and configurable indent width. Accessed via
//!   `format_module()` / `format_expr()` or `TlaFormatter::new(config)`.

// Compact printer (existing)
mod expr;
mod helpers;
mod module;
mod proof;

// Width-aware formatter (new)
pub mod config;
mod fmt_expr;
mod fmt_module;
mod fmt_proof;
pub mod formatter;

#[cfg(test)]
mod tests;

use crate::ast::{Expr, Module};
pub use config::FormatConfig;
pub use formatter::TlaFormatter;

/// A wrapper for indentation-aware writing (compact, single-line output).
pub(crate) struct PrettyPrinter {
    output: String,
    indent: usize,
    indent_str: &'static str,
}

impl Default for PrettyPrinter {
    fn default() -> Self {
        Self::new()
    }
}

impl PrettyPrinter {
    pub(crate) fn new() -> Self {
        Self {
            output: String::new(),
            indent: 0,
            indent_str: "  ",
        }
    }

    pub(crate) fn finish(self) -> String {
        self.output
    }

    pub(super) fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.output.push_str(self.indent_str);
        }
    }

    pub(super) fn write(&mut self, s: &str) {
        self.output.push_str(s);
    }

    pub(super) fn writeln(&mut self, s: &str) {
        self.output.push_str(s);
        self.output.push('\n');
    }

    pub(super) fn newline(&mut self) {
        self.output.push('\n');
    }

    pub(super) fn indent(&mut self) {
        self.indent += 1;
    }

    pub(super) fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    pub(super) fn push_char(&mut self, c: char) {
        self.output.push(c);
    }
}

/// Pretty print a module (compact, single-line expressions).
pub fn pretty_module(module: &Module) -> String {
    let mut pp = PrettyPrinter::new();
    pp.print_module(module);
    pp.finish()
}

/// Pretty print an expression (compact, single-line).
pub fn pretty_expr(expr: &Expr) -> String {
    let mut pp = PrettyPrinter::new();
    pp.print_expr(expr);
    pp.finish()
}

/// Format a module using the width-aware TLA+ formatter with default config.
pub fn format_module(module: &Module) -> String {
    TlaFormatter::default().format_module(module)
}

/// Format a module using the width-aware TLA+ formatter with custom config.
pub fn format_module_with_config(module: &Module, config: FormatConfig) -> String {
    TlaFormatter::new(config).format_module(module)
}

/// Format a single expression using the width-aware formatter with default config.
pub fn format_expr(expr: &Expr) -> String {
    TlaFormatter::default().format_expr(expr)
}
