// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 rename` — rename operators or variables across a spec.
//!
//! Performs a semantic rename of an operator or variable throughout
//! the specification, showing the resulting changes.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the rename command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RenameOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Rename an identifier across a TLA+ spec.
pub(crate) fn cmd_rename(
    file: &Path,
    from: &str,
    to: &str,
    format: RenameOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    let source = read_source(file)?;

    // Validate by parsing.
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("lowering produced no module")?;

    // Verify the identifier exists.
    let mut found = false;
    for unit in &module.units {
        match &unit.node {
            tla_core::ast::Unit::Variable(decls) => {
                for d in decls {
                    if d.node == from {
                        found = true;
                    }
                }
            }
            tla_core::ast::Unit::Constant(decls) => {
                for d in decls {
                    if d.name.node == from {
                        found = true;
                    }
                }
            }
            tla_core::ast::Unit::Operator(def) => {
                if def.name.node == from {
                    found = true;
                }
            }
            _ => {}
        }
    }

    if !found {
        bail!("identifier `{from}` not found in spec");
    }

    // Perform text-level rename (word-boundary aware).
    let renamed = rename_identifier(&source, from, to);
    let changes = count_replacements(&source, from);

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        RenameOutputFormat::Human => {
            println!("rename: {} -> {} in {}", from, to, file.display());
            println!("  occurrences replaced: {changes}");
            println!();
            println!("--- Renamed ---");
            print!("{renamed}");
            println!("--- end ---");
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        RenameOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "from": from,
                "to": to,
                "occurrences": changes,
                "renamed_source": renamed,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Replace all word-boundary occurrences of `from` with `to`.
fn rename_identifier(source: &str, from: &str, to: &str) -> String {
    let mut result = String::with_capacity(source.len());
    let mut chars: Vec<char> = source.chars().collect();
    let from_chars: Vec<char> = from.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if i + from_chars.len() <= chars.len()
            && chars[i..i + from_chars.len()] == from_chars[..]
        {
            // Check word boundaries.
            let before_ok = i == 0 || !is_ident_char(chars[i - 1]);
            let after_ok = i + from_chars.len() >= chars.len()
                || !is_ident_char(chars[i + from_chars.len()]);
            if before_ok && after_ok {
                result.push_str(to);
                i += from_chars.len();
                continue;
            }
        }
        result.push(chars[i]);
        i += 1;
    }
    result
}

fn count_replacements(source: &str, from: &str) -> usize {
    let chars: Vec<char> = source.chars().collect();
    let from_chars: Vec<char> = from.chars().collect();
    let mut count = 0;
    let mut i = 0;

    while i < chars.len() {
        if i + from_chars.len() <= chars.len()
            && chars[i..i + from_chars.len()] == from_chars[..]
        {
            let before_ok = i == 0 || !is_ident_char(chars[i - 1]);
            let after_ok = i + from_chars.len() >= chars.len()
                || !is_ident_char(chars[i + from_chars.len()]);
            if before_ok && after_ok {
                count += 1;
                i += from_chars.len();
                continue;
            }
        }
        i += 1;
    }
    count
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}
