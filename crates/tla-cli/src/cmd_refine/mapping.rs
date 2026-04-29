// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Refinement mapping construction and parsing.
//!
//! A refinement mapping defines how implementation variables relate to abstract
//! variables. It can be specified explicitly via a mapping file or inferred
//! automatically by matching variable names between the two specs.
//!
//! ## Mapping file format
//!
//! ```text
//! \* This is a comment
//! impl_var |-> abstract_var
//! someExpr |-> abstractExpr
//! ```
//!
//! Each non-comment, non-blank line must contain exactly one `|->` separator.
//! The left side is the implementation variable name (or expression), and the
//! right side is the corresponding abstract variable (or expression).

use std::collections::BTreeSet;
use std::path::Path;

use anyhow::{bail, Context, Result};
use serde::Serialize;

use super::types::SpecInfo;

// ---------------------------------------------------------------------------
// Mapping types
// ---------------------------------------------------------------------------

/// A complete refinement mapping between implementation and abstract specs.
#[derive(Debug, Clone, Serialize)]
pub(super) struct RefinementMapping {
    /// Individual variable-to-variable (or expression) mappings.
    pub(super) entries: Vec<MappingEntry>,
    /// How this mapping was derived.
    pub(super) source: MappingSource,
}

/// A single entry in the refinement mapping.
#[derive(Debug, Clone, Serialize)]
pub(super) struct MappingEntry {
    /// The implementation-side variable or expression (as raw string).
    pub(super) impl_var: String,
    /// The abstract-side variable or expression (as raw string).
    pub(super) abstract_var: String,
    /// Whether this entry was automatically inferred.
    pub(super) auto_inferred: bool,
}

/// How the refinement mapping was derived.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(super) enum MappingSource {
    /// Loaded from a user-supplied mapping file.
    File,
    /// Automatically inferred by matching variable names.
    Auto,
}

// ---------------------------------------------------------------------------
// Parse mapping file
// ---------------------------------------------------------------------------

/// Parse a refinement mapping file.
///
/// Format: one `impl_var |-> abstract_var` per line.
/// Lines starting with `\*` or `(*` are comments; blank lines are skipped.
pub(super) fn parse_mapping_file(path: &Path) -> Result<RefinementMapping> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("read mapping file {}", path.display()))?;

    let mut entries = Vec::new();

    for (line_num, line) in content.lines().enumerate() {
        let trimmed = line.trim();

        // Skip blank lines.
        if trimmed.is_empty() {
            continue;
        }

        // Skip TLA+-style comments.
        if trimmed.starts_with("\\*") || trimmed.starts_with("(*") {
            continue;
        }

        // Skip single-line `(* ... *)` comments.
        if trimmed.starts_with("(*") && trimmed.ends_with("*)") {
            continue;
        }

        // Parse the mapping entry: `lhs |-> rhs`.
        let entry = parse_mapping_line(trimmed, line_num + 1, path)?;
        entries.push(entry);
    }

    if entries.is_empty() {
        bail!(
            "mapping file {} contains no mapping entries",
            path.display()
        );
    }

    Ok(RefinementMapping {
        entries,
        source: MappingSource::File,
    })
}

/// Parse a single mapping line: `impl_var |-> abstract_var`.
fn parse_mapping_line(line: &str, line_num: usize, path: &Path) -> Result<MappingEntry> {
    // The TLA+ `|->` operator is the standard mapping separator.
    let parts: Vec<&str> = line.splitn(2, "|->").collect();
    if parts.len() != 2 {
        bail!(
            "{}:{}: expected `impl_var |-> abstract_var`, got: {}",
            path.display(),
            line_num,
            line
        );
    }

    let impl_var = parts[0].trim().to_string();
    let abstract_var = parts[1].trim().to_string();

    if impl_var.is_empty() {
        bail!(
            "{}:{}: empty implementation variable in mapping",
            path.display(),
            line_num
        );
    }
    if abstract_var.is_empty() {
        bail!(
            "{}:{}: empty abstract variable in mapping",
            path.display(),
            line_num
        );
    }

    Ok(MappingEntry {
        impl_var,
        abstract_var,
        auto_inferred: false,
    })
}

// ---------------------------------------------------------------------------
// Automatic mapping
// ---------------------------------------------------------------------------

/// Build a refinement mapping automatically by matching variable names.
///
/// For each abstract variable, if an implementation variable with the same
/// name exists, create an identity mapping. This is the most common case
/// (the abstract spec uses a subset of the implementation variables).
pub(super) fn build_auto_mapping(
    impl_info: &SpecInfo,
    abstract_info: &SpecInfo,
) -> Result<RefinementMapping> {
    let impl_vars: BTreeSet<&str> = impl_info.variables.iter().map(|s| s.as_str()).collect();
    let impl_ops: BTreeSet<&str> = impl_info.operators.keys().map(|s| s.as_str()).collect();

    let mut entries = Vec::new();

    for abs_var in &abstract_info.variables {
        // First try: exact variable name match.
        if impl_vars.contains(abs_var.as_str()) {
            entries.push(MappingEntry {
                impl_var: abs_var.clone(),
                abstract_var: abs_var.clone(),
                auto_inferred: true,
            });
            continue;
        }

        // Second try: look for an operator with a matching name in the
        // implementation. This handles cases where the refinement mapping
        // is defined via an operator (e.g., `bar == impl_expr`).
        if impl_ops.contains(abs_var.as_str()) {
            entries.push(MappingEntry {
                impl_var: abs_var.clone(),
                abstract_var: abs_var.clone(),
                auto_inferred: true,
            });
            continue;
        }

        // No match found -- this variable will be reported as unmapped.
    }

    if entries.is_empty() && !abstract_info.variables.is_empty() {
        eprintln!(
            "Warning: automatic refinement mapping found no matching variables \
             between {} and {}.",
            impl_info.module_name, abstract_info.module_name
        );
        eprintln!(
            "  Implementation variables: {}",
            impl_info.variables.join(", ")
        );
        eprintln!(
            "  Abstract variables: {}",
            abstract_info.variables.join(", ")
        );
        eprintln!("  Consider providing an explicit mapping file with --mapping.");
    }

    Ok(RefinementMapping {
        entries,
        source: MappingSource::Auto,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_mapping_line_simple() {
        let entry = parse_mapping_line("x |-> y", 1, Path::new("test.map")).expect("should parse");
        assert_eq!(entry.impl_var, "x");
        assert_eq!(entry.abstract_var, "y");
        assert!(!entry.auto_inferred);
    }

    #[test]
    fn test_parse_mapping_line_with_spaces() {
        let entry = parse_mapping_line("  implState  |->  absState  ", 1, Path::new("test.map"))
            .expect("should parse");
        assert_eq!(entry.impl_var, "implState");
        assert_eq!(entry.abstract_var, "absState");
    }

    #[test]
    fn test_parse_mapping_line_expression() {
        let entry = parse_mapping_line("pc[self] |-> abstractPC", 1, Path::new("test.map"))
            .expect("should parse");
        assert_eq!(entry.impl_var, "pc[self]");
        assert_eq!(entry.abstract_var, "abstractPC");
    }

    #[test]
    fn test_parse_mapping_line_missing_separator() {
        let result = parse_mapping_line("x = y", 1, Path::new("test.map"));
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_mapping_line_empty_lhs() {
        let result = parse_mapping_line("|-> y", 1, Path::new("test.map"));
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_mapping_line_empty_rhs() {
        let result = parse_mapping_line("x |->", 1, Path::new("test.map"));
        assert!(result.is_err());
    }
}
