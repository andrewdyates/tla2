// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 diff` — semantic diff for comparing two TLA+ specifications.
//!
//! Parses both specs to AST, then compares:
//! - Added/removed/modified operators
//! - Variable declaration changes
//! - Constant declaration changes
//! - EXTENDS changes
//! - Invariant changes (when .cfg files are provided)

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{ConstantDecl, Module, OperatorDef, Unit};
use tla_core::{lower_main_module, pretty_expr, FileId};

use crate::cli_schema::DiffOutputFormat;
use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_diff(
    old_file: &Path,
    new_file: &Path,
    old_config: Option<&Path>,
    new_config: Option<&Path>,
    format: DiffOutputFormat,
    operators_only: bool,
) -> Result<()> {
    let old_module = parse_and_lower(old_file)?;
    let new_module = parse_and_lower(new_file)?;

    let old_source = read_source(old_file)?;
    let new_source = read_source(new_file)?;

    let mut diff = SpecDiff::default();

    // EXTENDS changes
    if !operators_only {
        diff.extends = diff_extends(&old_module, &new_module);
    }

    // Variable changes
    if !operators_only {
        diff.variables = diff_variables(&old_module, &new_module);
    }

    // Constant changes
    if !operators_only {
        diff.constants = diff_constants(&old_module, &new_module);
    }

    // Operator changes
    diff.operators = diff_operators(&old_module, &new_module, &old_source, &new_source);

    // Invariant changes from .cfg files
    if !operators_only {
        diff.invariants = diff_invariants(old_file, new_file, old_config, new_config);
    }

    // Output
    match format {
        DiffOutputFormat::Human => print_human(old_file, new_file, &diff),
        DiffOutputFormat::Json => print_json(&diff),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Diff data structures
// ---------------------------------------------------------------------------

#[derive(Debug, Default, serde::Serialize)]
struct SpecDiff {
    extends: ExtendsDiff,
    variables: ListDiff,
    constants: ListDiff,
    operators: OperatorsDiff,
    invariants: ListDiff,
}

#[derive(Debug, Default, serde::Serialize)]
struct ExtendsDiff {
    added: Vec<String>,
    removed: Vec<String>,
}

#[derive(Debug, Default, serde::Serialize)]
struct ListDiff {
    added: Vec<String>,
    removed: Vec<String>,
}

#[derive(Debug, Default, serde::Serialize)]
struct OperatorsDiff {
    added: Vec<OperatorInfo>,
    removed: Vec<OperatorInfo>,
    modified: Vec<ModifiedOperator>,
}

#[derive(Debug, serde::Serialize)]
struct OperatorInfo {
    name: String,
    line: usize,
    arity: usize,
}

#[derive(Debug, serde::Serialize)]
struct ModifiedOperator {
    name: String,
    old_line: usize,
    new_line: usize,
    old_body: String,
    new_body: String,
}

impl SpecDiff {
    fn is_empty(&self) -> bool {
        self.extends.added.is_empty()
            && self.extends.removed.is_empty()
            && self.variables.added.is_empty()
            && self.variables.removed.is_empty()
            && self.constants.added.is_empty()
            && self.constants.removed.is_empty()
            && self.operators.added.is_empty()
            && self.operators.removed.is_empty()
            && self.operators.modified.is_empty()
            && self.invariants.added.is_empty()
            && self.invariants.removed.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Parse + lower helper
// ---------------------------------------------------------------------------

fn parse_and_lower(file: &Path) -> Result<Module> {
    let source = read_source(file)?;
    let parse_result = tla_core::parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diagnostic =
                tla_core::parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "parse failed for {}: {} error(s)",
            file.display(),
            parse_result.errors.len()
        );
    }
    let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lower failed for {}: {} error(s)",
            file.display(),
            result.errors.len()
        );
    }
    result
        .module
        .context(format!("lower produced no module for {}", file.display()))
}

// ---------------------------------------------------------------------------
// EXTENDS diff
// ---------------------------------------------------------------------------

fn diff_extends(old: &Module, new: &Module) -> ExtendsDiff {
    let old_set: BTreeSet<&str> = old.extends.iter().map(|s| s.node.as_str()).collect();
    let new_set: BTreeSet<&str> = new.extends.iter().map(|s| s.node.as_str()).collect();

    ExtendsDiff {
        added: new_set
            .difference(&old_set)
            .map(|s| (*s).to_string())
            .collect(),
        removed: old_set
            .difference(&new_set)
            .map(|s| (*s).to_string())
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// Variable diff
// ---------------------------------------------------------------------------

fn collect_variables(module: &Module) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for decl in decls {
                vars.insert(decl.node.clone());
            }
        }
    }
    vars
}

fn diff_variables(old: &Module, new: &Module) -> ListDiff {
    let old_vars = collect_variables(old);
    let new_vars = collect_variables(new);

    ListDiff {
        added: new_vars.difference(&old_vars).cloned().collect(),
        removed: old_vars.difference(&new_vars).cloned().collect(),
    }
}

// ---------------------------------------------------------------------------
// Constant diff
// ---------------------------------------------------------------------------

fn collect_constants(module: &Module) -> BTreeSet<String> {
    let mut consts = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                consts.insert(format_constant_decl(decl));
            }
        }
    }
    consts
}

fn format_constant_decl(decl: &ConstantDecl) -> String {
    match decl.arity {
        Some(arity) if arity > 0 => {
            let underscores: Vec<&str> = (0..arity).map(|_| "_").collect();
            format!("{}({})", decl.name.node, underscores.join(", "))
        }
        _ => decl.name.node.clone(),
    }
}

fn diff_constants(old: &Module, new: &Module) -> ListDiff {
    let old_consts = collect_constants(old);
    let new_consts = collect_constants(new);

    ListDiff {
        added: new_consts.difference(&old_consts).cloned().collect(),
        removed: old_consts.difference(&new_consts).cloned().collect(),
    }
}

// ---------------------------------------------------------------------------
// Operator diff
// ---------------------------------------------------------------------------

/// Compute line number from byte offset within source text.
fn line_of(source: &str, byte_offset: u32) -> usize {
    let offset = byte_offset as usize;
    let clamped = offset.min(source.len());
    source[..clamped].bytes().filter(|&b| b == b'\n').count() + 1
}

fn collect_operators(module: &Module) -> BTreeMap<String, &OperatorDef> {
    let mut ops = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            ops.insert(def.name.node.clone(), def);
        }
    }
    ops
}

fn diff_operators(old: &Module, new: &Module, old_source: &str, new_source: &str) -> OperatorsDiff {
    let old_ops = collect_operators(old);
    let new_ops = collect_operators(new);

    let mut added = Vec::new();
    let mut removed = Vec::new();
    let mut modified = Vec::new();

    // Find added and modified
    for (name, new_def) in &new_ops {
        match old_ops.get(name) {
            None => {
                added.push(OperatorInfo {
                    name: name.clone(),
                    line: line_of(new_source, new_def.name.span.start),
                    arity: new_def.params.len(),
                });
            }
            Some(old_def) => {
                // Compare by pretty-printing bodies (ignores span differences)
                let old_body = pretty_expr(&old_def.body.node);
                let new_body = pretty_expr(&new_def.body.node);
                if old_body != new_body {
                    modified.push(ModifiedOperator {
                        name: name.clone(),
                        old_line: line_of(old_source, old_def.name.span.start),
                        new_line: line_of(new_source, new_def.name.span.start),
                        old_body,
                        new_body,
                    });
                }
            }
        }
    }

    // Find removed
    for (name, old_def) in &old_ops {
        if !new_ops.contains_key(name) {
            removed.push(OperatorInfo {
                name: name.clone(),
                line: line_of(old_source, old_def.name.span.start),
                arity: old_def.params.len(),
            });
        }
    }

    OperatorsDiff {
        added,
        removed,
        modified,
    }
}

// ---------------------------------------------------------------------------
// Invariant diff (from .cfg files)
// ---------------------------------------------------------------------------

fn load_config_invariants(spec_file: &Path, config_path: Option<&Path>) -> Vec<String> {
    let cfg_path = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut p = spec_file.to_path_buf();
            p.set_extension("cfg");
            p
        }
    };
    let source = match std::fs::read_to_string(&cfg_path) {
        Ok(s) => s,
        Err(_) => return Vec::new(),
    };
    match tla_check::Config::parse(&source) {
        Ok(config) => config.invariants,
        Err(_) => Vec::new(),
    }
}

fn diff_invariants(
    old_file: &Path,
    new_file: &Path,
    old_config: Option<&Path>,
    new_config: Option<&Path>,
) -> ListDiff {
    let old_invs: BTreeSet<String> = load_config_invariants(old_file, old_config)
        .into_iter()
        .collect();
    let new_invs: BTreeSet<String> = load_config_invariants(new_file, new_config)
        .into_iter()
        .collect();

    ListDiff {
        added: new_invs.difference(&old_invs).cloned().collect(),
        removed: old_invs.difference(&new_invs).cloned().collect(),
    }
}

// ---------------------------------------------------------------------------
// Human-readable output
// ---------------------------------------------------------------------------

fn print_human(old_file: &Path, new_file: &Path, diff: &SpecDiff) {
    if diff.is_empty() {
        println!("No semantic differences found.");
        return;
    }

    println!("--- {}", old_file.display());
    println!("+++ {}", new_file.display());
    println!();

    // EXTENDS
    if !diff.extends.added.is_empty() || !diff.extends.removed.is_empty() {
        println!("EXTENDS:");
        for name in &diff.extends.added {
            println!("  \x1b[32m+ {name}\x1b[0m");
        }
        for name in &diff.extends.removed {
            println!("  \x1b[31m- {name}\x1b[0m");
        }
        println!();
    }

    // Variables
    if !diff.variables.added.is_empty() || !diff.variables.removed.is_empty() {
        println!("Variables:");
        for name in &diff.variables.added {
            println!("  \x1b[32m+ {name:<20}\x1b[0m (added)");
        }
        for name in &diff.variables.removed {
            println!("  \x1b[31m- {name:<20}\x1b[0m (removed)");
        }
        println!();
    }

    // Constants
    if !diff.constants.added.is_empty() || !diff.constants.removed.is_empty() {
        println!("Constants:");
        for name in &diff.constants.added {
            println!("  \x1b[32m+ {name:<20}\x1b[0m (added)");
        }
        for name in &diff.constants.removed {
            println!("  \x1b[31m- {name:<20}\x1b[0m (removed)");
        }
        println!();
    }

    // Operators
    let has_op_changes = !diff.operators.added.is_empty()
        || !diff.operators.removed.is_empty()
        || !diff.operators.modified.is_empty();
    if has_op_changes {
        println!("Operators:");
        for op in &diff.operators.added {
            println!(
                "  \x1b[32m+ {:<20}\x1b[0m (added, line {}, arity {})",
                op.name, op.line, op.arity
            );
        }
        for op in &diff.operators.removed {
            println!(
                "  \x1b[31m- {:<20}\x1b[0m (removed, was line {}, arity {})",
                op.name, op.line, op.arity
            );
        }
        for op in &diff.operators.modified {
            println!(
                "  \x1b[33m~ {:<20}\x1b[0m (modified, line {} -> {})",
                op.name, op.old_line, op.new_line
            );
            print_inline_diff(&op.old_body, &op.new_body);
        }
        println!();
    }

    // Invariants
    if !diff.invariants.added.is_empty() || !diff.invariants.removed.is_empty() {
        println!("Invariants (from .cfg):");
        for name in &diff.invariants.added {
            println!("  \x1b[32m+ {name}\x1b[0m");
        }
        for name in &diff.invariants.removed {
            println!("  \x1b[31m- {name}\x1b[0m");
        }
        println!();
    } else if !diff.is_empty() {
        // Only print "unchanged" for invariants if other diffs exist
        println!("Invariants (from .cfg):");
        println!("  (unchanged)");
        println!();
    }
}

/// Print a simple line-level diff of two pretty-printed operator bodies.
fn print_inline_diff(old_body: &str, new_body: &str) {
    let old_lines: Vec<&str> = old_body.lines().collect();
    let new_lines: Vec<&str> = new_body.lines().collect();

    // Simple LCS-based diff
    let lcs = compute_lcs(&old_lines, &new_lines);
    let mut oi = 0usize;
    let mut ni = 0usize;
    let mut li = 0usize;

    while oi < old_lines.len() || ni < new_lines.len() {
        if li < lcs.len()
            && oi < old_lines.len()
            && ni < new_lines.len()
            && old_lines[oi] == lcs[li]
            && new_lines[ni] == lcs[li]
        {
            // Common line
            println!("      {}", old_lines[oi]);
            oi += 1;
            ni += 1;
            li += 1;
        } else if li < lcs.len() && ni < new_lines.len() && new_lines[ni] == lcs[li] {
            // Old line removed
            println!("    \x1b[31m- {}\x1b[0m", old_lines[oi]);
            oi += 1;
        } else if li < lcs.len() && oi < old_lines.len() && old_lines[oi] == lcs[li] {
            // New line added
            println!("    \x1b[32m+ {}\x1b[0m", new_lines[ni]);
            ni += 1;
        } else {
            // Both differ from LCS — print removals then additions
            if oi < old_lines.len() {
                println!("    \x1b[31m- {}\x1b[0m", old_lines[oi]);
                oi += 1;
            }
            if ni < new_lines.len() {
                println!("    \x1b[32m+ {}\x1b[0m", new_lines[ni]);
                ni += 1;
            }
        }
    }
}

/// Compute the longest common subsequence of two string slices.
fn compute_lcs<'a>(a: &[&'a str], b: &[&'a str]) -> Vec<&'a str> {
    let m = a.len();
    let n = b.len();
    // DP table
    let mut dp = vec![vec![0u32; n + 1]; m + 1];
    for i in 1..=m {
        for j in 1..=n {
            if a[i - 1] == b[j - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }
    // Backtrack
    let mut result = Vec::with_capacity(dp[m][n] as usize);
    let mut i = m;
    let mut j = n;
    while i > 0 && j > 0 {
        if a[i - 1] == b[j - 1] {
            result.push(a[i - 1]);
            i -= 1;
            j -= 1;
        } else if dp[i - 1][j] >= dp[i][j - 1] {
            i -= 1;
        } else {
            j -= 1;
        }
    }
    result.reverse();
    result
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

fn print_json(diff: &SpecDiff) {
    let json = serde_json::to_string_pretty(diff).expect("invariant: SpecDiff is serializable");
    println!("{json}");
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::Spanned;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_line_of_basic() {
        let source = "line1\nline2\nline3\n";
        assert_eq!(line_of(source, 0), 1);
        assert_eq!(line_of(source, 5), 1); // the \n itself
        assert_eq!(line_of(source, 6), 2); // first char of line2
        assert_eq!(line_of(source, 12), 3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compute_lcs_identical() {
        let a = vec!["a", "b", "c"];
        let b = vec!["a", "b", "c"];
        assert_eq!(compute_lcs(&a, &b), vec!["a", "b", "c"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compute_lcs_disjoint() {
        let a = vec!["a", "b"];
        let b = vec!["c", "d"];
        let result: Vec<&str> = compute_lcs(&a, &b);
        assert!(result.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compute_lcs_insertion() {
        let a = vec!["a", "c"];
        let b = vec!["a", "b", "c"];
        assert_eq!(compute_lcs(&a, &b), vec!["a", "c"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_constant_decl_no_arity() {
        let decl = ConstantDecl {
            name: Spanned::dummy("N".to_string()),
            arity: None,
        };
        assert_eq!(format_constant_decl(&decl), "N");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_constant_decl_with_arity() {
        let decl = ConstantDecl {
            name: Spanned::dummy("F".to_string()),
            arity: Some(2),
        };
        assert_eq!(format_constant_decl(&decl), "F(_, _)");
    }
}
