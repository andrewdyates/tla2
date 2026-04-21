// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 compare` — structural comparison of two TLA+ specifications.
//!
//! Parses both specs to AST, then compares their structure:
//! - Operators: added, removed, or modified (detected via body text hash)
//! - Variables: added or removed
//! - Constants: added or removed
//! - EXTENDS: added or removed
//! - INSTANCE: added or removed
//!
//! Outputs a human-readable colored diff or JSON summary.

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{ConstantDecl, InstanceDecl, Module, OperatorDef, Unit};
use tla_core::{lower_main_module, pretty_expr, FileId, SyntaxNode};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Output format enum
// ---------------------------------------------------------------------------

/// Output format for the `compare` subcommand.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum CompareOutputFormat {
    /// Human-readable colored output (default).
    #[default]
    Human,
    /// Machine-readable JSON output.
    Json,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Compare two TLA+ specifications structurally.
///
/// Parses both files, lowers to AST, then reports structural differences in
/// operators, variables, constants, EXTENDS, and INSTANCE declarations.
pub(crate) fn cmd_compare(
    left: &Path,
    right: &Path,
    format: CompareOutputFormat,
) -> Result<()> {
    let left_module = parse_and_lower(left)?;
    let right_module = parse_and_lower(right)?;

    let left_source = read_source(left)?;
    let right_source = read_source(right)?;

    let mut report = CompareReport::default();

    report.extends = compare_extends(&left_module, &right_module);
    report.variables = compare_variables(&left_module, &right_module);
    report.constants = compare_constants(&left_module, &right_module);
    report.operators =
        compare_operators(&left_module, &right_module, &left_source, &right_source);
    report.instances = compare_instances(&left_module, &right_module);

    match format {
        CompareOutputFormat::Human => print_human(left, right, &report),
        CompareOutputFormat::Json => print_json(&report),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Report data structures
// ---------------------------------------------------------------------------

#[derive(Debug, Default, serde::Serialize)]
struct CompareReport {
    extends: SetDiff,
    variables: SetDiff,
    constants: SetDiff,
    operators: OperatorComparison,
    instances: SetDiff,
}

/// A simple added/removed diff for named items.
#[derive(Debug, Default, serde::Serialize)]
struct SetDiff {
    added: Vec<String>,
    removed: Vec<String>,
}

/// Comparison results for operators, including modification detection.
#[derive(Debug, Default, serde::Serialize)]
struct OperatorComparison {
    added: Vec<OperatorSummary>,
    removed: Vec<OperatorSummary>,
    modified: Vec<ModifiedOperator>,
    unchanged: usize,
}

/// Summary of an operator (name, line, arity).
#[derive(Debug, serde::Serialize)]
struct OperatorSummary {
    name: String,
    line: usize,
    arity: usize,
}

/// An operator present in both files whose body changed.
#[derive(Debug, serde::Serialize)]
struct ModifiedOperator {
    name: String,
    left_line: usize,
    right_line: usize,
    left_body: String,
    right_body: String,
    left_body_hash: u64,
    right_body_hash: u64,
}

impl CompareReport {
    fn is_empty(&self) -> bool {
        self.extends.is_empty()
            && self.variables.is_empty()
            && self.constants.is_empty()
            && self.operators.added.is_empty()
            && self.operators.removed.is_empty()
            && self.operators.modified.is_empty()
            && self.instances.is_empty()
    }

    fn total_changes(&self) -> usize {
        self.extends.total()
            + self.variables.total()
            + self.constants.total()
            + self.operators.added.len()
            + self.operators.removed.len()
            + self.operators.modified.len()
            + self.instances.total()
    }
}

impl SetDiff {
    fn is_empty(&self) -> bool {
        self.added.is_empty() && self.removed.is_empty()
    }

    fn total(&self) -> usize {
        self.added.len() + self.removed.len()
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
    let tree = SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
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
// Hashing helper
// ---------------------------------------------------------------------------

/// Compute a deterministic hash of a pretty-printed operator body.
fn body_hash(pretty: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    pretty.hash(&mut hasher);
    hasher.finish()
}

// ---------------------------------------------------------------------------
// Line number helper
// ---------------------------------------------------------------------------

/// Compute a 1-based line number from a byte offset within source text.
fn line_of(source: &str, byte_offset: u32) -> usize {
    let offset = (byte_offset as usize).min(source.len());
    source[..offset].bytes().filter(|&b| b == b'\n').count() + 1
}

// ---------------------------------------------------------------------------
// EXTENDS comparison
// ---------------------------------------------------------------------------

fn compare_extends(left: &Module, right: &Module) -> SetDiff {
    let left_set: BTreeSet<&str> = left.extends.iter().map(|s| s.node.as_str()).collect();
    let right_set: BTreeSet<&str> = right.extends.iter().map(|s| s.node.as_str()).collect();

    SetDiff {
        added: right_set.difference(&left_set).map(|s| (*s).to_string()).collect(),
        removed: left_set.difference(&right_set).map(|s| (*s).to_string()).collect(),
    }
}

// ---------------------------------------------------------------------------
// Variable comparison
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

fn compare_variables(left: &Module, right: &Module) -> SetDiff {
    let left_vars = collect_variables(left);
    let right_vars = collect_variables(right);

    SetDiff {
        added: right_vars.difference(&left_vars).cloned().collect(),
        removed: left_vars.difference(&right_vars).cloned().collect(),
    }
}

// ---------------------------------------------------------------------------
// Constant comparison
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

fn compare_constants(left: &Module, right: &Module) -> SetDiff {
    let left_consts = collect_constants(left);
    let right_consts = collect_constants(right);

    SetDiff {
        added: right_consts.difference(&left_consts).cloned().collect(),
        removed: left_consts.difference(&right_consts).cloned().collect(),
    }
}

// ---------------------------------------------------------------------------
// Operator comparison
// ---------------------------------------------------------------------------

fn collect_operators(module: &Module) -> BTreeMap<String, &OperatorDef> {
    let mut ops = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            ops.insert(def.name.node.clone(), def);
        }
    }
    ops
}

fn compare_operators(
    left: &Module,
    right: &Module,
    left_source: &str,
    right_source: &str,
) -> OperatorComparison {
    let left_ops = collect_operators(left);
    let right_ops = collect_operators(right);

    let mut added = Vec::new();
    let mut removed = Vec::new();
    let mut modified = Vec::new();
    let mut unchanged: usize = 0;

    // Detect added and modified operators.
    for (name, right_def) in &right_ops {
        match left_ops.get(name) {
            None => {
                added.push(OperatorSummary {
                    name: name.clone(),
                    line: line_of(right_source, right_def.name.span.start),
                    arity: right_def.params.len(),
                });
            }
            Some(left_def) => {
                let left_body = pretty_expr(&left_def.body.node);
                let right_body = pretty_expr(&right_def.body.node);
                let left_h = body_hash(&left_body);
                let right_h = body_hash(&right_body);

                if left_h != right_h || left_body != right_body {
                    modified.push(ModifiedOperator {
                        name: name.clone(),
                        left_line: line_of(left_source, left_def.name.span.start),
                        right_line: line_of(right_source, right_def.name.span.start),
                        left_body,
                        right_body,
                        left_body_hash: left_h,
                        right_body_hash: right_h,
                    });
                } else {
                    unchanged += 1;
                }
            }
        }
    }

    // Detect removed operators.
    for (name, left_def) in &left_ops {
        if !right_ops.contains_key(name) {
            removed.push(OperatorSummary {
                name: name.clone(),
                line: line_of(left_source, left_def.name.span.start),
                arity: left_def.params.len(),
            });
        }
    }

    OperatorComparison {
        added,
        removed,
        modified,
        unchanged,
    }
}

// ---------------------------------------------------------------------------
// INSTANCE comparison
// ---------------------------------------------------------------------------

/// Produce a canonical string for an `InstanceDecl` suitable for set comparison.
fn format_instance_decl(inst: &InstanceDecl) -> String {
    if inst.substitutions.is_empty() {
        inst.module.node.clone()
    } else {
        let subs: Vec<String> = inst
            .substitutions
            .iter()
            .map(|s| format!("{} <- {}", s.from.node, pretty_expr(&s.to.node)))
            .collect();
        format!("{} WITH {}", inst.module.node, subs.join(", "))
    }
}

fn collect_instances(module: &Module) -> BTreeSet<String> {
    let mut instances = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Instance(inst) = &unit.node {
            instances.insert(format_instance_decl(inst));
        }
    }
    instances
}

fn compare_instances(left: &Module, right: &Module) -> SetDiff {
    let left_insts = collect_instances(left);
    let right_insts = collect_instances(right);

    SetDiff {
        added: right_insts.difference(&left_insts).cloned().collect(),
        removed: left_insts.difference(&right_insts).cloned().collect(),
    }
}

// ---------------------------------------------------------------------------
// Human-readable output
// ---------------------------------------------------------------------------

fn print_human(left_file: &Path, right_file: &Path, report: &CompareReport) {
    if report.is_empty() {
        println!("Specifications are structurally identical.");
        if report.operators.unchanged > 0 {
            println!(
                "  ({} operator{} unchanged)",
                report.operators.unchanged,
                if report.operators.unchanged == 1 { "" } else { "s" }
            );
        }
        return;
    }

    println!("Comparing TLA+ specifications:");
    println!("  left:  {}", left_file.display());
    println!("  right: {}", right_file.display());
    println!();

    // EXTENDS
    print_set_diff_section("EXTENDS", &report.extends);

    // Variables
    print_set_diff_section("Variables", &report.variables);

    // Constants
    print_set_diff_section("Constants", &report.constants);

    // INSTANCE
    print_set_diff_section("INSTANCE", &report.instances);

    // Operators
    let has_op_changes = !report.operators.added.is_empty()
        || !report.operators.removed.is_empty()
        || !report.operators.modified.is_empty();

    if has_op_changes {
        println!("Operators:");
        for op in &report.operators.added {
            println!(
                "  \x1b[32m+ {:<24}\x1b[0m (added, line {}, arity {})",
                op.name, op.line, op.arity
            );
        }
        for op in &report.operators.removed {
            println!(
                "  \x1b[31m- {:<24}\x1b[0m (removed, was line {}, arity {})",
                op.name, op.line, op.arity
            );
        }
        for op in &report.operators.modified {
            println!(
                "  \x1b[33m~ {:<24}\x1b[0m (modified, line {} -> {})",
                op.name, op.left_line, op.right_line
            );
            print_body_diff(&op.left_body, &op.right_body);
        }
        if report.operators.unchanged > 0 {
            println!(
                "  ({} operator{} unchanged)",
                report.operators.unchanged,
                if report.operators.unchanged == 1 { "" } else { "s" }
            );
        }
        println!();
    }

    // Summary line
    println!(
        "Total: {} structural change{}",
        report.total_changes(),
        if report.total_changes() == 1 { "" } else { "s" }
    );
}

/// Print a named section of added/removed items.
fn print_set_diff_section(label: &str, diff: &SetDiff) {
    if diff.is_empty() {
        return;
    }
    println!("{label}:");
    for name in &diff.added {
        println!("  \x1b[32m+ {name}\x1b[0m");
    }
    for name in &diff.removed {
        println!("  \x1b[31m- {name}\x1b[0m");
    }
    println!();
}

/// Print an inline line-level diff of two pretty-printed operator bodies.
fn print_body_diff(left_body: &str, right_body: &str) {
    let left_lines: Vec<&str> = left_body.lines().collect();
    let right_lines: Vec<&str> = right_body.lines().collect();

    let lcs = compute_lcs(&left_lines, &right_lines);
    let mut li = 0usize;
    let mut ri = 0usize;
    let mut ci = 0usize;

    while li < left_lines.len() || ri < right_lines.len() {
        if ci < lcs.len()
            && li < left_lines.len()
            && ri < right_lines.len()
            && left_lines[li] == lcs[ci]
            && right_lines[ri] == lcs[ci]
        {
            // Common line.
            println!("      {}", left_lines[li]);
            li += 1;
            ri += 1;
            ci += 1;
        } else if ci < lcs.len()
            && ri < right_lines.len()
            && right_lines[ri] == lcs[ci]
        {
            // Left line removed.
            println!("    \x1b[31m- {}\x1b[0m", left_lines[li]);
            li += 1;
        } else if ci < lcs.len()
            && li < left_lines.len()
            && left_lines[li] == lcs[ci]
        {
            // Right line added.
            println!("    \x1b[32m+ {}\x1b[0m", right_lines[ri]);
            ri += 1;
        } else {
            // Both differ from LCS — show removal then addition.
            if li < left_lines.len() {
                println!("    \x1b[31m- {}\x1b[0m", left_lines[li]);
                li += 1;
            }
            if ri < right_lines.len() {
                println!("    \x1b[32m+ {}\x1b[0m", right_lines[ri]);
                ri += 1;
            }
        }
    }
}

/// Compute the longest common subsequence of two string slices.
fn compute_lcs<'a>(a: &[&'a str], b: &[&'a str]) -> Vec<&'a str> {
    let m = a.len();
    let n = b.len();
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

fn print_json(report: &CompareReport) {
    let json =
        serde_json::to_string_pretty(report).expect("invariant: CompareReport is serializable");
    println!("{json}");
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::Spanned;

    // -- line_of --

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_line_of_first_line() {
        let source = "hello\nworld\n";
        assert_eq!(line_of(source, 0), 1);
        assert_eq!(line_of(source, 4), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_line_of_second_line() {
        let source = "hello\nworld\n";
        assert_eq!(line_of(source, 6), 2);
        assert_eq!(line_of(source, 10), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_line_of_clamps_beyond_end() {
        let source = "abc";
        // Offset beyond source length is clamped.
        assert_eq!(line_of(source, 999), 1);
    }

    // -- body_hash --

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_body_hash_equal_strings() {
        assert_eq!(body_hash("x + y"), body_hash("x + y"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_body_hash_different_strings() {
        assert_ne!(body_hash("x + y"), body_hash("x - y"));
    }

    // -- compute_lcs --

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_lcs_identical() {
        let a = vec!["a", "b", "c"];
        let b = vec!["a", "b", "c"];
        assert_eq!(compute_lcs(&a, &b), vec!["a", "b", "c"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_lcs_disjoint() {
        let a = vec!["a", "b"];
        let b = vec!["c", "d"];
        let result: Vec<&str> = compute_lcs(&a, &b);
        assert!(result.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_lcs_insertion() {
        let a = vec!["a", "c"];
        let b = vec!["a", "b", "c"];
        assert_eq!(compute_lcs(&a, &b), vec!["a", "c"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_lcs_empty_inputs() {
        let empty: Vec<&str> = vec![];
        assert!(compute_lcs(&empty, &empty).is_empty());
        assert!(compute_lcs(&["a"], &empty).is_empty());
        assert!(compute_lcs(&empty, &["a"]).is_empty());
    }

    // -- format_constant_decl --

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_constant_decl_simple() {
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
            arity: Some(3),
        };
        assert_eq!(format_constant_decl(&decl), "F(_, _, _)");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_constant_decl_zero_arity() {
        let decl = ConstantDecl {
            name: Spanned::dummy("C".to_string()),
            arity: Some(0),
        };
        assert_eq!(format_constant_decl(&decl), "C");
    }

    // -- format_instance_decl --

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_instance_decl_no_substitutions() {
        let inst = InstanceDecl {
            module: Spanned::dummy("Naturals".to_string()),
            substitutions: vec![],
            local: false,
        };
        assert_eq!(format_instance_decl(&inst), "Naturals");
    }

    // -- SetDiff --

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_diff_empty() {
        let diff = SetDiff::default();
        assert!(diff.is_empty());
        assert_eq!(diff.total(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_diff_with_items() {
        let diff = SetDiff {
            added: vec!["x".to_string()],
            removed: vec!["y".to_string(), "z".to_string()],
        };
        assert!(!diff.is_empty());
        assert_eq!(diff.total(), 3);
    }

    // -- CompareReport --

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_report_empty() {
        let report = CompareReport::default();
        assert!(report.is_empty());
        assert_eq!(report.total_changes(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_report_counts_all_sections() {
        let report = CompareReport {
            extends: SetDiff {
                added: vec!["TLC".to_string()],
                removed: vec![],
            },
            variables: SetDiff {
                added: vec!["x".to_string()],
                removed: vec!["y".to_string()],
            },
            constants: SetDiff::default(),
            operators: OperatorComparison {
                added: vec![OperatorSummary {
                    name: "NewOp".to_string(),
                    line: 10,
                    arity: 0,
                }],
                removed: vec![],
                modified: vec![],
                unchanged: 5,
            },
            instances: SetDiff {
                added: vec![],
                removed: vec!["OldModule".to_string()],
            },
        };
        assert!(!report.is_empty());
        // extends(1) + vars(2) + consts(0) + ops_added(1) + instances(1) = 5
        assert_eq!(report.total_changes(), 5);
    }

    // -- JSON round-trip --

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_report_serializes_to_json() {
        let report = CompareReport {
            extends: SetDiff {
                added: vec!["Sequences".to_string()],
                removed: vec![],
            },
            ..CompareReport::default()
        };
        let json = serde_json::to_string_pretty(&report)
            .expect("should serialize CompareReport to JSON");
        assert!(json.contains("Sequences"));
        assert!(json.contains("\"added\""));
    }
}
