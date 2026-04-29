// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 validate` -- deep pre-flight validation of a TLA+ specification.
//!
//! Parses a TLA+ spec and its config, then runs 12 semantic validation checks
//! (V001-V012) that catch errors TLC would report at startup. Validates
//! operator references, variable declarations, config-spec consistency,
//! EXTENDS resolution, Init/Next existence, arity mismatches, RECURSIVE
//! declarations, and INSTANCE substitution targets.

mod checks;

use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{Module, Unit};
use tla_core::span::Span;
use tla_core::{lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId};

use crate::cli_schema::ValidateOutputFormat;
use crate::helpers::read_source;

use self::checks::{
    check_config_constants, check_config_invariants, check_config_properties,
    check_extends_modules, check_init_exists, check_instance_substitutions, check_next_exists,
    check_operator_arity, check_operator_references, check_recursive_declarations,
    check_symmetry_set, check_variable_references,
};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_validate(
    file: &Path,
    config_path: Option<&Path>,
    format: ValidateOutputFormat,
    strict: bool,
) -> Result<()> {
    let source = read_source(file)?;

    // Parse
    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diag = parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diag.eprint(&file_path, &source);
        }
        bail!(
            "validate aborted: {} parse error(s)",
            parse_result.errors.len()
        );
    }
    let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);

    // Lower CST -> AST
    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let lower_result = lower_main_module(FileId(0), &tree, hint_name);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diag = lower_error_diagnostic(&file_path, &err.message, err.span);
            diag.eprint(&file_path, &source);
        }
        bail!(
            "validate aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("validate: lowering produced no module")?;

    // Parse config if present
    let config = load_config(file, config_path);

    // Run all validation checks
    let mut issues = Vec::new();
    check_operator_references(&module, &mut issues);
    check_variable_references(&module, &mut issues);
    check_config_constants(&module, &config, &mut issues);
    check_extends_modules(file, &module, &mut issues);
    check_init_exists(&module, &config, &mut issues);
    check_next_exists(&module, &config, &mut issues);
    check_config_invariants(&module, &config, &mut issues);
    check_config_properties(&module, &config, &mut issues);
    check_symmetry_set(&module, &config, &mut issues);
    check_recursive_declarations(&module, &mut issues);
    check_operator_arity(&module, &mut issues);
    check_instance_substitutions(&module, &mut issues);

    // Output
    let file_path = file.display().to_string();
    match format {
        ValidateOutputFormat::Human => print_human(&file_path, &source, &issues),
        ValidateOutputFormat::Json => print_json(&file_path, &source, &issues)?,
    }

    // Determine exit code
    let has_errors = issues
        .iter()
        .any(|i| matches!(i.severity, IssueSeverity::Error));
    let has_warnings = issues
        .iter()
        .any(|i| matches!(i.severity, IssueSeverity::Warning));

    if has_errors || (strict && has_warnings) {
        std::process::exit(1);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Validation types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum IssueSeverity {
    Error,
    Warning,
}

impl std::fmt::Display for IssueSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IssueSeverity::Error => write!(f, "error"),
            IssueSeverity::Warning => write!(f, "warning"),
        }
    }
}

#[derive(Debug, Clone, serde::Serialize)]
pub(crate) struct ValidationIssue {
    /// Validation code (e.g., "V001")
    pub code: &'static str,
    /// Severity level
    pub severity: IssueSeverity,
    /// Human-readable message
    pub message: String,
    /// Source span (byte offsets)
    #[serde(skip)]
    pub span: Span,
}

/// Extracted config info for validation.
#[derive(Default)]
pub(crate) struct ConfigInfo {
    pub(crate) init: Option<String>,
    pub(crate) next: Option<String>,
    pub(crate) invariants: Vec<String>,
    pub(crate) properties: Vec<String>,
    pub(crate) constant_names: Vec<String>,
    pub(crate) symmetry: Option<String>,
    pub(crate) has_config: bool,
}

// ---------------------------------------------------------------------------
// Config loading
// ---------------------------------------------------------------------------

fn load_config(file: &Path, config_path: Option<&Path>) -> ConfigInfo {
    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    if !config_path_buf.exists() {
        return ConfigInfo::default();
    }

    let source = match std::fs::read_to_string(&config_path_buf) {
        Ok(s) => s,
        Err(_) => return ConfigInfo::default(),
    };

    match tla_check::Config::parse(&source) {
        Ok(config) => ConfigInfo {
            init: config.init.clone(),
            next: config.next.clone(),
            invariants: config.invariants.clone(),
            properties: config.properties.clone(),
            constant_names: config.constants.keys().cloned().collect(),
            symmetry: config.symmetry.clone(),
            has_config: true,
        },
        Err(_) => ConfigInfo::default(),
    }
}

// ---------------------------------------------------------------------------
// Helpers shared by output functions
// ---------------------------------------------------------------------------

/// Collect all operator names defined in the module (including from extended
/// standard library modules, whose operators are resolved at eval time).
pub(crate) fn collect_defined_operators(module: &Module) -> std::collections::HashSet<String> {
    let mut ops = std::collections::HashSet::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            ops.insert(op.name.node.clone());
        }
    }

    // Add operators from EXTENDS standard library modules
    for ext in &module.extends {
        let name = ext.node.as_str();
        if tla_core::is_stdlib_module(name) {
            for (op_name, _arity) in tla_core::get_module_operators(name) {
                ops.insert(op_name.to_string());
            }
        }
    }

    // Add TLA+ built-in operators that don't require EXTENDS
    for builtin in &[
        "TRUE",
        "FALSE",
        "BOOLEAN",
        "STRING",
        "ENABLED",
        "UNCHANGED",
        "DOMAIN",
        "SUBSET",
        "UNION",
        "CHOOSE",
        "CASE",
        "IF",
        "THEN",
        "ELSE",
        "LET",
        "IN",
        "EXCEPT",
        "Nat",
        "Int",
        "Real",
    ] {
        ops.insert(builtin.to_string());
    }
    ops
}

/// Collect all declared variable names.
pub(crate) fn collect_variables(module: &Module) -> std::collections::HashSet<String> {
    let mut vars = std::collections::HashSet::new();
    for unit in &module.units {
        if let Unit::Variable(names) = &unit.node {
            for name in names {
                vars.insert(name.node.clone());
            }
        }
    }
    vars
}

/// Collect all declared constant names.
pub(crate) fn collect_constants(module: &Module) -> std::collections::HashSet<String> {
    let mut consts = std::collections::HashSet::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                consts.insert(decl.name.node.clone());
            }
        }
    }
    consts
}

// ---------------------------------------------------------------------------
// Span -> line/column conversion
// ---------------------------------------------------------------------------

fn line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, ch) in source.char_indices() {
        if ch == '\n' {
            starts.push(i + 1);
        }
    }
    starts
}

fn offset_to_line_col(offset: u32, starts: &[usize]) -> (usize, usize) {
    let offset = offset as usize;
    let line_idx = match starts.binary_search(&offset) {
        Ok(i) => i,
        Err(i) => i.saturating_sub(1),
    };
    let col = offset.saturating_sub(starts[line_idx]);
    (line_idx + 1, col + 1)
}

// ---------------------------------------------------------------------------
// Output formatting
// ---------------------------------------------------------------------------

fn print_human(file_path: &str, source: &str, issues: &[ValidationIssue]) {
    let starts = line_starts(source);

    let error_count = issues
        .iter()
        .filter(|i| matches!(i.severity, IssueSeverity::Error))
        .count();
    let warning_count = issues
        .iter()
        .filter(|i| matches!(i.severity, IssueSeverity::Warning))
        .count();
    let total_checks = 12;
    let checks_passed = total_checks
        - issues
            .iter()
            .map(|i| i.code)
            .collect::<std::collections::HashSet<_>>()
            .len();

    if issues.is_empty() {
        println!("All {total_checks} validation checks passed for {file_path}");
        return;
    }

    for issue in issues {
        let (line, col) = offset_to_line_col(issue.span.start, &starts);

        let severity_str = match issue.severity {
            IssueSeverity::Error => "\x1b[31mERROR\x1b[0m",
            IssueSeverity::Warning => "\x1b[33mWARNING\x1b[0m",
        };

        println!("[{}] {}: {}", issue.code, severity_str, issue.message);
        println!("  --> {file_path}:{line}:{col}");
        println!();
    }

    // Summary
    let mut summary_parts = Vec::new();
    summary_parts.push(format!("{checks_passed} checks passed"));
    if error_count > 0 {
        summary_parts.push(format!(
            "{error_count} error{}",
            if error_count == 1 { "" } else { "s" }
        ));
    }
    if warning_count > 0 {
        summary_parts.push(format!(
            "{warning_count} warning{}",
            if warning_count == 1 { "" } else { "s" }
        ));
    }
    println!("Summary: {}", summary_parts.join(", "));
}

fn print_json(file_path: &str, source: &str, issues: &[ValidationIssue]) -> Result<()> {
    let starts = line_starts(source);

    let error_count = issues
        .iter()
        .filter(|i| matches!(i.severity, IssueSeverity::Error))
        .count();
    let warning_count = issues
        .iter()
        .filter(|i| matches!(i.severity, IssueSeverity::Warning))
        .count();
    let total_checks = 12;
    let failing_codes: std::collections::HashSet<_> = issues.iter().map(|i| i.code).collect();
    let checks_passed = total_checks - failing_codes.len();

    let json_issues: Vec<serde_json::Value> = issues
        .iter()
        .map(|issue| {
            let (line, col) = offset_to_line_col(issue.span.start, &starts);
            serde_json::json!({
                "code": issue.code,
                "severity": issue.severity,
                "message": issue.message,
                "file": file_path,
                "line": line,
                "column": col,
            })
        })
        .collect();

    let output = serde_json::json!({
        "file": file_path,
        "issues": json_issues,
        "summary": {
            "checks_passed": checks_passed,
            "errors": error_count,
            "warnings": warning_count,
            "total_checks": total_checks,
        },
        "valid": error_count == 0,
    });

    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::{lower_main_module, parse, FileId, SyntaxNode};

    fn parse_module(source: &str) -> Module {
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );
        let tree = SyntaxNode::new_root(result.green_node);
        let lower_result = lower_main_module(FileId(0), &tree, None);
        assert!(
            lower_result.errors.is_empty(),
            "lower errors: {:?}",
            lower_result.errors
        );
        lower_result.module.expect("no module produced")
    }

    #[test]
    fn test_clean_spec_no_issues() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
===="#,
        );
        let config = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["TypeOK".to_string()],
            has_config: true,
            ..Default::default()
        };
        let mut issues = Vec::new();
        check_init_exists(&module, &config, &mut issues);
        check_next_exists(&module, &config, &mut issues);
        check_config_invariants(&module, &config, &mut issues);
        assert!(issues.is_empty(), "expected no issues: {issues:?}");
    }

    #[test]
    fn test_missing_init() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Foo == x = 0
Next == x' = x + 1
===="#,
        );
        let config = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            has_config: true,
            ..Default::default()
        };
        let mut issues = Vec::new();
        check_init_exists(&module, &config, &mut issues);
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].code, "V005");
    }

    #[test]
    fn test_missing_invariant_in_spec() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        let config = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["TypeOK".to_string()],
            has_config: true,
            ..Default::default()
        };
        let mut issues = Vec::new();
        check_config_invariants(&module, &config, &mut issues);
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].code, "V007");
        assert!(issues[0].message.contains("TypeOK"));
    }

    #[test]
    fn test_operator_arity_mismatch() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Op(a, b) == a + b
Init == x = Op(1, 2, 3)
Next == x' = x
===="#,
        );
        let mut issues = Vec::new();
        check_operator_arity(&module, &mut issues);
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].code, "V011");
    }

    #[test]
    fn test_recursive_without_declaration() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
RECURSIVE Fact(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
Init == x = Fact(5)
Next == x' = x
===="#,
        );
        let mut issues = Vec::new();
        check_recursive_declarations(&module, &mut issues);
        // Fact IS declared with RECURSIVE, so no issue
        assert!(issues.is_empty(), "expected no issues: {issues:?}");
    }

    #[test]
    fn test_recursive_missing_declaration() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
Init == x = Fact(5)
Next == x' = x
===="#,
        );
        let mut issues = Vec::new();
        check_recursive_declarations(&module, &mut issues);
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].code, "V010");
        assert!(issues[0].message.contains("Fact"));
    }

    #[test]
    fn test_config_constant_mismatch() {
        let module = parse_module(
            r#"---- MODULE Test ----
CONSTANT N, M
VARIABLE x
Init == x = N
Next == x' = x + M
===="#,
        );
        let config = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            constant_names: vec!["N".to_string(), "P".to_string()],
            has_config: true,
            ..Default::default()
        };
        let mut issues = Vec::new();
        check_config_constants(&module, &config, &mut issues);
        // "P" is in config but not in spec => warning
        // "M" is in spec but not in config => error
        assert!(issues.len() >= 1);
        let codes: Vec<_> = issues.iter().map(|i| i.code).collect();
        assert!(codes.contains(&"V003"), "expected V003, got: {codes:?}");
    }
}
