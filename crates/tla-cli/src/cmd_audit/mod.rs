// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 audit` -- comprehensive project-level audit of a TLA+ specification directory.
//!
//! Scans a directory for `.tla` and `.cfg` files, then runs structural checks:
//! spec/config pairing, parse validation, naming conventions, complexity metrics,
//! anti-pattern detection, and config completeness. Produces a scorecard with
//! pass/warn/fail per check in human (colored table) or JSON format.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use tla_core::ast::{Expr, Module, Unit};
use tla_core::{lower_main_module, parse, FileId, SyntaxNode};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the audit report.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum AuditOutputFormat {
    #[default]
    Human,
    Json,
}

/// Result status for an individual audit check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "lowercase")]
enum CheckStatus {
    Pass,
    Warn,
    Fail,
}

impl std::fmt::Display for CheckStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckStatus::Pass => write!(f, "PASS"),
            CheckStatus::Warn => write!(f, "WARN"),
            CheckStatus::Fail => write!(f, "FAIL"),
        }
    }
}

/// A single check result on the audit scorecard.
#[derive(Clone, Debug, serde::Serialize)]
struct CheckResult {
    code: &'static str,
    name: &'static str,
    status: CheckStatus,
    details: Vec<String>,
}

/// Complexity metrics for a single `.tla` file.
#[derive(Clone, Debug, Default, serde::Serialize)]
struct FileMetrics {
    file: String,
    operator_count: usize,
    variable_count: usize,
    constant_count: usize,
    max_nesting_depth: usize,
    max_quantifier_depth: usize,
}

/// Parsed file bundle used throughout the audit checks.
type ParsedFile = (PathBuf, String, Option<Module>, Vec<String>);

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_audit(dir: &Path, format: AuditOutputFormat) -> Result<()> {
    let dir = dir
        .canonicalize()
        .with_context(|| format!("canonicalize audit directory: {}", dir.display()))?;

    let tla_files = discover_files(&dir, "tla");
    let cfg_files = discover_files(&dir, "cfg");

    let stem_set = |files: &[PathBuf]| -> HashSet<String> {
        files
            .iter()
            .filter_map(|p| p.file_stem().map(|s| s.to_string_lossy().into_owned()))
            .collect()
    };
    let tla_set = stem_set(&tla_files);
    let cfg_set = stem_set(&cfg_files);

    let parsed: Vec<ParsedFile> = tla_files
        .iter()
        .map(|path| {
            let source = std::fs::read_to_string(path).unwrap_or_default();
            let (module, errors) = try_parse_module(path, &source);
            (path.clone(), source, module, errors)
        })
        .collect();

    let checks = vec![
        check_spec_config_pairing(&tla_set, &cfg_set),
        check_parse_validation(&parsed),
        check_naming_conventions(&parsed),
        check_complexity(&parsed),
        check_anti_patterns(&parsed),
        check_config_completeness(&dir, &parsed, &cfg_files),
    ];

    let metrics: Vec<FileMetrics> = parsed
        .iter()
        .filter_map(|(path, _, m, _)| m.as_ref().map(|m| collect_file_metrics(path, m)))
        .collect();

    let has_fail = checks.iter().any(|c| matches!(c.status, CheckStatus::Fail));

    match format {
        AuditOutputFormat::Human => print_human(&dir, &tla_files, &cfg_files, &checks, &metrics),
        AuditOutputFormat::Json => print_json(&dir, &tla_files, &cfg_files, &checks, &metrics)?,
    }

    if has_fail {
        std::process::exit(1);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// File discovery
// ---------------------------------------------------------------------------

fn discover_files(dir: &Path, extension: &str) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.extension().map_or(false, |e| e == extension))
        .collect();
    files.sort();
    files
}

// ---------------------------------------------------------------------------
// Parsing helper
// ---------------------------------------------------------------------------

fn try_parse_module(path: &Path, source: &str) -> (Option<Module>, Vec<String>) {
    let parse_result = parse(source);
    if !parse_result.errors.is_empty() {
        let errors = parse_result
            .errors
            .iter()
            .map(|e| format!("{}:{}: {}", path.display(), e.start, e.message))
            .collect();
        return (None, errors);
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);
    let hint = path
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let lower_result = lower_main_module(FileId(0), &tree, hint);
    if !lower_result.errors.is_empty() {
        let errors = lower_result
            .errors
            .iter()
            .map(|e| format!("{}:{}: {}", path.display(), e.span.start, e.message))
            .collect();
        return (None, errors);
    }
    (lower_result.module, Vec::new())
}

// ---------------------------------------------------------------------------
// A001: Spec/config pairing
// ---------------------------------------------------------------------------

fn check_spec_config_pairing(tla_set: &HashSet<String>, cfg_set: &HashSet<String>) -> CheckResult {
    let mut details = Vec::new();
    for name in tla_set.iter().filter(|n| !cfg_set.contains(n.as_str())) {
        details.push(format!("{name}.tla has no matching .cfg file"));
    }
    for name in cfg_set.iter().filter(|n| !tla_set.contains(n.as_str())) {
        details.push(format!("{name}.cfg has no matching .tla file"));
    }
    let status = if tla_set.is_empty() {
        CheckStatus::Fail
    } else if details.is_empty() {
        CheckStatus::Pass
    } else {
        CheckStatus::Warn
    };
    CheckResult {
        code: "A001",
        name: "Spec/config pairing",
        status,
        details,
    }
}

// ---------------------------------------------------------------------------
// A002: Parse validation
// ---------------------------------------------------------------------------

fn check_parse_validation(parsed: &[ParsedFile]) -> CheckResult {
    let mut details = Vec::new();
    for (path, _, module, errors) in parsed {
        if module.is_none() {
            details.push(format!(
                "{}: {} parse/lower error(s)",
                path.display(),
                errors.len()
            ));
            for err in errors.iter().take(3) {
                details.push(format!("  {err}"));
            }
        }
    }
    let status = if details.is_empty() {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    };
    CheckResult {
        code: "A002",
        name: "Parse validation",
        status,
        details,
    }
}

// ---------------------------------------------------------------------------
// A003: Naming conventions (module name matches filename)
// ---------------------------------------------------------------------------

fn check_naming_conventions(parsed: &[ParsedFile]) -> CheckResult {
    let mut details = Vec::new();
    for (path, _, module, _) in parsed {
        let Some(module) = module else { continue };
        let expected = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        if !expected.is_empty() && module.name.node != expected {
            details.push(format!(
                "{}: module name `{}` does not match filename `{expected}`",
                path.display(),
                module.name.node
            ));
        }
    }
    let status = if details.is_empty() {
        CheckStatus::Pass
    } else {
        CheckStatus::Warn
    };
    CheckResult {
        code: "A003",
        name: "Naming conventions",
        status,
        details,
    }
}

// ---------------------------------------------------------------------------
// A004: Complexity metrics (thresholds on nesting, quantifiers, operator count)
// ---------------------------------------------------------------------------

fn check_complexity(parsed: &[ParsedFile]) -> CheckResult {
    let mut details = Vec::new();
    for (path, _, module, _) in parsed {
        let Some(module) = module else { continue };
        let m = collect_file_metrics(path, module);
        if m.max_nesting_depth > 6 {
            details.push(format!(
                "{}: max nesting depth {} (threshold 6)",
                path.display(),
                m.max_nesting_depth
            ));
        }
        if m.max_quantifier_depth > 3 {
            details.push(format!(
                "{}: max quantifier depth {} (threshold 3)",
                path.display(),
                m.max_quantifier_depth
            ));
        }
        if m.operator_count > 50 {
            details.push(format!(
                "{}: {} operators (consider splitting)",
                path.display(),
                m.operator_count
            ));
        }
    }
    let status = if details.is_empty() {
        CheckStatus::Pass
    } else {
        CheckStatus::Warn
    };
    CheckResult {
        code: "A004",
        name: "Complexity metrics",
        status,
        details,
    }
}

// ---------------------------------------------------------------------------
// A005: Anti-patterns (missing EXTENDS, duplicate ops, unbounded quantifiers)
// ---------------------------------------------------------------------------

fn check_anti_patterns(parsed: &[ParsedFile]) -> CheckResult {
    let mut details = Vec::new();
    for (path, _, module, _) in parsed {
        let Some(module) = module else { continue };
        let fname = path.display();

        if module.extends.is_empty() {
            details.push(format!("{fname}: no EXTENDS declaration"));
        }

        // Duplicate operator names
        let mut seen_ops: HashSet<&str> = HashSet::new();
        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                if !seen_ops.insert(op.name.node.as_str()) {
                    details.push(format!("{fname}: duplicate operator `{}`", op.name.node));
                }
            }
        }

        // Unbounded quantifiers
        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                find_unbounded_quantifiers(
                    &op.body.node,
                    &op.name.node,
                    &fname.to_string(),
                    &mut details,
                );
            }
        }
    }
    let status = if details.is_empty() {
        CheckStatus::Pass
    } else {
        CheckStatus::Warn
    };
    CheckResult {
        code: "A005",
        name: "Anti-patterns",
        status,
        details,
    }
}

fn find_unbounded_quantifiers(expr: &Expr, op_name: &str, fname: &str, out: &mut Vec<String>) {
    match expr {
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bv in bounds {
                if bv.domain.is_none() {
                    out.push(format!(
                        "{fname}: unbounded quantifier `{}` in `{op_name}`",
                        bv.name.node
                    ));
                }
                if let Some(d) = &bv.domain {
                    find_unbounded_quantifiers(&d.node, op_name, fname, out);
                }
            }
            find_unbounded_quantifiers(&body.node, op_name, fname, out);
        }
        Expr::Choose(bv, body) => {
            if bv.domain.is_none() {
                out.push(format!(
                    "{fname}: unbounded CHOOSE `{}` in `{op_name}`",
                    bv.name.node
                ));
            }
            if let Some(d) = &bv.domain {
                find_unbounded_quantifiers(&d.node, op_name, fname, out);
            }
            find_unbounded_quantifiers(&body.node, op_name, fname, out);
        }
        Expr::If(a, b, c) => {
            for e in [a, b, c] {
                find_unbounded_quantifiers(&e.node, op_name, fname, out);
            }
        }
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::In(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b) => {
            find_unbounded_quantifiers(&a.node, op_name, fname, out);
            find_unbounded_quantifiers(&b.node, op_name, fname, out);
        }
        Expr::Not(e)
        | Expr::Prime(e)
        | Expr::Neg(e)
        | Expr::Unchanged(e)
        | Expr::Powerset(e)
        | Expr::Domain(e)
        | Expr::BigUnion(e) => {
            find_unbounded_quantifiers(&e.node, op_name, fname, out);
        }
        Expr::Apply(func, args) => {
            find_unbounded_quantifiers(&func.node, op_name, fname, out);
            for arg in args {
                find_unbounded_quantifiers(&arg.node, op_name, fname, out);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                find_unbounded_quantifiers(&def.body.node, op_name, fname, out);
            }
            find_unbounded_quantifiers(&body.node, op_name, fname, out);
        }
        Expr::SetEnum(es) | Expr::Tuple(es) => {
            for e in es {
                find_unbounded_quantifiers(&e.node, op_name, fname, out);
            }
        }
        Expr::SetFilter(_, _) | Expr::SetBuilder(_, _) => {}
        Expr::Case(arms, other) => {
            for arm in arms {
                find_unbounded_quantifiers(&arm.guard.node, op_name, fname, out);
                find_unbounded_quantifiers(&arm.body.node, op_name, fname, out);
            }
            if let Some(o) = other {
                find_unbounded_quantifiers(&o.node, op_name, fname, out);
            }
        }
        Expr::Label(label) => {
            find_unbounded_quantifiers(&label.body.node, op_name, fname, out);
        }
        _ => {} // Leaves and remaining forms
    }
}

// ---------------------------------------------------------------------------
// A006: Config completeness (all CONSTANTs assigned)
// ---------------------------------------------------------------------------

fn check_config_completeness(
    dir: &Path,
    parsed: &[ParsedFile],
    cfg_files: &[PathBuf],
) -> CheckResult {
    let mut details = Vec::new();
    for (path, _, module, _) in parsed {
        let Some(module) = module else { continue };
        let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        let cfg_path = dir.join(format!("{stem}.cfg"));
        if !cfg_files.contains(&cfg_path) {
            continue;
        }

        let spec_constants: HashSet<String> = module
            .units
            .iter()
            .flat_map(|u| match &u.node {
                Unit::Constant(decls) => decls
                    .iter()
                    .map(|d| d.name.node.clone())
                    .collect::<Vec<_>>(),
                _ => Vec::new(),
            })
            .collect();
        if spec_constants.is_empty() {
            continue;
        }

        let cfg_source = match std::fs::read_to_string(&cfg_path) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let cfg_constants: HashSet<String> = match tla_check::Config::parse(&cfg_source) {
            Ok(c) => c.constants.keys().cloned().collect(),
            Err(_) => {
                details.push(format!("{}: .cfg parse error", cfg_path.display()));
                continue;
            }
        };
        for name in spec_constants
            .iter()
            .filter(|c| !cfg_constants.contains(c.as_str()))
        {
            details.push(format!("{stem}.cfg: CONSTANT `{name}` not assigned"));
        }
    }
    let status = if details.is_empty() {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    };
    CheckResult {
        code: "A006",
        name: "Config completeness",
        status,
        details,
    }
}

// ---------------------------------------------------------------------------
// Per-file metrics
// ---------------------------------------------------------------------------

fn collect_file_metrics(path: &Path, module: &Module) -> FileMetrics {
    let mut m = FileMetrics {
        file: path.display().to_string(),
        ..Default::default()
    };
    for unit in &module.units {
        match &unit.node {
            Unit::Operator(_) => m.operator_count += 1,
            Unit::Variable(names) => m.variable_count += names.len(),
            Unit::Constant(decls) => m.constant_count += decls.len(),
            _ => {}
        }
    }
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            let (n, q) = expr_depths(&op.body.node, 0, 0);
            m.max_nesting_depth = m.max_nesting_depth.max(n);
            m.max_quantifier_depth = m.max_quantifier_depth.max(q);
        }
    }
    m
}

fn expr_depths(expr: &Expr, nest: usize, quant: usize) -> (usize, usize) {
    match expr {
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            let (mut bn, mut bq) = (nest + 1, quant + 1);
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    let (n, q) = expr_depths(&d.node, bn, bq);
                    bn = bn.max(n);
                    bq = bq.max(q);
                }
            }
            let (n, q) = expr_depths(&body.node, bn, bq);
            (bn.max(n), bq.max(q))
        }
        Expr::If(a, b, c) => {
            let nn = nest + 1;
            let (mut bn, mut bq) = (nn, quant);
            for e in [a, b, c] {
                let (n, q) = expr_depths(&e.node, nn, quant);
                bn = bn.max(n);
                bq = bq.max(q);
            }
            (bn, bq)
        }
        Expr::Choose(bv, body) => {
            let (nn, nq) = (nest + 1, quant + 1);
            let (mut bn, mut bq) = (nn, nq);
            if let Some(d) = &bv.domain {
                let (n, q) = expr_depths(&d.node, nn, nq);
                bn = bn.max(n);
                bq = bq.max(q);
            }
            let (n, q) = expr_depths(&body.node, nn, nq);
            (bn.max(n), bq.max(q))
        }
        Expr::Let(defs, body) => {
            let nn = nest + 1;
            let (mut bn, mut bq) = (nn, quant);
            for def in defs {
                let (n, q) = expr_depths(&def.body.node, nn, quant);
                bn = bn.max(n);
                bq = bq.max(q);
            }
            let (n, q) = expr_depths(&body.node, nn, quant);
            (bn.max(n), bq.max(q))
        }
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::In(a, b)
        | Expr::Eq(a, b) => {
            let (n1, q1) = expr_depths(&a.node, nest, quant);
            let (n2, q2) = expr_depths(&b.node, nest, quant);
            (n1.max(n2), q1.max(q2))
        }
        Expr::Not(e) | Expr::Prime(e) | Expr::Neg(e) | Expr::Unchanged(e) => {
            expr_depths(&e.node, nest, quant)
        }
        Expr::Apply(func, args) => {
            let (mut bn, mut bq) = expr_depths(&func.node, nest, quant);
            for arg in args {
                let (n, q) = expr_depths(&arg.node, nest, quant);
                bn = bn.max(n);
                bq = bq.max(q);
            }
            (bn, bq)
        }
        _ => (nest, quant),
    }
}

// ---------------------------------------------------------------------------
// Output formatting: Human
// ---------------------------------------------------------------------------

fn print_human(
    dir: &Path,
    tla: &[PathBuf],
    cfg: &[PathBuf],
    checks: &[CheckResult],
    metrics: &[FileMetrics],
) {
    println!(
        "Audit Report: {} ({} .tla, {} .cfg)",
        dir.display(),
        tla.len(),
        cfg.len()
    );
    println!("{}", "=".repeat(70));
    println!();
    println!(
        "  {:<8} {:<26} {:<6} {}",
        "Code", "Check", "Status", "Details"
    );
    println!("  {}", "-".repeat(64));

    for c in checks {
        let color = match c.status {
            CheckStatus::Pass => "\x1b[32mPASS\x1b[0m",
            CheckStatus::Warn => "\x1b[33mWARN\x1b[0m",
            CheckStatus::Fail => "\x1b[31mFAIL\x1b[0m",
        };
        let detail = if c.details.is_empty() {
            "OK".into()
        } else {
            format!("{} finding(s)", c.details.len())
        };
        println!("  {:<8} {:<26} {:<15} {}", c.code, c.name, color, detail);
    }

    let non_passing: Vec<_> = checks
        .iter()
        .filter(|c| !matches!(c.status, CheckStatus::Pass))
        .collect();
    if !non_passing.is_empty() {
        println!("\nDetails:\n{}", "-".repeat(70));
        for c in non_passing {
            println!("\n  [{}] {} ({})", c.code, c.name, c.status);
            for d in &c.details {
                println!("    - {d}");
            }
        }
    }

    if !metrics.is_empty() {
        println!("\nComplexity Metrics:\n{}", "-".repeat(70));
        println!(
            "  {:<30} {:>5} {:>5} {:>5} {:>5} {:>5}",
            "File", "Ops", "Vars", "Cnst", "Nest", "Quant"
        );
        for m in metrics {
            let short = Path::new(&m.file)
                .file_name()
                .map(|f| f.to_string_lossy().into_owned())
                .unwrap_or_default();
            println!(
                "  {:<30} {:>5} {:>5} {:>5} {:>5} {:>5}",
                short,
                m.operator_count,
                m.variable_count,
                m.constant_count,
                m.max_nesting_depth,
                m.max_quantifier_depth
            );
        }
    }

    println!();
    let (p, w, f) = count_statuses(checks);
    print!("Summary: {p}/{} passed", checks.len());
    if w > 0 {
        print!(", {w} warning(s)");
    }
    if f > 0 {
        print!(", {f} failure(s)");
    }
    println!();
}

fn count_statuses(checks: &[CheckResult]) -> (usize, usize, usize) {
    let p = checks
        .iter()
        .filter(|c| matches!(c.status, CheckStatus::Pass))
        .count();
    let w = checks
        .iter()
        .filter(|c| matches!(c.status, CheckStatus::Warn))
        .count();
    let f = checks
        .iter()
        .filter(|c| matches!(c.status, CheckStatus::Fail))
        .count();
    (p, w, f)
}

// ---------------------------------------------------------------------------
// Output formatting: JSON
// ---------------------------------------------------------------------------

fn print_json(
    dir: &Path,
    tla: &[PathBuf],
    cfg: &[PathBuf],
    checks: &[CheckResult],
    metrics: &[FileMetrics],
) -> Result<()> {
    let (p, w, f) = count_statuses(checks);
    let output = serde_json::json!({
        "directory": dir.display().to_string(),
        "tla_files": tla.len(),
        "cfg_files": cfg.len(),
        "checks": checks,
        "metrics": metrics,
        "summary": { "total": checks.len(), "pass": p, "warn": w, "fail": f },
        "clean": f == 0 && w == 0,
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

    fn parse_module_from_source(source: &str) -> Module {
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );
        let tree = SyntaxNode::new_root(result.green_node);
        let lr = lower_main_module(FileId(0), &tree, None);
        assert!(lr.errors.is_empty(), "lower errors: {:?}", lr.errors);
        lr.module.expect("no module produced")
    }

    #[test]
    fn test_pairing_all_matched() {
        let tla = HashSet::from(["Spec".into(), "MC".into()]);
        let cfg = HashSet::from(["Spec".into(), "MC".into()]);
        let r = check_spec_config_pairing(&tla, &cfg);
        assert_eq!(r.status, CheckStatus::Pass);
    }

    #[test]
    fn test_pairing_missing_cfg() {
        let tla = HashSet::from(["Spec".into(), "Helper".into()]);
        let cfg = HashSet::from(["Spec".into()]);
        let r = check_spec_config_pairing(&tla, &cfg);
        assert_eq!(r.status, CheckStatus::Warn);
        assert!(r.details.iter().any(|d| d.contains("Helper.tla")));
    }

    #[test]
    fn test_pairing_empty_dir() {
        let r = check_spec_config_pairing(&HashSet::new(), &HashSet::new());
        assert_eq!(r.status, CheckStatus::Fail);
    }

    #[test]
    fn test_parse_validation_clean() {
        let src = "---- MODULE T ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====";
        let (m, e) = try_parse_module(Path::new("T.tla"), src);
        let r = check_parse_validation(&[(PathBuf::from("T.tla"), src.into(), m, e)]);
        assert_eq!(r.status, CheckStatus::Pass);
    }

    #[test]
    fn test_parse_validation_error() {
        let (m, e) = try_parse_module(Path::new("Bad.tla"), "NOT VALID TLA+");
        let r =
            check_parse_validation(&[(PathBuf::from("Bad.tla"), "NOT VALID TLA+".into(), m, e)]);
        assert_eq!(r.status, CheckStatus::Fail);
    }

    #[test]
    fn test_naming_match() {
        let src = "---- MODULE Correct ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====";
        let (m, e) = try_parse_module(Path::new("Correct.tla"), src);
        let r = check_naming_conventions(&[(PathBuf::from("Correct.tla"), src.into(), m, e)]);
        assert_eq!(r.status, CheckStatus::Pass);
    }

    #[test]
    fn test_naming_mismatch() {
        let src = "---- MODULE Wrong ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====";
        let (m, e) = try_parse_module(Path::new("Right.tla"), src);
        let r = check_naming_conventions(&[(PathBuf::from("Right.tla"), src.into(), m, e)]);
        assert_eq!(r.status, CheckStatus::Warn);
        assert!(r.details[0].contains("Wrong"));
    }

    #[test]
    fn test_anti_pattern_missing_extends() {
        let src = "---- MODULE T ----\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n====";
        let (m, e) = try_parse_module(Path::new("T.tla"), src);
        let r = check_anti_patterns(&[(PathBuf::from("T.tla"), src.into(), m, e)]);
        assert_eq!(r.status, CheckStatus::Warn);
        assert!(r.details.iter().any(|d| d.contains("EXTENDS")));
    }

    #[test]
    fn test_anti_pattern_clean() {
        let src = "---- MODULE T ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n====";
        let (m, e) = try_parse_module(Path::new("T.tla"), src);
        let r = check_anti_patterns(&[(PathBuf::from("T.tla"), src.into(), m, e)]);
        assert_eq!(r.status, CheckStatus::Pass);
    }

    #[test]
    fn test_complexity_low() {
        let src = "---- MODULE T ----\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n====";
        let (m, e) = try_parse_module(Path::new("T.tla"), src);
        let r = check_complexity(&[(PathBuf::from("T.tla"), src.into(), m, e)]);
        assert_eq!(r.status, CheckStatus::Pass);
    }

    #[test]
    fn test_file_metrics() {
        let m = parse_module_from_source(
            "---- MODULE T ----\nEXTENDS Naturals\nCONSTANT N\nVARIABLE x, y\nInit == x = 0 /\\ y = 0\nNext == x' = x /\\ y' = y\nTypeOK == x \\in Nat\nH(a) == a + N\n====",
        );
        let fm = collect_file_metrics(Path::new("T.tla"), &m);
        assert_eq!(fm.operator_count, 4);
        assert_eq!(fm.variable_count, 2);
        assert_eq!(fm.constant_count, 1);
    }

    #[test]
    fn test_depth_nested_quantifiers() {
        let m = parse_module_from_source(
            "---- MODULE T ----\nVARIABLE x\nInit == x = 0\nNext == \\E n \\in {1,2} : \\A m \\in {3,4} : x' = n + m\n====",
        );
        let fm = collect_file_metrics(Path::new("T.tla"), &m);
        assert!(
            fm.max_nesting_depth >= 2,
            "nesting >= 2, got {}",
            fm.max_nesting_depth
        );
        assert!(
            fm.max_quantifier_depth >= 2,
            "quant >= 2, got {}",
            fm.max_quantifier_depth
        );
    }

    #[test]
    fn test_check_status_display() {
        assert_eq!(format!("{}", CheckStatus::Pass), "PASS");
        assert_eq!(format!("{}", CheckStatus::Warn), "WARN");
        assert_eq!(format!("{}", CheckStatus::Fail), "FAIL");
    }

    #[test]
    fn test_audit_output_format_default() {
        assert_eq!(AuditOutputFormat::default(), AuditOutputFormat::Human);
    }

    #[test]
    fn test_discover_nonexistent() {
        assert!(discover_files(Path::new("/nonexistent/path"), "tla").is_empty());
    }
}
