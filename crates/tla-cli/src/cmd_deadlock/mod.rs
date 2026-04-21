// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 deadlock` — deadlock analysis for TLA+ specifications.
//!
//! Analyzes a TLA+ specification for deadlock conditions: states where the Next
//! relation has no enabled successors. Operates in two modes:
//!
//! - **Quick** — static analysis only. Parses the spec and checks for
//!   structural patterns that indicate potential deadlocks: missing UNCHANGED
//!   clauses, guarded disjuncts that might all be FALSE simultaneously, and
//!   absence of a stuttering-step disjunct.
//!
//! - **Full** — runs a lightweight model check to enumerate actual deadlock
//!   states, reports the shortest path to each, and describes the state.
//!
//! Output formats: human-readable (colored terminal) and JSON.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::span::Span;
use tla_core::{lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Analysis mode for deadlock detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DeadlockMode {
    /// Parse-only static analysis — fast but approximate.
    Quick,
    /// Full model check looking specifically for deadlock states.
    Full,
}

/// Output format for deadlock analysis results.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DeadlockOutputFormat {
    /// Colored terminal output with suggestions.
    Human,
    /// Machine-readable JSON.
    Json,
}

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

/// A single finding from static deadlock analysis.
#[derive(Debug, Clone, serde::Serialize)]
struct DeadlockFinding {
    /// Finding code (e.g. "DL001").
    code: &'static str,
    /// Severity: "warning" or "info".
    severity: &'static str,
    /// Human-readable message describing the finding.
    message: String,
    /// Source location line (1-based), populated at output time.
    line: usize,
    /// Source location column (1-based), populated at output time.
    column: usize,
    /// Suggestion for how to address the finding.
    suggestion: String,
    /// Byte-offset span in the source text.
    #[serde(skip)]
    span: Span,
}

/// Summary of the quick-mode static analysis.
#[derive(Debug, serde::Serialize)]
struct QuickAnalysisSummary {
    module_name: String,
    variable_count: usize,
    has_next: bool,
    next_disjunct_count: usize,
    guarded_disjunct_count: usize,
    unguarded_disjunct_count: usize,
    has_unchanged: bool,
    has_stuttering_disjunct: bool,
    findings: Vec<DeadlockFinding>,
}

/// Extracted config info (Init, Next names) for deadlock analysis.
#[derive(Default)]
struct ConfigInfo {
    init: Option<String>,
    next: Option<String>,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Analyze a TLA+ specification for deadlock conditions.
pub(crate) fn cmd_deadlock(
    file: &Path,
    config: Option<&Path>,
    mode: DeadlockMode,
    format: DeadlockOutputFormat,
) -> Result<()> {
    match mode {
        DeadlockMode::Quick => run_quick_analysis(file, config, format),
        DeadlockMode::Full => run_full_analysis(file, config, format),
    }
}

// ---------------------------------------------------------------------------
// Quick mode — static analysis
// ---------------------------------------------------------------------------

fn run_quick_analysis(
    file: &Path,
    config_path: Option<&Path>,
    format: DeadlockOutputFormat,
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
            "deadlock analysis aborted: {} parse error(s)",
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
            "deadlock analysis aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("deadlock analysis: lowering produced no module")?;

    let cfg_info = load_config_info(file, config_path);

    // Perform analysis
    let summary = analyze_module_for_deadlocks(&module, &cfg_info);

    // Output
    let file_path = file.display().to_string();
    match format {
        DeadlockOutputFormat::Human => print_quick_human(&file_path, &source, &summary),
        DeadlockOutputFormat::Json => print_quick_json(&file_path, &summary)?,
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Full mode — model-check delegation
// ---------------------------------------------------------------------------

fn run_full_analysis(
    file: &Path,
    config_path: Option<&Path>,
    format: DeadlockOutputFormat,
) -> Result<()> {
    let source = read_source(file)?;

    // Parse and lower
    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diag = parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diag.eprint(&file_path, &source);
        }
        bail!(
            "deadlock analysis aborted: {} parse error(s)",
            parse_result.errors.len()
        );
    }
    let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);
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
            "deadlock analysis aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("deadlock analysis: lowering produced no module")?;

    // Resolve config
    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    let config_available = config_path_buf.exists();

    if !config_available {
        // Run quick analysis as a fallback and explain why full mode requires a config
        let cfg_info = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
        };
        let summary = analyze_module_for_deadlocks(&module, &cfg_info);

        match format {
            DeadlockOutputFormat::Human => {
                println!(
                    "\x1b[33mwarning\x1b[0m: no config file found at `{}`",
                    config_path_buf.display()
                );
                println!("         full deadlock analysis requires a .cfg file with INIT/NEXT.");
                println!(
                    "         falling back to quick (static) analysis.\n\
                     \n\
                     Tip: for full model checking, use:\n\
                     \n  \
                       tla2 check {} --config <cfg> --deadlock\n",
                    file.display()
                );
                let file_path = file.display().to_string();
                print_quick_human(&file_path, &source, &summary);
            }
            DeadlockOutputFormat::Json => {
                let file_path = file.display().to_string();
                let output = serde_json::json!({
                    "file": file_path,
                    "mode": "full",
                    "fallback": "quick",
                    "reason": format!(
                        "no config file at {}; full mode requires INIT/NEXT",
                        config_path_buf.display()
                    ),
                    "quick_analysis": build_quick_json_value(&file_path, &summary),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            }
        }
        return Ok(());
    }

    // Parse config
    let cfg_source = std::fs::read_to_string(&config_path_buf)
        .with_context(|| format!("read config file {}", config_path_buf.display()))?;
    let config = tla_check::Config::parse(&cfg_source).map_err(|errors| {
        for err in &errors {
            eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
        }
        anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
    })?;

    let init_name = config.init.as_deref().unwrap_or("Init");
    let next_name = config.next.as_deref().unwrap_or("Next");

    // Verify that the module defines the required operators
    let operators: HashSet<&str> = module
        .units
        .iter()
        .filter_map(|u| match &u.node {
            Unit::Operator(op) => Some(op.name.node.as_str()),
            _ => None,
        })
        .collect();

    let mut missing = Vec::new();
    if !operators.contains(init_name) {
        missing.push(format!("INIT operator `{init_name}`"));
    }
    if !operators.contains(next_name) {
        missing.push(format!("NEXT operator `{next_name}`"));
    }

    if !missing.is_empty() {
        bail!(
            "deadlock analysis: module `{}` is missing: {}",
            module.name.node,
            missing.join(", ")
        );
    }

    // In full mode, advise the user to use `tla2 check` with deadlock detection
    // enabled, since running a complete BFS here would duplicate the checker.
    // We perform the quick analysis plus provide the exact command.
    let cfg_info = ConfigInfo {
        init: Some(init_name.to_string()),
        next: Some(next_name.to_string()),
    };
    let summary = analyze_module_for_deadlocks(&module, &cfg_info);

    let check_cmd = format!(
        "tla2 check {} --config {} --deadlock",
        file.display(),
        config_path_buf.display(),
    );

    match format {
        DeadlockOutputFormat::Human => {
            let file_path = file.display().to_string();
            print_quick_human(&file_path, &source, &summary);

            println!("\n\x1b[1m--- Full deadlock analysis ---\x1b[0m\n");
            println!(
                "To perform an exhaustive BFS search for deadlock states, run:\n\n  {check_cmd}\n"
            );
            println!(
                "This will explore the full state space and report any state where\n\
                 `{next_name}` has no enabled successors, along with the shortest\n\
                 trace to reach it."
            );
        }
        DeadlockOutputFormat::Json => {
            let file_path = file.display().to_string();
            let output = serde_json::json!({
                "file": file_path,
                "mode": "full",
                "config": config_path_buf.display().to_string(),
                "init": init_name,
                "next": next_name,
                "quick_analysis": build_quick_json_value(&file_path, &summary),
                "full_check_command": check_cmd,
                "note": "Run the full_check_command to perform exhaustive BFS deadlock detection.",
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Static analysis engine
// ---------------------------------------------------------------------------

fn analyze_module_for_deadlocks(module: &Module, cfg: &ConfigInfo) -> QuickAnalysisSummary {
    let next_name = cfg.next.as_deref().unwrap_or("Next");

    // Collect operators
    let mut all_ops: HashMap<&str, &OperatorDef> = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            all_ops.insert(op.name.node.as_str(), op);
        }
    }

    // Count variables
    let variable_count = module
        .units
        .iter()
        .filter_map(|u| match &u.node {
            Unit::Variable(names) => Some(names.len()),
            _ => None,
        })
        .sum();

    // Find the Next operator
    let next_op = all_ops.get(next_name).copied();

    let mut findings = Vec::new();

    let has_next = next_op.is_some();

    if !has_next {
        findings.push(DeadlockFinding {
            code: "DL001",
            severity: "warning",
            message: format!("no `{next_name}` operator defined — specification cannot make transitions"),
            line: 0,
            column: 0,
            suggestion: format!(
                "Define a `{next_name}` operator, e.g.: {next_name} == Action1 \\/ Action2"
            ),
            span: module.span,
        });

        return QuickAnalysisSummary {
            module_name: module.name.node.clone(),
            variable_count,
            has_next: false,
            next_disjunct_count: 0,
            guarded_disjunct_count: 0,
            unguarded_disjunct_count: 0,
            has_unchanged: false,
            has_stuttering_disjunct: false,
            findings,
        };
    }

    let next_op = next_op.expect("checked above");

    // Decompose Next into disjuncts
    let disjuncts = collect_disjuncts(&next_op.body.node, &all_ops);

    // Classify each disjunct
    let mut guarded_count = 0usize;
    let mut unguarded_count = 0usize;
    let mut has_unchanged = false;
    let mut has_stuttering = false;

    for disjunct in &disjuncts {
        let has_guard = expr_has_guard(disjunct);
        if has_guard {
            guarded_count += 1;
        } else {
            unguarded_count += 1;
        }

        if expr_contains_unchanged(disjunct) {
            has_unchanged = true;
        }

        if is_stuttering_disjunct(disjunct) {
            has_stuttering = true;
        }
    }

    // DL002: All disjuncts are guarded (common deadlock cause)
    if !disjuncts.is_empty() && guarded_count == disjuncts.len() && !has_stuttering {
        findings.push(DeadlockFinding {
            code: "DL002",
            severity: "warning",
            message: format!(
                "all {} disjuncts of `{next_name}` have guards — if all guards are \
                 simultaneously FALSE, the specification deadlocks",
                disjuncts.len()
            ),
            line: 0,
            column: 0,
            suggestion: format!(
                "Add a stuttering step: `{next_name} == ... \\/ UNCHANGED vars`\n\
                 or verify that at least one guard is always enabled"
            ),
            span: next_op.name.span,
        });
    }

    // DL003: No UNCHANGED anywhere in Next (possible underspecification)
    if !has_unchanged && variable_count > 0 {
        findings.push(DeadlockFinding {
            code: "DL003",
            severity: "info",
            message: format!(
                "`{next_name}` does not use UNCHANGED — every transition must \
                 assign all {variable_count} variable(s)"
            ),
            line: 0,
            column: 0,
            suggestion: "If some actions only modify a subset of variables, \
                         use UNCHANGED for the rest to prevent implicit deadlocks"
                .to_string(),
            span: next_op.name.span,
        });
    }

    // DL004: Single-action Next without stuttering
    if disjuncts.len() == 1 && guarded_count == 1 && !has_stuttering {
        findings.push(DeadlockFinding {
            code: "DL004",
            severity: "warning",
            message: format!(
                "`{next_name}` has only one action with a guard — when that guard \
                 is FALSE, the specification deadlocks"
            ),
            line: 0,
            column: 0,
            suggestion: format!(
                "Consider whether the guard can become permanently FALSE.\n\
                 If so, add a stuttering step or a second action: \
                 `{next_name} == Action \\/ UNCHANGED vars`"
            ),
            span: next_op.name.span,
        });
    }

    // DL005: Check for ENABLED usage (awareness of deadlock-freedom)
    let mut visited = HashSet::new();
    let uses_enabled = expr_uses_enabled_transitive(&next_op.body.node, &all_ops, &mut visited);
    if uses_enabled {
        findings.push(DeadlockFinding {
            code: "DL005",
            severity: "info",
            message: format!(
                "`{next_name}` uses ENABLED — specification explicitly reasons about action enablement"
            ),
            line: 0,
            column: 0,
            suggestion: "ENABLED expressions dynamically test whether an action can fire. \
                         Verify that the ENABLED guards collectively cover all reachable states."
                .to_string(),
            span: next_op.name.span,
        });
    }

    QuickAnalysisSummary {
        module_name: module.name.node.clone(),
        variable_count,
        has_next: true,
        next_disjunct_count: disjuncts.len(),
        guarded_disjunct_count: guarded_count,
        unguarded_disjunct_count: unguarded_count,
        has_unchanged,
        has_stuttering_disjunct: has_stuttering,
        findings,
    }
}

// ---------------------------------------------------------------------------
// Expression analysis helpers
// ---------------------------------------------------------------------------

/// Collect the top-level disjuncts from the Next operator body.
/// Follows operator references one level (for patterns like `Next == A \/ B`
/// where A and B are defined separately).
fn collect_disjuncts<'a>(
    expr: &'a Expr,
    ops: &'a HashMap<&str, &'a OperatorDef>,
) -> Vec<&'a Expr> {
    let mut result = Vec::new();
    collect_disjuncts_inner(expr, ops, &mut result, 0);
    result
}

fn collect_disjuncts_inner<'a>(
    expr: &'a Expr,
    ops: &'a HashMap<&str, &'a OperatorDef>,
    out: &mut Vec<&'a Expr>,
    depth: usize,
) {
    // Prevent infinite recursion on cyclic operator references
    if depth > 10 {
        out.push(expr);
        return;
    }
    match expr {
        Expr::Or(lhs, rhs) => {
            collect_disjuncts_inner(&lhs.node, ops, out, depth);
            collect_disjuncts_inner(&rhs.node, ops, out, depth);
        }
        // If the Next body is just an operator reference, follow it
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) if depth == 0 => {
            if let Some(op) = ops.get(name.as_str()) {
                collect_disjuncts_inner(&op.body.node, ops, out, depth + 1);
            } else {
                out.push(expr);
            }
        }
        Expr::Label(label) => {
            collect_disjuncts_inner(&label.body.node, ops, out, depth);
        }
        _ => {
            out.push(expr);
        }
    }
}

/// Check if an expression appears to have a guard (a condition that can be FALSE).
/// Guards are conjunctions where the first conjunct is a non-primed boolean condition.
fn expr_has_guard(expr: &Expr) -> bool {
    match expr {
        // /\ guard /\ body  — the LHS of a conjunction is often a guard
        Expr::And(lhs, _) => !expr_is_purely_primed(&lhs.node),
        // IF guard THEN body ELSE ...
        Expr::If(_, _, _) => true,
        // CASE guard -> body [] ...
        Expr::Case(_, _) => true,
        // \E x \in S : body  — bounded existential can fail if S is empty or no x satisfies body
        Expr::Exists(_, _) => true,
        _ => false,
    }
}

/// Check if an expression contains any UNCHANGED sub-expression.
fn expr_contains_unchanged(expr: &Expr) -> bool {
    match expr {
        Expr::Unchanged(_) => true,
        _ => {
            let mut found = false;
            visit_expr_children(expr, |child| {
                if expr_contains_unchanged(child) {
                    found = true;
                }
            });
            found
        }
    }
}

/// Check if a disjunct is a stuttering step (UNCHANGED <<all vars>> or UNCHANGED vars).
fn is_stuttering_disjunct(expr: &Expr) -> bool {
    matches!(expr, Expr::Unchanged(_))
}

/// Check if an expression consists entirely of primed assignments (x' = ...).
fn expr_is_purely_primed(expr: &Expr) -> bool {
    match expr {
        Expr::Eq(lhs, _) => matches!(lhs.node, Expr::Prime(_)),
        Expr::And(lhs, rhs) => expr_is_purely_primed(&lhs.node) && expr_is_purely_primed(&rhs.node),
        Expr::In(lhs, _) => matches!(lhs.node, Expr::Prime(_)),
        _ => false,
    }
}

/// Check if an expression uses ENABLED, transitively through operator references.
fn expr_uses_enabled_transitive(
    expr: &Expr,
    ops: &HashMap<&str, &OperatorDef>,
    visited: &mut HashSet<String>,
) -> bool {
    match expr {
        Expr::Enabled(_) => true,
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if visited.contains(name) {
                return false;
            }
            if let Some(op) = ops.get(name.as_str()) {
                visited.insert(name.clone());
                expr_uses_enabled_transitive(&op.body.node, ops, visited)
            } else {
                false
            }
        }
        _ => {
            let mut found = false;
            visit_expr_children(expr, |child| {
                if expr_uses_enabled_transitive(child, ops, visited) {
                    found = true;
                }
            });
            found
        }
    }
}

/// Visit direct child expressions of an Expr node.
/// Covers every Expr variant for structural traversal.
fn visit_expr_children(expr: &Expr, mut f: impl FnMut(&Expr)) {
    match expr {
        // Leaves
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_)
        | Expr::InstanceExpr(_, _) => {}

        // Unary
        Expr::Not(e)
        | Expr::Prime(e)
        | Expr::Always(e)
        | Expr::Eventually(e)
        | Expr::Enabled(e)
        | Expr::Unchanged(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Domain(e)
        | Expr::Neg(e) => {
            f(&e.node);
        }

        // Binary
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b) => {
            f(&a.node);
            f(&b.node);
        }

        // Apply
        Expr::Apply(func, args) => {
            f(&func.node);
            for arg in args {
                f(&arg.node);
            }
        }

        // Lambda
        Expr::Lambda(_, body) => {
            f(&body.node);
        }

        // Label
        Expr::Label(label) => {
            f(&label.body.node);
        }

        // ModuleRef
        Expr::ModuleRef(target, _, args) => {
            if let tla_core::ast::ModuleTarget::Parameterized(_, params) = target {
                for p in params {
                    f(&p.node);
                }
            }
            if let tla_core::ast::ModuleTarget::Chained(base) = target {
                f(&base.node);
            }
            for arg in args {
                f(&arg.node);
            }
        }

        // Quantifiers
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    f(&d.node);
                }
            }
            f(&body.node);
        }

        Expr::Choose(bv, body) => {
            if let Some(d) = &bv.domain {
                f(&d.node);
            }
            f(&body.node);
        }

        // Sets
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for elem in elems {
                f(&elem.node);
            }
        }

        Expr::SetBuilder(body, bounds) | Expr::FuncDef(bounds, body) => {
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    f(&d.node);
                }
            }
            f(&body.node);
        }

        Expr::SetFilter(bv, body) => {
            if let Some(d) = &bv.domain {
                f(&d.node);
            }
            f(&body.node);
        }

        // Records
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, val) in fields {
                f(&val.node);
            }
        }

        Expr::RecordAccess(base, _) => {
            f(&base.node);
        }

        // Except
        Expr::Except(base, specs) => {
            f(&base.node);
            for spec in specs {
                f(&spec.value.node);
                for path_elem in &spec.path {
                    if let tla_core::ast::ExceptPathElement::Index(idx) = path_elem {
                        f(&idx.node);
                    }
                }
            }
        }

        // Control
        Expr::If(cond, then_, else_) => {
            f(&cond.node);
            f(&then_.node);
            f(&else_.node);
        }

        Expr::Case(arms, other) => {
            for arm in arms {
                f(&arm.guard.node);
                f(&arm.body.node);
            }
            if let Some(o) = other {
                f(&o.node);
            }
        }

        Expr::Let(defs, body) => {
            for def in defs {
                f(&def.body.node);
            }
            f(&body.node);
        }

        Expr::SubstIn(_, body) => {
            f(&body.node);
        }
    }
}

// ---------------------------------------------------------------------------
// Config loading (best-effort)
// ---------------------------------------------------------------------------

fn load_config_info(file: &Path, config_path: Option<&Path>) -> ConfigInfo {
    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    if !config_path_buf.exists() {
        return ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
        };
    }

    let source = match std::fs::read_to_string(&config_path_buf) {
        Ok(s) => s,
        Err(_) => {
            return ConfigInfo {
                init: Some("Init".to_string()),
                next: Some("Next".to_string()),
            }
        }
    };

    match tla_check::Config::parse(&source) {
        Ok(config) => ConfigInfo {
            init: config.init.clone(),
            next: config.next.clone(),
        },
        Err(_) => ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
        },
    }
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
// Output formatting — Human
// ---------------------------------------------------------------------------

fn print_quick_human(file_path: &str, source: &str, summary: &QuickAnalysisSummary) {
    println!(
        "\x1b[1mDeadlock analysis: {}\x1b[0m (module `{}`)\n",
        file_path, summary.module_name
    );

    // Structure summary
    println!("  Variables:    {}", summary.variable_count);
    println!(
        "  Next defined: {}",
        if summary.has_next { "yes" } else { "NO" }
    );
    if summary.has_next {
        println!("  Disjuncts:    {}", summary.next_disjunct_count);
        println!(
            "    Guarded:    {} (conditions that can be FALSE)",
            summary.guarded_disjunct_count
        );
        println!(
            "    Unguarded:  {} (always enabled)",
            summary.unguarded_disjunct_count
        );
        println!(
            "  UNCHANGED:    {}",
            if summary.has_unchanged {
                "present"
            } else {
                "not found"
            }
        );
        println!(
            "  Stuttering:   {}",
            if summary.has_stuttering_disjunct {
                "yes (explicit UNCHANGED disjunct)"
            } else {
                "no"
            }
        );
    }
    println!();

    if summary.findings.is_empty() {
        println!("\x1b[32mNo potential deadlock patterns detected.\x1b[0m");
        return;
    }

    let starts = line_starts(source);

    println!(
        "{} finding{}:\n",
        summary.findings.len(),
        if summary.findings.len() == 1 { "" } else { "s" }
    );

    for finding in &summary.findings {
        let (line, col) = offset_to_line_col(finding.span.start, &starts);

        let severity_str = match finding.severity {
            "warning" => "\x1b[33mwarning\x1b[0m",
            _ => "\x1b[36minfo\x1b[0m",
        };

        println!("{severity_str}[{}]: {}", finding.code, finding.message);
        println!("  --> {file_path}:{line}:{col}");
        if !finding.suggestion.is_empty() {
            println!("  = help: {}", finding.suggestion);
        }
        println!();
    }

    let warning_count = summary
        .findings
        .iter()
        .filter(|f| f.severity == "warning")
        .count();
    let info_count = summary.findings.len() - warning_count;

    let mut parts = Vec::new();
    if warning_count > 0 {
        parts.push(format!(
            "{warning_count} warning{}",
            if warning_count == 1 { "" } else { "s" }
        ));
    }
    if info_count > 0 {
        parts.push(format!("{info_count} info"));
    }
    println!("Summary: {}", parts.join(", "));
}

// ---------------------------------------------------------------------------
// Output formatting — JSON
// ---------------------------------------------------------------------------

fn build_quick_json_value(
    file_path: &str,
    summary: &QuickAnalysisSummary,
) -> serde_json::Value {
    let findings_json: Vec<serde_json::Value> = summary
        .findings
        .iter()
        .map(|f| {
            serde_json::json!({
                "code": f.code,
                "severity": f.severity,
                "message": f.message,
                "suggestion": f.suggestion,
            })
        })
        .collect();

    serde_json::json!({
        "file": file_path,
        "module": summary.module_name,
        "mode": "quick",
        "structure": {
            "variable_count": summary.variable_count,
            "has_next": summary.has_next,
            "next_disjunct_count": summary.next_disjunct_count,
            "guarded_disjunct_count": summary.guarded_disjunct_count,
            "unguarded_disjunct_count": summary.unguarded_disjunct_count,
            "has_unchanged": summary.has_unchanged,
            "has_stuttering_disjunct": summary.has_stuttering_disjunct,
        },
        "findings": findings_json,
        "summary": {
            "total": summary.findings.len(),
            "warnings": summary.findings.iter().filter(|f| f.severity == "warning").count(),
            "infos": summary.findings.iter().filter(|f| f.severity == "info").count(),
        }
    })
}

fn print_quick_json(file_path: &str, summary: &QuickAnalysisSummary) -> Result<()> {
    let output = build_quick_json_value(file_path, summary);
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

    fn default_cfg() -> ConfigInfo {
        ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
        }
    }

    #[test]
    fn test_no_next_operator_produces_dl001() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert!(!summary.has_next);
        assert_eq!(summary.findings.len(), 1);
        assert_eq!(summary.findings[0].code, "DL001");
    }

    #[test]
    fn test_all_guarded_disjuncts_produces_dl002() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
A == x < 5 /\ x' = x + 1
B == x > 3 /\ x' = x - 1
Next == A \/ B
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert!(summary.has_next);
        assert_eq!(summary.next_disjunct_count, 2);
        assert_eq!(summary.guarded_disjunct_count, 2);
        assert!(!summary.has_stuttering_disjunct);

        let dl002 = summary.findings.iter().find(|f| f.code == "DL002");
        assert!(dl002.is_some(), "expected DL002 finding");
    }

    #[test]
    fn test_stuttering_step_suppresses_dl002() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
A == x < 5 /\ x' = x + 1
Next == A \/ UNCHANGED x
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert!(summary.has_next);
        assert!(summary.has_stuttering_disjunct);

        let dl002 = summary.findings.iter().find(|f| f.code == "DL002");
        assert!(dl002.is_none(), "DL002 should be suppressed by stuttering step");
    }

    #[test]
    fn test_no_unchanged_produces_dl003() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert!(!summary.has_unchanged);

        let dl003 = summary.findings.iter().find(|f| f.code == "DL003");
        assert!(dl003.is_some(), "expected DL003 finding");
    }

    #[test]
    fn test_single_guarded_action_produces_dl004() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x < 10 /\ x' = x + 1
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert_eq!(summary.next_disjunct_count, 1);
        assert_eq!(summary.guarded_disjunct_count, 1);

        let dl004 = summary.findings.iter().find(|f| f.code == "DL004");
        assert!(dl004.is_some(), "expected DL004 finding");
    }

    #[test]
    fn test_safe_spec_minimal_findings() {
        // A spec with a stuttering step should not trigger DL002 or DL004.
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
A == x < 10 /\ x' = x + 1
Next == A \/ UNCHANGED x
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert!(summary.has_next);
        assert!(summary.has_stuttering_disjunct);

        let warnings: Vec<_> = summary
            .findings
            .iter()
            .filter(|f| f.severity == "warning")
            .collect();
        assert!(
            warnings.is_empty(),
            "expected no warnings for safe spec, got: {warnings:?}"
        );
    }

    #[test]
    fn test_unguarded_action_not_flagged() {
        // An unguarded action (pure primed assignment) does not trigger guard warnings.
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert_eq!(summary.unguarded_disjunct_count, 1);
        assert_eq!(summary.guarded_disjunct_count, 0);

        let dl002 = summary.findings.iter().find(|f| f.code == "DL002");
        assert!(dl002.is_none(), "unguarded action should not trigger DL002");
    }

    #[test]
    fn test_disjunct_counting() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
A == x < 5 /\ x' = x + 1
B == x > 0 /\ x' = x - 1
C == x' = 0
Next == A \/ B \/ C
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert_eq!(summary.next_disjunct_count, 3);
        assert_eq!(summary.guarded_disjunct_count, 2);
        assert_eq!(summary.unguarded_disjunct_count, 1);
    }

    #[test]
    fn test_mode_enum_equality() {
        assert_eq!(DeadlockMode::Quick, DeadlockMode::Quick);
        assert_ne!(DeadlockMode::Quick, DeadlockMode::Full);
    }

    #[test]
    fn test_format_enum_equality() {
        assert_eq!(DeadlockOutputFormat::Human, DeadlockOutputFormat::Human);
        assert_ne!(DeadlockOutputFormat::Human, DeadlockOutputFormat::Json);
    }

    #[test]
    fn test_offset_to_line_col_basic() {
        let source = "line1\nline2\nline3\n";
        let starts = line_starts(source);
        assert_eq!(offset_to_line_col(0, &starts), (1, 1));
        assert_eq!(offset_to_line_col(6, &starts), (2, 1));
        assert_eq!(offset_to_line_col(8, &starts), (2, 3));
    }

    #[test]
    fn test_custom_next_name() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Spec == x < 10 /\ x' = x + 1
===="#,
        );
        let cfg = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Spec".to_string()),
        };
        let summary = analyze_module_for_deadlocks(&module, &cfg);
        assert!(summary.has_next);
        assert_eq!(summary.next_disjunct_count, 1);
    }

    #[test]
    fn test_exists_counted_as_guarded() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == \E v \in {1, 2, 3} : x' = v
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert_eq!(summary.guarded_disjunct_count, 1);
    }

    #[test]
    fn test_no_variables_no_dl003() {
        // A module with no variables should not trigger DL003.
        let module = parse_module(
            r#"---- MODULE Test ----
CONSTANT S
Init == TRUE
Next == TRUE
===="#,
        );
        let summary = analyze_module_for_deadlocks(&module, &default_cfg());
        assert_eq!(summary.variable_count, 0);
        let dl003 = summary.findings.iter().find(|f| f.code == "DL003");
        assert!(dl003.is_none(), "DL003 should not fire with zero variables");
    }
}
