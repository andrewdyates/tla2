// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 lint` — static analysis and linting for TLA+ specifications.
//!
//! Parses a TLA+ spec and reports warnings about common issues:
//! unused operators, unused variables, shadowed names, missing Init/Next,
//! stuttering detection, and naming convention warnings.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{BoundVar, Expr, Module, OperatorDef, Unit};
use tla_core::span::Span;
use tla_core::{lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId};

use crate::cli_schema::LintOutputFormat;
use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_lint(
    file: &Path,
    config_path: Option<&Path>,
    format: LintOutputFormat,
    min_severity: LintSeverity,
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
        bail!("lint aborted: {} parse error(s)", parse_result.errors.len());
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
            "lint aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("lint: lowering produced no module")?;

    // Parse config if present, to determine Init/Next/invariants for reachability analysis
    let cfg_info = load_config_info(file, config_path);

    // Run all lint checks
    let file_path = file.display().to_string();
    let mut warnings = Vec::new();
    check_missing_init_next(&module, &cfg_info, &mut warnings);
    check_convention_warnings(&module, &mut warnings);
    check_unused_operators(&module, &cfg_info, &mut warnings);
    check_unused_variables(&module, &cfg_info, &mut warnings);
    check_shadowed_names(&module, &mut warnings);
    check_stuttering(&module, &cfg_info, &mut warnings);

    // Filter by severity
    let warnings: Vec<LintWarning> = warnings
        .into_iter()
        .filter(|w| w.severity as u8 <= min_severity as u8)
        .collect();

    // Output
    match format {
        LintOutputFormat::Human => print_human(&file_path, &source, &warnings),
        LintOutputFormat::Json => print_json(&file_path, &warnings)?,
    }

    if warnings.iter().any(|w| matches!(w.severity, LintSeverity::Warning)) {
        // Exit with 0 — lint warnings are informational, not errors
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Lint types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum LintSeverity {
    Warning = 0,
    Info = 1,
}

impl std::fmt::Display for LintSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LintSeverity::Warning => write!(f, "warning"),
            LintSeverity::Info => write!(f, "info"),
        }
    }
}

impl std::str::FromStr for LintSeverity {
    type Err = String;
    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "warning" | "warn" => Ok(LintSeverity::Warning),
            "info" => Ok(LintSeverity::Info),
            other => Err(format!("unknown severity: {other}")),
        }
    }
}

#[derive(Debug, Clone, serde::Serialize)]
pub(crate) struct LintWarning {
    /// Lint code (e.g., "W001")
    pub code: &'static str,
    /// Severity level
    pub severity: LintSeverity,
    /// Human-readable message
    pub message: String,
    /// Source span (byte offsets)
    #[serde(skip)]
    pub span: Span,
    /// Line number (1-based), populated at output time
    pub line: usize,
    /// Column number (1-based), populated at output time
    pub column: usize,
    /// Suggestion for fixing the issue
    pub suggestion: String,
}

/// Extracted config info relevant to linting (Init, Next, invariants).
#[derive(Default)]
struct ConfigInfo {
    init: Option<String>,
    next: Option<String>,
    invariants: Vec<String>,
    properties: Vec<String>,
}

// ---------------------------------------------------------------------------
// Config loading (best-effort, does not fail the lint)
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
        // No config — fall back to convention names
        return ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
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
        },
        Err(_) => ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        },
    }
}

// ---------------------------------------------------------------------------
// Lint checks
// ---------------------------------------------------------------------------

/// W001: Missing Init operator
/// W002: Missing Next operator
fn check_missing_init_next(module: &Module, cfg: &ConfigInfo, warnings: &mut Vec<LintWarning>) {
    let operators: HashSet<&str> = module
        .units
        .iter()
        .filter_map(|u| match &u.node {
            Unit::Operator(op) => Some(op.name.node.as_str()),
            _ => None,
        })
        .collect();

    let init_name = cfg.init.as_deref().unwrap_or("Init");
    let next_name = cfg.next.as_deref().unwrap_or("Next");

    if !operators.contains(init_name) {
        warnings.push(LintWarning {
            code: "W001",
            severity: LintSeverity::Warning,
            message: format!("no `{init_name}` operator defined"),
            span: module.span,
            line: 0,
            column: 0,
            suggestion: format!(
                "Define an `{init_name}` operator that specifies initial states"
            ),
        });
    }

    if !operators.contains(next_name) {
        warnings.push(LintWarning {
            code: "W002",
            severity: LintSeverity::Warning,
            message: format!("no `{next_name}` operator defined"),
            span: module.span,
            line: 0,
            column: 0,
            suggestion: format!(
                "Define a `{next_name}` operator that specifies state transitions"
            ),
        });
    }
}

/// W003: Convention warning — lowercase init/next might be intended as Init/Next
fn check_convention_warnings(module: &Module, warnings: &mut Vec<LintWarning>) {
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            let name = &op.name.node;
            let lower = name.to_lowercase();
            if (lower == "init" && name != "Init") || (lower == "next" && name != "Next") {
                let expected = if lower == "init" { "Init" } else { "Next" };
                warnings.push(LintWarning {
                    code: "W003",
                    severity: LintSeverity::Info,
                    message: format!(
                        "operator `{name}` looks like it might be intended as `{expected}`"
                    ),
                    span: op.name.span,
                    line: 0,
                    column: 0,
                    suggestion: format!("Rename `{name}` to `{expected}` if this is the {lower} predicate"),
                });
            }
        }
    }
}

/// W004: Unused operator — defined but never referenced by Init, Next, invariants,
/// or other reachable operators.
fn check_unused_operators(module: &Module, cfg: &ConfigInfo, warnings: &mut Vec<LintWarning>) {
    // Collect all operator definitions
    let mut all_ops: HashMap<&str, &OperatorDef> = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            all_ops.insert(op.name.node.as_str(), op);
        }
    }

    // Build the set of "root" operators (reachable from config)
    let mut roots: Vec<String> = Vec::new();
    if let Some(init) = &cfg.init {
        roots.push(init.clone());
    }
    if let Some(next) = &cfg.next {
        roots.push(next.clone());
    }
    for inv in &cfg.invariants {
        roots.push(inv.clone());
    }
    for prop in &cfg.properties {
        roots.push(prop.clone());
    }

    // If no config roots found, treat all operators as potentially reachable
    // (cannot determine unused without knowing the entry points)
    if roots.is_empty() {
        return;
    }

    // Compute transitive closure of referenced operators
    let mut referenced: HashSet<String> = HashSet::new();
    let mut worklist: Vec<String> = roots;
    while let Some(name) = worklist.pop() {
        if !referenced.insert(name.clone()) {
            continue;
        }
        if let Some(op) = all_ops.get(name.as_str()) {
            let refs = collect_ident_refs(&op.body.node);
            for r in refs {
                if all_ops.contains_key(r.as_str()) && !referenced.contains(&r) {
                    worklist.push(r);
                }
            }
        }
    }

    // Report operators not in the transitive closure
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            let name = op.name.node.as_str();
            // Skip LOCAL operators (they're intentionally private helper defs)
            // and operators whose names start with _ (conventional "unused" marker)
            if op.local || name.starts_with('_') {
                continue;
            }
            if !referenced.contains(name) {
                warnings.push(LintWarning {
                    code: "W004",
                    severity: LintSeverity::Info,
                    message: format!("operator `{name}` is defined but never referenced"),
                    span: op.name.span,
                    line: 0,
                    column: 0,
                    suggestion: format!(
                        "Remove `{name}` or add it to the .cfg file as an INVARIANT or PROPERTY"
                    ),
                });
            }
        }
    }
}

/// W005: Unused variable — VARIABLE declared but not referenced in Init or Next.
fn check_unused_variables(module: &Module, cfg: &ConfigInfo, warnings: &mut Vec<LintWarning>) {
    // Collect variables
    let mut variables: Vec<(&str, Span)> = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(names) = &unit.node {
            for name in names {
                variables.push((name.node.as_str(), name.span));
            }
        }
    }

    if variables.is_empty() {
        return;
    }

    // Collect all identifier references in Init and Next bodies
    let init_name = cfg.init.as_deref().unwrap_or("Init");
    let next_name = cfg.next.as_deref().unwrap_or("Next");

    // Collect all operators reachable from Init and Next
    let mut all_ops: HashMap<&str, &OperatorDef> = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            all_ops.insert(op.name.node.as_str(), op);
        }
    }

    // Compute transitive closure from Init and Next
    let mut reachable_ops: HashSet<String> = HashSet::new();
    let mut worklist: Vec<String> = vec![init_name.to_string(), next_name.to_string()];
    while let Some(name) = worklist.pop() {
        if !reachable_ops.insert(name.clone()) {
            continue;
        }
        if let Some(op) = all_ops.get(name.as_str()) {
            let refs = collect_ident_refs(&op.body.node);
            for r in refs {
                if all_ops.contains_key(r.as_str()) && !reachable_ops.contains(&r) {
                    worklist.push(r);
                }
            }
        }
    }

    // Collect all ident references in reachable operators
    let mut all_refs: HashSet<String> = HashSet::new();
    for op_name in &reachable_ops {
        if let Some(op) = all_ops.get(op_name.as_str()) {
            let refs = collect_ident_refs(&op.body.node);
            all_refs.extend(refs);
        }
    }

    // Also collect references from invariants and properties
    for inv_name in cfg.invariants.iter().chain(cfg.properties.iter()) {
        if let Some(op) = all_ops.get(inv_name.as_str()) {
            let refs = collect_ident_refs(&op.body.node);
            all_refs.extend(refs);
        }
    }

    for (var_name, span) in &variables {
        if !all_refs.contains(*var_name) {
            warnings.push(LintWarning {
                code: "W005",
                severity: LintSeverity::Warning,
                message: format!("variable `{var_name}` is declared but never used in Init/Next"),
                span: *span,
                line: 0,
                column: 0,
                suggestion: format!(
                    "Remove `{var_name}` from the VARIABLE declaration if it is not needed"
                ),
            });
        }
    }
}

/// W006: Shadowed name — a local quantifier variable shadows a module-level operator.
fn check_shadowed_names(module: &Module, warnings: &mut Vec<LintWarning>) {
    // Collect all module-level names (operators, constants, variables)
    let mut module_names: HashSet<String> = HashSet::new();
    for unit in &module.units {
        match &unit.node {
            Unit::Operator(op) => {
                module_names.insert(op.name.node.clone());
            }
            Unit::Constant(decls) => {
                for decl in decls {
                    module_names.insert(decl.name.node.clone());
                }
            }
            Unit::Variable(names) => {
                for name in names {
                    module_names.insert(name.node.clone());
                }
            }
            _ => {}
        }
    }

    // Walk all operator bodies looking for quantifier bindings that shadow
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            check_shadows_in_expr(&op.body.node, &module_names, op.name.span, warnings);
        }
    }
}

/// Recursively check for shadowed names in an expression.
fn check_shadows_in_expr(
    expr: &Expr,
    module_names: &HashSet<String>,
    _context_span: Span,
    warnings: &mut Vec<LintWarning>,
) {
    match expr {
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            check_bound_var_shadows(bounds, module_names, warnings);
            // Recurse into domains
            for bv in bounds {
                if let Some(domain) = &bv.domain {
                    check_shadows_in_expr(&domain.node, module_names, _context_span, warnings);
                }
            }
            check_shadows_in_expr(&body.node, module_names, _context_span, warnings);
        }
        Expr::Choose(bv, body) => {
            check_single_bound_var_shadow(bv, module_names, warnings);
            if let Some(domain) = &bv.domain {
                check_shadows_in_expr(&domain.node, module_names, _context_span, warnings);
            }
            check_shadows_in_expr(&body.node, module_names, _context_span, warnings);
        }
        Expr::SetFilter(bv, body) => {
            check_single_bound_var_shadow(bv, module_names, warnings);
            if let Some(domain) = &bv.domain {
                check_shadows_in_expr(&domain.node, module_names, _context_span, warnings);
            }
            check_shadows_in_expr(&body.node, module_names, _context_span, warnings);
        }
        Expr::SetBuilder(body, bounds) | Expr::FuncDef(bounds, body) => {
            check_bound_var_shadows(bounds, module_names, warnings);
            for bv in bounds {
                if let Some(domain) = &bv.domain {
                    check_shadows_in_expr(&domain.node, module_names, _context_span, warnings);
                }
            }
            check_shadows_in_expr(&body.node, module_names, _context_span, warnings);
        }
        Expr::Let(defs, body) => {
            for def in defs {
                check_shadows_in_expr(&def.body.node, module_names, _context_span, warnings);
            }
            check_shadows_in_expr(&body.node, module_names, _context_span, warnings);
        }
        // Recurse into all sub-expressions for other forms
        _ => visit_expr_children(expr, |child| {
            check_shadows_in_expr(child, module_names, _context_span, warnings);
        }),
    }
}

fn check_bound_var_shadows(
    bounds: &[BoundVar],
    module_names: &HashSet<String>,
    warnings: &mut Vec<LintWarning>,
) {
    for bv in bounds {
        check_single_bound_var_shadow(bv, module_names, warnings);
    }
}

fn check_single_bound_var_shadow(
    bv: &BoundVar,
    module_names: &HashSet<String>,
    warnings: &mut Vec<LintWarning>,
) {
    let name = &bv.name.node;
    if module_names.contains(name) {
        warnings.push(LintWarning {
            code: "W006",
            severity: LintSeverity::Warning,
            message: format!(
                "quantifier variable `{name}` shadows a module-level definition"
            ),
            span: bv.name.span,
            line: 0,
            column: 0,
            suggestion: format!(
                "Rename the quantifier variable to avoid confusion with the module-level `{name}`"
            ),
        });
    }
}

/// W007: Stuttering detection — Next action that may not include UNCHANGED for some variables.
fn check_stuttering(module: &Module, cfg: &ConfigInfo, warnings: &mut Vec<LintWarning>) {
    let next_name = cfg.next.as_deref().unwrap_or("Next");

    // Find the Next operator
    let next_op = module.units.iter().find_map(|u| match &u.node {
        Unit::Operator(op) if op.name.node == next_name => Some(op),
        _ => None,
    });

    let next_op = match next_op {
        Some(op) => op,
        None => return,
    };

    // Collect all VARIABLE names
    let mut all_vars: HashSet<String> = HashSet::new();
    for unit in &module.units {
        if let Unit::Variable(names) = &unit.node {
            for name in names {
                all_vars.insert(name.node.clone());
            }
        }
    }

    if all_vars.is_empty() {
        return;
    }

    // Collect all operators for transitive analysis
    let mut all_ops: HashMap<&str, &OperatorDef> = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            all_ops.insert(op.name.node.as_str(), op);
        }
    }

    // Collect primed variables and UNCHANGED variables transitively from Next
    let mut primed_vars: HashSet<String> = HashSet::new();
    let mut unchanged_vars: HashSet<String> = HashSet::new();
    let mut visited: HashSet<String> = HashSet::new();
    collect_primed_and_unchanged(
        &next_op.body.node,
        &all_ops,
        &mut primed_vars,
        &mut unchanged_vars,
        &mut visited,
    );

    // Variables that are neither primed nor in UNCHANGED
    let covered: HashSet<&String> = primed_vars.union(&unchanged_vars).collect();
    let mut uncovered: Vec<&String> = all_vars
        .iter()
        .filter(|v| !covered.contains(v))
        .collect();
    uncovered.sort();

    if !uncovered.is_empty() {
        let var_list = uncovered
            .iter()
            .map(|v| format!("`{v}`"))
            .collect::<Vec<_>>()
            .join(", ");
        warnings.push(LintWarning {
            code: "W007",
            severity: LintSeverity::Info,
            message: format!(
                "`{next_name}` may not specify the next value for: {var_list}"
            ),
            span: next_op.name.span,
            line: 0,
            column: 0,
            suggestion: format!(
                "Add `UNCHANGED <<{vars}>>` to a disjunct of `{next_name}` or ensure all variables are primed",
                vars = uncovered.iter().map(|v| v.as_str()).collect::<Vec<_>>().join(", ")
            ),
        });
    }
}

// ---------------------------------------------------------------------------
// Expression analysis helpers
// ---------------------------------------------------------------------------

/// Collect all identifier references in an expression (non-recursive into operator bodies).
fn collect_ident_refs(expr: &Expr) -> HashSet<String> {
    let mut refs = HashSet::new();
    collect_ident_refs_inner(expr, &mut refs);
    refs
}

fn collect_ident_refs_inner(expr: &Expr, refs: &mut HashSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            refs.insert(name.clone());
        }
        Expr::Apply(func, args) => {
            collect_ident_refs_inner(&func.node, refs);
            for arg in args {
                collect_ident_refs_inner(&arg.node, refs);
            }
        }
        _ => visit_expr_children(expr, |child| {
            collect_ident_refs_inner(child, refs);
        }),
    }
}

/// Collect primed variables and UNCHANGED variables transitively through operator calls.
fn collect_primed_and_unchanged(
    expr: &Expr,
    all_ops: &HashMap<&str, &OperatorDef>,
    primed: &mut HashSet<String>,
    unchanged: &mut HashSet<String>,
    visited: &mut HashSet<String>,
) {
    match expr {
        Expr::Prime(inner) => {
            // x' — the inner expression names a primed variable
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner.node {
                primed.insert(name.clone());
            }
        }
        Expr::Unchanged(inner) => {
            // UNCHANGED <<x, y>> or UNCHANGED x
            collect_unchanged_vars(&inner.node, unchanged);
        }
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            // If this ident refers to an operator, follow it transitively
            if all_ops.contains_key(name.as_str()) && !visited.contains(name) {
                visited.insert(name.clone());
                if let Some(op) = all_ops.get(name.as_str()) {
                    collect_primed_and_unchanged(
                        &op.body.node, all_ops, primed, unchanged, visited,
                    );
                }
            }
        }
        Expr::Apply(func, args) => {
            // Follow operator calls
            if let Expr::Ident(name, _) = &func.node {
                if all_ops.contains_key(name.as_str()) && !visited.contains(name) {
                    visited.insert(name.clone());
                    if let Some(op) = all_ops.get(name.as_str()) {
                        collect_primed_and_unchanged(
                            &op.body.node, all_ops, primed, unchanged, visited,
                        );
                    }
                }
            }
            collect_primed_and_unchanged(&func.node, all_ops, primed, unchanged, visited);
            for arg in args {
                collect_primed_and_unchanged(&arg.node, all_ops, primed, unchanged, visited);
            }
        }
        _ => visit_expr_children(expr, |child| {
            collect_primed_and_unchanged(child, all_ops, primed, unchanged, visited);
        }),
    }
}

/// Extract variable names from an UNCHANGED expression (handles tuples and single vars).
fn collect_unchanged_vars(expr: &Expr, unchanged: &mut HashSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            unchanged.insert(name.clone());
        }
        Expr::Tuple(elems) => {
            for elem in elems {
                collect_unchanged_vars(&elem.node, unchanged);
            }
        }
        _ => {}
    }
}

/// Visit all direct child expressions of an Expr node, calling `f` on each.
/// This is a structural traversal helper that covers every Expr variant.
fn visit_expr_children(expr: &Expr, mut f: impl FnMut(&Expr)) {
    match expr {
        // Leaves
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _) | Expr::OpRef(_) | Expr::InstanceExpr(_, _) => {}

        // Unary
        Expr::Not(e) | Expr::Prime(e) | Expr::Always(e) | Expr::Eventually(e)
        | Expr::Enabled(e) | Expr::Unchanged(e) | Expr::Powerset(e)
        | Expr::BigUnion(e) | Expr::Domain(e) | Expr::Neg(e) => {
            f(&e.node);
        }

        // Binary
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) | Expr::Equiv(a, b)
        | Expr::In(a, b) | Expr::NotIn(a, b) | Expr::Subseteq(a, b)
        | Expr::Union(a, b) | Expr::Intersect(a, b) | Expr::SetMinus(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Leq(a, b)
        | Expr::Gt(a, b) | Expr::Geq(a, b) | Expr::Add(a, b) | Expr::Sub(a, b)
        | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::IntDiv(a, b) | Expr::Mod(a, b)
        | Expr::Pow(a, b) | Expr::Range(a, b) | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b) | Expr::StrongFair(a, b) | Expr::FuncApply(a, b)
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
// Span -> line/column conversion
// ---------------------------------------------------------------------------

/// Build a line-starts table from source text (byte offsets of each line start).
fn line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, ch) in source.char_indices() {
        if ch == '\n' {
            starts.push(i + 1);
        }
    }
    starts
}

/// Convert a byte offset to (line, column), both 1-based.
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

fn print_human(file_path: &str, source: &str, warnings: &[LintWarning]) {
    if warnings.is_empty() {
        println!("No lint warnings found in {file_path}");
        return;
    }

    let starts = line_starts(source);

    println!(
        "{} lint warning{} in {file_path}:",
        warnings.len(),
        if warnings.len() == 1 { "" } else { "s" }
    );
    println!();

    for w in warnings {
        let (line, col) = offset_to_line_col(w.span.start, &starts);

        // Severity color prefix
        let severity_str = match w.severity {
            LintSeverity::Warning => "\x1b[33mwarning\x1b[0m",
            LintSeverity::Info => "\x1b[36minfo\x1b[0m",
        };

        println!(
            "{severity_str}[{}]: {}",
            w.code, w.message
        );
        println!(
            "  --> {file_path}:{line}:{col}"
        );
        if !w.suggestion.is_empty() {
            println!("  = help: {}", w.suggestion);
        }
        println!();
    }

    let warn_count = warnings
        .iter()
        .filter(|w| matches!(w.severity, LintSeverity::Warning))
        .count();
    let info_count = warnings.len() - warn_count;

    let mut summary_parts = Vec::new();
    if warn_count > 0 {
        summary_parts.push(format!(
            "{warn_count} warning{}",
            if warn_count == 1 { "" } else { "s" }
        ));
    }
    if info_count > 0 {
        summary_parts.push(format!(
            "{info_count} info",
        ));
    }
    println!("Summary: {}", summary_parts.join(", "));
}

fn print_json(file_path: &str, warnings: &[LintWarning]) -> Result<()> {
    let starts_source = std::fs::read_to_string(file_path).unwrap_or_default();
    let starts = line_starts(&starts_source);

    let json_warnings: Vec<serde_json::Value> = warnings
        .iter()
        .map(|w| {
            let (line, col) = offset_to_line_col(w.span.start, &starts);
            serde_json::json!({
                "code": w.code,
                "severity": w.severity,
                "message": w.message,
                "file": file_path,
                "line": line,
                "column": col,
                "suggestion": w.suggestion,
            })
        })
        .collect();

    let output = serde_json::json!({
        "file": file_path,
        "warnings": json_warnings,
        "summary": {
            "total": warnings.len(),
            "warnings": warnings.iter().filter(|w| matches!(w.severity, LintSeverity::Warning)).count(),
            "infos": warnings.iter().filter(|w| matches!(w.severity, LintSeverity::Info)).count(),
        }
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
        assert!(result.errors.is_empty(), "parse errors: {:?}", result.errors);
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
            invariants: vec!["TypeOK".to_string()],
            properties: Vec::new(),
        }
    }

    #[test]
    fn test_missing_init_next_both_present() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        let mut warnings = Vec::new();
        check_missing_init_next(&module, &default_cfg(), &mut warnings);
        assert!(warnings.is_empty(), "expected no warnings: {warnings:?}");
    }

    #[test]
    fn test_missing_init_next_missing_both() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Foo == x = 0
===="#,
        );
        let mut warnings = Vec::new();
        check_missing_init_next(&module, &default_cfg(), &mut warnings);
        assert_eq!(warnings.len(), 2);
        assert_eq!(warnings[0].code, "W001");
        assert_eq!(warnings[1].code, "W002");
    }

    #[test]
    fn test_convention_warning_lowercase_init() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
init == x = 0
Next == x' = x + 1
===="#,
        );
        let mut warnings = Vec::new();
        check_convention_warnings(&module, &mut warnings);
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].code, "W003");
        assert!(warnings[0].message.contains("init"));
    }

    #[test]
    fn test_unused_operator() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
Unused == TRUE
===="#,
        );
        let cfg = default_cfg();
        let mut warnings = Vec::new();
        check_unused_operators(&module, &cfg, &mut warnings);
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].code, "W004");
        assert!(warnings[0].message.contains("Unused"));
    }

    #[test]
    fn test_unused_operator_transitively_used() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Helper == x + 1
Init == x = 0
Next == x' = Helper
TypeOK == x \in Nat
===="#,
        );
        let cfg = default_cfg();
        let mut warnings = Vec::new();
        check_unused_operators(&module, &cfg, &mut warnings);
        assert!(
            warnings.is_empty(),
            "Helper is transitively used, expected no warnings: {warnings:?}"
        );
    }

    #[test]
    fn test_unused_variable() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
===="#,
        );
        let cfg = default_cfg();
        let mut warnings = Vec::new();
        check_unused_variables(&module, &cfg, &mut warnings);
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].code, "W005");
        assert!(warnings[0].message.contains("y"));
    }

    #[test]
    fn test_shadowed_name() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == \E x \in {1, 2} : x' = x
===="#,
        );
        let mut warnings = Vec::new();
        check_shadowed_names(&module, &mut warnings);
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].code, "W006");
        assert!(warnings[0].message.contains("shadows"));
    }

    #[test]
    fn test_offset_to_line_col_basic() {
        let source = "line1\nline2\nline3\n";
        let starts = line_starts(source);
        assert_eq!(offset_to_line_col(0, &starts), (1, 1));
        assert_eq!(offset_to_line_col(6, &starts), (2, 1));
        assert_eq!(offset_to_line_col(8, &starts), (2, 3));
    }
}
