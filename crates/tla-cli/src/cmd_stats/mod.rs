// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 stats` -- specification statistics and complexity metrics.
//!
//! Parses a TLA+ spec and reports structural metrics: line counts,
//! declaration counts, operator complexity, nesting depths, primed variable
//! usage, UNCHANGED usage, and state-space size hints.

use std::collections::HashSet;
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{Expr, Module, Unit};
use tla_core::{lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId, SyntaxNode};

use crate::cli_schema::StatsOutputFormat;
use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_stats(
    file: &Path,
    config_path: Option<&Path>,
    format: StatsOutputFormat,
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
        bail!("stats aborted: {} parse error(s)", parse_result.errors.len());
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

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
            "stats aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("stats: lowering produced no module")?;

    // Parse config if present (for action structure analysis)
    let cfg_info = load_config_info(file, config_path);

    // Collect all metrics
    let stats = collect_stats(&source, &module, &cfg_info);

    // Output
    let file_path = file.display().to_string();
    match format {
        StatsOutputFormat::Human => print_human(&file_path, &stats),
        StatsOutputFormat::Json => print_json(&file_path, &stats)?,
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Stats structure
// ---------------------------------------------------------------------------

struct SpecStats {
    // Line counts
    total_lines: usize,
    blank_lines: usize,
    comment_lines: usize,
    code_lines: usize,

    // Module structure
    extends_count: usize,
    instance_count: usize,
    variable_count: usize,
    constant_count: usize,

    // Operators
    operator_count: usize,
    parameterized_ops: usize,
    constant_ops: usize,
    recursive_ops: usize,

    // Complexity
    max_nesting_depth: usize,
    max_quantifier_depth: usize,
    primed_variable_count: usize,
    unchanged_usage_count: usize,

    // State space hints
    state_variables: Vec<String>,
    boolean_vars: usize,
    range_vars: Vec<(String, i64, i64)>,
    estimated_state_space: Option<u64>,

    // Action structure
    next_disjunct_count: usize,
}

// ---------------------------------------------------------------------------
// Config info (best-effort, for action structure)
// ---------------------------------------------------------------------------

struct ConfigInfo {
    next: Option<String>,
}

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
            next: Some("Next".to_string()),
        };
    }

    let source = match std::fs::read_to_string(&config_path_buf) {
        Ok(s) => s,
        Err(_) => {
            return ConfigInfo {
                next: Some("Next".to_string()),
            }
        }
    };

    match tla_check::Config::parse(&source) {
        Ok(config) => ConfigInfo {
            next: config.next.clone(),
        },
        Err(_) => ConfigInfo {
            next: Some("Next".to_string()),
        },
    }
}

// ---------------------------------------------------------------------------
// Stats collection
// ---------------------------------------------------------------------------

fn collect_stats(source: &str, module: &Module, cfg: &ConfigInfo) -> SpecStats {
    let (total_lines, blank_lines, comment_lines) = count_lines(source);
    let code_lines = total_lines.saturating_sub(blank_lines + comment_lines);

    let (extends_count, instance_count, variable_count, constant_count) =
        count_declarations(module);

    let (operator_count, parameterized_ops, constant_ops, recursive_ops) = count_operators(module);

    let (max_nesting_depth, max_quantifier_depth) = compute_depths(module);

    let (primed_variable_count, unchanged_usage_count) = count_temporal(module);

    let state_variables = collect_state_variables(module);
    let (boolean_vars, range_vars) = estimate_domains(module, &state_variables);
    let estimated_state_space = estimate_state_space(
        state_variables.len(),
        boolean_vars,
        &range_vars,
    );

    let next_disjunct_count = count_next_disjuncts(module, cfg);

    SpecStats {
        total_lines,
        blank_lines,
        comment_lines,
        code_lines,
        extends_count,
        instance_count,
        variable_count,
        constant_count,
        operator_count,
        parameterized_ops,
        constant_ops,
        recursive_ops,
        max_nesting_depth,
        max_quantifier_depth,
        primed_variable_count,
        unchanged_usage_count,
        state_variables,
        boolean_vars,
        range_vars,
        estimated_state_space,
        next_disjunct_count,
    }
}

// ---------------------------------------------------------------------------
// Line counting
// ---------------------------------------------------------------------------

fn count_lines(source: &str) -> (usize, usize, usize) {
    let mut total = 0;
    let mut blank = 0;
    let mut comment = 0;

    for line in source.lines() {
        total += 1;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            blank += 1;
        } else if trimmed.starts_with("\\*") || trimmed.starts_with("(*") {
            comment += 1;
        }
    }

    // Handle the case where the file doesn't end with a newline
    if total == 0 && !source.is_empty() {
        total = 1;
    }

    (total, blank, comment)
}

// ---------------------------------------------------------------------------
// Declaration counting
// ---------------------------------------------------------------------------

fn count_declarations(module: &Module) -> (usize, usize, usize, usize) {
    let extends_count = module.extends.len();
    let mut instance_count = 0;
    let mut variable_count = 0;
    let mut constant_count = 0;

    for unit in &module.units {
        match &unit.node {
            Unit::Instance(_) => instance_count += 1,
            Unit::Variable(names) => variable_count += names.len(),
            Unit::Constant(decls) => constant_count += decls.len(),
            _ => {}
        }
    }

    (extends_count, instance_count, variable_count, constant_count)
}

// ---------------------------------------------------------------------------
// Operator counting
// ---------------------------------------------------------------------------

fn count_operators(module: &Module) -> (usize, usize, usize, usize) {
    let mut total = 0;
    let mut parameterized = 0;
    let mut constant = 0;
    let mut recursive = 0;

    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            total += 1;
            if op.params.is_empty() {
                constant += 1;
            } else {
                parameterized += 1;
            }
            if op.is_recursive {
                recursive += 1;
            }
        }
    }

    (total, parameterized, constant, recursive)
}

// ---------------------------------------------------------------------------
// Depth computation
// ---------------------------------------------------------------------------

fn compute_depths(module: &Module) -> (usize, usize) {
    let mut max_nesting = 0;
    let mut max_quantifier = 0;

    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            let (n, q) = expr_depths(&op.body.node, 0, 0);
            max_nesting = max_nesting.max(n);
            max_quantifier = max_quantifier.max(q);
        }
    }

    (max_nesting, max_quantifier)
}

/// Returns (max_nesting_depth, max_quantifier_depth) seen in the expression tree.
fn expr_depths(expr: &Expr, nesting: usize, quant_depth: usize) -> (usize, usize) {
    let mut best_nesting = nesting;
    let mut best_quant = quant_depth;

    match expr {
        // Quantifiers increase both nesting and quantifier depth
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            let new_nesting = nesting + 1;
            let new_quant = quant_depth + 1;
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    let (n, q) = expr_depths(&d.node, new_nesting, new_quant);
                    best_nesting = best_nesting.max(n);
                    best_quant = best_quant.max(q);
                }
            }
            let (n, q) = expr_depths(&body.node, new_nesting, new_quant);
            best_nesting = best_nesting.max(n);
            best_quant = best_quant.max(q);
        }

        // Nesting-increasing constructs (but not quantifier depth)
        Expr::If(cond, then_, else_) => {
            let new_nesting = nesting + 1;
            for child in [&cond.node, &then_.node, &else_.node] {
                let (n, q) = expr_depths(child, new_nesting, quant_depth);
                best_nesting = best_nesting.max(n);
                best_quant = best_quant.max(q);
            }
        }
        Expr::Case(arms, other) => {
            let new_nesting = nesting + 1;
            for arm in arms {
                for child in [&arm.guard.node, &arm.body.node] {
                    let (n, q) = expr_depths(child, new_nesting, quant_depth);
                    best_nesting = best_nesting.max(n);
                    best_quant = best_quant.max(q);
                }
            }
            if let Some(o) = other {
                let (n, q) = expr_depths(&o.node, new_nesting, quant_depth);
                best_nesting = best_nesting.max(n);
                best_quant = best_quant.max(q);
            }
        }
        Expr::Let(defs, body) => {
            let new_nesting = nesting + 1;
            for def in defs {
                let (n, q) = expr_depths(&def.body.node, new_nesting, quant_depth);
                best_nesting = best_nesting.max(n);
                best_quant = best_quant.max(q);
            }
            let (n, q) = expr_depths(&body.node, new_nesting, quant_depth);
            best_nesting = best_nesting.max(n);
            best_quant = best_quant.max(q);
        }

        Expr::SetBuilder(body, bounds) | Expr::FuncDef(bounds, body) => {
            let new_nesting = nesting + 1;
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    let (n, q) = expr_depths(&d.node, new_nesting, quant_depth);
                    best_nesting = best_nesting.max(n);
                    best_quant = best_quant.max(q);
                }
            }
            let (n, q) = expr_depths(&body.node, new_nesting, quant_depth);
            best_nesting = best_nesting.max(n);
            best_quant = best_quant.max(q);
        }
        Expr::SetFilter(bv, body) => {
            let new_nesting = nesting + 1;
            if let Some(d) = &bv.domain {
                let (n, q) = expr_depths(&d.node, new_nesting, quant_depth);
                best_nesting = best_nesting.max(n);
                best_quant = best_quant.max(q);
            }
            let (n, q) = expr_depths(&body.node, new_nesting, quant_depth);
            best_nesting = best_nesting.max(n);
            best_quant = best_quant.max(q);
        }
        Expr::Choose(bv, body) => {
            let new_nesting = nesting + 1;
            let new_quant = quant_depth + 1;
            if let Some(d) = &bv.domain {
                let (n, q) = expr_depths(&d.node, new_nesting, new_quant);
                best_nesting = best_nesting.max(n);
                best_quant = best_quant.max(q);
            }
            let (n, q) = expr_depths(&body.node, new_nesting, new_quant);
            best_nesting = best_nesting.max(n);
            best_quant = best_quant.max(q);
        }

        // Everything else: recurse at the same depth
        _ => {
            visit_expr_children(expr, |child| {
                let (n, q) = expr_depths(child, nesting, quant_depth);
                best_nesting = best_nesting.max(n);
                best_quant = best_quant.max(q);
            });
        }
    }

    (best_nesting, best_quant)
}

// ---------------------------------------------------------------------------
// Temporal / action counting
// ---------------------------------------------------------------------------

fn count_temporal(module: &Module) -> (usize, usize) {
    let mut primed_vars: HashSet<String> = HashSet::new();
    let mut unchanged_count = 0;

    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            count_temporal_in_expr(&op.body.node, &mut primed_vars, &mut unchanged_count);
        }
    }

    (primed_vars.len(), unchanged_count)
}

fn count_temporal_in_expr(
    expr: &Expr,
    primed_vars: &mut HashSet<String>,
    unchanged_count: &mut usize,
) {
    match expr {
        Expr::Prime(inner) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner.node {
                primed_vars.insert(name.clone());
            }
            // Also recurse into the inner expression
            count_temporal_in_expr(&inner.node, primed_vars, unchanged_count);
        }
        Expr::Unchanged(_) => {
            *unchanged_count += 1;
            // Still recurse
            visit_expr_children(expr, |child| {
                count_temporal_in_expr(child, primed_vars, unchanged_count);
            });
        }
        _ => {
            visit_expr_children(expr, |child| {
                count_temporal_in_expr(child, primed_vars, unchanged_count);
            });
        }
    }
}

// ---------------------------------------------------------------------------
// State variable collection and domain estimation
// ---------------------------------------------------------------------------

fn collect_state_variables(module: &Module) -> Vec<String> {
    let mut vars = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(names) = &unit.node {
            for name in names {
                vars.push(name.node.clone());
            }
        }
    }
    vars
}

/// Estimate variable domains from Init operator patterns.
/// Returns (boolean_var_count, [(var_name, lo, hi)] for range vars).
fn estimate_domains(
    module: &Module,
    state_variables: &[String],
) -> (usize, Vec<(String, i64, i64)>) {
    // Find the Init operator
    let init_op = module.units.iter().find_map(|u| match &u.node {
        Unit::Operator(op) if op.name.node == "Init" => Some(op),
        _ => None,
    });

    let init_op = match init_op {
        Some(op) => op,
        None => return (0, Vec::new()),
    };

    let var_set: HashSet<&str> = state_variables.iter().map(|s| s.as_str()).collect();
    let mut boolean_count = 0;
    let mut range_vars = Vec::new();

    // Look for patterns: var = TRUE/FALSE, var \in BOOLEAN, var \in a..b
    scan_init_domains(
        &init_op.body.node,
        &var_set,
        &mut boolean_count,
        &mut range_vars,
    );

    (boolean_count, range_vars)
}

fn scan_init_domains(
    expr: &Expr,
    vars: &HashSet<&str>,
    boolean_count: &mut usize,
    range_vars: &mut Vec<(String, i64, i64)>,
) {
    match expr {
        // var \in BOOLEAN
        Expr::In(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                if vars.contains(name.as_str()) {
                    if is_boolean_ref(&rhs.node) {
                        *boolean_count += 1;
                    } else if let Expr::Range(lo, hi) = &rhs.node {
                        if let (Some(lo_val), Some(hi_val)) =
                            (extract_int(&lo.node), extract_int(&hi.node))
                        {
                            range_vars.push((name.clone(), lo_val, hi_val));
                        }
                    }
                }
            }
            // Recurse into both sides
            scan_init_domains(&lhs.node, vars, boolean_count, range_vars);
            scan_init_domains(&rhs.node, vars, boolean_count, range_vars);
        }
        // var = TRUE or var = FALSE
        Expr::Eq(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                if vars.contains(name.as_str()) && matches!(rhs.node, Expr::Bool(_)) {
                    // Initial value is a boolean, but this is a single-value init,
                    // not necessarily declaring the domain as BOOLEAN.
                }
            }
            scan_init_domains(&lhs.node, vars, boolean_count, range_vars);
            scan_init_domains(&rhs.node, vars, boolean_count, range_vars);
        }
        _ => {
            visit_expr_children(expr, |child| {
                scan_init_domains(child, vars, boolean_count, range_vars);
            });
        }
    }
}

fn is_boolean_ref(expr: &Expr) -> bool {
    matches!(expr, Expr::Ident(name, _) if name == "BOOLEAN")
}

fn extract_int(expr: &Expr) -> Option<i64> {
    if let Expr::Int(n) = expr {
        n.try_into().ok()
    } else if let Expr::Neg(inner) = expr {
        if let Expr::Int(n) = &inner.node {
            let val: i64 = n.try_into().ok()?;
            Some(-val)
        } else {
            None
        }
    } else {
        None
    }
}

fn estimate_state_space(
    total_vars: usize,
    boolean_vars: usize,
    range_vars: &[(String, i64, i64)],
) -> Option<u64> {
    let known_vars = boolean_vars + range_vars.len();
    if known_vars == 0 || known_vars < total_vars {
        // Cannot estimate if some variables have unknown domains
        return None;
    }

    let mut product: u64 = 1;
    // Each boolean variable contributes factor of 2
    for _ in 0..boolean_vars {
        product = product.checked_mul(2)?;
    }
    // Each range variable a..b contributes (b - a + 1)
    for (_, lo, hi) in range_vars {
        let size = (hi - lo + 1).max(0) as u64;
        product = product.checked_mul(size)?;
    }

    Some(product)
}

// ---------------------------------------------------------------------------
// Action structure: count Next disjuncts
// ---------------------------------------------------------------------------

fn count_next_disjuncts(module: &Module, cfg: &ConfigInfo) -> usize {
    let next_name = cfg.next.as_deref().unwrap_or("Next");

    let next_op = module.units.iter().find_map(|u| match &u.node {
        Unit::Operator(op) if op.name.node == next_name => Some(op),
        _ => None,
    });

    match next_op {
        Some(op) => count_top_disjuncts(&op.body.node),
        None => 0,
    }
}

/// Count top-level disjuncts in an expression (recursive through \/).
fn count_top_disjuncts(expr: &Expr) -> usize {
    match expr {
        Expr::Or(lhs, rhs) => count_top_disjuncts(&lhs.node) + count_top_disjuncts(&rhs.node),
        Expr::Label(label) => count_top_disjuncts(&label.body.node),
        _ => 1,
    }
}

// ---------------------------------------------------------------------------
// Expression visitor helper (structural traversal)
// ---------------------------------------------------------------------------

/// Visit all direct child expressions of an Expr node, calling `f` on each.
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
// Output formatting: Human
// ---------------------------------------------------------------------------

fn print_human(file_path: &str, stats: &SpecStats) {
    println!("Specification Statistics: {file_path}");
    println!("{}", "=".repeat(60));

    // Line counts
    println!();
    println!("  Lines");
    println!("  -----");
    println!("  Total:    {:>8}", stats.total_lines);
    println!("  Code:     {:>8}", stats.code_lines);
    println!("  Blank:    {:>8}", stats.blank_lines);
    println!("  Comment:  {:>8}", stats.comment_lines);

    // Module structure
    println!();
    println!("  Declarations");
    println!("  ------------");
    println!("  EXTENDS:    {:>6}", stats.extends_count);
    println!("  INSTANCE:   {:>6}", stats.instance_count);
    println!("  VARIABLE:   {:>6}", stats.variable_count);
    println!("  CONSTANT:   {:>6}", stats.constant_count);

    // Operators
    println!();
    println!("  Operators");
    println!("  ---------");
    println!("  Total:          {:>6}", stats.operator_count);
    println!("  Parameterized:  {:>6}", stats.parameterized_ops);
    println!("  Constant:       {:>6}", stats.constant_ops);
    println!("  Recursive:      {:>6}", stats.recursive_ops);

    // Complexity
    println!();
    println!("  Complexity");
    println!("  ----------");
    println!("  Max nesting depth:      {:>4}", stats.max_nesting_depth);
    println!("  Max quantifier depth:   {:>4}", stats.max_quantifier_depth);
    println!("  Primed variables:       {:>4}", stats.primed_variable_count);
    println!("  UNCHANGED usages:       {:>4}", stats.unchanged_usage_count);

    // State space hints
    println!();
    println!("  State Space Hints");
    println!("  -----------------");
    println!(
        "  State variables:  {}",
        if stats.state_variables.is_empty() {
            "(none)".to_string()
        } else {
            stats.state_variables.join(", ")
        }
    );
    if stats.boolean_vars > 0 {
        println!("  Boolean vars:     {}", stats.boolean_vars);
    }
    for (name, lo, hi) in &stats.range_vars {
        println!("  Range var:        {name} in {lo}..{hi} ({} values)", hi - lo + 1);
    }
    match stats.estimated_state_space {
        Some(est) => println!("  Estimated states: {est}"),
        None => println!("  Estimated states: (unknown -- not all variable domains detectable)"),
    }

    // Action structure
    println!();
    println!("  Action Structure");
    println!("  ----------------");
    println!("  Next disjuncts: {:>6}", stats.next_disjunct_count);

    println!();
}

// ---------------------------------------------------------------------------
// Output formatting: JSON
// ---------------------------------------------------------------------------

fn print_json(file_path: &str, stats: &SpecStats) -> Result<()> {
    let output = serde_json::json!({
        "file": file_path,
        "lines": {
            "total": stats.total_lines,
            "code": stats.code_lines,
            "blank": stats.blank_lines,
            "comment": stats.comment_lines,
        },
        "declarations": {
            "extends": stats.extends_count,
            "instance": stats.instance_count,
            "variable": stats.variable_count,
            "constant": stats.constant_count,
        },
        "operators": {
            "total": stats.operator_count,
            "parameterized": stats.parameterized_ops,
            "constant": stats.constant_ops,
            "recursive": stats.recursive_ops,
        },
        "complexity": {
            "max_nesting_depth": stats.max_nesting_depth,
            "max_quantifier_depth": stats.max_quantifier_depth,
            "primed_variables": stats.primed_variable_count,
            "unchanged_usages": stats.unchanged_usage_count,
        },
        "state_space": {
            "variables": stats.state_variables,
            "boolean_vars": stats.boolean_vars,
            "range_vars": stats.range_vars.iter().map(|(name, lo, hi)| {
                serde_json::json!({
                    "name": name,
                    "low": lo,
                    "high": hi,
                    "cardinality": hi - lo + 1,
                })
            }).collect::<Vec<_>>(),
            "estimated_states": stats.estimated_state_space,
        },
        "actions": {
            "next_disjuncts": stats.next_disjunct_count,
        },
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
    fn test_count_lines_basic() {
        let source = "---- MODULE M ----\n\nVARIABLE x\n\\* comment\nInit == x = 0\n====\n";
        let (total, blank, comment) = count_lines(source);
        assert_eq!(total, 6);
        assert_eq!(blank, 1);
        assert_eq!(comment, 1);
    }

    #[test]
    fn test_count_declarations() {
        let module = parse_module(
            r#"---- MODULE Test ----
EXTENDS Naturals, Sequences
VARIABLE x, y, z
CONSTANT N
Init == x = 0 /\ y = 0 /\ z = 0
Next == x' = x
===="#,
        );
        let (extends, instances, vars, consts) = count_declarations(&module);
        assert_eq!(extends, 2);
        assert_eq!(instances, 0);
        assert_eq!(vars, 3);
        assert_eq!(consts, 1);
    }

    #[test]
    fn test_count_operators() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
Helper(a, b) == a + b
===="#,
        );
        let (total, parameterized, constant, recursive) = count_operators(&module);
        assert_eq!(total, 4);
        assert_eq!(parameterized, 1);
        assert_eq!(constant, 3);
        assert_eq!(recursive, 0);
    }

    #[test]
    fn test_count_next_disjuncts() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 \/ x' = x - 1 \/ x' = 0
===="#,
        );
        let cfg = ConfigInfo {
            next: Some("Next".to_string()),
        };
        let count = count_next_disjuncts(&module, &cfg);
        assert_eq!(count, 3);
    }

    #[test]
    fn test_depth_computation() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == \E n \in {1, 2} : \A m \in {3, 4} : x' = n + m
===="#,
        );
        let (nesting, quant) = compute_depths(&module);
        assert!(nesting >= 2, "nesting should be at least 2, got {nesting}");
        assert!(
            quant >= 2,
            "quantifier depth should be at least 2, got {quant}"
        );
    }

    #[test]
    fn test_boolean_domain_detection() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE flag, count
Init == flag \in BOOLEAN /\ count \in 0..10
Next == flag' = ~flag /\ count' = count + 1
===="#,
        );
        let vars = collect_state_variables(&module);
        let (bool_count, range_vars) = estimate_domains(&module, &vars);
        assert_eq!(bool_count, 1);
        assert_eq!(range_vars.len(), 1);
        assert_eq!(range_vars[0].0, "count");
        assert_eq!(range_vars[0].1, 0);
        assert_eq!(range_vars[0].2, 10);
    }

    #[test]
    fn test_state_space_estimate() {
        // 2 booleans * 11 range values = 44
        assert_eq!(estimate_state_space(3, 2, &[("x".into(), 0, 10)]), Some(44));
        // Unknown domains -> None
        assert_eq!(estimate_state_space(3, 1, &[]), None);
    }

    #[test]
    fn test_temporal_counting() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y, z
Init == x = 0 /\ y = 0 /\ z = 0
Next == x' = y /\ y' = x /\ UNCHANGED z
===="#,
        );
        let (primed, unchanged) = count_temporal(&module);
        assert_eq!(primed, 2, "expected 2 primed vars (x, y)");
        assert_eq!(unchanged, 1, "expected 1 UNCHANGED usage");
    }
}
