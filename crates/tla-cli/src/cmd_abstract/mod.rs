// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 abstract` -- generate a simplified abstract view of a TLA+ specification.
//!
//! Produces a high-level summary of the state machine:
//! - State variables and their types (when inferrable from Init)
//! - Init predicate summary
//! - Next relation: actions (disjuncts) with names and affected variables
//! - Invariants from the config
//! - Constants and their constraints
//! - EXTENDS dependencies
//!
//! Output formats: human (structured text), JSON, Mermaid (state diagram).
//! Detail levels: Brief (action names only), Normal (actions + variables), Full (everything).

use std::path::Path;

use anyhow::{bail, Context, Result};
use serde::Serialize;

use tla_core::ast::{Expr, Module, Unit};
use tla_core::{lower_main_module, parse, parse_error_diagnostic, pretty_expr, FileId, SyntaxNode};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public enums
// ---------------------------------------------------------------------------

/// Output format for the abstract view.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AbstractOutputFormat {
    Human,
    Json,
    Mermaid,
}

/// Level of detail in the abstract output.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AbstractDetail {
    /// Just action names.
    Brief,
    /// Actions + affected variables.
    Normal,
    /// Everything including expression summaries.
    Full,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Generate an abstract view of a TLA+ specification.
pub(crate) fn cmd_abstract(
    file: &Path,
    config: Option<&Path>,
    format: AbstractOutputFormat,
    detail: AbstractDetail,
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
        bail!("parse failed with {} error(s)", parse_result.errors.len());
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
            let diag = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diag.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", lower_result.errors.len());
    }
    let module = lower_result
        .module
        .context("lowering produced no module")?;

    // Load config (optional)
    let cfg = load_config(file, config);

    // Build abstract model
    let model = build_abstract_model(&module, cfg.as_ref(), detail);

    // Emit
    match format {
        AbstractOutputFormat::Human => emit_human(&model, detail),
        AbstractOutputFormat::Json => emit_json(&model)?,
        AbstractOutputFormat::Mermaid => emit_mermaid(&model, detail),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Config loading (same pattern as cmd_deps)
// ---------------------------------------------------------------------------

fn load_config(file: &Path, config_path: Option<&Path>) -> Option<tla_check::Config> {
    let config_path = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            if !cfg.exists() {
                return None;
            }
            cfg
        }
    };
    let config_source = std::fs::read_to_string(&config_path).ok()?;
    tla_check::Config::parse(&config_source).ok()
}

// ---------------------------------------------------------------------------
// Abstract model types
// ---------------------------------------------------------------------------

#[derive(Debug, Serialize)]
struct AbstractModel {
    module_name: String,
    extends: Vec<String>,
    constants: Vec<ConstantInfo>,
    variables: Vec<VariableInfo>,
    init: Option<InitSummary>,
    actions: Vec<ActionInfo>,
    invariants: Vec<String>,
    properties: Vec<String>,
    symmetry: Option<String>,
    /// Total operator count (including helper operators).
    operator_count: usize,
}

#[derive(Debug, Serialize)]
struct ConstantInfo {
    name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    value: Option<String>,
}

#[derive(Debug, Serialize)]
struct VariableInfo {
    name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    init_value: Option<String>,
}

#[derive(Debug, Serialize)]
struct InitSummary {
    operator: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    description: Option<String>,
}

#[derive(Debug, Serialize)]
struct ActionInfo {
    name: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    affected_variables: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    expression: Option<String>,
}

// ---------------------------------------------------------------------------
// Model construction
// ---------------------------------------------------------------------------

fn build_abstract_model(
    module: &Module,
    config: Option<&tla_check::Config>,
    detail: AbstractDetail,
) -> AbstractModel {
    let module_name = module.name.node.clone();
    let extends: Vec<String> = module.extends.iter().map(|e| e.node.clone()).collect();

    // Extract variables
    let variable_names = extract_variable_names(module);

    // Extract constants
    let constant_names = extract_constant_names(module);

    // Determine Init/Next from config or convention
    let init_name = config
        .and_then(|c| c.init.clone())
        .unwrap_or_else(|| "Init".to_string());
    let next_name = config
        .and_then(|c| c.next.clone())
        .unwrap_or_else(|| "Next".to_string());

    // Find Init operator and summarize initial values
    let init_op = find_operator(module, &init_name);
    let init_values = init_op.map(|op| extract_init_values(&op.body.node, &variable_names));

    // Build variable infos with init values
    let variables: Vec<VariableInfo> = variable_names
        .iter()
        .map(|name| {
            let init_value = init_values
                .as_ref()
                .and_then(|vals| vals.iter().find(|(n, _)| n == name))
                .map(|(_, v)| v.clone());
            VariableInfo {
                name: name.clone(),
                init_value,
            }
        })
        .collect();

    // Build init summary
    let init = init_op.map(|op| {
        let description = if matches!(detail, AbstractDetail::Full) {
            Some(summarize_expr(&op.body.node, 120))
        } else {
            None
        };
        InitSummary {
            operator: init_name.clone(),
            description,
        }
    });

    // Extract actions from Next relation
    let next_op = find_operator(module, &next_name);
    let actions = next_op
        .map(|op| extract_actions(module, &op.body.node, &variable_names, detail))
        .unwrap_or_default();

    // Build constant infos with config values
    let constants: Vec<ConstantInfo> = constant_names
        .iter()
        .map(|name| {
            let value = config
                .and_then(|c| c.constants.get(name))
                .map(|v| v.to_string());
            ConstantInfo {
                name: name.clone(),
                value,
            }
        })
        .collect();

    // Invariants and properties from config
    let invariants = config
        .map(|c| c.invariants.clone())
        .unwrap_or_default();
    let properties = config
        .map(|c| c.properties.clone())
        .unwrap_or_default();
    let symmetry = config.and_then(|c| c.symmetry.clone());

    // Count total operators
    let operator_count = module
        .units
        .iter()
        .filter(|u| matches!(u.node, Unit::Operator(_)))
        .count();

    AbstractModel {
        module_name,
        extends,
        constants,
        variables,
        init,
        actions,
        invariants,
        properties,
        symmetry,
        operator_count,
    }
}

// ---------------------------------------------------------------------------
// AST extraction helpers
// ---------------------------------------------------------------------------

fn extract_variable_names(module: &Module) -> Vec<String> {
    let mut names = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for v in vars {
                names.push(v.node.clone());
            }
        }
    }
    names
}

fn extract_constant_names(module: &Module) -> Vec<String> {
    let mut names = Vec::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                names.push(decl.name.node.clone());
            }
        }
    }
    names
}

fn find_operator<'a>(module: &'a Module, name: &str) -> Option<&'a tla_core::ast::OperatorDef> {
    module.units.iter().find_map(|u| {
        if let Unit::Operator(op) = &u.node {
            if op.name.node == name {
                return Some(op);
            }
        }
        None
    })
}

/// Extract variable initial values from an Init predicate body.
///
/// Looks for conjuncts of the form `var = expr` or `var \in set`.
fn extract_init_values(expr: &Expr, variable_names: &[String]) -> Vec<(String, String)> {
    let mut values = Vec::new();
    let conjuncts = flatten_and(expr);
    for conj in &conjuncts {
        match conj {
            Expr::Eq(lhs, rhs) => {
                if let Some(name) = expr_as_var_name(&lhs.node, variable_names) {
                    values.push((name, summarize_expr(&rhs.node, 60)));
                }
            }
            Expr::In(lhs, rhs) => {
                if let Some(name) = expr_as_var_name(&lhs.node, variable_names) {
                    values.push((name, format!("\\in {}", summarize_expr(&rhs.node, 60))));
                }
            }
            _ => {}
        }
    }
    values
}

/// Flatten nested `/\` (And) into a list of conjuncts.
fn flatten_and(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::And(lhs, rhs) => {
            let mut result = flatten_and(&lhs.node);
            result.extend(flatten_and(&rhs.node));
            result
        }
        Expr::Label(label) => flatten_and(&label.body.node),
        _ => vec![expr],
    }
}

/// Flatten nested `\/` (Or) into a list of disjuncts.
fn flatten_or(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::Or(lhs, rhs) => {
            let mut result = flatten_or(&lhs.node);
            result.extend(flatten_or(&rhs.node));
            result
        }
        Expr::Label(label) => flatten_or(&label.body.node),
        _ => vec![expr],
    }
}

/// If the expression is a simple variable name (Ident or StateVar), return it.
fn expr_as_var_name(expr: &Expr, variable_names: &[String]) -> Option<String> {
    match expr {
        Expr::Ident(name, _) if variable_names.contains(name) => Some(name.clone()),
        Expr::StateVar(name, _, _) => Some(name.clone()),
        _ => None,
    }
}

/// Extract action names from a Next relation body.
///
/// Looks for top-level disjunction whose arms are named operator references
/// (possibly with existential quantifiers for process parameters).
fn extract_actions(
    module: &Module,
    next_body: &Expr,
    variable_names: &[String],
    detail: AbstractDetail,
) -> Vec<ActionInfo> {
    let disjuncts = flatten_or(next_body);
    let mut actions = Vec::new();

    for disj in &disjuncts {
        if let Some(action) = extract_single_action(module, disj, variable_names, detail) {
            actions.push(action);
        } else {
            // Unnamed disjunct -- give it a synthetic name
            let affected = if matches!(detail, AbstractDetail::Brief) {
                Vec::new()
            } else {
                collect_primed_variables(disj, variable_names)
            };
            let expression = if matches!(detail, AbstractDetail::Full) {
                Some(summarize_expr(disj, 80))
            } else {
                None
            };
            actions.push(ActionInfo {
                name: format!("<anonymous_{}>", actions.len()),
                affected_variables: affected,
                expression,
            });
        }
    }

    actions
}

/// Try to identify a single named action from a disjunct.
///
/// Recognizes patterns:
/// - `ActionName` (bare operator reference)
/// - `ActionName(args)` (operator application)
/// - `\E p \in S : ActionName(p)` (existential wrapper)
fn extract_single_action(
    module: &Module,
    expr: &Expr,
    variable_names: &[String],
    detail: AbstractDetail,
) -> Option<ActionInfo> {
    match expr {
        // Direct operator reference: `ActionName`
        Expr::Ident(name, _) => {
            let affected = if matches!(detail, AbstractDetail::Brief) {
                Vec::new()
            } else {
                find_operator(module, name)
                    .map(|op| collect_primed_variables(&op.body.node, variable_names))
                    .unwrap_or_default()
            };
            let expression = if matches!(detail, AbstractDetail::Full) {
                find_operator(module, name)
                    .map(|op| summarize_expr(&op.body.node, 80))
            } else {
                None
            };
            Some(ActionInfo {
                name: name.clone(),
                affected_variables: affected,
                expression,
            })
        }
        // Operator application: `ActionName(args)`
        Expr::Apply(op_expr, _args) => {
            if let Expr::Ident(name, _) = &op_expr.node {
                let affected = if matches!(detail, AbstractDetail::Brief) {
                    Vec::new()
                } else {
                    find_operator(module, name)
                        .map(|op| collect_primed_variables(&op.body.node, variable_names))
                        .unwrap_or_default()
                };
                let expression = if matches!(detail, AbstractDetail::Full) {
                    find_operator(module, name)
                        .map(|op| summarize_expr(&op.body.node, 80))
                } else {
                    None
                };
                Some(ActionInfo {
                    name: name.clone(),
                    affected_variables: affected,
                    expression,
                })
            } else {
                None
            }
        }
        // Existential wrapper: `\E p \in S : Body`
        Expr::Exists(vars, body) => {
            let inner = extract_single_action(module, &body.node, variable_names, detail);
            if let Some(mut action) = inner {
                let param_names: Vec<String> =
                    vars.iter().map(|v| v.name.node.clone()).collect();
                action.name = format!(
                    "\\E {} : {}",
                    param_names.join(", "),
                    action.name
                );
                Some(action)
            } else {
                None
            }
        }
        // Label wrapper (e.g., P0:: body)
        Expr::Label(label) => {
            extract_single_action(module, &label.body.node, variable_names, detail)
        }
        _ => None,
    }
}

/// Collect variable names that are primed in the expression (i.e., assigned in Next).
fn collect_primed_variables(expr: &Expr, variable_names: &[String]) -> Vec<String> {
    let mut result = Vec::new();
    collect_primed_vars_recursive(expr, variable_names, &mut result);
    result.sort();
    result.dedup();
    result
}

fn collect_primed_vars_recursive(
    expr: &Expr,
    variable_names: &[String],
    out: &mut Vec<String>,
) {
    match expr {
        Expr::Prime(inner) => {
            if let Some(name) = expr_as_var_name(&inner.node, variable_names) {
                out.push(name);
            }
        }
        Expr::Unchanged(inner) => {
            // UNCHANGED <<x, y>> means x' = x /\ y' = y
            collect_unchanged_vars(&inner.node, variable_names, out);
        }
        // Recurse into children for all compound expressions
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::Subseteq(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b)
        | Expr::Range(a, b)
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
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b) => {
            collect_primed_vars_recursive(&a.node, variable_names, out);
            collect_primed_vars_recursive(&b.node, variable_names, out);
        }
        Expr::Not(inner)
        | Expr::Neg(inner)
        | Expr::Powerset(inner)
        | Expr::BigUnion(inner)
        | Expr::Domain(inner)
        | Expr::Always(inner)
        | Expr::Eventually(inner)
        | Expr::Enabled(inner) => {
            collect_primed_vars_recursive(&inner.node, variable_names, out);
        }
        Expr::If(cond, then_, else_) => {
            collect_primed_vars_recursive(&cond.node, variable_names, out);
            collect_primed_vars_recursive(&then_.node, variable_names, out);
            collect_primed_vars_recursive(&else_.node, variable_names, out);
        }
        Expr::Forall(vars, body) | Expr::Exists(vars, body) | Expr::SetBuilder(body, vars) => {
            for v in vars {
                if let Some(d) = &v.domain {
                    collect_primed_vars_recursive(&d.node, variable_names, out);
                }
            }
            collect_primed_vars_recursive(&body.node, variable_names, out);
        }
        Expr::Choose(var, body) | Expr::SetFilter(var, body) => {
            if let Some(d) = &var.domain {
                collect_primed_vars_recursive(&d.node, variable_names, out);
            }
            collect_primed_vars_recursive(&body.node, variable_names, out);
        }
        Expr::FuncDef(vars, body) => {
            for v in vars {
                if let Some(d) = &v.domain {
                    collect_primed_vars_recursive(&d.node, variable_names, out);
                }
            }
            collect_primed_vars_recursive(&body.node, variable_names, out);
        }
        Expr::Let(defs, body) => {
            for def in defs {
                collect_primed_vars_recursive(&def.body.node, variable_names, out);
            }
            collect_primed_vars_recursive(&body.node, variable_names, out);
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for e in elems {
                collect_primed_vars_recursive(&e.node, variable_names, out);
            }
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, e) in fields {
                collect_primed_vars_recursive(&e.node, variable_names, out);
            }
        }
        Expr::RecordAccess(base, _) => {
            collect_primed_vars_recursive(&base.node, variable_names, out);
        }
        Expr::Apply(func, args) => {
            collect_primed_vars_recursive(&func.node, variable_names, out);
            for a in args {
                collect_primed_vars_recursive(&a.node, variable_names, out);
            }
        }
        Expr::Except(base, specs) => {
            collect_primed_vars_recursive(&base.node, variable_names, out);
            for spec in specs {
                for path_elem in &spec.path {
                    if let tla_core::ast::ExceptPathElement::Index(idx) = path_elem {
                        collect_primed_vars_recursive(&idx.node, variable_names, out);
                    }
                }
                collect_primed_vars_recursive(&spec.value.node, variable_names, out);
            }
        }
        Expr::Case(arms, other) => {
            for arm in arms {
                collect_primed_vars_recursive(&arm.guard.node, variable_names, out);
                collect_primed_vars_recursive(&arm.body.node, variable_names, out);
            }
            if let Some(o) = other {
                collect_primed_vars_recursive(&o.node, variable_names, out);
            }
        }
        Expr::Label(label) => {
            collect_primed_vars_recursive(&label.body.node, variable_names, out);
        }
        Expr::Lambda(_, body) => {
            collect_primed_vars_recursive(&body.node, variable_names, out);
        }
        Expr::SubstIn(_, body) => {
            collect_primed_vars_recursive(&body.node, variable_names, out);
        }
        Expr::ModuleRef(_, _, args) => {
            for a in args {
                collect_primed_vars_recursive(&a.node, variable_names, out);
            }
        }
        // Leaves: no children to recurse into
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_)
        | Expr::InstanceExpr(_, _) => {}
    }
}

/// Collect variable names from UNCHANGED expressions.
fn collect_unchanged_vars(expr: &Expr, variable_names: &[String], out: &mut Vec<String>) {
    match expr {
        Expr::Tuple(elems) => {
            for e in elems {
                if let Some(name) = expr_as_var_name(&e.node, variable_names) {
                    out.push(name);
                }
            }
        }
        _ => {
            if let Some(name) = expr_as_var_name(expr, variable_names) {
                out.push(name);
            }
        }
    }
}

/// Produce a truncated human-readable summary of an expression.
fn summarize_expr(expr: &Expr, max_len: usize) -> String {
    let full = pretty_expr(expr);
    if full.len() <= max_len {
        full
    } else {
        let truncated: String = full.chars().take(max_len.saturating_sub(3)).collect();
        format!("{}...", truncated)
    }
}

// ---------------------------------------------------------------------------
// Output: Human-readable
// ---------------------------------------------------------------------------

fn emit_human(model: &AbstractModel, detail: AbstractDetail) {
    println!("=== Abstract View: {} ===", model.module_name);
    println!();

    // EXTENDS
    if !model.extends.is_empty() {
        println!("EXTENDS {}", model.extends.join(", "));
        println!();
    }

    // Constants
    if !model.constants.is_empty() {
        println!("Constants ({}):", model.constants.len());
        for c in &model.constants {
            if let Some(val) = &c.value {
                println!("  {} = {}", c.name, val);
            } else {
                println!("  {}", c.name);
            }
        }
        println!();
    }

    // Variables
    if !model.variables.is_empty() {
        println!("Variables ({}):", model.variables.len());
        for v in &model.variables {
            if let Some(init) = &v.init_value {
                println!("  {} (init: {})", v.name, init);
            } else {
                println!("  {}", v.name);
            }
        }
        println!();
    }

    // Init
    if let Some(init) = &model.init {
        println!("Init: {}", init.operator);
        if let Some(desc) = &init.description {
            println!("  {}", desc);
        }
        println!();
    }

    // Actions (Next)
    if !model.actions.is_empty() {
        println!("Actions ({}):", model.actions.len());
        for action in &model.actions {
            match detail {
                AbstractDetail::Brief => {
                    println!("  - {}", action.name);
                }
                AbstractDetail::Normal | AbstractDetail::Full => {
                    if action.affected_variables.is_empty() {
                        println!("  - {}", action.name);
                    } else {
                        println!(
                            "  - {} [modifies: {}]",
                            action.name,
                            action.affected_variables.join(", ")
                        );
                    }
                    if let Some(expr) = &action.expression {
                        println!("    {}", expr);
                    }
                }
            }
        }
        println!();
    }

    // Invariants
    if !model.invariants.is_empty() {
        println!("Invariants ({}):", model.invariants.len());
        for inv in &model.invariants {
            println!("  - {}", inv);
        }
        println!();
    }

    // Properties
    if !model.properties.is_empty() {
        println!("Properties ({}):", model.properties.len());
        for prop in &model.properties {
            println!("  - {}", prop);
        }
        println!();
    }

    // Symmetry
    if let Some(sym) = &model.symmetry {
        println!("Symmetry: {}", sym);
        println!();
    }

    // Summary
    println!(
        "Summary: {} variable(s), {} constant(s), {} action(s), {} invariant(s), {} operator(s) total",
        model.variables.len(),
        model.constants.len(),
        model.actions.len(),
        model.invariants.len(),
        model.operator_count,
    );
}

// ---------------------------------------------------------------------------
// Output: JSON
// ---------------------------------------------------------------------------

fn emit_json(model: &AbstractModel) -> Result<()> {
    let json = serde_json::to_string_pretty(model).context("serialize abstract model to JSON")?;
    println!("{}", json);
    Ok(())
}

// ---------------------------------------------------------------------------
// Output: Mermaid state diagram
// ---------------------------------------------------------------------------

fn emit_mermaid(model: &AbstractModel, detail: AbstractDetail) {
    println!("stateDiagram-v2");

    // Init transition
    if let Some(init) = &model.init {
        println!("    [*] --> {}", init.operator);
    }

    // Each action becomes a transition from a generic "State" node to itself
    // (state machines are cyclic). For better diagrams, we show each action
    // as a self-loop on the state space.
    if model.actions.is_empty() {
        println!("    state \"{}\" as S", model.module_name);
    } else {
        println!("    state \"{}\" as S", model.module_name);
        for action in &model.actions {
            let label = match detail {
                AbstractDetail::Brief => action.name.clone(),
                AbstractDetail::Normal | AbstractDetail::Full => {
                    if action.affected_variables.is_empty() {
                        action.name.clone()
                    } else {
                        format!(
                            "{} [{}]",
                            action.name,
                            action.affected_variables.join(", ")
                        )
                    }
                }
            };
            println!("    S --> S : {}", label);
        }
    }

    // Note for invariants
    if !model.invariants.is_empty() {
        println!("    note right of S");
        println!("        Invariants:");
        for inv in &model.invariants {
            println!("        - {}", inv);
        }
        println!("    end note");
    }

    // Note for variables
    if !model.variables.is_empty() && !matches!(detail, AbstractDetail::Brief) {
        println!("    note left of S");
        println!("        Variables:");
        for v in &model.variables {
            if let Some(init) = &v.init_value {
                println!("        {} = {}", v.name, init);
            } else {
                println!("        {}", v.name);
            }
        }
        println!("    end note");
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::parse;

    fn parse_module(source: &str) -> Module {
        let parse_result = parse(source);
        assert!(parse_result.errors.is_empty(), "parse errors: {:?}", parse_result.errors);
        let tree = SyntaxNode::new_root(parse_result.green_node);
        let lower_result = tla_core::lower(FileId(0), &tree);
        assert!(lower_result.errors.is_empty(), "lower errors: {:?}", lower_result.errors);
        lower_result.module.expect("no module produced")
    }

    #[test]
    fn test_extract_variable_names() {
        let module = parse_module(
            "---- MODULE Test ----\nVARIABLE x, y, z\nFoo == TRUE\n====",
        );
        let vars = extract_variable_names(&module);
        assert_eq!(vars, vec!["x", "y", "z"]);
    }

    #[test]
    fn test_extract_constant_names() {
        let module = parse_module(
            "---- MODULE Test ----\nCONSTANT N, M\nFoo == N + M\n====",
        );
        let consts = extract_constant_names(&module);
        assert_eq!(consts, vec!["N", "M"]);
    }

    #[test]
    fn test_find_operator_present() {
        let module = parse_module(
            "---- MODULE Test ----\nFoo == 42\nBar == TRUE\n====",
        );
        assert!(find_operator(&module, "Foo").is_some());
        assert!(find_operator(&module, "Bar").is_some());
        assert!(find_operator(&module, "Baz").is_none());
    }

    #[test]
    fn test_flatten_and_simple() {
        let module = parse_module(
            "---- MODULE Test ----\nFoo == 1 = 1 /\\ 2 = 2 /\\ 3 = 3\n====",
        );
        let op = find_operator(&module, "Foo").unwrap();
        let conjuncts = flatten_and(&op.body.node);
        assert_eq!(conjuncts.len(), 3);
    }

    #[test]
    fn test_flatten_or_simple() {
        let module = parse_module(
            "---- MODULE Test ----\nFoo == 1 = 1 \\/ 2 = 2 \\/ 3 = 3\n====",
        );
        let op = find_operator(&module, "Foo").unwrap();
        let disjuncts = flatten_or(&op.body.node);
        assert_eq!(disjuncts.len(), 3);
    }

    #[test]
    fn test_extract_init_values() {
        let module = parse_module(
            "---- MODULE Test ----\nVARIABLE x, y\nInit == x = 0 /\\ y = {}\n====",
        );
        let vars = extract_variable_names(&module);
        let init_op = find_operator(&module, "Init").unwrap();
        let values = extract_init_values(&init_op.body.node, &vars);
        assert_eq!(values.len(), 2);
        assert_eq!(values[0].0, "x");
        assert_eq!(values[1].0, "y");
    }

    #[test]
    fn test_collect_primed_variables() {
        let module = parse_module(
            "---- MODULE Test ----\nVARIABLE x, y, z\nA == x' = 1 /\\ y' = 2 /\\ UNCHANGED z\n====",
        );
        let vars = extract_variable_names(&module);
        let op = find_operator(&module, "A").unwrap();
        let primed = collect_primed_variables(&op.body.node, &vars);
        // x and y are primed, z is in UNCHANGED (which also primes it)
        assert!(primed.contains(&"x".to_string()));
        assert!(primed.contains(&"y".to_string()));
        assert!(primed.contains(&"z".to_string()));
    }

    #[test]
    fn test_summarize_expr_short() {
        let module = parse_module(
            "---- MODULE Test ----\nFoo == 42\n====",
        );
        let op = find_operator(&module, "Foo").unwrap();
        let summary = summarize_expr(&op.body.node, 80);
        assert!(summary.contains("42"));
        assert!(!summary.contains("..."));
    }

    #[test]
    fn test_summarize_expr_truncated() {
        let module = parse_module(
            "---- MODULE Test ----\nFoo == 1 + 2 + 3 + 4 + 5\n====",
        );
        let op = find_operator(&module, "Foo").unwrap();
        let summary = summarize_expr(&op.body.node, 5);
        assert!(summary.ends_with("..."));
    }

    #[test]
    fn test_build_abstract_model_basic() {
        let module = parse_module(
            "---- MODULE Test ----\n\
             CONSTANT N\n\
             VARIABLE x, y\n\
             Init == x = 0 /\\ y = 1\n\
             A == x' = x + 1 /\\ UNCHANGED y\n\
             B == y' = y + 1 /\\ UNCHANGED x\n\
             Next == A \\/ B\n\
             ====",
        );
        let model = build_abstract_model(&module, None, AbstractDetail::Normal);
        assert_eq!(model.module_name, "Test");
        assert_eq!(model.variables.len(), 2);
        assert_eq!(model.constants.len(), 1);
        assert_eq!(model.actions.len(), 2);
        // Check action names
        let action_names: Vec<&str> = model.actions.iter().map(|a| a.name.as_str()).collect();
        assert!(action_names.contains(&"A"));
        assert!(action_names.contains(&"B"));
    }

    #[test]
    fn test_build_model_no_init_no_next() {
        let module = parse_module(
            "---- MODULE Empty ----\nFoo == TRUE\n====",
        );
        let model = build_abstract_model(&module, None, AbstractDetail::Brief);
        assert_eq!(model.module_name, "Empty");
        assert!(model.init.is_none());
        assert!(model.actions.is_empty());
    }

    #[test]
    fn test_abstract_output_format_variants() {
        assert_ne!(AbstractOutputFormat::Human, AbstractOutputFormat::Json);
        assert_ne!(AbstractOutputFormat::Json, AbstractOutputFormat::Mermaid);
    }

    #[test]
    fn test_abstract_detail_variants() {
        assert_ne!(AbstractDetail::Brief, AbstractDetail::Normal);
        assert_ne!(AbstractDetail::Normal, AbstractDetail::Full);
    }

    #[test]
    fn test_emit_json_roundtrip() {
        let module = parse_module(
            "---- MODULE Spec ----\n\
             VARIABLE pc\n\
             Init == pc = \"start\"\n\
             Step == pc' = \"end\"\n\
             Next == Step\n\
             ====",
        );
        let model = build_abstract_model(&module, None, AbstractDetail::Full);
        let json = serde_json::to_string_pretty(&model).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["module_name"], "Spec");
        assert_eq!(parsed["variables"].as_array().unwrap().len(), 1);
        assert_eq!(parsed["actions"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn test_extract_actions_with_exists() {
        let module = parse_module(
            "---- MODULE Test ----\n\
             CONSTANT Procs\n\
             VARIABLE pc\n\
             Move(p) == pc' = p\n\
             Next == \\E p \\in Procs : Move(p)\n\
             ====",
        );
        let vars = extract_variable_names(&module);
        let next_op = find_operator(&module, "Next").unwrap();
        let actions = extract_actions(&module, &next_op.body.node, &vars, AbstractDetail::Normal);
        assert_eq!(actions.len(), 1);
        assert!(actions[0].name.contains("Move"));
        assert!(actions[0].name.contains("\\E"));
    }

    #[test]
    fn test_collect_unchanged_vars_tuple() {
        let module = parse_module(
            "---- MODULE Test ----\n\
             VARIABLE a, b, c\n\
             Act == a' = 1 /\\ UNCHANGED <<b, c>>\n\
             ====",
        );
        let vars = extract_variable_names(&module);
        let op = find_operator(&module, "Act").unwrap();
        let primed = collect_primed_variables(&op.body.node, &vars);
        assert!(primed.contains(&"a".to_string()));
        assert!(primed.contains(&"b".to_string()));
        assert!(primed.contains(&"c".to_string()));
    }

    #[test]
    fn test_extends_extracted() {
        let module = parse_module(
            "---- MODULE Test ----\nEXTENDS Naturals, Sequences\nFoo == TRUE\n====",
        );
        let model = build_abstract_model(&module, None, AbstractDetail::Brief);
        assert_eq!(model.extends, vec!["Naturals", "Sequences"]);
    }
}
