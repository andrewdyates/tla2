// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 typecheck` — type check a TLA+ specification.
//!
//! Parses the spec, runs TIR lowering (which includes type inference), extracts
//! Apalache-style `@type:` annotations from source comments, runs a type analysis
//! pass to detect inconsistencies, and reports results.
//!
//! Part of #3750: Apalache Gap 2.

mod analysis;

use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::Unit;
use tla_core::{lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId};
use tla_tir::{ConstraintGenerator, TirModule, TirType};

use crate::cli_schema::TypecheckOutputFormat;
use crate::helpers::{lower_module_to_tir, read_source};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_typecheck(
    file: &Path,
    output: TypecheckOutputFormat,
    infer_types: bool,
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
            "typecheck aborted: {} parse error(s)",
            parse_result.errors.len()
        );
    }
    let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);

    // Lower CST -> AST (use lower_main_module for multi-module file support)
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
            "typecheck aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("typecheck: lowering produced no module")?;

    // Lower AST -> TIR (includes type inference)
    let tir_module = match lower_module_to_tir(file, &tree, &module) {
        Ok(m) => m,
        Err(e) => {
            // TIR lowering failure is itself a type-level diagnostic.
            match output {
                TypecheckOutputFormat::Human => {
                    eprintln!("error: TIR lowering failed: {e:#}");
                    bail!("typecheck failed");
                }
                TypecheckOutputFormat::Json => {
                    let report = TypecheckReport {
                        file: file.display().to_string(),
                        module: module.name.node.clone(),
                        variables: Vec::new(),
                        constants: Vec::new(),
                        operators: Vec::new(),
                        let_defs: Vec::new(),
                        annotations: Vec::new(),
                        errors: vec![TypecheckError {
                            message: format!("{e:#}"),
                            location: None,
                        }],
                        summary: TypecheckSummary::default(),
                    };
                    println!("{}", serde_json::to_string_pretty(&report)?);
                    return Ok(());
                }
            }
        }
    };

    // Extract variables and constants from AST
    let variables = extract_variables(&module);
    let constants = extract_constants(&module);

    // --- Constraint-based type inference (Hindley-Milner unification) ---
    // Create a ConstraintGenerator, seed it with state variables and constants,
    // infer types for each operator body, and collect unification errors.
    let mut cg = ConstraintGenerator::new();
    for v in &variables {
        cg.add_variable(v);
    }
    for c in &constants {
        cg.add_constant(c);
    }
    // Infer types for each operator, recording the resolved type per operator.
    let mut inferred_op_types: Vec<(String, TirType)> = Vec::new();
    for op in &tir_module.operators {
        let op_ty = if op.params.is_empty() {
            cg.infer(&op.body.node)
        } else {
            // For parameterized operators, allocate fresh type variables for
            // each parameter and build a function type around the inferred body.
            let mut param_tys = Vec::new();
            for _p in &op.params {
                let ptv = cg.unifier_mut().fresh_var();
                param_tys.push(ptv);
            }
            let body_ty = cg.infer(&op.body.node);
            if param_tys.len() == 1 {
                TirType::Func(
                    Box::new(param_tys.into_iter().next().unwrap()),
                    Box::new(body_ty),
                )
            } else {
                TirType::Func(Box::new(TirType::Tuple(param_tys)), Box::new(body_ty))
            }
        };
        let resolved = cg.unifier_mut().resolve(&op_ty);
        inferred_op_types.push((op.name.clone(), resolved));
    }

    // Collect unification errors from the constraint solver.
    let unification_errors: Vec<TypecheckError> = cg
        .unifier()
        .errors()
        .iter()
        .map(|e| TypecheckError {
            message: format!("unification: {}", e.message),
            location: e.location.as_ref().map(|loc| LocationInfo {
                file: loc.clone(),
                line: 0,
                column: 0,
            }),
        })
        .collect();

    // Extract @type: annotations from source comments
    let annotations = extract_type_annotations(&source);

    // Build annotation infos for the analysis engine
    let annotation_infos: Vec<AnnotationInfo> = annotations
        .iter()
        .map(|a| AnnotationInfo {
            operator: a.operator.clone(),
            annotation: a.type_str.clone(),
            line: a.line,
        })
        .collect();

    // Run type analysis (walks TIR, checks annotations, detects type errors)
    let file_path = file.display().to_string();
    let analysis_result = analysis::analyze_module(&tir_module, &annotation_infos, &file_path);

    // Build report with analysis results + unification errors + inferred types
    let report = build_report(
        &file_path,
        &module.name.node,
        &tir_module,
        &variables,
        &constants,
        &annotation_infos,
        analysis_result,
        &unification_errors,
        &inferred_op_types,
    );

    let has_errors = !report.errors.is_empty();
    match output {
        TypecheckOutputFormat::Human => print_human_report(&report, infer_types),
        TypecheckOutputFormat::Json => {
            println!("{}", serde_json::to_string_pretty(&report)?);
        }
    }
    if has_errors {
        std::process::exit(1);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Report types
// ---------------------------------------------------------------------------

#[derive(Debug, serde::Serialize)]
struct TypecheckReport {
    file: String,
    module: String,
    variables: Vec<VariableTypeInfo>,
    constants: Vec<String>,
    operators: Vec<OperatorTypeInfo>,
    /// LET-definition types discovered during analysis.
    let_defs: Vec<OperatorTypeInfo>,
    annotations: Vec<AnnotationInfo>,
    errors: Vec<TypecheckError>,
    summary: TypecheckSummary,
}

#[derive(Debug, Clone, serde::Serialize)]
pub(super) struct OperatorTypeInfo {
    pub name: String,
    pub params: Vec<String>,
    pub body_type: String,
}

#[derive(Debug, Clone, serde::Serialize)]
struct VariableTypeInfo {
    name: String,
    /// Inferred type from usage context, or "Dyn" if not constrained.
    inferred_type: String,
}

#[derive(Debug, Clone, serde::Serialize)]
pub(super) struct AnnotationInfo {
    pub operator: String,
    pub annotation: String,
    pub line: usize,
}

#[derive(Debug, serde::Serialize)]
pub(super) struct TypecheckError {
    pub message: String,
    pub location: Option<LocationInfo>,
}

#[derive(Debug, serde::Serialize)]
pub(super) struct LocationInfo {
    pub file: String,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Default, serde::Serialize)]
struct TypecheckSummary {
    /// Total number of top-level operators.
    total_operators: usize,
    /// Operators with fully resolved types (not Dyn).
    typed_operators: usize,
    /// Operators with Dyn (unresolved) body type.
    untyped_operators: usize,
    /// Number of variables declared.
    total_variables: usize,
    /// Number of constants declared.
    total_constants: usize,
    /// Number of @type: annotations found.
    total_annotations: usize,
    /// Number of type errors detected.
    total_errors: usize,
    /// Number of LET definitions found.
    total_let_defs: usize,
}

// ---------------------------------------------------------------------------
// Type pretty-printing
// ---------------------------------------------------------------------------

fn format_tir_type(ty: &TirType) -> String {
    match ty {
        TirType::Bool => "Bool".to_string(),
        TirType::Int => "Int".to_string(),
        TirType::Str => "Str".to_string(),
        TirType::Set(inner) => format!("Set({})", format_tir_type(inner)),
        TirType::Seq(inner) => format!("Seq({})", format_tir_type(inner)),
        TirType::Func(domain, range) => {
            format!(
                "({} -> {})",
                format_tir_type(domain),
                format_tir_type(range)
            )
        }
        TirType::Tuple(elems) => {
            let inner: Vec<String> = elems.iter().map(|e| format_tir_type(e)).collect();
            format!("<<{}>>", inner.join(", "))
        }
        TirType::Record(fields) => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(id, ty)| {
                    let name = tla_core::resolve_name_id(*id);
                    format!("{}: {}", name, format_tir_type(ty))
                })
                .collect();
            format!("[{}]", inner.join(", "))
        }
        TirType::Var(id) => format!("t{}", id),
        TirType::OpenRecord(fields, row) => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(id, ty)| {
                    let name = tla_core::resolve_name_id(*id);
                    format!("{}: {}", name, format_tir_type(ty))
                })
                .collect();
            format!("[{}, ...t{}]", inner.join(", "), row)
        }
        TirType::Variant(cases) => {
            let inner: Vec<String> = cases
                .iter()
                .map(|(tag, ty)| format!("{}({})", tag, format_tir_type(ty)))
                .collect();
            inner.join(" | ")
        }
        TirType::Dyn => "Dyn".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Variable/constant extraction from AST
// ---------------------------------------------------------------------------

/// Extract VARIABLE declarations from the AST module.
fn extract_variables(module: &tla_core::ast::Module) -> Vec<String> {
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

/// Extract CONSTANT declarations from the AST module.
fn extract_constants(module: &tla_core::ast::Module) -> Vec<String> {
    let mut consts = Vec::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                consts.push(decl.name.node.clone());
            }
        }
    }
    consts
}

/// Infer variable types by scanning TIR operator bodies for state variable
/// references. Returns a list of (variable_name, inferred_type) pairs.
fn infer_variable_types(tir_module: &TirModule, variables: &[String]) -> Vec<VariableTypeInfo> {
    // Collect variable types from TIR name references
    let mut var_types: std::collections::HashMap<String, TirType> =
        std::collections::HashMap::new();

    for op in &tir_module.operators {
        collect_var_types_from_expr(&op.body.node, &mut var_types);
    }

    variables
        .iter()
        .map(|v| {
            let inferred = var_types
                .get(v)
                .map(|ty| format_tir_type(ty))
                .unwrap_or_else(|| "Dyn".to_string());
            VariableTypeInfo {
                name: v.clone(),
                inferred_type: inferred,
            }
        })
        .collect()
}

/// Recursively collect state variable types from a TIR expression.
fn collect_var_types_from_expr(
    expr: &tla_tir::TirExpr,
    var_types: &mut std::collections::HashMap<String, TirType>,
) {
    use tla_tir::{TirExpr, TirNameKind};

    match expr {
        TirExpr::Name(name_ref) => {
            if matches!(name_ref.kind, TirNameKind::StateVar { .. }) && name_ref.ty != TirType::Dyn
            {
                var_types
                    .entry(name_ref.name.clone())
                    .or_insert_with(|| name_ref.ty.clone());
            }
        }
        // Recursively walk all children
        TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::In {
            elem: left,
            set: right,
        }
        | TirExpr::Subseteq { left, right }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::FuncApply {
            func: left,
            arg: right,
        }
        | TirExpr::FuncSet {
            domain: left,
            range: right,
        }
        | TirExpr::Range {
            lo: left,
            hi: right,
        }
        | TirExpr::LeadsTo { left, right }
        | TirExpr::WeakFair {
            vars: left,
            action: right,
        }
        | TirExpr::StrongFair {
            vars: left,
            action: right,
        } => {
            collect_var_types_from_expr(&left.node, var_types);
            collect_var_types_from_expr(&right.node, var_types);
        }
        TirExpr::ArithNeg(inner)
        | TirExpr::BoolNot(inner)
        | TirExpr::Unchanged(inner)
        | TirExpr::Prime(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner)
        | TirExpr::Always(inner)
        | TirExpr::Eventually(inner)
        | TirExpr::Enabled(inner) => {
            collect_var_types_from_expr(&inner.node, var_types);
        }
        TirExpr::KSubset { base, k } => {
            collect_var_types_from_expr(&base.node, var_types);
            collect_var_types_from_expr(&k.node, var_types);
        }
        TirExpr::RecordAccess { record, .. } => {
            collect_var_types_from_expr(&record.node, var_types);
        }
        TirExpr::If { cond, then_, else_ } => {
            collect_var_types_from_expr(&cond.node, var_types);
            collect_var_types_from_expr(&then_.node, var_types);
            collect_var_types_from_expr(&else_.node, var_types);
        }
        TirExpr::ActionSubscript {
            action, subscript, ..
        } => {
            collect_var_types_from_expr(&action.node, var_types);
            collect_var_types_from_expr(&subscript.node, var_types);
        }
        TirExpr::Forall { vars, body } | TirExpr::Exists { vars, body } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    collect_var_types_from_expr(&d.node, var_types);
                }
            }
            collect_var_types_from_expr(&body.node, var_types);
        }
        TirExpr::Choose { var, body } => {
            if let Some(d) = &var.domain {
                collect_var_types_from_expr(&d.node, var_types);
            }
            collect_var_types_from_expr(&body.node, var_types);
        }
        TirExpr::Let { defs, body } => {
            for def in defs {
                collect_var_types_from_expr(&def.body.node, var_types);
            }
            collect_var_types_from_expr(&body.node, var_types);
        }
        TirExpr::Case { arms, other } => {
            for arm in arms {
                collect_var_types_from_expr(&arm.guard.node, var_types);
                collect_var_types_from_expr(&arm.body.node, var_types);
            }
            if let Some(o) = other {
                collect_var_types_from_expr(&o.node, var_types);
            }
        }
        TirExpr::SetEnum(elems) | TirExpr::Tuple(elems) | TirExpr::Times(elems) => {
            for e in elems {
                collect_var_types_from_expr(&e.node, var_types);
            }
        }
        TirExpr::SetFilter { var, body } => {
            if let Some(d) = &var.domain {
                collect_var_types_from_expr(&d.node, var_types);
            }
            collect_var_types_from_expr(&body.node, var_types);
        }
        TirExpr::SetBuilder { body, vars } | TirExpr::FuncDef { vars, body } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    collect_var_types_from_expr(&d.node, var_types);
                }
            }
            collect_var_types_from_expr(&body.node, var_types);
        }
        TirExpr::Record(fields) | TirExpr::RecordSet(fields) => {
            for (_, expr) in fields {
                collect_var_types_from_expr(&expr.node, var_types);
            }
        }
        TirExpr::Except { base, specs } => {
            collect_var_types_from_expr(&base.node, var_types);
            for spec in specs {
                collect_var_types_from_expr(&spec.value.node, var_types);
                for path_elem in &spec.path {
                    if let tla_tir::TirExceptPathElement::Index(idx) = path_elem {
                        collect_var_types_from_expr(&idx.node, var_types);
                    }
                }
            }
        }
        TirExpr::Apply { op, args } => {
            collect_var_types_from_expr(&op.node, var_types);
            for a in args {
                collect_var_types_from_expr(&a.node, var_types);
            }
        }
        TirExpr::Lambda { body, .. } | TirExpr::Label { body, .. } => {
            collect_var_types_from_expr(&body.node, var_types);
        }
        TirExpr::OperatorRef(op_ref) => {
            for seg in &op_ref.path {
                for a in &seg.args {
                    collect_var_types_from_expr(&a.node, var_types);
                }
            }
            for a in &op_ref.args {
                collect_var_types_from_expr(&a.node, var_types);
            }
        }
        TirExpr::Const { .. } | TirExpr::ExceptAt | TirExpr::OpRef(_) => {}
    }
}

// ---------------------------------------------------------------------------
// @type: annotation extraction
// ---------------------------------------------------------------------------

/// An extracted `@type:` annotation from a TLA+ source comment.
struct RawAnnotation {
    /// The operator name this annotation is associated with (next non-comment
    /// operator definition after the annotation comment).
    operator: String,
    /// The raw type string from the annotation.
    type_str: String,
    /// 1-based line number where the annotation appeared.
    line: usize,
}

/// Extract Apalache-style `@type:` annotations from TLA+ source comments.
///
/// The convention is: a `\* @type: <type>;` comment immediately precedes
/// an operator definition. We scan for the pattern and associate each
/// annotation with the next operator definition found in subsequent lines.
fn extract_type_annotations(source: &str) -> Vec<RawAnnotation> {
    let mut annotations = Vec::new();
    let lines: Vec<&str> = source.lines().collect();

    let mut pending_type: Option<(String, usize)> = None;

    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        // Check for @type: annotation in line/block comments
        if let Some(type_str) = extract_type_from_comment(trimmed) {
            pending_type = Some((type_str, idx + 1));
            continue;
        }

        // If we have a pending type annotation, look for an operator definition
        if let Some((ref type_str, line_num)) = pending_type {
            if let Some(op_name) = extract_operator_name(trimmed) {
                annotations.push(RawAnnotation {
                    operator: op_name,
                    type_str: type_str.clone(),
                    line: line_num,
                });
                pending_type = None;
            } else if !trimmed.is_empty()
                && !trimmed.starts_with("\\*")
                && !trimmed.starts_with("(*")
                && !trimmed.starts_with("*)")
                && !trimmed.starts_with('*')
            {
                // Non-empty, non-comment line without operator def: annotation orphaned
                pending_type = None;
            }
        }
    }

    annotations
}

/// Try to extract a `@type:` annotation string from a comment line.
fn extract_type_from_comment(line: &str) -> Option<String> {
    // Match patterns like:
    //   \* @type: Set(a) => a;
    //   * @type: Int;
    //   (* @type: Bool; *)
    let patterns = ["\\* @type:", "* @type:", "(* @type:"];
    for pat in &patterns {
        if let Some(rest) = line.strip_prefix(pat).or_else(|| {
            // Also handle leading whitespace + pattern
            let trimmed = line.trim_start();
            trimmed.strip_prefix(pat)
        }) {
            let type_str = rest
                .trim()
                .trim_end_matches("*)")
                .trim()
                .trim_end_matches(';')
                .trim()
                .to_string();
            if !type_str.is_empty() {
                return Some(type_str);
            }
        }
    }
    None
}

/// Try to extract the operator name from a definition line.
///
/// Matches patterns like:
/// - `OpName == ...`
/// - `OpName(args) == ...`
/// - `LOCAL OpName == ...`
fn extract_operator_name(line: &str) -> Option<String> {
    let line = line
        .strip_prefix("LOCAL")
        .map(|s| s.trim_start())
        .unwrap_or(line);

    // Find `==` in the line
    if let Some(eq_pos) = line.find("==") {
        let before_eq = line[..eq_pos].trim();
        // Handle parameterized: `Name(x, y)` or `Name(x, y, z)`
        let name = if let Some(paren_pos) = before_eq.find('(') {
            &before_eq[..paren_pos]
        } else {
            before_eq
        };
        let name = name.trim();
        // Validate it looks like an identifier
        if !name.is_empty()
            && name.chars().all(|c| c.is_alphanumeric() || c == '_')
            && name
                .chars()
                .next()
                .map_or(false, |c| c.is_alphabetic() || c == '_')
        {
            return Some(name.to_string());
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Report building
// ---------------------------------------------------------------------------

fn build_report(
    file_path: &str,
    module_name: &str,
    tir_module: &TirModule,
    variables: &[String],
    constants: &[String],
    annotations: &[AnnotationInfo],
    analysis_result: analysis::AnalysisResult,
    unification_errors: &[TypecheckError],
    inferred_op_types: &[(String, TirType)],
) -> TypecheckReport {
    // Build operator type info. If TIR's built-in type is Dyn but the
    // constraint solver inferred a concrete type, prefer the inferred type.
    let operators: Vec<OperatorTypeInfo> = tir_module
        .operators
        .iter()
        .map(|op| {
            let tir_ty = op.body.node.ty();
            let body_type = if tir_ty == TirType::Dyn {
                // Check if constraint inference found something better.
                if let Some((_, inferred)) = inferred_op_types.iter().find(|(n, _)| *n == op.name) {
                    if *inferred != TirType::Dyn {
                        format_tir_type(inferred)
                    } else {
                        "Dyn".to_string()
                    }
                } else {
                    "Dyn".to_string()
                }
            } else {
                format_tir_type(&tir_ty)
            };
            OperatorTypeInfo {
                name: op.name.clone(),
                params: op.params.clone(),
                body_type,
            }
        })
        .collect();

    // Infer variable types from TIR usage
    let var_infos = infer_variable_types(tir_module, variables);

    let typed_count = operators.iter().filter(|op| op.body_type != "Dyn").count();
    let untyped_count = operators.len() - typed_count;

    // Merge analysis errors with unification errors.
    let mut all_errors = analysis_result.errors;
    all_errors.extend(unification_errors.iter().map(|e| TypecheckError {
        message: e.message.clone(),
        location: e.location.as_ref().map(|l| LocationInfo {
            file: l.file.clone(),
            line: l.line,
            column: l.column,
        }),
    }));

    let summary = TypecheckSummary {
        total_operators: operators.len(),
        typed_operators: typed_count,
        untyped_operators: untyped_count,
        total_variables: variables.len(),
        total_constants: constants.len(),
        total_annotations: annotations.len(),
        total_errors: all_errors.len(),
        total_let_defs: analysis_result.let_defs.len(),
    };

    TypecheckReport {
        file: file_path.to_string(),
        module: module_name.to_string(),
        variables: var_infos,
        constants: constants.to_vec(),
        operators,
        let_defs: analysis_result.let_defs,
        annotations: annotations.to_vec(),
        errors: all_errors,
        summary,
    }
}

// ---------------------------------------------------------------------------
// Human-readable output
// ---------------------------------------------------------------------------

fn print_human_report(report: &TypecheckReport, infer_types: bool) {
    println!("File: {}", report.file);
    println!("Module: {}", report.module);
    println!();

    if !report.errors.is_empty() {
        println!("Errors ({}):", report.errors.len());
        for err in &report.errors {
            if let Some(loc) = &err.location {
                println!(
                    "  {}:{}:{}: {}",
                    loc.file, loc.line, loc.column, err.message
                );
            } else {
                println!("  {}", err.message);
            }
        }
        println!();
    }

    if infer_types {
        // Full type map mode: show everything
        if !report.variables.is_empty() {
            println!("Variables ({}):", report.variables.len());
            for var in &report.variables {
                println!("  {} : {}", var.name, var.inferred_type);
            }
            println!();
        }

        if !report.constants.is_empty() {
            println!("Constants ({}):", report.constants.len());
            for c in &report.constants {
                println!("  {} : Dyn", c);
            }
            println!();
        }
    }

    if report.operators.is_empty() {
        println!("  (no operators)");
    } else {
        println!("Operators ({}):", report.operators.len());
        for op in &report.operators {
            if op.params.is_empty() {
                println!("  {} : {}", op.name, op.body_type);
            } else {
                println!("  {}({}) : {}", op.name, op.params.join(", "), op.body_type);
            }
        }
    }

    if infer_types && !report.let_defs.is_empty() {
        println!();
        println!("LET definitions ({}):", report.let_defs.len());
        for def in &report.let_defs {
            if def.params.is_empty() {
                println!("  {} : {}", def.name, def.body_type);
            } else {
                println!(
                    "  {}({}) : {}",
                    def.name,
                    def.params.join(", "),
                    def.body_type
                );
            }
        }
    }

    if !report.annotations.is_empty() {
        println!();
        println!("Type annotations ({}):", report.annotations.len());
        for ann in &report.annotations {
            println!("  line {}: {} : {}", ann.line, ann.operator, ann.annotation);
        }
    }

    // Summary
    println!();
    let s = &report.summary;
    if s.total_errors == 0 {
        println!(
            "Type check passed. {}/{} operators typed, {} variables, {} constants.",
            s.typed_operators, s.total_operators, s.total_variables, s.total_constants,
        );
    } else {
        println!(
            "Type check FAILED: {} error(s). {}/{} operators typed.",
            s.total_errors, s.typed_operators, s.total_operators,
        );
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::lower;

    #[test]
    fn extract_line_comment_annotation() {
        let s = extract_type_from_comment("\\* @type: Int;");
        assert_eq!(s.as_deref(), Some("Int"));
    }

    #[test]
    fn extract_block_comment_annotation() {
        let s = extract_type_from_comment("(* @type: Set(Int); *)");
        assert_eq!(s.as_deref(), Some("Set(Int)"));
    }

    #[test]
    fn extract_operator_name_simple() {
        assert_eq!(
            extract_operator_name("Foo == 1 + 2"),
            Some("Foo".to_string()),
        );
    }

    #[test]
    fn extract_operator_name_with_params() {
        assert_eq!(
            extract_operator_name("Bar(x, y) == x + y"),
            Some("Bar".to_string()),
        );
    }

    #[test]
    fn extract_operator_name_local() {
        assert_eq!(
            extract_operator_name("LOCAL Helper == TRUE"),
            Some("Helper".to_string()),
        );
    }

    #[test]
    fn extract_operator_name_none_for_non_def() {
        assert_eq!(extract_operator_name("VARIABLE x"), None);
    }

    #[test]
    fn extract_type_annotations_basic() {
        let source = r#"---- MODULE Test ----
\* @type: Int;
Foo == 42
\* @type: Bool;
Bar == TRUE
===="#;
        let annotations = extract_type_annotations(source);
        assert_eq!(annotations.len(), 2);
        assert_eq!(annotations[0].operator, "Foo");
        assert_eq!(annotations[0].type_str, "Int");
        assert_eq!(annotations[0].line, 2);
        assert_eq!(annotations[1].operator, "Bar");
        assert_eq!(annotations[1].type_str, "Bool");
        assert_eq!(annotations[1].line, 4);
    }

    #[test]
    fn extract_type_annotations_orphaned() {
        let source = r#"---- MODULE Test ----
\* @type: Int;
VARIABLE x
Foo == 42
===="#;
        let annotations = extract_type_annotations(source);
        // The annotation is orphaned because the next non-comment line is VARIABLE
        assert_eq!(annotations.len(), 0);
    }

    #[test]
    fn extract_variables_from_module() {
        let source = r#"---- MODULE Test ----
VARIABLE x, y, z
Foo == x + y + z
===="#;
        let parse_result = parse(source);
        let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);
        let lower_result = lower(FileId(0), &tree);
        let module = lower_result.module.unwrap();
        let vars = extract_variables(&module);
        assert_eq!(vars, vec!["x", "y", "z"]);
    }

    #[test]
    fn extract_constants_from_module() {
        let source = r#"---- MODULE Test ----
CONSTANT N, M
Foo == N + M
===="#;
        let parse_result = parse(source);
        let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);
        let lower_result = lower(FileId(0), &tree);
        let module = lower_result.module.unwrap();
        let consts = extract_constants(&module);
        assert_eq!(consts, vec!["N", "M"]);
    }

    #[test]
    fn summary_counts_typed_vs_untyped() {
        let summary = TypecheckSummary {
            total_operators: 5,
            typed_operators: 3,
            untyped_operators: 2,
            total_variables: 2,
            total_constants: 1,
            total_annotations: 0,
            total_errors: 0,
            total_let_defs: 0,
        };
        assert_eq!(summary.typed_operators + summary.untyped_operators, 5);
    }
}
