// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 convert` — format conversion for TLA+ and related formats.
//!
//! Supported conversions:
//! - **tla-to-json**: Parse TLA+ spec, emit structured JSON AST
//! - **json-to-tla**: Read JSON AST, pretty-print as TLA+ source
//! - **tla-to-markdown**: Generate documentation from a TLA+ spec
//! - **trace-to-table**: Convert a JSON counterexample trace to a readable table

use std::collections::HashMap;
use std::io::Write;
use std::path::Path;

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use tla_check::{JsonOutput, StateInfo};
use tla_core::ast::{
    BoundVar, ConstantDecl, ExceptPathElement, Expr, InstanceDecl, Module,
    OperatorDef, Unit,
};
use tla_core::{lower_main_module, FileId};

use crate::cli_schema::{ConvertFrom, ConvertTo};
use crate::helpers::{parse_or_report, read_source};

// ---------------------------------------------------------------------------
// JSON AST types — serializable representation of the TLA+ module structure
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonModule {
    pub name: String,
    pub extends: Vec<String>,
    pub variables: Vec<String>,
    pub constants: Vec<JsonConstant>,
    pub operators: Vec<JsonOperator>,
    pub instances: Vec<JsonInstance>,
    pub assumes: Vec<JsonAssume>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonConstant {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arity: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonOperator {
    pub name: String,
    pub params: Vec<JsonParam>,
    pub local: bool,
    pub body: JsonExpr,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonParam {
    pub name: String,
    #[serde(skip_serializing_if = "is_zero")]
    pub arity: usize,
}

fn is_zero(v: &usize) -> bool {
    *v == 0
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonInstance {
    pub module: String,
    pub local: bool,
    pub substitutions: Vec<JsonSubstitution>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonSubstitution {
    pub from: String,
    pub to: JsonExpr,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonAssume {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub expr: JsonExpr,
}

/// Simplified expression tree for JSON serialization.
///
/// Covers all major expression forms. Complex nested expressions are
/// represented recursively. This is intentionally a simplification —
/// round-tripping preserves structure but not spans or internal IDs.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub(crate) enum JsonExpr {
    #[serde(rename = "bool")]
    Bool { value: bool },
    #[serde(rename = "int")]
    Int { value: String },
    #[serde(rename = "string")]
    StringLit { value: String },
    #[serde(rename = "ident")]
    Ident { name: String },
    #[serde(rename = "apply")]
    Apply {
        operator: Box<JsonExpr>,
        args: Vec<JsonExpr>,
    },
    #[serde(rename = "and")]
    And {
        left: Box<JsonExpr>,
        right: Box<JsonExpr>,
    },
    #[serde(rename = "or")]
    Or {
        left: Box<JsonExpr>,
        right: Box<JsonExpr>,
    },
    #[serde(rename = "not")]
    Not { operand: Box<JsonExpr> },
    #[serde(rename = "implies")]
    Implies {
        left: Box<JsonExpr>,
        right: Box<JsonExpr>,
    },
    #[serde(rename = "equiv")]
    Equiv {
        left: Box<JsonExpr>,
        right: Box<JsonExpr>,
    },
    #[serde(rename = "forall")]
    Forall {
        bounds: Vec<JsonBound>,
        body: Box<JsonExpr>,
    },
    #[serde(rename = "exists")]
    Exists {
        bounds: Vec<JsonBound>,
        body: Box<JsonExpr>,
    },
    #[serde(rename = "choose")]
    Choose {
        bound: JsonBound,
        body: Box<JsonExpr>,
    },
    #[serde(rename = "set_enum")]
    SetEnum { elements: Vec<JsonExpr> },
    #[serde(rename = "set_builder")]
    SetBuilder {
        expr: Box<JsonExpr>,
        bounds: Vec<JsonBound>,
    },
    #[serde(rename = "set_filter")]
    SetFilter {
        bound: JsonBound,
        predicate: Box<JsonExpr>,
    },
    #[serde(rename = "in")]
    In {
        left: Box<JsonExpr>,
        right: Box<JsonExpr>,
    },
    #[serde(rename = "not_in")]
    NotIn {
        left: Box<JsonExpr>,
        right: Box<JsonExpr>,
    },
    #[serde(rename = "if_then_else")]
    IfThenElse {
        cond: Box<JsonExpr>,
        then_: Box<JsonExpr>,
        else_: Box<JsonExpr>,
    },
    #[serde(rename = "let_in")]
    LetIn {
        defs: Vec<JsonOperator>,
        body: Box<JsonExpr>,
    },
    #[serde(rename = "prime")]
    Prime { operand: Box<JsonExpr> },
    #[serde(rename = "tuple")]
    Tuple { elements: Vec<JsonExpr> },
    #[serde(rename = "record")]
    Record { fields: Vec<JsonRecordField> },
    #[serde(rename = "record_set")]
    RecordSet { fields: Vec<JsonRecordField> },
    #[serde(rename = "function")]
    Function {
        bounds: Vec<JsonBound>,
        body: Box<JsonExpr>,
    },
    #[serde(rename = "func_apply")]
    FuncApply {
        func: Box<JsonExpr>,
        arg: Box<JsonExpr>,
    },
    #[serde(rename = "func_set")]
    FuncSet {
        domain: Box<JsonExpr>,
        range: Box<JsonExpr>,
    },
    #[serde(rename = "except")]
    Except {
        base: Box<JsonExpr>,
        updates: Vec<JsonExceptUpdate>,
    },
    #[serde(rename = "lambda")]
    Lambda {
        params: Vec<String>,
        body: Box<JsonExpr>,
    },
    #[serde(rename = "unchanged")]
    Unchanged { expr: Box<JsonExpr> },
    #[serde(rename = "enabled")]
    Enabled { expr: Box<JsonExpr> },
    #[serde(rename = "domain")]
    Domain { expr: Box<JsonExpr> },
    #[serde(rename = "case")]
    Case {
        arms: Vec<JsonCaseArm>,
        #[serde(skip_serializing_if = "Option::is_none")]
        other: Option<Box<JsonExpr>>,
    },
    #[serde(rename = "module_ref")]
    ModuleRef {
        module: String,
        name: String,
        args: Vec<JsonExpr>,
    },
    #[serde(rename = "op_ref")]
    OpRef { name: String },
    #[serde(rename = "binary_op")]
    BinaryOp {
        op: String,
        left: Box<JsonExpr>,
        right: Box<JsonExpr>,
    },
    #[serde(rename = "unary_op")]
    UnaryOp { op: String, operand: Box<JsonExpr> },
    /// Catch-all for complex expressions not individually enumerated.
    #[serde(rename = "other")]
    Other { description: String },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonBound {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub domain: Option<Box<JsonExpr>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonRecordField {
    pub name: String,
    pub value: JsonExpr,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonExceptUpdate {
    pub path: Vec<JsonExpr>,
    pub value: JsonExpr,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct JsonCaseArm {
    pub guard: JsonExpr,
    pub body: JsonExpr,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Configuration for the convert command.
pub(crate) struct ConvertConfig {
    pub input: std::path::PathBuf,
    pub from: ConvertFrom,
    pub to: ConvertTo,
    pub output: Option<std::path::PathBuf>,
}

/// Run the convert command.
pub(crate) fn cmd_convert(config: ConvertConfig) -> Result<()> {
    match (&config.from, &config.to) {
        (ConvertFrom::Tla, ConvertTo::Json) => tla_to_json(&config),
        (ConvertFrom::Json, ConvertTo::Tla) => json_to_tla(&config),
        (ConvertFrom::Tla, ConvertTo::Markdown) => tla_to_markdown(&config),
        (ConvertFrom::Trace, ConvertTo::Table) => trace_to_table(&config),
        (from, to) => bail!(
            "Unsupported conversion: {:?} -> {:?}. Supported: \
             tla->json, json->tla, tla->markdown, trace->table",
            from,
            to
        ),
    }
}

// ---------------------------------------------------------------------------
// tla-to-json
// ---------------------------------------------------------------------------

fn tla_to_json(config: &ConvertConfig) -> Result<()> {
    let module = parse_tla_module(&config.input)?;
    let json_module = module_to_json(&module);
    let json_str =
        serde_json::to_string_pretty(&json_module).context("Failed to serialize module to JSON")?;
    write_output(config.output.as_deref(), json_str.as_bytes())
}

// ---------------------------------------------------------------------------
// json-to-tla
// ---------------------------------------------------------------------------

fn json_to_tla(config: &ConvertConfig) -> Result<()> {
    let content = std::fs::read_to_string(&config.input)
        .with_context(|| format!("Failed to read {}", config.input.display()))?;
    let json_module: JsonModule = serde_json::from_str(&content)
        .with_context(|| format!("Failed to parse JSON from {}", config.input.display()))?;
    let tla_source = json_module_to_tla(&json_module);
    write_output(config.output.as_deref(), tla_source.as_bytes())
}

// ---------------------------------------------------------------------------
// tla-to-markdown
// ---------------------------------------------------------------------------

fn tla_to_markdown(config: &ConvertConfig) -> Result<()> {
    let source = read_source(&config.input)?;
    let module = parse_tla_module(&config.input)?;

    let mut out = String::new();

    // Title
    out.push_str(&format!("# Module: {}\n\n", module.name.node));

    // Extract header comment (lines before ---- MODULE)
    let header_comment = extract_header_comment(&source);
    if !header_comment.is_empty() {
        out.push_str(&format!("{header_comment}\n\n"));
    }

    // Extends
    if !module.extends.is_empty() {
        let extends: Vec<&str> = module.extends.iter().map(|e| e.node.as_str()).collect();
        out.push_str(&format!("**Extends:** {}\n\n", extends.join(", ")));
    }

    // Constants table
    let constants = collect_constants(&module);
    if !constants.is_empty() {
        out.push_str("## Constants\n\n");
        out.push_str("| Name | Arity |\n");
        out.push_str("|------|-------|\n");
        for c in &constants {
            let arity_str = c.arity.map_or("-".to_string(), |a| a.to_string());
            out.push_str(&format!("| `{}` | {} |\n", c.name.node, arity_str));
        }
        out.push('\n');
    }

    // Variables table
    let variables = collect_variables(&module);
    if !variables.is_empty() {
        out.push_str("## Variables\n\n");
        out.push_str("| Name |\n");
        out.push_str("|------|\n");
        for v in &variables {
            out.push_str(&format!("| `{v}` |\n"));
        }
        out.push('\n');
    }

    // Operators
    let operators = collect_operators(&module);
    if !operators.is_empty() {
        out.push_str("## Operators\n\n");
        for op in &operators {
            let params: Vec<&str> = op.params.iter().map(|p| p.name.node.as_str()).collect();
            let sig = if params.is_empty() {
                format!("`{}`", op.name.node)
            } else {
                format!("`{}({})`", op.name.node, params.join(", "))
            };
            let visibility = if op.local { " *(local)*" } else { "" };
            out.push_str(&format!("### {sig}{visibility}\n\n"));
        }
    }

    // Instances
    let instances = collect_instances(&module);
    if !instances.is_empty() {
        out.push_str("## Instances\n\n");
        for inst in &instances {
            let local = if inst.local { " *(local)*" } else { "" };
            out.push_str(&format!("- `INSTANCE {}`{local}\n", inst.module.node));
        }
        out.push('\n');
    }

    write_output(config.output.as_deref(), out.as_bytes())
}

// ---------------------------------------------------------------------------
// trace-to-table
// ---------------------------------------------------------------------------

fn trace_to_table(config: &ConvertConfig) -> Result<()> {
    let content = std::fs::read_to_string(&config.input)
        .with_context(|| format!("Failed to read {}", config.input.display()))?;
    let output: JsonOutput = serde_json::from_str(&content)
        .with_context(|| format!("Failed to parse JSON from {}", config.input.display()))?;

    let counterexample = output.counterexample.as_ref();
    if counterexample.is_none() || counterexample.is_some_and(|c| c.states.is_empty()) {
        println!("No counterexample trace found in the output file.");
        println!("Status: {}", output.result.status);
        return Ok(());
    }

    let ce = counterexample.expect("checked above");
    let states = &ce.states;

    // Collect all variable names across all states (stable order).
    let var_names = collect_trace_variable_names(states);
    if var_names.is_empty() {
        println!("(no variables in trace)");
        return Ok(());
    }

    // Build the table.
    let table = format_trace_table(states, &var_names);
    write_output(config.output.as_deref(), table.as_bytes())
}

// ---------------------------------------------------------------------------
// Helpers: parsing
// ---------------------------------------------------------------------------

fn parse_tla_module(file: &Path) -> Result<Module> {
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;
    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        bail!(
            "TLA+ lowering failed with {} error(s)",
            result.errors.len()
        );
    }
    result.module.context("lower produced no module")
}

// ---------------------------------------------------------------------------
// Helpers: AST collection
// ---------------------------------------------------------------------------

fn collect_variables(module: &Module) -> Vec<String> {
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

fn collect_constants(module: &Module) -> Vec<&ConstantDecl> {
    let mut constants = Vec::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                constants.push(decl);
            }
        }
    }
    constants
}

fn collect_operators(module: &Module) -> Vec<&OperatorDef> {
    let mut ops = Vec::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            ops.push(op);
        }
    }
    ops
}

fn collect_instances(module: &Module) -> Vec<&InstanceDecl> {
    let mut insts = Vec::new();
    for unit in &module.units {
        if let Unit::Instance(inst) = &unit.node {
            insts.push(inst);
        }
    }
    insts
}

// ---------------------------------------------------------------------------
// Helpers: AST -> JSON conversion
// ---------------------------------------------------------------------------

fn module_to_json(module: &Module) -> JsonModule {
    let variables = collect_variables(module);

    let constants = collect_constants(module)
        .into_iter()
        .map(|c| JsonConstant {
            name: c.name.node.clone(),
            arity: c.arity,
        })
        .collect();

    let operators = collect_operators(module)
        .into_iter()
        .map(operator_to_json)
        .collect();

    let instances = collect_instances(module)
        .into_iter()
        .map(|inst| JsonInstance {
            module: inst.module.node.clone(),
            local: inst.local,
            substitutions: inst
                .substitutions
                .iter()
                .map(|s| JsonSubstitution {
                    from: s.from.node.clone(),
                    to: expr_to_json(&s.to.node),
                })
                .collect(),
        })
        .collect();

    let mut assumes = Vec::new();
    for unit in &module.units {
        if let Unit::Assume(decl) = &unit.node {
            assumes.push(JsonAssume {
                name: decl.name.as_ref().map(|n| n.node.clone()),
                expr: expr_to_json(&decl.expr.node),
            });
        }
    }

    JsonModule {
        name: module.name.node.clone(),
        extends: module.extends.iter().map(|e| e.node.clone()).collect(),
        variables,
        constants,
        operators,
        instances,
        assumes,
    }
}

fn operator_to_json(op: &OperatorDef) -> JsonOperator {
    JsonOperator {
        name: op.name.node.clone(),
        params: op
            .params
            .iter()
            .map(|p| JsonParam {
                name: p.name.node.clone(),
                arity: p.arity,
            })
            .collect(),
        local: op.local,
        body: expr_to_json(&op.body.node),
    }
}

fn bound_to_json(bv: &BoundVar) -> JsonBound {
    JsonBound {
        name: bv.name.node.clone(),
        domain: bv.domain.as_ref().map(|d| Box::new(expr_to_json(&d.node))),
    }
}

fn binary_op(op: &str, l: &Expr, r: &Expr) -> JsonExpr {
    JsonExpr::BinaryOp {
        op: op.to_string(),
        left: Box::new(expr_to_json(l)),
        right: Box::new(expr_to_json(r)),
    }
}

fn except_path_to_json(path: &[ExceptPathElement]) -> Vec<JsonExpr> {
    path.iter()
        .map(|elem| match elem {
            ExceptPathElement::Index(e) => expr_to_json(&e.node),
            ExceptPathElement::Field(field) => JsonExpr::StringLit {
                value: field.name.node.clone(),
            },
        })
        .collect()
}

#[allow(clippy::too_many_lines)]
fn expr_to_json(expr: &Expr) -> JsonExpr {
    match expr {
        Expr::Bool(b) => JsonExpr::Bool { value: *b },
        Expr::Int(n) => JsonExpr::Int {
            value: n.to_string(),
        },
        Expr::String(s) => JsonExpr::StringLit { value: s.clone() },
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            JsonExpr::Ident { name: name.clone() }
        }
        Expr::Apply(op, args) => JsonExpr::Apply {
            operator: Box::new(expr_to_json(&op.node)),
            args: args.iter().map(|a| expr_to_json(&a.node)).collect(),
        },
        Expr::OpRef(name) => JsonExpr::OpRef { name: name.clone() },
        Expr::ModuleRef(target, name, args) => JsonExpr::ModuleRef {
            module: target.to_string(),
            name: name.clone(),
            args: args.iter().map(|a| expr_to_json(&a.node)).collect(),
        },
        Expr::Lambda(params, body) => JsonExpr::Lambda {
            params: params.iter().map(|p| p.node.clone()).collect(),
            body: Box::new(expr_to_json(&body.node)),
        },
        Expr::Label(label) => expr_to_json(&label.body.node),
        Expr::And(l, r) => JsonExpr::And {
            left: Box::new(expr_to_json(&l.node)),
            right: Box::new(expr_to_json(&r.node)),
        },
        Expr::Or(l, r) => JsonExpr::Or {
            left: Box::new(expr_to_json(&l.node)),
            right: Box::new(expr_to_json(&r.node)),
        },
        Expr::Not(e) => JsonExpr::Not {
            operand: Box::new(expr_to_json(&e.node)),
        },
        Expr::Implies(l, r) => JsonExpr::Implies {
            left: Box::new(expr_to_json(&l.node)),
            right: Box::new(expr_to_json(&r.node)),
        },
        Expr::Equiv(l, r) => JsonExpr::Equiv {
            left: Box::new(expr_to_json(&l.node)),
            right: Box::new(expr_to_json(&r.node)),
        },
        Expr::Forall(bounds, body) => JsonExpr::Forall {
            bounds: bounds.iter().map(bound_to_json).collect(),
            body: Box::new(expr_to_json(&body.node)),
        },
        Expr::Exists(bounds, body) => JsonExpr::Exists {
            bounds: bounds.iter().map(bound_to_json).collect(),
            body: Box::new(expr_to_json(&body.node)),
        },
        Expr::Choose(bv, body) => JsonExpr::Choose {
            bound: bound_to_json(bv),
            body: Box::new(expr_to_json(&body.node)),
        },
        Expr::SetEnum(elems) => JsonExpr::SetEnum {
            elements: elems.iter().map(|e| expr_to_json(&e.node)).collect(),
        },
        Expr::SetBuilder(expr, bounds) => JsonExpr::SetBuilder {
            expr: Box::new(expr_to_json(&expr.node)),
            bounds: bounds.iter().map(bound_to_json).collect(),
        },
        Expr::SetFilter(bv, pred) => JsonExpr::SetFilter {
            bound: bound_to_json(bv),
            predicate: Box::new(expr_to_json(&pred.node)),
        },
        Expr::In(l, r) => JsonExpr::In {
            left: Box::new(expr_to_json(&l.node)),
            right: Box::new(expr_to_json(&r.node)),
        },
        Expr::NotIn(l, r) => JsonExpr::NotIn {
            left: Box::new(expr_to_json(&l.node)),
            right: Box::new(expr_to_json(&r.node)),
        },
        Expr::Subseteq(l, r) => binary_op("\\subseteq", &l.node, &r.node),
        Expr::Union(l, r) => binary_op("\\cup", &l.node, &r.node),
        Expr::Intersect(l, r) => binary_op("\\cap", &l.node, &r.node),
        Expr::SetMinus(l, r) => binary_op("\\", &l.node, &r.node),
        Expr::Powerset(e) => JsonExpr::UnaryOp {
            op: "SUBSET".to_string(),
            operand: Box::new(expr_to_json(&e.node)),
        },
        Expr::BigUnion(e) => JsonExpr::UnaryOp {
            op: "UNION".to_string(),
            operand: Box::new(expr_to_json(&e.node)),
        },
        Expr::If(c, t, e) => JsonExpr::IfThenElse {
            cond: Box::new(expr_to_json(&c.node)),
            then_: Box::new(expr_to_json(&t.node)),
            else_: Box::new(expr_to_json(&e.node)),
        },
        Expr::Let(defs, body) => JsonExpr::LetIn {
            defs: defs.iter().map(operator_to_json).collect(),
            body: Box::new(expr_to_json(&body.node)),
        },
        Expr::Prime(e) => JsonExpr::Prime {
            operand: Box::new(expr_to_json(&e.node)),
        },
        Expr::Tuple(elems) => JsonExpr::Tuple {
            elements: elems.iter().map(|e| expr_to_json(&e.node)).collect(),
        },
        Expr::Times(elems) => {
            // Cartesian product: flatten to binary_op chain
            if elems.len() == 2 {
                binary_op("\\X", &elems[0].node, &elems[1].node)
            } else {
                JsonExpr::Apply {
                    operator: Box::new(JsonExpr::OpRef {
                        name: "\\X".to_string(),
                    }),
                    args: elems.iter().map(|e| expr_to_json(&e.node)).collect(),
                }
            }
        }
        Expr::Record(fields) => JsonExpr::Record {
            fields: fields
                .iter()
                .map(|(name, val)| JsonRecordField {
                    name: name.node.clone(),
                    value: expr_to_json(&val.node),
                })
                .collect(),
        },
        Expr::RecordAccess(expr, field) => JsonExpr::BinaryOp {
            op: ".".to_string(),
            left: Box::new(expr_to_json(&expr.node)),
            right: Box::new(JsonExpr::StringLit {
                value: field.name.node.clone(),
            }),
        },
        Expr::RecordSet(fields) => JsonExpr::RecordSet {
            fields: fields
                .iter()
                .map(|(name, val)| JsonRecordField {
                    name: name.node.clone(),
                    value: expr_to_json(&val.node),
                })
                .collect(),
        },
        Expr::FuncDef(bounds, body) => JsonExpr::Function {
            bounds: bounds.iter().map(bound_to_json).collect(),
            body: Box::new(expr_to_json(&body.node)),
        },
        Expr::FuncApply(func, arg) => JsonExpr::FuncApply {
            func: Box::new(expr_to_json(&func.node)),
            arg: Box::new(expr_to_json(&arg.node)),
        },
        Expr::FuncSet(domain, range) => JsonExpr::FuncSet {
            domain: Box::new(expr_to_json(&domain.node)),
            range: Box::new(expr_to_json(&range.node)),
        },
        Expr::Domain(e) => JsonExpr::Domain {
            expr: Box::new(expr_to_json(&e.node)),
        },
        Expr::Except(base, updates) => JsonExpr::Except {
            base: Box::new(expr_to_json(&base.node)),
            updates: updates
                .iter()
                .map(|u| JsonExceptUpdate {
                    path: except_path_to_json(&u.path),
                    value: expr_to_json(&u.value.node),
                })
                .collect(),
        },
        Expr::Unchanged(e) => JsonExpr::Unchanged {
            expr: Box::new(expr_to_json(&e.node)),
        },
        Expr::Enabled(e) => JsonExpr::Enabled {
            expr: Box::new(expr_to_json(&e.node)),
        },
        Expr::Case(arms, other) => JsonExpr::Case {
            arms: arms
                .iter()
                .map(|a| JsonCaseArm {
                    guard: expr_to_json(&a.guard.node),
                    body: expr_to_json(&a.body.node),
                })
                .collect(),
            other: other.as_ref().map(|o| Box::new(expr_to_json(&o.node))),
        },
        Expr::Always(e) => JsonExpr::UnaryOp {
            op: "[]".to_string(),
            operand: Box::new(expr_to_json(&e.node)),
        },
        Expr::Eventually(e) => JsonExpr::UnaryOp {
            op: "<>".to_string(),
            operand: Box::new(expr_to_json(&e.node)),
        },
        Expr::LeadsTo(l, r) => binary_op("~>", &l.node, &r.node),
        Expr::WeakFair(vars, action) => JsonExpr::BinaryOp {
            op: "WF".to_string(),
            left: Box::new(expr_to_json(&vars.node)),
            right: Box::new(expr_to_json(&action.node)),
        },
        Expr::StrongFair(vars, action) => JsonExpr::BinaryOp {
            op: "SF".to_string(),
            left: Box::new(expr_to_json(&vars.node)),
            right: Box::new(expr_to_json(&action.node)),
        },
        // Comparison operators
        Expr::Eq(l, r) => binary_op("=", &l.node, &r.node),
        Expr::Neq(l, r) => binary_op("/=", &l.node, &r.node),
        Expr::Lt(l, r) => binary_op("<", &l.node, &r.node),
        Expr::Leq(l, r) => binary_op("<=", &l.node, &r.node),
        Expr::Gt(l, r) => binary_op(">", &l.node, &r.node),
        Expr::Geq(l, r) => binary_op(">=", &l.node, &r.node),
        // Arithmetic operators
        Expr::Add(l, r) => binary_op("+", &l.node, &r.node),
        Expr::Sub(l, r) => binary_op("-", &l.node, &r.node),
        Expr::Mul(l, r) => binary_op("*", &l.node, &r.node),
        Expr::Div(l, r) => binary_op("/", &l.node, &r.node),
        Expr::IntDiv(l, r) => binary_op("\\div", &l.node, &r.node),
        Expr::Mod(l, r) => binary_op("%", &l.node, &r.node),
        Expr::Pow(l, r) => binary_op("^", &l.node, &r.node),
        Expr::Neg(e) => JsonExpr::UnaryOp {
            op: "-".to_string(),
            operand: Box::new(expr_to_json(&e.node)),
        },
        Expr::Range(l, r) => binary_op("..", &l.node, &r.node),
        // Fallback for expressions without explicit handling
        _ => JsonExpr::Other {
            description: format!("{expr:?}"),
        },
    }
}

// ---------------------------------------------------------------------------
// Helpers: JSON -> TLA+ pretty-printing
// ---------------------------------------------------------------------------

fn json_module_to_tla(module: &JsonModule) -> String {
    let mut out = String::new();
    let sep = "-".repeat(4);

    out.push_str(&format!("{sep} MODULE {} {sep}\n", module.name));

    if !module.extends.is_empty() {
        out.push_str(&format!("EXTENDS {}\n", module.extends.join(", ")));
    }

    if !module.constants.is_empty() {
        let names: Vec<&str> = module.constants.iter().map(|c| c.name.as_str()).collect();
        out.push_str(&format!("\nCONSTANT {}\n", names.join(", ")));
    }

    if !module.variables.is_empty() {
        out.push_str(&format!("\nVARIABLE {}\n", module.variables.join(", ")));
    }

    for assume in &module.assumes {
        if let Some(name) = &assume.name {
            out.push_str(&format!(
                "\nASSUME {} == {}\n",
                name,
                json_expr_to_tla(&assume.expr)
            ));
        } else {
            out.push_str(&format!("\nASSUME {}\n", json_expr_to_tla(&assume.expr)));
        }
    }

    for inst in &module.instances {
        let local_prefix = if inst.local { "LOCAL " } else { "" };
        out.push_str(&format!("\n{local_prefix}INSTANCE {}", inst.module));
        if !inst.substitutions.is_empty() {
            let subs: Vec<String> = inst
                .substitutions
                .iter()
                .map(|s| format!("{} <- {}", s.from, json_expr_to_tla(&s.to)))
                .collect();
            out.push_str(&format!(" WITH {}", subs.join(", ")));
        }
        out.push('\n');
    }

    for op in &module.operators {
        let local_prefix = if op.local { "LOCAL " } else { "" };
        let params_str = if op.params.is_empty() {
            String::new()
        } else {
            let ps: Vec<&str> = op.params.iter().map(|p| p.name.as_str()).collect();
            format!("({})", ps.join(", "))
        };
        out.push_str(&format!(
            "\n{local_prefix}{}{params_str} ==\n  {}\n",
            op.name,
            json_expr_to_tla(&op.body)
        ));
    }

    out.push_str("\n====\n");
    out
}

fn json_expr_to_tla(expr: &JsonExpr) -> String {
    match expr {
        JsonExpr::Bool { value } => {
            if *value {
                "TRUE".to_string()
            } else {
                "FALSE".to_string()
            }
        }
        JsonExpr::Int { value } => value.clone(),
        JsonExpr::StringLit { value } => format!("\"{value}\""),
        JsonExpr::Ident { name } => name.clone(),
        JsonExpr::Apply { operator, args } => {
            let op_str = json_expr_to_tla(operator);
            if args.is_empty() {
                op_str
            } else {
                let arg_strs: Vec<String> = args.iter().map(json_expr_to_tla).collect();
                format!("{op_str}({})", arg_strs.join(", "))
            }
        }
        JsonExpr::And { left, right } => {
            format!(
                "({} /\\ {})",
                json_expr_to_tla(left),
                json_expr_to_tla(right)
            )
        }
        JsonExpr::Or { left, right } => {
            format!(
                "({} \\/ {})",
                json_expr_to_tla(left),
                json_expr_to_tla(right)
            )
        }
        JsonExpr::Not { operand } => format!("~({})", json_expr_to_tla(operand)),
        JsonExpr::Implies { left, right } => {
            format!(
                "({} => {})",
                json_expr_to_tla(left),
                json_expr_to_tla(right)
            )
        }
        JsonExpr::Equiv { left, right } => {
            format!(
                "({} <=> {})",
                json_expr_to_tla(left),
                json_expr_to_tla(right)
            )
        }
        JsonExpr::Forall { bounds, body } => {
            format!("\\A {} : {}", format_bounds(bounds), json_expr_to_tla(body))
        }
        JsonExpr::Exists { bounds, body } => {
            format!("\\E {} : {}", format_bounds(bounds), json_expr_to_tla(body))
        }
        JsonExpr::Choose { bound, body } => {
            format!(
                "CHOOSE {} : {}",
                format_single_bound(bound),
                json_expr_to_tla(body)
            )
        }
        JsonExpr::SetEnum { elements } => {
            let elems: Vec<String> = elements.iter().map(json_expr_to_tla).collect();
            format!("{{{}}}", elems.join(", "))
        }
        JsonExpr::SetBuilder { expr, bounds } => {
            format!(
                "{{{} : {}}}",
                json_expr_to_tla(expr),
                format_bounds(bounds)
            )
        }
        JsonExpr::SetFilter { bound, predicate } => {
            format!(
                "{{{} : {}}}",
                format_single_bound(bound),
                json_expr_to_tla(predicate)
            )
        }
        JsonExpr::In { left, right } => {
            format!(
                "({} \\in {})",
                json_expr_to_tla(left),
                json_expr_to_tla(right)
            )
        }
        JsonExpr::NotIn { left, right } => {
            format!(
                "({} \\notin {})",
                json_expr_to_tla(left),
                json_expr_to_tla(right)
            )
        }
        JsonExpr::IfThenElse { cond, then_, else_ } => {
            format!(
                "IF {} THEN {} ELSE {}",
                json_expr_to_tla(cond),
                json_expr_to_tla(then_),
                json_expr_to_tla(else_)
            )
        }
        JsonExpr::LetIn { defs, body } => {
            let mut s = "LET ".to_string();
            for def in defs {
                let params_str = if def.params.is_empty() {
                    String::new()
                } else {
                    let ps: Vec<&str> = def.params.iter().map(|p| p.name.as_str()).collect();
                    format!("({})", ps.join(", "))
                };
                s.push_str(&format!(
                    "{}{params_str} == {} ",
                    def.name,
                    json_expr_to_tla(&def.body)
                ));
            }
            s.push_str(&format!("IN {}", json_expr_to_tla(body)));
            s
        }
        JsonExpr::Prime { operand } => format!("{}'", json_expr_to_tla(operand)),
        JsonExpr::Tuple { elements } => {
            let elems: Vec<String> = elements.iter().map(json_expr_to_tla).collect();
            format!("<<{}>>", elems.join(", "))
        }
        JsonExpr::Record { fields } => {
            let fs: Vec<String> = fields
                .iter()
                .map(|f| format!("{} |-> {}", f.name, json_expr_to_tla(&f.value)))
                .collect();
            format!("[{}]", fs.join(", "))
        }
        JsonExpr::RecordSet { fields } => {
            let fs: Vec<String> = fields
                .iter()
                .map(|f| format!("{}: {}", f.name, json_expr_to_tla(&f.value)))
                .collect();
            format!("[{}]", fs.join(", "))
        }
        JsonExpr::Function { bounds, body } => {
            format!(
                "[{} |-> {}]",
                format_bounds(bounds),
                json_expr_to_tla(body)
            )
        }
        JsonExpr::FuncApply { func, arg } => {
            format!("{}[{}]", json_expr_to_tla(func), json_expr_to_tla(arg))
        }
        JsonExpr::FuncSet { domain, range } => {
            format!(
                "[{} -> {}]",
                json_expr_to_tla(domain),
                json_expr_to_tla(range)
            )
        }
        JsonExpr::Domain { expr } => format!("DOMAIN {}", json_expr_to_tla(expr)),
        JsonExpr::Except { base, updates } => {
            let upd_strs: Vec<String> = updates
                .iter()
                .map(|u| {
                    let path_strs: Vec<String> = u
                        .path
                        .iter()
                        .map(|p| format!("[{}]", json_expr_to_tla(p)))
                        .collect();
                    format!("!{} = {}", path_strs.join(""), json_expr_to_tla(&u.value))
                })
                .collect();
            format!(
                "[{} EXCEPT {}]",
                json_expr_to_tla(base),
                upd_strs.join(", ")
            )
        }
        JsonExpr::Lambda { params, body } => {
            format!("LAMBDA {} : {}", params.join(", "), json_expr_to_tla(body))
        }
        JsonExpr::Unchanged { expr } => format!("UNCHANGED {}", json_expr_to_tla(expr)),
        JsonExpr::Enabled { expr } => format!("ENABLED {}", json_expr_to_tla(expr)),
        JsonExpr::Case { arms, other } => {
            let mut s = "CASE ".to_string();
            for (i, arm) in arms.iter().enumerate() {
                if i > 0 {
                    s.push_str(" [] ");
                }
                s.push_str(&format!(
                    "{} -> {}",
                    json_expr_to_tla(&arm.guard),
                    json_expr_to_tla(&arm.body)
                ));
            }
            if let Some(o) = other {
                s.push_str(&format!(" [] OTHER -> {}", json_expr_to_tla(o)));
            }
            s
        }
        JsonExpr::ModuleRef {
            module, name, args, ..
        } => {
            if args.is_empty() {
                format!("{module}!{name}")
            } else {
                let arg_strs: Vec<String> = args.iter().map(json_expr_to_tla).collect();
                format!("{module}!{name}({})", arg_strs.join(", "))
            }
        }
        JsonExpr::OpRef { name } => name.clone(),
        JsonExpr::BinaryOp { op, left, right } => {
            format!(
                "({} {op} {})",
                json_expr_to_tla(left),
                json_expr_to_tla(right)
            )
        }
        JsonExpr::UnaryOp { op, operand } => {
            format!("{op} {}", json_expr_to_tla(operand))
        }
        JsonExpr::Other { description } => format!("(* {description} *)"),
    }
}

fn format_bounds(bounds: &[JsonBound]) -> String {
    let parts: Vec<String> = bounds.iter().map(format_single_bound).collect();
    parts.join(", ")
}

fn format_single_bound(b: &JsonBound) -> String {
    if let Some(domain) = &b.domain {
        format!("{} \\in {}", b.name, json_expr_to_tla(domain))
    } else {
        b.name.clone()
    }
}

// ---------------------------------------------------------------------------
// Helpers: header comment extraction
// ---------------------------------------------------------------------------

fn extract_header_comment(source: &str) -> String {
    let mut lines = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("----") && trimmed.contains("MODULE") {
            break;
        }
        // Skip empty lines at the very beginning.
        if lines.is_empty() && trimmed.is_empty() {
            continue;
        }
        // TLA+ line comments start with \*
        let cleaned = if let Some(rest) = trimmed.strip_prefix("\\*") {
            rest.trim().to_string()
        } else {
            trimmed.to_string()
        };
        lines.push(cleaned);
    }
    // Trim trailing empty lines.
    while lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    lines.join("\n")
}

// ---------------------------------------------------------------------------
// Helpers: trace table formatting
// ---------------------------------------------------------------------------

fn collect_trace_variable_names(states: &[StateInfo]) -> Vec<String> {
    let mut seen = HashMap::new();
    let mut order = Vec::new();
    for state in states {
        for key in state.variables.keys() {
            if !seen.contains_key(key) {
                seen.insert(key.clone(), order.len());
                order.push(key.clone());
            }
        }
    }
    order.sort();
    order
}

fn format_trace_table(states: &[StateInfo], var_names: &[String]) -> String {
    // Compute column widths.
    let step_header = "Step";
    let action_header = "Action";

    let mut col_widths: Vec<usize> = var_names.iter().map(|n| n.len()).collect();
    let mut step_width = step_header.len();
    let mut action_width = action_header.len();

    // Pre-compute cell values for each (state, var).
    let mut cell_values: Vec<Vec<String>> = Vec::with_capacity(states.len());
    for state in states {
        let step_str = state.index.to_string();
        step_width = step_width.max(step_str.len());

        let action_str = &state.action.name;
        action_width = action_width.max(action_str.len());

        let row: Vec<String> = var_names
            .iter()
            .enumerate()
            .map(|(i, name)| {
                let val_str = state
                    .variables
                    .get(name)
                    .map(|v| format!("{v:?}"))
                    .unwrap_or_else(|| "-".to_string());
                col_widths[i] = col_widths[i].max(val_str.len());
                val_str
            })
            .collect();
        cell_values.push(row);
    }

    let mut out = String::new();

    // Header row.
    out.push_str(&format!("| {:<step_width$} ", step_header));
    out.push_str(&format!("| {:<action_width$} ", action_header));
    for (i, name) in var_names.iter().enumerate() {
        out.push_str(&format!("| {:<width$} ", name, width = col_widths[i]));
    }
    out.push_str("|\n");

    // Separator row.
    out.push_str(&format!("|-{}-", "-".repeat(step_width)));
    out.push_str(&format!("|-{}-", "-".repeat(action_width)));
    for w in &col_widths {
        out.push_str(&format!("|-{}-", "-".repeat(*w)));
    }
    out.push_str("|\n");

    // Data rows.
    for (state_idx, state) in states.iter().enumerate() {
        out.push_str(&format!("| {:<step_width$} ", state.index));
        out.push_str(&format!("| {:<action_width$} ", state.action.name));
        for (i, val) in cell_values[state_idx].iter().enumerate() {
            out.push_str(&format!("| {:<width$} ", val, width = col_widths[i]));
        }
        out.push_str("|\n");
    }

    out
}

// ---------------------------------------------------------------------------
// Helpers: output writing
// ---------------------------------------------------------------------------

fn write_output(path: Option<&Path>, data: &[u8]) -> Result<()> {
    match path {
        Some(p) => {
            std::fs::write(p, data)
                .with_context(|| format!("Failed to write output to {}", p.display()))?;
            eprintln!("Wrote output to {}", p.display());
        }
        None => {
            std::io::stdout()
                .lock()
                .write_all(data)
                .context("Failed to write to stdout")?;
        }
    }
    Ok(())
}
