// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 doc` -- auto-generate documentation from TLA+ specifications.
//!
//! Parses a TLA+ spec to AST, extracts structural information and comments,
//! builds a cross-reference graph, and emits documentation in Markdown, HTML,
//! or JSON format.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::Write;
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{Expr, Module, Unit};
use tla_core::{lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId};

use crate::cli_schema::DocOutputFormat;
use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_doc(
    file: &Path,
    config_path: Option<&Path>,
    format: DocOutputFormat,
    output: Option<&Path>,
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
        bail!("doc aborted: {} parse error(s)", parse_result.errors.len());
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
            "doc aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("doc: lowering produced no module")?;

    // Load config info for entry-point marking
    let cfg_info = load_config_info(file, config_path);

    // Extract documentation model
    let doc = extract_doc_model(&module, &source, &cfg_info);

    // Render
    let rendered = match format {
        DocOutputFormat::Markdown => render_markdown(&doc),
        DocOutputFormat::Html => render_html(&doc),
        DocOutputFormat::Json => render_json(&doc)?,
    };

    // Write output
    if let Some(path) = output {
        std::fs::write(path, &rendered)
            .with_context(|| format!("write output to {}", path.display()))?;
    } else {
        let stdout = std::io::stdout();
        let mut out = stdout.lock();
        out.write_all(rendered.as_bytes())
            .context("write to stdout")?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Config loading (best-effort, for entry-point identification)
// ---------------------------------------------------------------------------

#[derive(Default)]
struct ConfigInfo {
    init: Option<String>,
    next: Option<String>,
    invariants: Vec<String>,
    properties: Vec<String>,
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
        },
        Err(_) => ConfigInfo::default(),
    }
}

// ---------------------------------------------------------------------------
// Documentation model
// ---------------------------------------------------------------------------

/// The full documentation model for a module.
struct DocModel {
    module_name: String,
    module_comment: String,
    extends: Vec<String>,
    instances: Vec<InstanceInfo>,
    constants: Vec<DeclInfo>,
    variables: Vec<DeclInfo>,
    operators: Vec<OperatorInfo>,
    theorems: Vec<TheoremInfo>,
    /// Which operators are config entry points (Init, Next, invariants, properties).
    entry_points: HashMap<String, EntryPointKind>,
    /// Cross-reference: operator name -> set of operator names it calls.
    calls: BTreeMap<String, Vec<String>>,
    /// Cross-reference: operator name -> set of operator names that call it.
    called_by: BTreeMap<String, Vec<String>>,
}

#[derive(Clone)]
struct InstanceInfo {
    module: String,
    local: bool,
}

#[derive(Clone)]
struct DeclInfo {
    name: String,
    comment: String,
}

struct OperatorInfo {
    name: String,
    params: Vec<String>,
    comment: String,
    local: bool,
    is_recursive: bool,
}

struct TheoremInfo {
    name: String,
    comment: String,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EntryPointKind {
    Init,
    Next,
    Invariant,
    Property,
}

impl std::fmt::Display for EntryPointKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EntryPointKind::Init => write!(f, "Init"),
            EntryPointKind::Next => write!(f, "Next"),
            EntryPointKind::Invariant => write!(f, "Invariant"),
            EntryPointKind::Property => write!(f, "Property"),
        }
    }
}

// ---------------------------------------------------------------------------
// Extract documentation from AST + source
// ---------------------------------------------------------------------------

fn extract_doc_model(module: &Module, source: &str, cfg: &ConfigInfo) -> DocModel {
    let source_lines: Vec<&str> = source.lines().collect();
    let line_starts = build_line_starts(source);

    // Module-level comment: lines before the MODULE header starting with \*
    let module_comment = extract_module_comment(&source_lines, module.span.start, &line_starts);

    // Build entry point map
    let mut entry_points = HashMap::new();
    if let Some(init) = &cfg.init {
        entry_points.insert(init.clone(), EntryPointKind::Init);
    }
    if let Some(next) = &cfg.next {
        entry_points.insert(next.clone(), EntryPointKind::Next);
    }
    for inv in &cfg.invariants {
        entry_points.insert(inv.clone(), EntryPointKind::Invariant);
    }
    for prop in &cfg.properties {
        entry_points.insert(prop.clone(), EntryPointKind::Property);
    }

    // Collect all operator names for cross-referencing
    let all_op_names: HashSet<String> = module
        .units
        .iter()
        .filter_map(|u| match &u.node {
            Unit::Operator(op) => Some(op.name.node.clone()),
            _ => None,
        })
        .collect();

    // Extract units
    let mut constants = Vec::new();
    let mut variables = Vec::new();
    let mut operators = Vec::new();
    let mut instances = Vec::new();
    let mut theorems = Vec::new();
    let mut calls: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut called_by: BTreeMap<String, Vec<String>> = BTreeMap::new();

    for unit in &module.units {
        let unit_line = offset_to_line(unit.span.start, &line_starts);
        let comment = extract_preceding_comment(&source_lines, unit_line);

        match &unit.node {
            Unit::Constant(decls) => {
                for (i, decl) in decls.iter().enumerate() {
                    let c = if i == 0 {
                        comment.clone()
                    } else {
                        String::new()
                    };
                    constants.push(DeclInfo {
                        name: decl.name.node.clone(),
                        comment: c,
                    });
                }
            }
            Unit::Variable(names) => {
                for (i, name) in names.iter().enumerate() {
                    let c = if i == 0 {
                        comment.clone()
                    } else {
                        String::new()
                    };
                    variables.push(DeclInfo {
                        name: name.node.clone(),
                        comment: c,
                    });
                }
            }
            Unit::Operator(op) => {
                let op_comment = extract_preceding_comment(
                    &source_lines,
                    offset_to_line(op.name.span.start, &line_starts),
                );
                let params: Vec<String> = op.params.iter().map(|p| p.name.node.clone()).collect();

                // Cross-reference: find ident references in the body
                let refs = collect_ident_refs(&op.body.node);
                let mut outgoing: Vec<String> = refs
                    .iter()
                    .filter(|r| all_op_names.contains(r.as_str()) && r.as_str() != op.name.node)
                    .cloned()
                    .collect();
                outgoing.sort();
                outgoing.dedup();

                for callee in &outgoing {
                    called_by
                        .entry(callee.clone())
                        .or_default()
                        .push(op.name.node.clone());
                }
                calls.insert(op.name.node.clone(), outgoing);

                operators.push(OperatorInfo {
                    name: op.name.node.clone(),
                    params,
                    comment: op_comment,
                    local: op.local,
                    is_recursive: op.is_recursive,
                });
            }
            Unit::Instance(inst) => {
                instances.push(InstanceInfo {
                    module: inst.module.node.clone(),
                    local: inst.local,
                });
            }
            Unit::Theorem(thm) => {
                let name = thm
                    .name
                    .as_ref()
                    .map(|n| n.node.clone())
                    .unwrap_or_else(|| "<anonymous>".to_string());
                theorems.push(TheoremInfo { name, comment });
            }
            Unit::Recursive(_) | Unit::Assume(_) | Unit::Separator => {}
        }
    }

    // Sort called_by values
    for v in called_by.values_mut() {
        v.sort();
        v.dedup();
    }

    DocModel {
        module_name: module.name.node.clone(),
        module_comment,
        extends: module.extends.iter().map(|e| e.node.clone()).collect(),
        instances,
        constants,
        variables,
        operators,
        theorems,
        entry_points,
        calls,
        called_by,
    }
}

// ---------------------------------------------------------------------------
// Comment extraction
// ---------------------------------------------------------------------------

/// Build a line-starts table from source text (byte offsets of each line start).
fn build_line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, ch) in source.char_indices() {
        if ch == '\n' {
            starts.push(i + 1);
        }
    }
    starts
}

/// Convert byte offset to 0-based line index.
fn offset_to_line(offset: u32, starts: &[usize]) -> usize {
    let offset = offset as usize;
    match starts.binary_search(&offset) {
        Ok(i) => i,
        Err(i) => i.saturating_sub(1),
    }
}

/// Extract the module-level comment: contiguous `\*` comment lines before the
/// MODULE header line.
fn extract_module_comment(
    source_lines: &[&str],
    module_start: u32,
    line_starts: &[usize],
) -> String {
    let module_line = offset_to_line(module_start, line_starts);
    extract_preceding_comment(source_lines, module_line)
}

/// Given a target line (0-based), walk backwards from the line immediately
/// before it and collect contiguous TLA+ comment lines (starting with `\*`).
/// Returns the assembled comment text with `\*` prefixes stripped.
fn extract_preceding_comment(source_lines: &[&str], target_line: usize) -> String {
    if target_line == 0 {
        return String::new();
    }

    let mut comment_lines = Vec::new();
    let mut line_idx = target_line.saturating_sub(1);

    loop {
        let line = source_lines.get(line_idx).copied().unwrap_or("");
        let trimmed = line.trim();

        if let Some(rest) = trimmed.strip_prefix("\\*") {
            comment_lines.push(rest.trim().to_string());
        } else if trimmed.starts_with("(*") && trimmed.ends_with("*)") {
            // Single-line block comment
            let inner = trimmed
                .strip_prefix("(*")
                .unwrap_or("")
                .strip_suffix("*)")
                .unwrap_or("");
            comment_lines.push(inner.trim().to_string());
        } else if !trimmed.is_empty() {
            break;
        } else {
            // Empty line breaks the comment block
            break;
        }

        if line_idx == 0 {
            break;
        }
        line_idx -= 1;
    }

    comment_lines.reverse();
    comment_lines.join("\n")
}

// ---------------------------------------------------------------------------
// Expression analysis (reused from lint)
// ---------------------------------------------------------------------------

/// Collect all identifier references in an expression.
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

/// Visit all direct child expressions of an Expr node.
/// (Same structural traversal as cmd_lint, covering every variant.)
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
// Markdown renderer
// ---------------------------------------------------------------------------

fn render_markdown(doc: &DocModel) -> String {
    let mut out = String::new();

    // Title
    out.push_str(&format!("# Module `{}`\n\n", doc.module_name));

    // Module comment
    if !doc.module_comment.is_empty() {
        out.push_str(&doc.module_comment);
        out.push_str("\n\n");
    }

    // EXTENDS
    if !doc.extends.is_empty() {
        out.push_str("## Extends\n\n");
        for ext in &doc.extends {
            out.push_str(&format!("- `{ext}`\n"));
        }
        out.push('\n');
    }

    // INSTANCE declarations
    if !doc.instances.is_empty() {
        out.push_str("## Instances\n\n");
        for inst in &doc.instances {
            let local_tag = if inst.local { " (LOCAL)" } else { "" };
            out.push_str(&format!("- `INSTANCE {}`{local_tag}\n", inst.module));
        }
        out.push('\n');
    }

    // CONSTANTS
    if !doc.constants.is_empty() {
        out.push_str("## Constants\n\n");
        out.push_str("| Name | Description |\n");
        out.push_str("|------|-------------|\n");
        for c in &doc.constants {
            let desc = if c.comment.is_empty() {
                "-".to_string()
            } else {
                c.comment.replace('\n', " ")
            };
            out.push_str(&format!("| `{}` | {} |\n", c.name, desc));
        }
        out.push('\n');
    }

    // VARIABLES
    if !doc.variables.is_empty() {
        out.push_str("## Variables\n\n");
        out.push_str("| Name | Description |\n");
        out.push_str("|------|-------------|\n");
        for v in &doc.variables {
            let desc = if v.comment.is_empty() {
                "-".to_string()
            } else {
                v.comment.replace('\n', " ")
            };
            out.push_str(&format!("| `{}` | {} |\n", v.name, desc));
        }
        out.push('\n');
    }

    // Entry Points section (if config is present)
    let entry_ops: Vec<&OperatorInfo> = doc
        .operators
        .iter()
        .filter(|op| doc.entry_points.contains_key(&op.name))
        .collect();
    if !entry_ops.is_empty() {
        out.push_str("## Entry Points\n\n");
        for op in &entry_ops {
            let kind = doc.entry_points.get(&op.name).expect("checked above");
            out.push_str(&format!("- **{}** `{}`", kind, format_signature(op)));
            out.push('\n');
        }
        out.push('\n');
    }

    // Operators
    if !doc.operators.is_empty() {
        out.push_str("## Operators\n\n");
        for op in &doc.operators {
            let mut tags = Vec::new();
            if op.local {
                tags.push("LOCAL");
            }
            if op.is_recursive {
                tags.push("RECURSIVE");
            }
            if let Some(kind) = doc.entry_points.get(&op.name) {
                tags.push(match kind {
                    EntryPointKind::Init => "INIT",
                    EntryPointKind::Next => "NEXT",
                    EntryPointKind::Invariant => "INVARIANT",
                    EntryPointKind::Property => "PROPERTY",
                });
            }

            let tag_str = if tags.is_empty() {
                String::new()
            } else {
                format!(" `[{}]`", tags.join(", "))
            };

            out.push_str(&format!("### `{}`{}\n\n", format_signature(op), tag_str));

            if !op.comment.is_empty() {
                out.push_str(&op.comment);
                out.push_str("\n\n");
            }

            // Cross-references
            if let Some(callees) = doc.calls.get(&op.name) {
                if !callees.is_empty() {
                    out.push_str(&format!(
                        "**Calls:** {}\n\n",
                        callees
                            .iter()
                            .map(|c| format!("`{c}`"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }
            }
            if let Some(callers) = doc.called_by.get(&op.name) {
                if !callers.is_empty() {
                    out.push_str(&format!(
                        "**Called by:** {}\n\n",
                        callers
                            .iter()
                            .map(|c| format!("`{c}`"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }
            }
        }
    }

    // Theorems
    if !doc.theorems.is_empty() {
        out.push_str("## Theorems\n\n");
        for thm in &doc.theorems {
            out.push_str(&format!("### `{}`\n\n", thm.name));
            if !thm.comment.is_empty() {
                out.push_str(&thm.comment);
                out.push_str("\n\n");
            }
        }
    }

    out
}

fn format_signature(op: &OperatorInfo) -> String {
    if op.params.is_empty() {
        op.name.clone()
    } else {
        format!("{}({})", op.name, op.params.join(", "))
    }
}

// ---------------------------------------------------------------------------
// HTML renderer
// ---------------------------------------------------------------------------

fn render_html(doc: &DocModel) -> String {
    let mut out = String::new();

    out.push_str("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    out.push_str("<meta charset=\"utf-8\">\n");
    out.push_str(&format!(
        "<title>Module {} - TLA+ Documentation</title>\n",
        html_escape(&doc.module_name)
    ));
    out.push_str("<style>\n");
    out.push_str(HTML_CSS);
    out.push_str("</style>\n");
    out.push_str("</head>\n<body>\n");

    // Sidebar navigation
    out.push_str("<nav class=\"sidebar\">\n");
    out.push_str(&format!("<h2>{}</h2>\n", html_escape(&doc.module_name)));
    out.push_str("<ul>\n");
    if !doc.extends.is_empty() {
        out.push_str("<li><a href=\"#extends\">Extends</a></li>\n");
    }
    if !doc.instances.is_empty() {
        out.push_str("<li><a href=\"#instances\">Instances</a></li>\n");
    }
    if !doc.constants.is_empty() {
        out.push_str("<li><a href=\"#constants\">Constants</a></li>\n");
    }
    if !doc.variables.is_empty() {
        out.push_str("<li><a href=\"#variables\">Variables</a></li>\n");
    }
    if !doc.operators.is_empty() {
        out.push_str("<li><a href=\"#operators\">Operators</a>\n<ul>\n");
        for op in &doc.operators {
            out.push_str(&format!(
                "<li><a href=\"#op-{}\">{}</a></li>\n",
                html_escape(&op.name),
                html_escape(&op.name)
            ));
        }
        out.push_str("</ul></li>\n");
    }
    if !doc.theorems.is_empty() {
        out.push_str("<li><a href=\"#theorems\">Theorems</a></li>\n");
    }
    out.push_str("</ul>\n</nav>\n");

    // Main content
    out.push_str("<main>\n");
    out.push_str(&format!(
        "<h1>Module <code>{}</code></h1>\n",
        html_escape(&doc.module_name)
    ));

    if !doc.module_comment.is_empty() {
        out.push_str(&format!(
            "<p class=\"module-comment\">{}</p>\n",
            html_escape(&doc.module_comment)
        ));
    }

    // Extends
    if !doc.extends.is_empty() {
        out.push_str("<section id=\"extends\">\n<h2>Extends</h2>\n<ul>\n");
        for ext in &doc.extends {
            out.push_str(&format!("<li><code>{}</code></li>\n", html_escape(ext)));
        }
        out.push_str("</ul>\n</section>\n");
    }

    // Instances
    if !doc.instances.is_empty() {
        out.push_str("<section id=\"instances\">\n<h2>Instances</h2>\n<ul>\n");
        for inst in &doc.instances {
            let local_tag = if inst.local {
                " <span class=\"tag\">LOCAL</span>"
            } else {
                ""
            };
            out.push_str(&format!(
                "<li><code>INSTANCE {}</code>{local_tag}</li>\n",
                html_escape(&inst.module)
            ));
        }
        out.push_str("</ul>\n</section>\n");
    }

    // Constants
    if !doc.constants.is_empty() {
        out.push_str("<section id=\"constants\">\n<h2>Constants</h2>\n");
        out.push_str(
            "<table>\n<thead><tr><th>Name</th><th>Description</th></tr></thead>\n<tbody>\n",
        );
        for c in &doc.constants {
            let desc = if c.comment.is_empty() {
                "-"
            } else {
                &c.comment
            };
            out.push_str(&format!(
                "<tr><td><code>{}</code></td><td>{}</td></tr>\n",
                html_escape(&c.name),
                html_escape(desc)
            ));
        }
        out.push_str("</tbody>\n</table>\n</section>\n");
    }

    // Variables
    if !doc.variables.is_empty() {
        out.push_str("<section id=\"variables\">\n<h2>Variables</h2>\n");
        out.push_str(
            "<table>\n<thead><tr><th>Name</th><th>Description</th></tr></thead>\n<tbody>\n",
        );
        for v in &doc.variables {
            let desc = if v.comment.is_empty() {
                "-"
            } else {
                &v.comment
            };
            out.push_str(&format!(
                "<tr><td><code>{}</code></td><td>{}</td></tr>\n",
                html_escape(&v.name),
                html_escape(desc)
            ));
        }
        out.push_str("</tbody>\n</table>\n</section>\n");
    }

    // Operators
    if !doc.operators.is_empty() {
        out.push_str("<section id=\"operators\">\n<h2>Operators</h2>\n");
        for op in &doc.operators {
            let sig = format_signature(op);
            let mut tags = Vec::new();
            if op.local {
                tags.push("LOCAL");
            }
            if op.is_recursive {
                tags.push("RECURSIVE");
            }
            if let Some(kind) = doc.entry_points.get(&op.name) {
                tags.push(match kind {
                    EntryPointKind::Init => "INIT",
                    EntryPointKind::Next => "NEXT",
                    EntryPointKind::Invariant => "INVARIANT",
                    EntryPointKind::Property => "PROPERTY",
                });
            }

            out.push_str(&format!(
                "<div class=\"operator\" id=\"op-{}\">\n",
                html_escape(&op.name)
            ));
            out.push_str(&format!("<h3><code>{}</code>", html_escape(&sig)));
            for tag in &tags {
                out.push_str(&format!(" <span class=\"tag\">{tag}</span>"));
            }
            out.push_str("</h3>\n");

            if !op.comment.is_empty() {
                out.push_str(&format!("<p>{}</p>\n", html_escape(&op.comment)));
            }

            // Cross-references
            if let Some(callees) = doc.calls.get(&op.name) {
                if !callees.is_empty() {
                    out.push_str("<p class=\"xref\"><strong>Calls:</strong> ");
                    let links: Vec<String> = callees
                        .iter()
                        .map(|c| {
                            format!("<a href=\"#op-{}\">{}</a>", html_escape(c), html_escape(c))
                        })
                        .collect();
                    out.push_str(&links.join(", "));
                    out.push_str("</p>\n");
                }
            }
            if let Some(callers) = doc.called_by.get(&op.name) {
                if !callers.is_empty() {
                    out.push_str("<p class=\"xref\"><strong>Called by:</strong> ");
                    let links: Vec<String> = callers
                        .iter()
                        .map(|c| {
                            format!("<a href=\"#op-{}\">{}</a>", html_escape(c), html_escape(c))
                        })
                        .collect();
                    out.push_str(&links.join(", "));
                    out.push_str("</p>\n");
                }
            }

            out.push_str("</div>\n");
        }
        out.push_str("</section>\n");
    }

    // Theorems
    if !doc.theorems.is_empty() {
        out.push_str("<section id=\"theorems\">\n<h2>Theorems</h2>\n");
        for thm in &doc.theorems {
            out.push_str(&format!(
                "<div class=\"theorem\">\n<h3><code>{}</code></h3>\n",
                html_escape(&thm.name)
            ));
            if !thm.comment.is_empty() {
                out.push_str(&format!("<p>{}</p>\n", html_escape(&thm.comment)));
            }
            out.push_str("</div>\n");
        }
        out.push_str("</section>\n");
    }

    out.push_str("</main>\n</body>\n</html>\n");
    out
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

const HTML_CSS: &str = r#"
:root {
    --bg: #fff;
    --fg: #1a1a1a;
    --sidebar-bg: #f5f5f5;
    --border: #ddd;
    --accent: #2563eb;
    --tag-bg: #e0e7ff;
    --tag-fg: #3730a3;
    --code-bg: #f0f0f0;
}
* { margin: 0; padding: 0; box-sizing: border-box; }
body {
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
    color: var(--fg);
    background: var(--bg);
    display: flex;
    line-height: 1.6;
}
nav.sidebar {
    width: 260px;
    min-height: 100vh;
    background: var(--sidebar-bg);
    border-right: 1px solid var(--border);
    padding: 1.5rem 1rem;
    position: fixed;
    overflow-y: auto;
    top: 0;
    left: 0;
    bottom: 0;
}
nav.sidebar h2 { font-size: 1.1rem; margin-bottom: 1rem; }
nav.sidebar ul { list-style: none; }
nav.sidebar li { margin: 0.2rem 0; }
nav.sidebar a { color: var(--accent); text-decoration: none; font-size: 0.9rem; }
nav.sidebar a:hover { text-decoration: underline; }
nav.sidebar ul ul { padding-left: 1rem; }
main {
    margin-left: 280px;
    padding: 2rem 3rem;
    max-width: 900px;
}
h1 { font-size: 1.8rem; margin-bottom: 1rem; }
h2 { font-size: 1.4rem; margin: 2rem 0 0.8rem; border-bottom: 1px solid var(--border); padding-bottom: 0.3rem; }
h3 { font-size: 1.1rem; margin: 0.5rem 0; }
code {
    background: var(--code-bg);
    padding: 0.15em 0.35em;
    border-radius: 3px;
    font-size: 0.9em;
}
table { border-collapse: collapse; margin: 0.5rem 0 1rem; width: 100%; }
th, td { border: 1px solid var(--border); padding: 0.4rem 0.7rem; text-align: left; }
th { background: var(--sidebar-bg); }
.tag {
    display: inline-block;
    background: var(--tag-bg);
    color: var(--tag-fg);
    font-size: 0.75rem;
    padding: 0.1em 0.5em;
    border-radius: 3px;
    vertical-align: middle;
    font-weight: 600;
}
.operator, .theorem { margin: 1rem 0; padding: 0.8rem 1rem; border: 1px solid var(--border); border-radius: 4px; }
.xref { font-size: 0.9rem; color: #555; margin: 0.3rem 0; }
.xref a { color: var(--accent); }
.module-comment { color: #555; margin-bottom: 1rem; white-space: pre-wrap; }
"#;

// ---------------------------------------------------------------------------
// JSON renderer
// ---------------------------------------------------------------------------

fn render_json(doc: &DocModel) -> Result<String> {
    let constants: Vec<serde_json::Value> = doc
        .constants
        .iter()
        .map(|c| {
            serde_json::json!({
                "name": c.name,
                "comment": c.comment,
            })
        })
        .collect();

    let variables: Vec<serde_json::Value> = doc
        .variables
        .iter()
        .map(|v| {
            serde_json::json!({
                "name": v.name,
                "comment": v.comment,
            })
        })
        .collect();

    let operators: Vec<serde_json::Value> = doc
        .operators
        .iter()
        .map(|op| {
            let entry_point = doc.entry_points.get(&op.name).map(|k| k.to_string());
            let calls = doc.calls.get(&op.name).cloned().unwrap_or_default();
            let called_by = doc.called_by.get(&op.name).cloned().unwrap_or_default();
            serde_json::json!({
                "name": op.name,
                "params": op.params,
                "signature": format_signature(op),
                "comment": op.comment,
                "local": op.local,
                "recursive": op.is_recursive,
                "entry_point": entry_point,
                "calls": calls,
                "called_by": called_by,
            })
        })
        .collect();

    let instances: Vec<serde_json::Value> = doc
        .instances
        .iter()
        .map(|i| {
            serde_json::json!({
                "module": i.module,
                "local": i.local,
            })
        })
        .collect();

    let theorems: Vec<serde_json::Value> = doc
        .theorems
        .iter()
        .map(|t| {
            serde_json::json!({
                "name": t.name,
                "comment": t.comment,
            })
        })
        .collect();

    let output = serde_json::json!({
        "module": doc.module_name,
        "module_comment": doc.module_comment,
        "extends": doc.extends,
        "instances": instances,
        "constants": constants,
        "variables": variables,
        "operators": operators,
        "theorems": theorems,
    });

    serde_json::to_string_pretty(&output).context("serialize documentation JSON")
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
    fn test_doc_extract_basic_module() {
        let source = r#"\* This module models a counter.
---- MODULE Counter ----
EXTENDS Naturals
CONSTANT Max
VARIABLE count

\* Initialize count to zero.
Init == count = 0

\* Increment if below max.
Next == count' = IF count < Max THEN count + 1 ELSE count

\* Type invariant
TypeOK == count \in 0..Max
===="#;
        let module = parse_module(source);
        let cfg = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["TypeOK".to_string()],
            properties: Vec::new(),
        };
        let doc = extract_doc_model(&module, source, &cfg);

        assert_eq!(doc.module_name, "Counter");
        assert_eq!(doc.module_comment, "This module models a counter.");
        assert_eq!(doc.extends, vec!["Naturals"]);
        assert_eq!(doc.constants.len(), 1);
        assert_eq!(doc.constants[0].name, "Max");
        assert_eq!(doc.variables.len(), 1);
        assert_eq!(doc.variables[0].name, "count");
        assert_eq!(doc.operators.len(), 3);
        assert!(doc.entry_points.contains_key("Init"));
        assert!(doc.entry_points.contains_key("Next"));
        assert!(doc.entry_points.contains_key("TypeOK"));
    }

    #[test]
    fn test_doc_cross_references() {
        let source = r#"---- MODULE Xref ----
VARIABLE x
Helper == x + 1
Init == x = 0
Next == x' = Helper
===="#;
        let module = parse_module(source);
        let cfg = ConfigInfo::default();
        let doc = extract_doc_model(&module, source, &cfg);

        // Next calls Helper
        let next_calls = doc.calls.get("Next").expect("Next should have calls");
        assert!(
            next_calls.contains(&"Helper".to_string()),
            "Next should call Helper: {next_calls:?}"
        );

        // Helper is called by Next
        let helper_callers = doc
            .called_by
            .get("Helper")
            .expect("Helper should have callers");
        assert!(
            helper_callers.contains(&"Next".to_string()),
            "Helper should be called by Next: {helper_callers:?}"
        );
    }

    #[test]
    fn test_doc_markdown_output_contains_sections() {
        let source = r#"---- MODULE Simple ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#;
        let module = parse_module(source);
        let cfg = ConfigInfo::default();
        let doc = extract_doc_model(&module, source, &cfg);
        let md = render_markdown(&doc);

        assert!(md.contains("# Module `Simple`"), "should have title");
        assert!(md.contains("## Variables"), "should have variables section");
        assert!(md.contains("## Operators"), "should have operators section");
        assert!(md.contains("### `Init`"), "should have Init operator");
        assert!(md.contains("### `Next`"), "should have Next operator");
    }

    #[test]
    fn test_doc_html_output_is_complete() {
        let source = r#"---- MODULE HtmlTest ----
VARIABLE x
Init == x = 0
===="#;
        let module = parse_module(source);
        let cfg = ConfigInfo::default();
        let doc = extract_doc_model(&module, source, &cfg);
        let html = render_html(&doc);

        assert!(html.contains("<!DOCTYPE html>"), "should be valid HTML");
        assert!(
            html.contains("<nav class=\"sidebar\">"),
            "should have sidebar"
        );
        assert!(html.contains("</html>"), "should close HTML");
        assert!(html.contains("HtmlTest"), "should contain module name");
    }

    #[test]
    fn test_doc_json_output_parses() {
        let source = r#"---- MODULE JsonTest ----
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#;
        let module = parse_module(source);
        let cfg = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let doc = extract_doc_model(&module, source, &cfg);
        let json_str = render_json(&doc).expect("JSON render should succeed");
        let parsed: serde_json::Value = serde_json::from_str(&json_str).expect("JSON should parse");

        assert_eq!(parsed["module"], "JsonTest");
        assert_eq!(parsed["constants"][0]["name"], "N");
        assert_eq!(parsed["variables"][0]["name"], "x");
        assert_eq!(parsed["operators"].as_array().expect("ops array").len(), 2);
        assert_eq!(
            parsed["operators"][0]["entry_point"],
            serde_json::Value::String("Init".to_string())
        );
    }

    #[test]
    fn test_doc_operator_comment_extraction() {
        let source = r#"---- MODULE Comments ----
VARIABLE x

\* This is the initial predicate.
\* It sets x to zero.
Init == x = 0

Next == x' = x + 1
===="#;
        let module = parse_module(source);
        let cfg = ConfigInfo::default();
        let doc = extract_doc_model(&module, source, &cfg);

        let init_op = doc
            .operators
            .iter()
            .find(|op| op.name == "Init")
            .expect("Init operator");
        assert!(
            init_op.comment.contains("initial predicate"),
            "should extract comment: {:?}",
            init_op.comment
        );
        assert!(
            init_op.comment.contains("sets x to zero"),
            "should extract multiline comment: {:?}",
            init_op.comment
        );
    }
}
