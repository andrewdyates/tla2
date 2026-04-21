// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 symmetry` — symmetry set analysis for TLA+ specifications.
//!
//! Analyzes a TLA+ spec and its config to detect which CONSTANT sets are used
//! symmetrically (no ordering, no distinguished elements), and suggests
//! SYMMETRY declarations that can reduce the state space.
//!
//! Symmetry reduction identifies states that differ only by a permutation of a
//! model-value set, reducing the explored state space by up to |S|! (factorial).
//!
//! # Detected symmetry-breaking patterns
//!
//! - **Ordering comparisons** (`<`, `>`, `<=`, `>=`) on set elements
//! - **Distinguished elements** — equality test against a specific model value
//! - **Asymmetric initial states** — different values for different elements
//! - **Arithmetic on elements** — model values are unordered atoms
//! - **Sequence indexing** — using set elements as sequence/tuple indices
//! - **CHOOSE** — deterministically selects an element, breaking symmetry

use std::collections::{HashMap, HashSet};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{BoundVar, ExceptPathElement, Expr, Module, ModuleTarget, OperatorDef, Unit};
use tla_core::span::Span;
use tla_core::{lower_main_module, parse, parse_error_diagnostic, FileId, SyntaxNode};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Output format for the symmetry analysis command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SymmetryOutputFormat {
    Human,
    Json,
}

/// Entry point for `tla2 symmetry`.
pub(crate) fn cmd_symmetry(
    file: &Path,
    config: Option<&Path>,
    format: SymmetryOutputFormat,
) -> Result<()> {
    let source = read_source(file)?;
    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diag = parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diag.eprint(&file_path, &source);
        }
        bail!("symmetry analysis aborted: {} parse error(s)", parse_result.errors.len());
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file.file_stem().and_then(|s| s.to_str()).filter(|s| !s.is_empty());
    let lower_result = lower_main_module(FileId(0), &tree, hint_name);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diag = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diag.eprint(&file_path, &source);
        }
        bail!("symmetry analysis aborted: {} lowering error(s)", lower_result.errors.len());
    }
    let module = lower_result.module.context("symmetry: lowering produced no module")?;

    let cfg = load_config(file, config);
    let candidates = identify_candidate_sets(&cfg);

    if candidates.is_empty() {
        return emit_no_candidates(file, format);
    }

    let all_ops = collect_operators(&module);
    let results: Vec<SetAnalysisResult> = candidates
        .iter()
        .map(|c| analyze_set(&module, &all_ops, c, &cfg))
        .collect();

    let file_path = file.display().to_string();
    match format {
        SymmetryOutputFormat::Human => print_human(&file_path, &source, &results, &cfg),
        SymmetryOutputFormat::Json => print_json(&file_path, &results)?,
    }
    Ok(())
}

fn emit_no_candidates(file: &Path, format: SymmetryOutputFormat) -> Result<()> {
    match format {
        SymmetryOutputFormat::Human => {
            println!("No model-value constant sets found in the configuration.");
            println!("Symmetry reduction requires sets like: CONSTANT Procs = {{p1, p2, p3}}");
        }
        SymmetryOutputFormat::Json => {
            let output = serde_json::json!({
                "file": file.display().to_string(),
                "candidates": [],
                "suggestion": null,
                "summary": { "total_candidates": 0, "symmetric": 0, "broken": 0 }
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct CandidateSet {
    name: String,
    elements: Vec<String>,
}

#[derive(Debug, Clone)]
struct SetAnalysisResult {
    candidate: CandidateSet,
    is_symmetric: bool,
    violations: Vec<SymmetryViolation>,
    reduction_factor: u64,
}

#[derive(Debug, Clone)]
struct SymmetryViolation {
    kind: ViolationKind,
    message: String,
    span: Span,
    operator: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum ViolationKind {
    OrderingComparison,
    DistinguishedElement,
    AsymmetricInit,
    ArithmeticOnElements,
    SequenceIndexing,
    ChooseOnElements,
    ElementAsFieldName,
}

impl ViolationKind {
    fn description(self) -> &'static str {
        match self {
            Self::OrderingComparison => "ordering comparison on set elements",
            Self::DistinguishedElement => "distinguished element (equality with specific value)",
            Self::AsymmetricInit => "asymmetric initial state assignment",
            Self::ArithmeticOnElements => "arithmetic on model values",
            Self::SequenceIndexing => "sequence/tuple indexing with model values",
            Self::ChooseOnElements => "CHOOSE may select a distinguished element",
            Self::ElementAsFieldName => "model value used as record field name",
        }
    }

    fn fix_suggestion(self) -> &'static str {
        match self {
            Self::OrderingComparison => "Remove ordering comparisons (<, >, <=, >=) on elements",
            Self::DistinguishedElement => "Replace equality tests against specific elements with universal quantification",
            Self::AsymmetricInit => "Use a symmetric initial state (same value for all elements)",
            Self::ArithmeticOnElements => "Model values are unordered atoms; arithmetic is meaningless",
            Self::SequenceIndexing => "Avoid using set elements as sequence/tuple indices",
            Self::ChooseOnElements => "CHOOSE deterministically selects an element; consider \\E instead",
            Self::ElementAsFieldName => "Use functions [x \\in S |-> ...] instead of element-named record fields",
        }
    }
}

#[derive(Default)]
struct ConfigInfo {
    init: Option<String>,
    next: Option<String>,
    invariants: Vec<String>,
    properties: Vec<String>,
    constants: HashMap<String, ConstantInfo>,
    existing_symmetry: Option<String>,
}

#[derive(Debug, Clone)]
enum ConstantInfo {
    ModelValueSet(Vec<String>),
    Other,
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
        return ConfigInfo {
            init: Some("Init".into()),
            next: Some("Next".into()),
            ..Default::default()
        };
    }

    let source = match std::fs::read_to_string(&config_path_buf) {
        Ok(s) => s,
        Err(_) => return ConfigInfo::default(),
    };

    match tla_check::Config::parse(&source) {
        Ok(config) => {
            let mut constants = HashMap::new();
            for (name, value) in &config.constants {
                let info = match value {
                    tla_check::ConstantValue::ModelValueSet(vs) => {
                        ConstantInfo::ModelValueSet(vs.clone())
                    }
                    _ => ConstantInfo::Other,
                };
                constants.insert(name.clone(), info);
            }
            ConfigInfo {
                init: config.init.clone(),
                next: config.next.clone(),
                invariants: config.invariants.clone(),
                properties: config.properties.clone(),
                constants,
                existing_symmetry: config.symmetry.clone(),
            }
        }
        Err(_) => ConfigInfo {
            init: Some("Init".into()),
            next: Some("Next".into()),
            ..Default::default()
        },
    }
}

// ---------------------------------------------------------------------------
// Candidate identification
// ---------------------------------------------------------------------------

fn identify_candidate_sets(cfg: &ConfigInfo) -> Vec<CandidateSet> {
    let mut candidates: Vec<CandidateSet> = cfg
        .constants
        .iter()
        .filter_map(|(name, info)| match info {
            ConstantInfo::ModelValueSet(elements) if elements.len() >= 2 => {
                Some(CandidateSet {
                    name: name.clone(),
                    elements: elements.clone(),
                })
            }
            _ => None,
        })
        .collect();
    candidates.sort_by(|a, b| a.name.cmp(&b.name));
    candidates
}

fn collect_operators(module: &Module) -> HashMap<String, OperatorDef> {
    module
        .units
        .iter()
        .filter_map(|unit| match &unit.node {
            Unit::Operator(op) => Some((op.name.node.clone(), op.clone())),
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Symmetry analysis
// ---------------------------------------------------------------------------

fn analyze_set(
    _module: &Module,
    all_ops: &HashMap<String, OperatorDef>,
    candidate: &CandidateSet,
    cfg: &ConfigInfo,
) -> SetAnalysisResult {
    let element_names: HashSet<&str> = candidate.elements.iter().map(|s| s.as_str()).collect();
    let mut violations = Vec::new();
    let reachable_ops = compute_reachable_ops(cfg, all_ops);

    for op_name in &reachable_ops {
        if let Some(op) = all_ops.get(op_name) {
            analyze_expr(
                &op.body.node,
                &candidate.name,
                &element_names,
                &op.name.node,
                all_ops,
                &mut violations,
                &mut HashSet::new(),
            );
        }
    }

    // Check for asymmetric initial state.
    let init_name = cfg.init.as_deref().unwrap_or("Init");
    if let Some(init_op) = all_ops.get(init_name) {
        check_asymmetric_init(
            &init_op.body.node,
            &candidate.name,
            &element_names,
            init_name,
            all_ops,
            &mut violations,
        );
    }

    // Deduplicate by (kind, operator, span).
    violations.sort_by(|a, b| {
        a.operator
            .cmp(&b.operator)
            .then(a.span.start.cmp(&b.span.start))
            .then((a.kind as u8).cmp(&(b.kind as u8)))
    });
    violations.dedup_by(|a, b| a.operator == b.operator && a.span == b.span && a.kind == b.kind);

    SetAnalysisResult {
        candidate: candidate.clone(),
        is_symmetric: violations.is_empty(),
        violations,
        reduction_factor: factorial(candidate.elements.len() as u64),
    }
}

fn compute_reachable_ops(
    cfg: &ConfigInfo,
    all_ops: &HashMap<String, OperatorDef>,
) -> HashSet<String> {
    let mut roots: Vec<String> = Vec::new();
    if let Some(init) = &cfg.init {
        roots.push(init.clone());
    }
    if let Some(next) = &cfg.next {
        roots.push(next.clone());
    }
    roots.extend(cfg.invariants.iter().cloned());
    roots.extend(cfg.properties.iter().cloned());

    if roots.is_empty() {
        return all_ops.keys().cloned().collect();
    }

    let mut reachable = HashSet::new();
    while let Some(name) = roots.pop() {
        if !reachable.insert(name.clone()) {
            continue;
        }
        if let Some(op) = all_ops.get(&name) {
            for r in collect_ident_refs(&op.body.node) {
                if all_ops.contains_key(&r) && !reachable.contains(&r) {
                    roots.push(r);
                }
            }
        }
    }
    reachable
}

/// Analyze an expression tree for symmetry-breaking patterns.
fn analyze_expr(
    expr: &Expr,
    set_name: &str,
    element_names: &HashSet<&str>,
    current_op: &str,
    all_ops: &HashMap<String, OperatorDef>,
    violations: &mut Vec<SymmetryViolation>,
    visited: &mut HashSet<String>,
) {
    match expr {
        // Ordering comparisons break symmetry.
        Expr::Lt(l, r) | Expr::Leq(l, r) | Expr::Gt(l, r) | Expr::Geq(l, r) => {
            if refs_set(&l.node, set_name, element_names)
                || refs_set(&r.node, set_name, element_names)
            {
                violations.push(SymmetryViolation {
                    kind: ViolationKind::OrderingComparison,
                    message: format!("ordering comparison on elements of `{set_name}`"),
                    span: span_union(&l.span, &r.span),
                    operator: current_op.to_string(),
                });
            }
            recurse_children(expr, set_name, element_names, current_op, all_ops, violations, visited);
        }

        // Equality/inequality: check for distinguished elements.
        Expr::Eq(l, r) | Expr::Neq(l, r) => {
            let l_elem = specific_element(&l.node, element_names);
            let r_elem = specific_element(&r.node, element_names);
            if l_elem.is_some() != r_elem.is_some() {
                let elem = l_elem.or(r_elem).expect("one must be Some");
                violations.push(SymmetryViolation {
                    kind: ViolationKind::DistinguishedElement,
                    message: format!(
                        "equality test with specific element `{elem}` of `{set_name}`"
                    ),
                    span: span_union(&l.span, &r.span),
                    operator: current_op.to_string(),
                });
            }
            recurse_children(expr, set_name, element_names, current_op, all_ops, violations, visited);
        }

        // Arithmetic on model values.
        Expr::Add(l, r) | Expr::Sub(l, r) | Expr::Mul(l, r) | Expr::Div(l, r)
        | Expr::IntDiv(l, r) | Expr::Mod(l, r) | Expr::Pow(l, r) => {
            if refs_set(&l.node, set_name, element_names)
                || refs_set(&r.node, set_name, element_names)
            {
                violations.push(SymmetryViolation {
                    kind: ViolationKind::ArithmeticOnElements,
                    message: format!("arithmetic on elements of `{set_name}`"),
                    span: span_union(&l.span, &r.span),
                    operator: current_op.to_string(),
                });
            }
            recurse_children(expr, set_name, element_names, current_op, all_ops, violations, visited);
        }

        // CHOOSE on set elements.
        Expr::Choose(bv, _body) => {
            if bv_ranges_over_set(bv, set_name, element_names) {
                violations.push(SymmetryViolation {
                    kind: ViolationKind::ChooseOnElements,
                    message: format!(
                        "CHOOSE over elements of `{set_name}` selects a distinguished element"
                    ),
                    span: bv.name.span,
                    operator: current_op.to_string(),
                });
            }
            recurse_children(expr, set_name, element_names, current_op, all_ops, violations, visited);
        }

        // Sequence indexing with model values.
        Expr::FuncApply(func, arg) => {
            if refs_set(&arg.node, set_name, element_names) && is_likely_sequence(&func.node) {
                violations.push(SymmetryViolation {
                    kind: ViolationKind::SequenceIndexing,
                    message: format!("element of `{set_name}` used as a sequence index"),
                    span: span_union(&func.span, &arg.span),
                    operator: current_op.to_string(),
                });
            }
            recurse_children(expr, set_name, element_names, current_op, all_ops, violations, visited);
        }

        // Follow operator references transitively.
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if all_ops.contains_key(name.as_str()) && visited.insert(name.clone()) {
                if let Some(op) = all_ops.get(name.as_str()) {
                    analyze_expr(
                        &op.body.node, set_name, element_names, &op.name.node,
                        all_ops, violations, visited,
                    );
                }
            }
        }

        Expr::Apply(func, _args) => {
            if let Expr::Ident(name, _) = &func.node {
                if all_ops.contains_key(name.as_str()) && visited.insert(name.clone()) {
                    if let Some(op) = all_ops.get(name.as_str()) {
                        analyze_expr(
                            &op.body.node, set_name, element_names, &op.name.node,
                            all_ops, violations, visited,
                        );
                    }
                }
            }
            recurse_children(expr, set_name, element_names, current_op, all_ops, violations, visited);
        }

        _ => recurse_children(expr, set_name, element_names, current_op, all_ops, violations, visited),
    }
}

/// Helper to recurse into all children of an expression.
fn recurse_children(
    expr: &Expr,
    set_name: &str,
    element_names: &HashSet<&str>,
    current_op: &str,
    all_ops: &HashMap<String, OperatorDef>,
    violations: &mut Vec<SymmetryViolation>,
    visited: &mut HashSet<String>,
) {
    visit_expr_children(expr, |child| {
        analyze_expr(child, set_name, element_names, current_op, all_ops, violations, visited);
    });
}

/// Check Init for asymmetric patterns (record fields named after elements).
fn check_asymmetric_init(
    expr: &Expr,
    set_name: &str,
    element_names: &HashSet<&str>,
    current_op: &str,
    all_ops: &HashMap<String, OperatorDef>,
    violations: &mut Vec<SymmetryViolation>,
) {
    match expr {
        Expr::Record(fields) => {
            let elem_fields: Vec<_> = fields
                .iter()
                .filter(|(n, _)| element_names.contains(n.node.as_str()))
                .collect();
            if elem_fields.len() >= 2 {
                let first_val = &elem_fields[0].1.node;
                if !elem_fields
                    .iter()
                    .all(|(_, v)| expr_eq_shallow(&v.node, first_val))
                {
                    violations.push(SymmetryViolation {
                        kind: ViolationKind::AsymmetricInit,
                        message: format!(
                            "elements of `{set_name}` have different initial values"
                        ),
                        span: fields
                            .first()
                            .map(|(n, _)| n.span)
                            .unwrap_or_default(),
                        operator: current_op.to_string(),
                    });
                }
            }
            for (name, _) in fields {
                if element_names.contains(name.node.as_str()) {
                    violations.push(SymmetryViolation {
                        kind: ViolationKind::ElementAsFieldName,
                        message: format!(
                            "element `{}` of `{set_name}` used as record field",
                            name.node
                        ),
                        span: name.span,
                        operator: current_op.to_string(),
                    });
                }
            }
        }
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if let Some(op) = all_ops.get(name.as_str()) {
                check_asymmetric_init(
                    &op.body.node, set_name, element_names, &op.name.node,
                    all_ops, violations,
                );
            }
        }
        _ => visit_expr_children(expr, |child| {
            check_asymmetric_init(
                child, set_name, element_names, current_op, all_ops, violations,
            );
        }),
    }
}

// ---------------------------------------------------------------------------
// Expression analysis helpers
// ---------------------------------------------------------------------------

fn refs_set(expr: &Expr, set_name: &str, element_names: &HashSet<&str>) -> bool {
    match expr {
        Expr::Ident(n, _) | Expr::StateVar(n, _, _) => {
            element_names.contains(n.as_str()) || n == set_name
        }
        _ => {
            let mut found = false;
            visit_expr_children(expr, |child| {
                if !found {
                    found = refs_set(child, set_name, element_names);
                }
            });
            found
        }
    }
}

fn specific_element<'a>(expr: &'a Expr, element_names: &HashSet<&str>) -> Option<&'a str> {
    match expr {
        Expr::Ident(n, _) | Expr::StateVar(n, _, _) if element_names.contains(n.as_str()) => {
            Some(n.as_str())
        }
        _ => None,
    }
}

fn bv_ranges_over_set(bv: &BoundVar, set_name: &str, element_names: &HashSet<&str>) -> bool {
    bv.domain.as_ref().map_or(false, |d| match &d.node {
        Expr::Ident(n, _) | Expr::StateVar(n, _, _) => {
            n == set_name || element_names.contains(n.as_str())
        }
        _ => false,
    })
}

fn is_likely_sequence(expr: &Expr) -> bool {
    match expr {
        Expr::Tuple(_) => true,
        Expr::Ident(n, _) => {
            let l = n.to_lowercase();
            l.contains("seq") || l.contains("log") || l.contains("queue") || l.contains("stack")
        }
        _ => false,
    }
}

fn expr_eq_shallow(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Bool(x), Expr::Bool(y)) => x == y,
        (Expr::Int(x), Expr::Int(y)) => x == y,
        (Expr::String(x), Expr::String(y)) => x == y,
        (Expr::Ident(x, _), Expr::Ident(y, _)) => x == y,
        _ => false,
    }
}

fn collect_ident_refs(expr: &Expr) -> HashSet<String> {
    let mut refs = HashSet::new();
    collect_ident_refs_inner(expr, &mut refs);
    refs
}

fn collect_ident_refs_inner(expr: &Expr, refs: &mut HashSet<String>) {
    match expr {
        Expr::Ident(n, _) | Expr::StateVar(n, _, _) => {
            refs.insert(n.clone());
        }
        Expr::Apply(func, args) => {
            collect_ident_refs_inner(&func.node, refs);
            for arg in args {
                collect_ident_refs_inner(&arg.node, refs);
            }
        }
        _ => visit_expr_children(expr, |child| collect_ident_refs_inner(child, refs)),
    }
}

fn span_union(a: &Span, b: &Span) -> Span {
    Span {
        file: a.file,
        start: a.start.min(b.start),
        end: a.end.max(b.end),
    }
}

fn factorial(n: u64) -> u64 {
    (2..=n).fold(1u64, |acc, i| acc.saturating_mul(i))
}

// ---------------------------------------------------------------------------
// Expression visitor — covers all Expr variants
// ---------------------------------------------------------------------------

fn visit_expr_children(expr: &Expr, mut f: impl FnMut(&Expr)) {
    match expr {
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _) | Expr::OpRef(_) | Expr::InstanceExpr(_, _) => {}

        Expr::Not(e) | Expr::Prime(e) | Expr::Always(e) | Expr::Eventually(e)
        | Expr::Enabled(e) | Expr::Unchanged(e) | Expr::Powerset(e)
        | Expr::BigUnion(e) | Expr::Domain(e) | Expr::Neg(e) => f(&e.node),

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

        Expr::Apply(func, args) => {
            f(&func.node);
            for a in args {
                f(&a.node);
            }
        }
        Expr::Lambda(_, body) => f(&body.node),
        Expr::Label(label) => f(&label.body.node),

        Expr::ModuleRef(target, _, args) => {
            match target {
                ModuleTarget::Parameterized(_, params) => {
                    for p in params {
                        f(&p.node);
                    }
                }
                ModuleTarget::Chained(base) => f(&base.node),
                ModuleTarget::Named(_) => {}
            }
            for a in args {
                f(&a.node);
            }
        }

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

        Expr::SetEnum(es) | Expr::Tuple(es) | Expr::Times(es) => {
            for e in es {
                f(&e.node);
            }
        }
        Expr::SetBuilder(body, bvs) | Expr::FuncDef(bvs, body) => {
            for bv in bvs {
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

        Expr::Record(fs) | Expr::RecordSet(fs) => {
            for (_, v) in fs {
                f(&v.node);
            }
        }
        Expr::RecordAccess(base, _) => f(&base.node),

        Expr::Except(base, specs) => {
            f(&base.node);
            for s in specs {
                f(&s.value.node);
                for p in &s.path {
                    if let ExceptPathElement::Index(i) = p {
                        f(&i.node);
                    }
                }
            }
        }

        Expr::If(c, t, e) => {
            f(&c.node);
            f(&t.node);
            f(&e.node);
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
            for d in defs {
                f(&d.body.node);
            }
            f(&body.node);
        }
        Expr::SubstIn(_, body) => f(&body.node),
    }
}

// ---------------------------------------------------------------------------
// Span -> line/column
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
    let off = offset as usize;
    let idx = match starts.binary_search(&off) {
        Ok(i) => i,
        Err(i) => i.saturating_sub(1),
    };
    (idx + 1, off.saturating_sub(starts[idx]) + 1)
}

// ---------------------------------------------------------------------------
// Human output
// ---------------------------------------------------------------------------

fn print_human(
    file_path: &str,
    source: &str,
    results: &[SetAnalysisResult],
    cfg: &ConfigInfo,
) {
    let starts = line_starts(source);
    println!("Symmetry Analysis: {file_path}");
    println!("{}", "=".repeat(60));

    if let Some(existing) = &cfg.existing_symmetry {
        println!("\n\x1b[36minfo\x1b[0m: existing SYMMETRY declaration: {existing}");
    }

    let mut symmetric = Vec::new();
    for result in results {
        let elems = result.candidate.elements.join(", ");
        println!();
        if result.is_symmetric {
            println!(
                "\x1b[32mSYMMETRIC\x1b[0m: {} = {{{}}}  (reduction: {}x)",
                result.candidate.name, elems, result.reduction_factor
            );
            println!("  No symmetry-breaking patterns detected.");
            symmetric.push(result);
        } else {
            println!(
                "\x1b[33mNOT SYMMETRIC\x1b[0m: {} = {{{}}}  ({} violation{})",
                result.candidate.name,
                elems,
                result.violations.len(),
                if result.violations.len() == 1 { "" } else { "s" }
            );
            for v in &result.violations {
                let (line, col) = offset_to_line_col(v.span.start, &starts);
                println!(
                    "  \x1b[33mwarning\x1b[0m[{}]: {}",
                    v.kind.description(),
                    v.message
                );
                println!("    --> {file_path}:{line}:{col} (in `{}`)", v.operator);
            }
        }
    }

    let broken_count = results.len() - symmetric.len();
    println!(
        "\n{}\nSummary: {} candidate{}, {} symmetric, {} with violations",
        "-".repeat(60),
        results.len(),
        if results.len() == 1 { "" } else { "s" },
        symmetric.len(),
        broken_count
    );

    if !symmetric.is_empty() {
        let perms: Vec<String> = symmetric
            .iter()
            .map(|r| format!("Permutations({})", r.candidate.name))
            .collect();
        let def = perms.join(" \\cup ");
        let total: u64 = symmetric
            .iter()
            .map(|r| r.reduction_factor)
            .fold(1, |a, f| a.saturating_mul(f));
        println!("\nSuggested SYMMETRY declaration:");
        println!("  \\* .tla: Symmetry == {def}");
        println!("  \\* .cfg: SYMMETRY Symmetry");
        println!("  Estimated reduction: up to {total}x");
    }

    if broken_count > 0 {
        println!("\nFixes to enable symmetry:");
        for r in results.iter().filter(|r| !r.is_symmetric) {
            let kinds: HashSet<ViolationKind> = r.violations.iter().map(|v| v.kind).collect();
            println!("  {}:", r.candidate.name);
            for k in &kinds {
                println!("    - {}", k.fix_suggestion());
            }
        }
    }
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

fn print_json(file_path: &str, results: &[SetAnalysisResult]) -> Result<()> {
    let candidates: Vec<serde_json::Value> = results
        .iter()
        .map(|r| {
            let violations: Vec<serde_json::Value> = r
                .violations
                .iter()
                .map(|v| {
                    serde_json::json!({
                        "kind": v.kind,
                        "message": v.message,
                        "operator": v.operator,
                        "span": { "start": v.span.start, "end": v.span.end },
                    })
                })
                .collect();
            serde_json::json!({
                "name": r.candidate.name,
                "elements": r.candidate.elements,
                "element_count": r.candidate.elements.len(),
                "is_symmetric": r.is_symmetric,
                "reduction_factor": r.reduction_factor,
                "violations": violations,
                "violation_count": r.violations.len(),
            })
        })
        .collect();

    let sym_count = results.iter().filter(|r| r.is_symmetric).count();
    let suggestion = if sym_count > 0 {
        let names: Vec<&str> = results
            .iter()
            .filter(|r| r.is_symmetric)
            .map(|r| r.candidate.name.as_str())
            .collect();
        let perms: Vec<String> = names.iter().map(|n| format!("Permutations({n})")).collect();
        let total: u64 = results
            .iter()
            .filter(|r| r.is_symmetric)
            .map(|r| r.reduction_factor)
            .fold(1, |a, f| a.saturating_mul(f));
        Some(serde_json::json!({
            "tla_definition": format!("Symmetry == {}", perms.join(" \\cup ")),
            "cfg_line": "SYMMETRY Symmetry",
            "symmetric_sets": names,
            "estimated_reduction": total,
        }))
    } else {
        None
    };

    let output = serde_json::json!({
        "file": file_path,
        "candidates": candidates,
        "suggestion": suggestion,
        "summary": {
            "total_candidates": results.len(),
            "symmetric": sym_count,
            "broken": results.len() - sym_count,
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

    fn parse_module(source: &str) -> Module {
        let result = parse(source);
        assert!(result.errors.is_empty(), "parse errors: {:?}", result.errors);
        let tree = SyntaxNode::new_root(result.green_node);
        let lr = lower_main_module(FileId(0), &tree, None);
        assert!(lr.errors.is_empty(), "lower errors: {:?}", lr.errors);
        lr.module.expect("no module")
    }

    fn candidate(name: &str, elems: &[&str]) -> CandidateSet {
        CandidateSet {
            name: name.into(),
            elements: elems.iter().map(|s| s.to_string()).collect(),
        }
    }

    fn cfg_with(name: &str, elems: &[&str]) -> ConfigInfo {
        let mut constants = HashMap::new();
        constants.insert(
            name.into(),
            ConstantInfo::ModelValueSet(elems.iter().map(|s| s.to_string()).collect()),
        );
        ConfigInfo {
            init: Some("Init".into()),
            next: Some("Next".into()),
            constants,
            ..Default::default()
        }
    }

    #[test]
    fn test_factorial() {
        assert_eq!(factorial(0), 1);
        assert_eq!(factorial(1), 1);
        assert_eq!(factorial(5), 120);
        assert_eq!(factorial(10), 3_628_800);
        assert_eq!(factorial(25), u64::MAX);
    }

    #[test]
    fn test_identify_candidates() {
        let cfg = cfg_with("Procs", &["p1", "p2", "p3"]);
        let cs = identify_candidate_sets(&cfg);
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].name, "Procs");
    }

    #[test]
    fn test_excludes_small_sets() {
        let mut constants = HashMap::new();
        constants.insert("S".into(), ConstantInfo::ModelValueSet(vec!["s1".into()]));
        let cfg = ConfigInfo { constants, ..Default::default() };
        assert!(identify_candidate_sets(&cfg).is_empty());
    }

    #[test]
    fn test_symmetric_spec() {
        let m = parse_module(
            r#"---- MODULE T ----
CONSTANT Procs
VARIABLE status
Init == status = [p \in Procs |-> "idle"]
Next == \E p \in Procs : status' = [status EXCEPT ![p] = "active"]
===="#,
        );
        let cfg = cfg_with("Procs", &["p1", "p2", "p3"]);
        let ops = collect_operators(&m);
        let r = analyze_set(&m, &ops, &candidate("Procs", &["p1", "p2", "p3"]), &cfg);
        assert!(r.is_symmetric, "violations: {:?}", r.violations);
        assert_eq!(r.reduction_factor, 6);
    }

    #[test]
    fn test_ordering_breaks_symmetry() {
        let m = parse_module(
            r#"---- MODULE T ----
CONSTANT Procs
VARIABLE x
Init == x = [p \in Procs |-> 0]
Next == \E p \in Procs, q \in Procs : p < q /\ x' = x
===="#,
        );
        let cfg = cfg_with("Procs", &["p1", "p2", "p3"]);
        let ops = collect_operators(&m);
        let r = analyze_set(&m, &ops, &candidate("Procs", &["p1", "p2", "p3"]), &cfg);
        assert!(!r.is_symmetric);
        assert!(r.violations.iter().any(|v| v.kind == ViolationKind::OrderingComparison));
    }

    #[test]
    fn test_distinguished_element_breaks_symmetry() {
        let m = parse_module(
            r#"---- MODULE T ----
CONSTANT Procs
VARIABLE status
Init == status = [p \in Procs |-> "idle"]
Next == \E p \in Procs :
    IF p = p1
    THEN status' = [status EXCEPT ![p] = "leader"]
    ELSE status' = [status EXCEPT ![p] = "follower"]
===="#,
        );
        let cfg = cfg_with("Procs", &["p1", "p2", "p3"]);
        let ops = collect_operators(&m);
        let r = analyze_set(&m, &ops, &candidate("Procs", &["p1", "p2", "p3"]), &cfg);
        assert!(!r.is_symmetric);
        assert!(r.violations.iter().any(|v| v.kind == ViolationKind::DistinguishedElement));
    }

    #[test]
    fn test_choose_breaks_symmetry() {
        let m = parse_module(
            r#"---- MODULE T ----
CONSTANT Procs
VARIABLE leader
Init == leader = CHOOSE p \in Procs : TRUE
Next == leader' = leader
===="#,
        );
        let cfg = cfg_with("Procs", &["p1", "p2", "p3"]);
        let ops = collect_operators(&m);
        let r = analyze_set(&m, &ops, &candidate("Procs", &["p1", "p2", "p3"]), &cfg);
        assert!(!r.is_symmetric);
        assert!(r.violations.iter().any(|v| v.kind == ViolationKind::ChooseOnElements));
    }

    #[test]
    fn test_arithmetic_breaks_symmetry() {
        let m = parse_module(
            r#"---- MODULE T ----
CONSTANT Procs
VARIABLE x
Init == x = 0
Next == \E p \in Procs : x' = x + p
===="#,
        );
        let cfg = cfg_with("Procs", &["p1", "p2", "p3"]);
        let ops = collect_operators(&m);
        let r = analyze_set(&m, &ops, &candidate("Procs", &["p1", "p2", "p3"]), &cfg);
        assert!(!r.is_symmetric);
        assert!(r.violations.iter().any(|v| v.kind == ViolationKind::ArithmeticOnElements));
    }

    #[test]
    fn test_multiple_independent_sets() {
        let m = parse_module(
            r#"---- MODULE T ----
CONSTANT Procs, Vals
VARIABLE s, d
Init == s = [p \in Procs |-> "idle"] /\ d = [v \in Vals |-> 0]
Next == \E p \in Procs, v \in Vals :
    /\ s' = [s EXCEPT ![p] = "active"]
    /\ d' = [d EXCEPT ![v] = 1]
===="#,
        );
        let mut constants = HashMap::new();
        constants.insert(
            "Procs".into(),
            ConstantInfo::ModelValueSet(vec!["p1".into(), "p2".into()]),
        );
        constants.insert(
            "Vals".into(),
            ConstantInfo::ModelValueSet(vec!["v1".into(), "v2".into(), "v3".into()]),
        );
        let cfg = ConfigInfo {
            init: Some("Init".into()),
            next: Some("Next".into()),
            constants,
            ..Default::default()
        };
        let ops = collect_operators(&m);
        for c in identify_candidate_sets(&cfg) {
            let r = analyze_set(&m, &ops, &c, &cfg);
            assert!(r.is_symmetric, "{} had violations: {:?}", c.name, r.violations);
        }
    }

    #[test]
    fn test_expr_eq_shallow_basic() {
        assert!(expr_eq_shallow(&Expr::Bool(true), &Expr::Bool(true)));
        assert!(!expr_eq_shallow(&Expr::Bool(true), &Expr::Bool(false)));
        assert!(expr_eq_shallow(
            &Expr::String("a".into()),
            &Expr::String("a".into())
        ));
        assert!(!expr_eq_shallow(
            &Expr::String("a".into()),
            &Expr::String("b".into())
        ));
    }
}
