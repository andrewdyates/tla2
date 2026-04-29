// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 partition` -- state space partitioning analysis for TLA+ specifications.
//!
//! Analyzes a TLA+ spec to identify natural partitioning boundaries for distributed
//! or parallel model checking. Examines how the state space can be divided by
//! variable domains, action independence, and symmetry classes.
//!
//! # Strategies
//!
//! 1. **Variable-domain partitioning** -- split states by the values of a finite-domain
//!    variable (e.g., partition by `pc` values when `pc \in {"init", "ready", "done"}`).
//!
//! 2. **Action-based partitioning** -- independent actions (those touching disjoint
//!    variable sets in the Next relation) can be checked in separate partitions.
//!
//! 3. **Symmetry-class partitioning** -- when SYMMETRY is declared, the symmetric
//!    elements form natural equivalence classes that can be explored independently.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;

use anyhow::{bail, Context, Result};
use serde::Serialize;

use tla_core::ast::{Expr, Module, Unit};
use tla_core::{lower_main_module, parse, FileId, SyntaxNode};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Output format for the partition command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PartitionOutputFormat {
    Human,
    Json,
}

/// Entry point for `tla2 partition`.
pub(crate) fn cmd_partition(
    file: &Path,
    config: Option<&Path>,
    num_partitions: usize,
    format: PartitionOutputFormat,
) -> Result<()> {
    if num_partitions == 0 {
        bail!("--partitions must be >= 1");
    }

    // Parse and lower.
    let source = read_source(file)?;
    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diagnostic =
                tla_core::parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("parse failed with {} error(s)", parse_result.errors.len());
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    let cfg = load_config(file, config);
    let analysis = PartitionAnalysis::run(&module, cfg.as_ref(), num_partitions);

    match format {
        PartitionOutputFormat::Human => print_human(&analysis),
        PartitionOutputFormat::Json => print_json(&analysis)?,
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Config loading (non-fatal -- analysis works without config)
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
// Analysis types
// ---------------------------------------------------------------------------

/// Complete partition analysis result.
#[derive(Debug, Clone, Serialize)]
struct PartitionAnalysis {
    module_name: String,
    variables: Vec<String>,
    finite_domain_vars: Vec<FiniteDomainVar>,
    actions: Vec<ActionInfo>,
    coupling_groups: Vec<CouplingGroup>,
    #[serde(skip_serializing_if = "Option::is_none")]
    symmetry_info: Option<SymmetryInfo>,
    strategies: Vec<PartitionStrategy>,
    requested_partitions: usize,
}

#[derive(Debug, Clone, Serialize)]
struct FiniteDomainVar {
    name: String,
    domain_size: usize,
    domain_source: DomainSource,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    values: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "snake_case")]
enum DomainSource {
    ConfigModelValueSet,
    InitSetEnum,
    InitRange,
    InitBoolean,
}

#[derive(Debug, Clone, Serialize)]
struct ActionInfo {
    name: String,
    reads: BTreeSet<String>,
    writes: BTreeSet<String>,
    unchanged: BTreeSet<String>,
}

#[derive(Debug, Clone, Serialize)]
struct CouplingGroup {
    variables: BTreeSet<String>,
    actions: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
struct SymmetryInfo {
    symmetry_set: String,
    symmetric_constants: Vec<String>,
    element_count: usize,
}

#[derive(Debug, Clone, Serialize)]
struct PartitionStrategy {
    kind: StrategyKind,
    description: String,
    natural_partitions: usize,
    balance_score: f64,
    effectiveness: f64,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    partitions: Vec<PartitionAssignment>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "snake_case")]
enum StrategyKind {
    VariableDomain { variable: String },
    ActionIndependence,
    SymmetryClass,
    Combined { primary_variable: String },
}

#[derive(Debug, Clone, Serialize)]
struct PartitionAssignment {
    partition_id: usize,
    label: String,
    estimated_fraction: f64,
}

// ---------------------------------------------------------------------------
// Analysis engine
// ---------------------------------------------------------------------------

impl PartitionAnalysis {
    fn run(module: &Module, config: Option<&tla_check::Config>, requested: usize) -> Self {
        let variables = collect_variables(module);
        let finite_domain_vars = collect_finite_domains(module, config, &variables);
        let actions = extract_actions(module, config, &variables);
        let coupling_groups = compute_coupling_groups(&actions, &variables);
        let symmetry_info = extract_symmetry_info(config);
        let strategies = generate_strategies(
            &finite_domain_vars,
            &actions,
            &coupling_groups,
            symmetry_info.as_ref(),
            requested,
        );
        Self {
            module_name: module.name.node.clone(),
            variables,
            finite_domain_vars,
            actions,
            coupling_groups,
            symmetry_info,
            strategies,
            requested_partitions: requested,
        }
    }
}

// ---------------------------------------------------------------------------
// Variable collection
// ---------------------------------------------------------------------------

fn collect_variables(module: &Module) -> Vec<String> {
    let mut vars = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for decl in decls {
                vars.push(decl.node.clone());
            }
        }
    }
    vars
}

// ---------------------------------------------------------------------------
// Finite domain detection
// ---------------------------------------------------------------------------

fn collect_finite_domains(
    module: &Module,
    config: Option<&tla_check::Config>,
    variables: &[String],
) -> Vec<FiniteDomainVar> {
    let mut result = Vec::new();

    // Build constant -> (size, values) map from config.
    let constant_sizes: HashMap<String, (usize, Vec<String>)> = config
        .map(|c| {
            c.constants
                .iter()
                .filter_map(|(name, val)| match val {
                    tla_check::ConstantValue::ModelValueSet(vals) => {
                        Some((name.clone(), (vals.len(), vals.clone())))
                    }
                    tla_check::ConstantValue::Value(v) => v
                        .trim()
                        .parse::<i64>()
                        .ok()
                        .map(|_| (name.clone(), (1, vec![v.clone()]))),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();

    // Analyze Init predicate for variable domains.
    let init_name = config.and_then(|c| c.init.as_deref()).unwrap_or("Init");
    if let Some(init_def) = find_operator(module, init_name) {
        let init_domains = extract_domains_from_expr(&init_def.body.node, variables);
        for (var_name, domain_info) in &init_domains {
            let fdv = match domain_info {
                DomainInfo::SetEnum(values) => FiniteDomainVar {
                    name: var_name.clone(),
                    domain_size: values.len(),
                    domain_source: DomainSource::InitSetEnum,
                    values: values.clone(),
                },
                DomainInfo::Range(lo, hi) => {
                    let size = (*hi - *lo + 1).max(0) as usize;
                    FiniteDomainVar {
                        name: var_name.clone(),
                        domain_size: size,
                        domain_source: DomainSource::InitRange,
                        values: (*lo..=*hi).map(|i| i.to_string()).collect(),
                    }
                }
                DomainInfo::Boolean => FiniteDomainVar {
                    name: var_name.clone(),
                    domain_size: 2,
                    domain_source: DomainSource::InitBoolean,
                    values: vec!["TRUE".to_string(), "FALSE".to_string()],
                },
                DomainInfo::ConstantRef(const_name) => {
                    if let Some((size, vals)) = constant_sizes.get(const_name.as_str()) {
                        FiniteDomainVar {
                            name: var_name.clone(),
                            domain_size: *size,
                            domain_source: DomainSource::ConfigModelValueSet,
                            values: vals.clone(),
                        }
                    } else {
                        continue;
                    }
                }
                DomainInfo::Unknown => continue,
            };
            result.push(fdv);
        }
    }

    // Check config constants directly for model value sets assigned to variables.
    if let Some(cfg) = config {
        let already: HashSet<String> = result.iter().map(|f| f.name.clone()).collect();
        for (name, val) in &cfg.constants {
            if variables.contains(name) && !already.contains(name.as_str()) {
                if let tla_check::ConstantValue::ModelValueSet(vals) = val {
                    result.push(FiniteDomainVar {
                        name: name.clone(),
                        domain_size: vals.len(),
                        domain_source: DomainSource::ConfigModelValueSet,
                        values: vals.clone(),
                    });
                }
            }
        }
    }

    result.sort_by(|a, b| b.domain_size.cmp(&a.domain_size).then(a.name.cmp(&b.name)));
    result
}

#[derive(Debug)]
enum DomainInfo {
    SetEnum(Vec<String>),
    Range(i64, i64),
    Boolean,
    ConstantRef(String),
    Unknown,
}

fn extract_domains_from_expr(expr: &Expr, variables: &[String]) -> Vec<(String, DomainInfo)> {
    let var_set: HashSet<&str> = variables.iter().map(|s| s.as_str()).collect();
    let mut domains = Vec::new();
    collect_domains_recursive(expr, &var_set, &mut domains);
    domains
}

fn collect_domains_recursive(
    expr: &Expr,
    variables: &HashSet<&str>,
    domains: &mut Vec<(String, DomainInfo)>,
) {
    match expr {
        Expr::In(lhs, rhs) => {
            if let Some(var_name) = extract_var_name(&lhs.node, variables) {
                domains.push((var_name, classify_domain(&rhs.node)));
            }
        }
        Expr::Eq(lhs, rhs) => {
            if let Some(var_name) = extract_var_name(&lhs.node, variables) {
                let domain = match &rhs.node {
                    Expr::Bool(_) => DomainInfo::Boolean,
                    Expr::Int(n) => DomainInfo::SetEnum(vec![n.to_string()]),
                    Expr::String(s) => DomainInfo::SetEnum(vec![s.clone()]),
                    _ => DomainInfo::Unknown,
                };
                domains.push((var_name, domain));
            }
        }
        Expr::And(lhs, rhs) => {
            collect_domains_recursive(&lhs.node, variables, domains);
            collect_domains_recursive(&rhs.node, variables, domains);
        }
        Expr::Let(_, body) => collect_domains_recursive(&body.node, variables, domains),
        Expr::Label(label) => collect_domains_recursive(&label.body.node, variables, domains),
        _ => {}
    }
}

fn classify_domain(expr: &Expr) -> DomainInfo {
    match expr {
        Expr::SetEnum(elems) => DomainInfo::SetEnum(
            elems
                .iter()
                .map(|e| tla_core::pretty_expr(&e.node))
                .collect(),
        ),
        Expr::Range(lo, hi) => match (try_extract_int(&lo.node), try_extract_int(&hi.node)) {
            (Some(l), Some(h)) => DomainInfo::Range(l, h),
            _ => DomainInfo::Unknown,
        },
        Expr::Ident(name, _) if name == "BOOLEAN" => DomainInfo::Boolean,
        Expr::Ident(name, _) => DomainInfo::ConstantRef(name.clone()),
        _ => DomainInfo::Unknown,
    }
}

fn extract_var_name(expr: &Expr, variables: &HashSet<&str>) -> Option<String> {
    match expr {
        Expr::Ident(name, _) if variables.contains(name.as_str()) => Some(name.clone()),
        Expr::StateVar(name, _, _) => Some(name.clone()),
        _ => None,
    }
}

fn try_extract_int(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Int(n) => n.try_into().ok(),
        Expr::Neg(inner) => {
            if let Expr::Int(n) = &inner.node {
                n.try_into().ok().map(|v: i64| -v)
            } else {
                None
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Action extraction
// ---------------------------------------------------------------------------

fn extract_actions(
    module: &Module,
    config: Option<&tla_check::Config>,
    variables: &[String],
) -> Vec<ActionInfo> {
    let next_name = config.and_then(|c| c.next.as_deref()).unwrap_or("Next");
    let next_def = match find_operator(module, next_name) {
        Some(def) => def,
        None => return Vec::new(),
    };
    let var_set: HashSet<&str> = variables.iter().map(|s| s.as_str()).collect();
    let disjuncts = decompose_disjunction(&next_def.body.node);

    disjuncts
        .iter()
        .enumerate()
        .map(|(idx, disjunct)| {
            let name = identify_action_name(disjunct, module)
                .unwrap_or_else(|| format!("Disjunct_{}", idx + 1));
            let mut reads = BTreeSet::new();
            let mut writes = BTreeSet::new();
            let mut unchanged = BTreeSet::new();
            collect_var_access(
                disjunct,
                &var_set,
                module,
                &mut reads,
                &mut writes,
                &mut unchanged,
            );
            ActionInfo {
                name,
                reads,
                writes,
                unchanged,
            }
        })
        .collect()
}

fn decompose_disjunction(expr: &Expr) -> Vec<&Expr> {
    let mut disjuncts = Vec::new();
    collect_disjuncts(expr, &mut disjuncts);
    disjuncts
}

fn collect_disjuncts<'a>(expr: &'a Expr, result: &mut Vec<&'a Expr>) {
    match expr {
        Expr::Or(lhs, rhs) => {
            collect_disjuncts(&lhs.node, result);
            collect_disjuncts(&rhs.node, result);
        }
        Expr::Label(label) => collect_disjuncts(&label.body.node, result),
        other => result.push(other),
    }
}

fn identify_action_name(expr: &Expr, module: &Module) -> Option<String> {
    match expr {
        Expr::Apply(op, _) => {
            if let Expr::Ident(name, _) = &op.node {
                if find_operator(module, name).is_some() {
                    return Some(name.clone());
                }
            }
            None
        }
        Expr::Ident(name, _) if find_operator(module, name).is_some() => Some(name.clone()),
        Expr::Exists(_, body) => identify_action_name(&body.node, module),
        Expr::And(lhs, _) => identify_action_name(&lhs.node, module),
        Expr::Label(label) => identify_action_name(&label.body.node, module),
        _ => None,
    }
}

/// Collect variable access (reads, writes, unchanged) from an expression.
/// Follows operator definitions one level deep to capture access patterns.
fn collect_var_access(
    expr: &Expr,
    variables: &HashSet<&str>,
    module: &Module,
    reads: &mut BTreeSet<String>,
    writes: &mut BTreeSet<String>,
    unchanged: &mut BTreeSet<String>,
) {
    let recurse = |e: &tla_core::Spanned<Expr>,
                   r: &mut BTreeSet<String>,
                   w: &mut BTreeSet<String>,
                   u: &mut BTreeSet<String>| {
        collect_var_access(&e.node, variables, module, r, w, u);
    };

    match expr {
        Expr::StateVar(name, _, _) => {
            reads.insert(name.clone());
        }
        Expr::Ident(name, _) if variables.contains(name.as_str()) => {
            reads.insert(name.clone());
        }
        Expr::Prime(inner) => match &inner.node {
            Expr::StateVar(name, _, _) | Expr::Ident(name, _)
                if variables.contains(name.as_str()) =>
            {
                writes.insert(name.clone());
            }
            _ => recurse(inner, reads, writes, unchanged),
        },
        Expr::Unchanged(inner) => collect_unchanged_vars(&inner.node, variables, unchanged),
        Expr::Apply(op, args) => {
            for arg in args {
                recurse(arg, reads, writes, unchanged);
            }
            if let Expr::Ident(name, _) = &op.node {
                if let Some(def) = find_operator(module, name) {
                    collect_var_access(&def.body.node, variables, module, reads, writes, unchanged);
                    return;
                }
            }
            recurse(op, reads, writes, unchanged);
        }
        // Binary operators
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
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
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Range(a, b)
        | Expr::FuncSet(a, b)
        | Expr::FuncApply(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
        | Expr::LeadsTo(a, b) => {
            recurse(a, reads, writes, unchanged);
            recurse(b, reads, writes, unchanged);
        }
        // Unary operators
        Expr::Not(x)
        | Expr::Neg(x)
        | Expr::Domain(x)
        | Expr::Powerset(x)
        | Expr::BigUnion(x)
        | Expr::Enabled(x)
        | Expr::Always(x)
        | Expr::Eventually(x) => {
            recurse(x, reads, writes, unchanged);
        }
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bv in bounds {
                if let Some(dom) = &bv.domain {
                    recurse(dom, reads, writes, unchanged);
                }
            }
            recurse(body, reads, writes, unchanged);
        }
        Expr::Choose(bv, body) => {
            if let Some(dom) = &bv.domain {
                recurse(dom, reads, writes, unchanged);
            }
            recurse(body, reads, writes, unchanged);
        }
        Expr::If(c, t, e) => {
            recurse(c, reads, writes, unchanged);
            recurse(t, reads, writes, unchanged);
            recurse(e, reads, writes, unchanged);
        }
        Expr::Case(arms, other) => {
            for arm in arms {
                recurse(&arm.guard, reads, writes, unchanged);
                recurse(&arm.body, reads, writes, unchanged);
            }
            if let Some(o) = other {
                recurse(o, reads, writes, unchanged);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                collect_var_access(&def.body.node, variables, module, reads, writes, unchanged);
            }
            recurse(body, reads, writes, unchanged);
        }
        Expr::SetEnum(es) | Expr::Tuple(es) | Expr::Times(es) => {
            for e in es {
                recurse(e, reads, writes, unchanged);
            }
        }
        Expr::SetBuilder(e, bounds) | Expr::FuncDef(bounds, e) => {
            for bv in bounds {
                if let Some(dom) = &bv.domain {
                    recurse(dom, reads, writes, unchanged);
                }
            }
            recurse(e, reads, writes, unchanged);
        }
        Expr::SetFilter(bv, body) => {
            if let Some(dom) = &bv.domain {
                recurse(dom, reads, writes, unchanged);
            }
            recurse(body, reads, writes, unchanged);
        }
        Expr::Except(base, specs) => {
            recurse(base, reads, writes, unchanged);
            for spec in specs {
                for elem in &spec.path {
                    if let tla_core::ast::ExceptPathElement::Index(idx) = elem {
                        recurse(idx, reads, writes, unchanged);
                    }
                }
                recurse(&spec.value, reads, writes, unchanged);
            }
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, v) in fields {
                recurse(v, reads, writes, unchanged);
            }
        }
        Expr::RecordAccess(base, _) => recurse(base, reads, writes, unchanged),
        Expr::Label(label) => recurse(&label.body, reads, writes, unchanged),
        Expr::SubstIn(_, body) | Expr::Lambda(_, body) => recurse(body, reads, writes, unchanged),
        Expr::ModuleRef(..)
        | Expr::InstanceExpr(..)
        | Expr::OpRef(..)
        | Expr::Bool(..)
        | Expr::Int(..)
        | Expr::String(..)
        | Expr::Ident(..) => {}
    }
}

fn collect_unchanged_vars(
    expr: &Expr,
    variables: &HashSet<&str>,
    unchanged: &mut BTreeSet<String>,
) {
    match expr {
        Expr::StateVar(name, _, _) | Expr::Ident(name, _) if variables.contains(name.as_str()) => {
            unchanged.insert(name.clone());
        }
        Expr::Tuple(elems) => {
            for e in elems {
                collect_unchanged_vars(&e.node, variables, unchanged);
            }
        }
        _ => {}
    }
}

fn find_operator<'a>(module: &'a Module, name: &str) -> Option<&'a tla_core::ast::OperatorDef> {
    module.units.iter().find_map(|u| {
        if let Unit::Operator(def) = &u.node {
            if def.name.node == name {
                return Some(def);
            }
        }
        None
    })
}

// ---------------------------------------------------------------------------
// Coupling analysis (union-find)
// ---------------------------------------------------------------------------

fn compute_coupling_groups(actions: &[ActionInfo], variables: &[String]) -> Vec<CouplingGroup> {
    if variables.is_empty() || actions.is_empty() {
        return Vec::new();
    }

    let var_idx: HashMap<&str, usize> = variables
        .iter()
        .enumerate()
        .map(|(i, v)| (v.as_str(), i))
        .collect();
    let n = variables.len();
    let mut parent: Vec<usize> = (0..n).collect();
    let mut rank = vec![0usize; n];

    let find = |parent: &mut Vec<usize>, mut x: usize| -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    };
    let union = |parent: &mut Vec<usize>, rank: &mut Vec<usize>, a: usize, b: usize| {
        let (ra, rb) = (find(parent, a), find(parent, b));
        if ra == rb {
            return;
        }
        if rank[ra] < rank[rb] {
            parent[ra] = rb;
        } else {
            if rank[ra] == rank[rb] {
                rank[ra] += 1;
            }
            parent[rb] = ra;
        }
    };

    for action in actions {
        let indices: Vec<usize> = action
            .reads
            .iter()
            .chain(action.writes.iter())
            .chain(action.unchanged.iter())
            .filter_map(|v| var_idx.get(v.as_str()).copied())
            .collect();
        for pair in indices.windows(2) {
            union(&mut parent, &mut rank, pair[0], pair[1]);
        }
    }

    let mut components: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    for (i, var) in variables.iter().enumerate() {
        components
            .entry(find(&mut parent, i))
            .or_default()
            .insert(var.clone());
    }

    components
        .into_values()
        .map(|vars| {
            let touching: Vec<String> = actions
                .iter()
                .filter(|a| {
                    a.reads
                        .iter()
                        .chain(a.writes.iter())
                        .chain(a.unchanged.iter())
                        .any(|v| vars.contains(v))
                })
                .map(|a| a.name.clone())
                .collect();
            CouplingGroup {
                variables: vars,
                actions: touching,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Symmetry extraction
// ---------------------------------------------------------------------------

fn extract_symmetry_info(config: Option<&tla_check::Config>) -> Option<SymmetryInfo> {
    let cfg = config?;
    let symmetry_set = cfg.symmetry.as_ref()?;

    let mut symmetric_constants = Vec::new();
    let mut element_count = 0;
    for (name, val) in &cfg.constants {
        if let tla_check::ConstantValue::ModelValueSet(vals) = val {
            symmetric_constants.push(name.clone());
            element_count = element_count.max(vals.len());
        }
    }

    Some(SymmetryInfo {
        symmetry_set: symmetry_set.clone(),
        symmetric_constants,
        element_count,
    })
}

// ---------------------------------------------------------------------------
// Strategy generation
// ---------------------------------------------------------------------------

fn generate_strategies(
    fdvars: &[FiniteDomainVar],
    actions: &[ActionInfo],
    groups: &[CouplingGroup],
    sym: Option<&SymmetryInfo>,
    requested: usize,
) -> Vec<PartitionStrategy> {
    let mut strategies = Vec::new();

    // Strategy 1: Variable-domain partitioning.
    for fdv in fdvars {
        if fdv.domain_size < 2 {
            continue;
        }
        let balance = compute_balance(fdv.domain_size, requested);
        let effectiveness = compute_variable_effectiveness(fdv, actions);
        strategies.push(PartitionStrategy {
            kind: StrategyKind::VariableDomain {
                variable: fdv.name.clone(),
            },
            description: format!(
                "Partition by `{}` ({} values from {})",
                fdv.name,
                fdv.domain_size,
                format_domain_source(&fdv.domain_source)
            ),
            natural_partitions: fdv.domain_size,
            balance_score: balance,
            effectiveness,
            partitions: build_variable_partitions(fdv, requested),
        });
    }

    // Strategy 2: Action independence.
    if groups.len() > 1 {
        let balance = compute_coupling_balance(groups);
        let eff = if groups.len() >= requested {
            0.8
        } else {
            0.4 * (groups.len() as f64 / requested as f64)
        };
        strategies.push(PartitionStrategy {
            kind: StrategyKind::ActionIndependence,
            description: format!(
                "{} independent variable groups -- actions on different groups \
                can be checked separately",
                groups.len()
            ),
            natural_partitions: groups.len(),
            balance_score: balance,
            effectiveness: eff,
            partitions: build_action_partitions(groups, requested),
        });
    }

    // Strategy 3: Symmetry-class partitioning.
    if let Some(s) = sym {
        if s.element_count >= 2 {
            let balance = compute_balance(s.element_count, requested);
            strategies.push(PartitionStrategy {
                kind: StrategyKind::SymmetryClass,
                description: format!(
                    "Partition by symmetry class `{}` ({} elements)",
                    s.symmetry_set, s.element_count
                ),
                natural_partitions: s.element_count,
                balance_score: balance,
                effectiveness: 0.9 * balance,
                partitions: build_symmetry_partitions(s, requested),
            });
        }
    }

    // Strategy 4: Combined (best variable + action independence).
    if let Some(best) = fdvars.first() {
        if best.domain_size >= 2 && groups.len() > 1 {
            let natural = best.domain_size * groups.len();
            let balance = compute_balance(natural, requested);
            strategies.push(PartitionStrategy {
                kind: StrategyKind::Combined {
                    primary_variable: best.name.clone(),
                },
                description: format!(
                    "Combined: `{}` ({} values) x {} groups = {} partitions",
                    best.name,
                    best.domain_size,
                    groups.len(),
                    natural
                ),
                natural_partitions: natural,
                balance_score: balance,
                effectiveness: 0.7 * balance,
                partitions: Vec::new(),
            });
        }
    }

    strategies.sort_by(|a, b| {
        b.effectiveness
            .partial_cmp(&a.effectiveness)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(
                b.balance_score
                    .partial_cmp(&a.balance_score)
                    .unwrap_or(std::cmp::Ordering::Equal),
            )
    });
    strategies
}

fn compute_balance(natural: usize, requested: usize) -> f64 {
    if natural == 0 || requested == 0 {
        return 0.0;
    }
    if natural == requested {
        return 1.0;
    }
    if natural >= requested {
        let per = natural / requested;
        let rem = natural % requested;
        if rem == 0 {
            1.0
        } else {
            per as f64 / (per + 1) as f64
        }
    } else {
        natural as f64 / requested as f64
    }
}

fn compute_coupling_balance(groups: &[CouplingGroup]) -> f64 {
    if groups.is_empty() {
        return 0.0;
    }
    let sizes: Vec<usize> = groups.iter().map(|g| g.variables.len()).collect();
    let (max, min) = (
        *sizes.iter().max().unwrap_or(&1),
        *sizes.iter().min().unwrap_or(&1),
    );
    if max == 0 {
        0.0
    } else {
        min as f64 / max as f64
    }
}

fn compute_variable_effectiveness(fdv: &FiniteDomainVar, actions: &[ActionInfo]) -> f64 {
    if actions.is_empty() {
        return 0.0;
    }
    let total = actions.len() as f64;
    let guard_count = actions
        .iter()
        .filter(|a| a.reads.contains(&fdv.name) && !a.writes.contains(&fdv.name))
        .count();
    let write_count = actions
        .iter()
        .filter(|a| a.writes.contains(&fdv.name))
        .count();
    let size_factor = if fdv.domain_size >= 2 { 1.0 } else { 0.1 };
    (0.6 * (guard_count as f64 / total)
        + 0.3 * (1.0 - write_count as f64 / total)
        + 0.1 * size_factor)
        .clamp(0.0, 1.0)
}

fn format_domain_source(source: &DomainSource) -> &'static str {
    match source {
        DomainSource::ConfigModelValueSet => "config model value set",
        DomainSource::InitSetEnum => "Init set enumeration",
        DomainSource::InitRange => "Init range expression",
        DomainSource::InitBoolean => "Init BOOLEAN",
    }
}

// ---------------------------------------------------------------------------
// Partition assignment builders
// ---------------------------------------------------------------------------

fn build_variable_partitions(fdv: &FiniteDomainVar, requested: usize) -> Vec<PartitionAssignment> {
    if fdv.values.is_empty() || requested == 0 {
        return Vec::new();
    }
    let n = fdv.values.len();
    let np = requested.min(n);
    let (per, rem) = (n / np, n % np);
    let frac = 1.0 / n as f64;
    let mut assignments = Vec::with_capacity(np);
    let mut offset = 0;
    for pid in 0..np {
        let count = per + if pid < rem { 1 } else { 0 };
        let slice = &fdv.values[offset..offset + count];
        let label = if count == 1 {
            format!("{} = {}", fdv.name, slice[0])
        } else {
            format!("{} in {{{}}}", fdv.name, slice.join(", "))
        };
        assignments.push(PartitionAssignment {
            partition_id: pid,
            label,
            estimated_fraction: count as f64 * frac,
        });
        offset += count;
    }
    assignments
}

fn build_action_partitions(groups: &[CouplingGroup], requested: usize) -> Vec<PartitionAssignment> {
    let ng = groups.len();
    groups
        .iter()
        .take(requested.min(ng))
        .enumerate()
        .map(|(pid, g)| {
            let vars: Vec<&str> = g.variables.iter().map(|s| s.as_str()).collect();
            PartitionAssignment {
                partition_id: pid,
                label: format!(
                    "vars: {{{}}} (actions: {})",
                    vars.join(", "),
                    g.actions.join(", ")
                ),
                estimated_fraction: 1.0 / ng as f64,
            }
        })
        .collect()
}

fn build_symmetry_partitions(sym: &SymmetryInfo, requested: usize) -> Vec<PartitionAssignment> {
    let n = sym.element_count;
    if n == 0 {
        return Vec::new();
    }
    let np = requested.min(n);
    let (per, rem, frac) = (n / np, n % np, 1.0 / n as f64);
    (0..np)
        .map(|pid| {
            let count = per + if pid < rem { 1 } else { 0 };
            PartitionAssignment {
                partition_id: pid,
                label: format!(
                    "symmetry class {} ({} element{})",
                    pid + 1,
                    count,
                    if count == 1 { "" } else { "s" }
                ),
                estimated_fraction: count as f64 * frac,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Output formatting
// ---------------------------------------------------------------------------

fn print_human(analysis: &PartitionAnalysis) {
    println!("=== Partition Analysis: {} ===\n", analysis.module_name);
    println!(
        "State variables ({}): {}\n",
        analysis.variables.len(),
        analysis.variables.join(", ")
    );

    if analysis.finite_domain_vars.is_empty() {
        println!("No finite-domain variables detected.");
        println!("  Hint: Provide a .cfg file with CONSTANT assignments to enable partitioning.");
    } else {
        println!("Finite-domain variables:");
        for fdv in &analysis.finite_domain_vars {
            let vals = if fdv.values.len() <= 8 {
                format!(" = {{{}}}", fdv.values.join(", "))
            } else {
                format!(" ({} values)", fdv.values.len())
            };
            println!(
                "  {} : |domain| = {} [{}]{}",
                fdv.name,
                fdv.domain_size,
                format_domain_source(&fdv.domain_source),
                vals
            );
        }
    }
    println!();

    if analysis.actions.is_empty() {
        println!("No actions found in the Next relation.");
    } else {
        println!("Actions ({}):", analysis.actions.len());
        for a in &analysis.actions {
            let fmt = |s: &BTreeSet<String>| {
                if s.is_empty() {
                    "-".to_string()
                } else {
                    s.iter().cloned().collect::<Vec<_>>().join(", ")
                }
            };
            println!(
                "  {} : reads={{{}}} writes={{{}}}",
                a.name,
                fmt(&a.reads),
                fmt(&a.writes)
            );
            if !a.unchanged.is_empty() {
                println!(
                    "    UNCHANGED {{{}}}",
                    a.unchanged
                        .iter()
                        .map(|s| s.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
        }
    }
    println!();

    if analysis.coupling_groups.len() > 1 {
        println!(
            "Variable coupling: {} independent groups",
            analysis.coupling_groups.len()
        );
        for (i, g) in analysis.coupling_groups.iter().enumerate() {
            let vars: Vec<&str> = g.variables.iter().map(|s| s.as_str()).collect();
            println!(
                "  Group {}: {{{}}} (touched by: {})",
                i + 1,
                vars.join(", "),
                g.actions.join(", ")
            );
        }
    } else if analysis.coupling_groups.len() == 1 {
        println!("Variable coupling: all variables are coupled (single group)");
    }
    println!();

    if let Some(sym) = &analysis.symmetry_info {
        println!(
            "Symmetry: {} ({} element{})",
            sym.symmetry_set,
            sym.element_count,
            if sym.element_count == 1 { "" } else { "s" }
        );
        if !sym.symmetric_constants.is_empty() {
            println!(
                "  Symmetric constants: {}",
                sym.symmetric_constants.join(", ")
            );
        }
        println!();
    }

    let ps = if analysis.requested_partitions == 1 {
        ""
    } else {
        "s"
    };
    println!(
        "=== Partitioning Strategies (target: {} partition{}) ===\n",
        analysis.requested_partitions, ps
    );

    if analysis.strategies.is_empty() {
        println!("No partitioning strategies available.");
        println!("  Consider: add finite-domain constants, factor the Next relation into");
        println!("  independent sub-actions, or declare SYMMETRY.");
    } else {
        for (i, s) in analysis.strategies.iter().enumerate() {
            let tag = if i == 0 { " [RECOMMENDED]" } else { "" };
            println!(
                "{}. {}{} (effectiveness: {:.0}%, balance: {:.0}%)",
                i + 1,
                s.description,
                tag,
                s.effectiveness * 100.0,
                s.balance_score * 100.0
            );
            println!(
                "   Natural partitions: {} -> requested: {}",
                s.natural_partitions, analysis.requested_partitions
            );
            for pa in &s.partitions {
                println!(
                    "   [P{}] {} ({:.1}%)",
                    pa.partition_id,
                    pa.label,
                    pa.estimated_fraction * 100.0
                );
            }
            println!();
        }
    }
}

fn print_json(analysis: &PartitionAnalysis) -> Result<()> {
    let json = serde_json::to_string_pretty(analysis).context("serialize partition analysis")?;
    println!("{json}");
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_partition_output_format_eq() {
        assert_eq!(PartitionOutputFormat::Human, PartitionOutputFormat::Human);
        assert_ne!(PartitionOutputFormat::Human, PartitionOutputFormat::Json);
    }

    #[test]
    fn test_compute_balance_equal() {
        assert!((compute_balance(4, 4) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_compute_balance_double() {
        assert!((compute_balance(8, 4) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_compute_balance_uneven() {
        let b = compute_balance(5, 4);
        assert!(b > 0.4 && b < 1.0);
    }

    #[test]
    fn test_compute_balance_fewer_natural() {
        assert!((compute_balance(2, 4) - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_compute_balance_zero() {
        assert!(compute_balance(0, 4).abs() < f64::EPSILON);
        assert!(compute_balance(4, 0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coupling_balance_uniform() {
        let groups = vec![
            CouplingGroup {
                variables: ["a", "b"].iter().map(|s| s.to_string()).collect(),
                actions: vec!["A1".to_string()],
            },
            CouplingGroup {
                variables: ["c", "d"].iter().map(|s| s.to_string()).collect(),
                actions: vec!["A2".to_string()],
            },
        ];
        assert!((compute_coupling_balance(&groups) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_coupling_balance_skewed() {
        let groups = vec![
            CouplingGroup {
                variables: ["a", "b", "c", "d"].iter().map(|s| s.to_string()).collect(),
                actions: vec!["A1".to_string()],
            },
            CouplingGroup {
                variables: ["e"].iter().map(|s| s.to_string()).collect(),
                actions: vec!["A2".to_string()],
            },
        ];
        assert!((compute_coupling_balance(&groups) - 0.25).abs() < f64::EPSILON);
    }

    #[test]
    fn test_decompose_disjunction_single() {
        let expr = Expr::Bool(true);
        assert_eq!(decompose_disjunction(&expr).len(), 1);
    }

    #[test]
    fn test_build_variable_partitions_even() {
        let fdv = FiniteDomainVar {
            name: "pc".to_string(),
            domain_size: 4,
            domain_source: DomainSource::InitSetEnum,
            values: vec!["init".into(), "ready".into(), "run".into(), "done".into()],
        };
        let parts = build_variable_partitions(&fdv, 4);
        assert_eq!(parts.len(), 4);
        for (i, pa) in parts.iter().enumerate() {
            assert_eq!(pa.partition_id, i);
            assert!((pa.estimated_fraction - 0.25).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_build_variable_partitions_fewer_requested() {
        let fdv = FiniteDomainVar {
            name: "x".to_string(),
            domain_size: 6,
            domain_source: DomainSource::InitRange,
            values: (1..=6).map(|i| i.to_string()).collect(),
        };
        let parts = build_variable_partitions(&fdv, 3);
        assert_eq!(parts.len(), 3);
        for pa in &parts {
            assert!((pa.estimated_fraction - 2.0 / 6.0).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_build_variable_partitions_more_than_values() {
        let fdv = FiniteDomainVar {
            name: "b".to_string(),
            domain_size: 2,
            domain_source: DomainSource::InitBoolean,
            values: vec!["TRUE".into(), "FALSE".into()],
        };
        assert_eq!(build_variable_partitions(&fdv, 8).len(), 2);
    }

    #[test]
    fn test_symmetry_partitions() {
        let sym = SymmetryInfo {
            symmetry_set: "Perms".into(),
            symmetric_constants: vec!["Procs".into()],
            element_count: 3,
        };
        let parts = build_symmetry_partitions(&sym, 3);
        assert_eq!(parts.len(), 3);
        for pa in &parts {
            assert!((pa.estimated_fraction - 1.0 / 3.0).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_action_partitions() {
        let groups = vec![
            CouplingGroup {
                variables: ["x"].iter().map(|s| s.to_string()).collect(),
                actions: vec!["IncX".into()],
            },
            CouplingGroup {
                variables: ["y"].iter().map(|s| s.to_string()).collect(),
                actions: vec!["IncY".into()],
            },
        ];
        assert_eq!(build_action_partitions(&groups, 4).len(), 2);
    }

    #[test]
    fn test_collect_variables_empty() {
        let module = Module {
            name: tla_core::Spanned::dummy("Test".to_string()),
            extends: Vec::new(),
            units: Vec::new(),
            action_subscript_spans: Default::default(),
            span: tla_core::Span::dummy(),
        };
        assert!(collect_variables(&module).is_empty());
    }

    #[test]
    fn test_variable_effectiveness_read_guard() {
        let fdv = FiniteDomainVar {
            name: "pc".into(),
            domain_size: 3,
            domain_source: DomainSource::InitSetEnum,
            values: vec!["a".into(), "b".into(), "c".into()],
        };
        let actions = vec![
            ActionInfo {
                name: "A".into(),
                reads: ["pc"].iter().map(|s| s.to_string()).collect(),
                writes: ["x"].iter().map(|s| s.to_string()).collect(),
                unchanged: BTreeSet::new(),
            },
            ActionInfo {
                name: "B".into(),
                reads: ["pc"].iter().map(|s| s.to_string()).collect(),
                writes: ["y"].iter().map(|s| s.to_string()).collect(),
                unchanged: BTreeSet::new(),
            },
        ];
        assert!(compute_variable_effectiveness(&fdv, &actions) > 0.5);
    }

    #[test]
    fn test_variable_effectiveness_always_written() {
        let fdv = FiniteDomainVar {
            name: "counter".into(),
            domain_size: 10,
            domain_source: DomainSource::InitRange,
            values: (0..10).map(|i| i.to_string()).collect(),
        };
        let actions = vec![ActionInfo {
            name: "Step".into(),
            reads: ["counter"].iter().map(|s| s.to_string()).collect(),
            writes: ["counter"].iter().map(|s| s.to_string()).collect(),
            unchanged: BTreeSet::new(),
        }];
        assert!(compute_variable_effectiveness(&fdv, &actions) < 0.5);
    }

    #[test]
    fn test_generate_strategies_empty() {
        assert!(generate_strategies(&[], &[], &[], None, 4).is_empty());
    }

    #[test]
    fn test_classify_domain_boolean() {
        use tla_core::name_intern::NameId;
        assert!(matches!(
            classify_domain(&Expr::Ident("BOOLEAN".into(), NameId::INVALID)),
            DomainInfo::Boolean
        ));
    }

    #[test]
    fn test_classify_domain_set_enum() {
        use tla_core::Spanned;
        let elems = vec![
            Spanned::dummy(Expr::String("a".into())),
            Spanned::dummy(Expr::String("b".into())),
        ];
        match classify_domain(&Expr::SetEnum(elems)) {
            DomainInfo::SetEnum(vals) => assert_eq!(vals.len(), 2),
            other => panic!("expected SetEnum, got {other:?}"),
        }
    }

    #[test]
    fn test_classify_domain_range() {
        use num_bigint::BigInt;
        use tla_core::Spanned;
        let expr = Expr::Range(
            Box::new(Spanned::dummy(Expr::Int(BigInt::from(1)))),
            Box::new(Spanned::dummy(Expr::Int(BigInt::from(5)))),
        );
        match classify_domain(&expr) {
            DomainInfo::Range(lo, hi) => {
                assert_eq!(lo, 1);
                assert_eq!(hi, 5);
            }
            other => panic!("expected Range, got {other:?}"),
        }
    }
}
