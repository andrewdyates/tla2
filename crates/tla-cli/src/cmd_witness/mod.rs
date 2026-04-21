// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 witness` -- witness trace generation for TLA+ specifications.
//!
//! Generates concrete execution paths that demonstrate a property holds or show
//! how an invariant is maintained. Unlike `tla2 check` which searches for
//! violations, `witness` searches for *positive examples*: traces from an
//! initial state to a state satisfying a given target predicate.
//!
//! Modes:
//!
//! - **Structural analysis** -- parse the spec, identify the target operator,
//!   analyze which operators reference it, and report how deep a BFS search
//!   would need to be. This is the default when full evaluation is not wired.
//!
//! - **BFS search** (future) -- perform a simplified BFS up to `max_depth` to
//!   discover concrete traces where the target predicate holds at the final
//!   state.
//!
//! Output formats: human-readable (colored terminal) and JSON.

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::span::Span;
use tla_core::{lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for witness trace results.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WitnessOutputFormat {
    /// Colored terminal output with step-by-step trace display.
    Human,
    /// Machine-readable JSON output.
    Json,
}

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

/// A reference from one operator to another in the dependency graph.
#[derive(Debug, Clone, serde::Serialize)]
struct OperatorRef {
    /// The operator that contains the reference.
    from: String,
    /// The operator being referenced.
    to: String,
    /// Whether the reference is direct (in the body) or transitive.
    direct: bool,
}

/// Information about a single operator relevant to witness generation.
#[derive(Debug, Clone, serde::Serialize)]
struct OperatorInfo {
    name: String,
    param_count: usize,
    has_priming: bool,
    is_action: bool,
    is_predicate: bool,
    line: usize,
    column: usize,
    #[serde(skip)]
    span: Span,
}

/// Configuration extracted from the .cfg file (or defaults).
#[derive(Debug, Default)]
struct ConfigInfo {
    init: Option<String>,
    next: Option<String>,
    invariants: Vec<String>,
}

/// Analysis of a BFS witness search feasibility.
#[derive(Debug, serde::Serialize)]
struct WitnessAnalysis {
    module_name: String,
    target: String,
    target_found: bool,
    target_info: Option<OperatorInfo>,
    init_name: String,
    next_name: String,
    has_init: bool,
    has_next: bool,
    variable_count: usize,
    operator_count: usize,
    max_depth: usize,
    requested_count: usize,
    /// Operators that directly or transitively reference the target.
    references_to_target: Vec<OperatorRef>,
    /// Operators that the target directly or transitively references.
    target_dependencies: Vec<OperatorRef>,
    /// The action disjuncts of Next that could lead to a target-satisfying state.
    relevant_actions: Vec<String>,
    /// Estimated search characteristics.
    search_notes: Vec<String>,
}

/// A single step in a witness trace (for future BFS output).
#[derive(Debug, Clone, serde::Serialize)]
struct WitnessStep {
    depth: usize,
    description: String,
}

/// A complete witness trace.
#[derive(Debug, Clone, serde::Serialize)]
struct WitnessTrace {
    target: String,
    depth: usize,
    steps: Vec<WitnessStep>,
}

/// Top-level result of the witness command.
#[derive(Debug, serde::Serialize)]
struct WitnessResult {
    file: String,
    analysis: WitnessAnalysis,
    traces: Vec<WitnessTrace>,
    status: String,
    message: String,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Generate witness traces for a TLA+ specification.
///
/// Searches for traces from `Init` where the `target` predicate holds at the
/// final state. Currently performs structural analysis; full BFS evaluation
/// requires the checker runtime.
pub(crate) fn cmd_witness(
    file: &Path,
    config: Option<&Path>,
    target: &str,
    max_depth: usize,
    count: usize,
    format: WitnessOutputFormat,
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
            "witness generation aborted: {} parse error(s)",
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
            "witness generation aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("witness generation: lowering produced no module")?;

    // Load config
    let cfg_info = load_config_info(file, config);

    // Perform structural analysis
    let analysis = analyze_witness_feasibility(&module, &cfg_info, target, max_depth, count);

    // Build result
    let file_path = file.display().to_string();
    let status = if !analysis.target_found {
        "target_not_found"
    } else if !analysis.has_init {
        "missing_init"
    } else if !analysis.has_next {
        "missing_next"
    } else {
        "analysis_complete"
    };

    let message = build_status_message(&analysis, status);

    let result = WitnessResult {
        file: file_path.clone(),
        analysis,
        traces: Vec::new(), // BFS traces not yet implemented
        status: status.to_string(),
        message,
    };

    // Output
    match format {
        WitnessOutputFormat::Human => print_human(&file_path, &source, &result),
        WitnessOutputFormat::Json => print_json(&result)?,
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Structural analysis engine
// ---------------------------------------------------------------------------

fn analyze_witness_feasibility(
    module: &Module,
    cfg: &ConfigInfo,
    target: &str,
    max_depth: usize,
    count: usize,
) -> WitnessAnalysis {
    let init_name = cfg.init.as_deref().unwrap_or("Init");
    let next_name = cfg.next.as_deref().unwrap_or("Next");

    // Collect all operator definitions
    let mut all_ops: HashMap<&str, &OperatorDef> = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            all_ops.insert(op.name.node.as_str(), op);
        }
    }

    // Count variables
    let variable_count: usize = module
        .units
        .iter()
        .filter_map(|u| match &u.node {
            Unit::Variable(names) => Some(names.len()),
            _ => None,
        })
        .sum();

    let operator_count = all_ops.len();
    let has_init = all_ops.contains_key(init_name);
    let has_next = all_ops.contains_key(next_name);
    let target_found = all_ops.contains_key(target);

    // Build operator info for the target
    let target_info = all_ops.get(target).map(|op| {
        let has_priming = expr_contains_prime(&op.body.node);
        let is_action = has_priming;
        let is_predicate = !has_priming && op.params.is_empty();
        OperatorInfo {
            name: op.name.node.clone(),
            param_count: op.params.len(),
            has_priming,
            is_action,
            is_predicate,
            line: 0,
            column: 0,
            span: op.name.span,
        }
    });

    // Build dependency graph: which operators reference which
    let dep_graph = build_dependency_graph(&all_ops);

    // Find operators that reference the target (directly or transitively)
    let refs_to_target = find_references_to(&dep_graph, target);

    // Find operators that the target depends on
    let target_deps = find_dependencies_of(&dep_graph, target);

    // Determine relevant actions from Next
    let relevant_actions = if has_next {
        find_relevant_actions(all_ops[next_name], &all_ops, target, &dep_graph)
    } else {
        Vec::new()
    };

    // Generate search notes
    let search_notes = generate_search_notes(
        target,
        &target_info,
        has_init,
        has_next,
        variable_count,
        max_depth,
        &relevant_actions,
        &cfg.invariants,
    );

    WitnessAnalysis {
        module_name: module.name.node.clone(),
        target: target.to_string(),
        target_found,
        target_info,
        init_name: init_name.to_string(),
        next_name: next_name.to_string(),
        has_init,
        has_next,
        variable_count,
        operator_count,
        max_depth,
        requested_count: count,
        references_to_target: refs_to_target,
        target_dependencies: target_deps,
        relevant_actions,
        search_notes,
    }
}

// ---------------------------------------------------------------------------
// Dependency graph construction
// ---------------------------------------------------------------------------

/// A directed graph: operator name -> set of operator names it references.
type DepGraph = HashMap<String, HashSet<String>>;

/// Build a dependency graph from operator definitions.
fn build_dependency_graph(ops: &HashMap<&str, &OperatorDef>) -> DepGraph {
    let op_names: HashSet<&str> = ops.keys().copied().collect();
    let mut graph = DepGraph::new();

    for (&name, op) in ops {
        let mut refs = HashSet::new();
        collect_ident_refs(&op.body.node, &op_names, &mut refs);
        graph.insert(name.to_string(), refs);
    }

    graph
}

/// Collect all identifier references within an expression that correspond to
/// known operator names.
fn collect_ident_refs(expr: &Expr, known_ops: &HashSet<&str>, out: &mut HashSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if known_ops.contains(name.as_str()) {
                out.insert(name.clone());
            }
        }
        _ => {
            visit_expr_children(expr, |child| {
                collect_ident_refs(child, known_ops, out);
            });
        }
    }
}

/// Find all operators that reference `target` (directly or transitively).
fn find_references_to(graph: &DepGraph, target: &str) -> Vec<OperatorRef> {
    let mut result = Vec::new();

    // Direct references
    for (from, deps) in graph {
        if deps.contains(target) {
            result.push(OperatorRef {
                from: from.clone(),
                to: target.to_string(),
                direct: true,
            });
        }
    }

    // Transitive references via BFS from each operator
    let mut transitive_refs: HashSet<String> = HashSet::new();
    for (from, _) in graph {
        if from == target {
            continue;
        }
        if result.iter().any(|r| r.from == *from) {
            continue; // Already found as direct
        }
        if can_reach(graph, from, target) {
            transitive_refs.insert(from.clone());
        }
    }

    for from in transitive_refs {
        result.push(OperatorRef {
            from,
            to: target.to_string(),
            direct: false,
        });
    }

    result.sort_by(|a, b| a.from.cmp(&b.from));
    result
}

/// Find all operators that `target` depends on (directly or transitively).
fn find_dependencies_of(graph: &DepGraph, target: &str) -> Vec<OperatorRef> {
    let mut result = Vec::new();
    let direct_deps: HashSet<String> = graph
        .get(target)
        .cloned()
        .unwrap_or_default();

    for dep in &direct_deps {
        result.push(OperatorRef {
            from: target.to_string(),
            to: dep.clone(),
            direct: true,
        });
    }

    // Transitive dependencies via BFS
    let mut visited = HashSet::new();
    visited.insert(target.to_string());
    let mut queue: VecDeque<String> = direct_deps.iter().cloned().collect();
    visited.extend(direct_deps.iter().cloned());

    while let Some(current) = queue.pop_front() {
        if let Some(deps) = graph.get(&current) {
            for dep in deps {
                if visited.insert(dep.clone()) {
                    result.push(OperatorRef {
                        from: target.to_string(),
                        to: dep.clone(),
                        direct: false,
                    });
                    queue.push_back(dep.clone());
                }
            }
        }
    }

    result.sort_by(|a, b| a.to.cmp(&b.to));
    result
}

/// BFS reachability check: can `from` reach `target` in the dependency graph?
fn can_reach(graph: &DepGraph, from: &str, target: &str) -> bool {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(from.to_string());
    visited.insert(from.to_string());

    while let Some(current) = queue.pop_front() {
        if let Some(deps) = graph.get(&current) {
            for dep in deps {
                if dep == target {
                    return true;
                }
                if visited.insert(dep.clone()) {
                    queue.push_back(dep.clone());
                }
            }
        }
    }

    false
}

// ---------------------------------------------------------------------------
// Action analysis
// ---------------------------------------------------------------------------

/// Find which action disjuncts of the Next operator are relevant to reaching
/// a state satisfying the target.
fn find_relevant_actions(
    next_op: &OperatorDef,
    ops: &HashMap<&str, &OperatorDef>,
    target: &str,
    dep_graph: &DepGraph,
) -> Vec<String> {
    let disjuncts = collect_disjuncts(&next_op.body.node, ops);
    let mut relevant = Vec::new();

    for disjunct in &disjuncts {
        let action_name = extract_action_name(disjunct, ops);
        // An action is relevant if:
        // 1. It modifies variables that the target references, OR
        // 2. The target or any of its dependencies appear in the action body, OR
        // 3. We cannot determine relevance (conservative: include it)
        let target_deps: HashSet<String> = dep_graph
            .get(target)
            .cloned()
            .unwrap_or_default();

        let action_refs = collect_all_idents(disjunct);
        let is_relevant = action_refs.contains(target)
            || action_refs.iter().any(|r| target_deps.contains(r))
            || action_name.is_none(); // Conservative: include unnamed/complex actions

        if is_relevant {
            relevant.push(action_name.unwrap_or_else(|| "<complex expression>".to_string()));
        }
    }

    // If no specific relevant actions found, all actions are potentially relevant
    if relevant.is_empty() && !disjuncts.is_empty() {
        for disjunct in &disjuncts {
            let name = extract_action_name(disjunct, ops)
                .unwrap_or_else(|| "<complex expression>".to_string());
            relevant.push(name);
        }
    }

    relevant.sort();
    relevant.dedup();
    relevant
}

/// Extract all identifier names from an expression.
fn collect_all_idents(expr: &Expr) -> HashSet<String> {
    let mut result = HashSet::new();
    collect_all_idents_inner(expr, &mut result);
    result
}

fn collect_all_idents_inner(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            out.insert(name.clone());
        }
        _ => {
            visit_expr_children(expr, |child| {
                collect_all_idents_inner(child, out);
            });
        }
    }
}

/// Try to extract a simple action name from a disjunct expression.
fn extract_action_name(expr: &Expr, ops: &HashMap<&str, &OperatorDef>) -> Option<String> {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if ops.contains_key(name.as_str()) {
                Some(name.clone())
            } else {
                None
            }
        }
        Expr::Apply(func, _) => {
            if let Expr::Ident(name, _) = &func.node {
                Some(name.clone())
            } else {
                None
            }
        }
        Expr::Label(label) => extract_action_name(&label.body.node, ops),
        // For conjunctions like `guard /\ body`, try to identify the action
        Expr::And(_, _) => None,
        Expr::Exists(_, body) => extract_action_name(&body.node, ops),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Search notes generation
// ---------------------------------------------------------------------------

fn generate_search_notes(
    target: &str,
    target_info: &Option<OperatorInfo>,
    has_init: bool,
    has_next: bool,
    variable_count: usize,
    max_depth: usize,
    relevant_actions: &[String],
    invariants: &[String],
) -> Vec<String> {
    let mut notes = Vec::new();

    if let Some(info) = target_info {
        if info.is_predicate {
            notes.push(format!(
                "`{target}` is a state predicate (no parameters, no priming) -- \
                 suitable as a witness target"
            ));
        } else if info.is_action {
            notes.push(format!(
                "`{target}` contains primed variables -- it is an action, not a \
                 state predicate. Witness search will look for states where this \
                 action is enabled."
            ));
        } else if info.param_count > 0 {
            notes.push(format!(
                "`{target}` takes {} parameter(s) -- witness search requires a \
                 concrete instantiation",
                info.param_count,
            ));
        }
    }

    if !has_init {
        notes.push(
            "No Init operator found -- BFS search cannot determine initial states.".to_string(),
        );
    }
    if !has_next {
        notes.push(
            "No Next operator found -- BFS search cannot explore transitions.".to_string(),
        );
    }

    if variable_count == 0 {
        notes.push("No variables declared -- state space is trivial.".to_string());
    } else {
        notes.push(format!(
            "State space has {variable_count} variable(s); BFS up to depth {max_depth} \
             may explore up to O(branching_factor^{max_depth}) states."
        ));
    }

    if !relevant_actions.is_empty() {
        notes.push(format!(
            "{} action(s) could be relevant to reaching a {target}-satisfying state: {}",
            relevant_actions.len(),
            relevant_actions.join(", ")
        ));
    }

    // Check if target is listed as an invariant
    if invariants.contains(&target.to_string()) {
        notes.push(format!(
            "`{target}` is listed as an INVARIANT in the config. If it holds \
             in all reachable states, every state is a witness."
        ));
    }

    notes
}

// ---------------------------------------------------------------------------
// Status message
// ---------------------------------------------------------------------------

fn build_status_message(analysis: &WitnessAnalysis, status: &str) -> String {
    match status {
        "target_not_found" => format!(
            "Target operator `{}` not found in module `{}`. \
             Available operators: check with `tla2 search operator {}`.",
            analysis.target, analysis.module_name, analysis.target,
        ),
        "missing_init" => format!(
            "No `{}` operator defined -- cannot determine initial states for BFS.",
            analysis.init_name,
        ),
        "missing_next" => format!(
            "No `{}` operator defined -- cannot explore transitions for BFS.",
            analysis.next_name,
        ),
        "analysis_complete" => {
            let action_hint = if analysis.relevant_actions.is_empty() {
                String::new()
            } else {
                format!(
                    " {} relevant action(s) identified.",
                    analysis.relevant_actions.len()
                )
            };
            format!(
                "Structural analysis of `{}` complete. \
                 Target `{}` found with {} direct reference(s) and {} dependenc(ies).{}",
                analysis.module_name,
                analysis.target,
                analysis
                    .references_to_target
                    .iter()
                    .filter(|r| r.direct)
                    .count(),
                analysis
                    .target_dependencies
                    .iter()
                    .filter(|r| r.direct)
                    .count(),
                action_hint,
            )
        }
        other => format!("Unknown status: {other}"),
    }
}

// ---------------------------------------------------------------------------
// Expression analysis helpers
// ---------------------------------------------------------------------------

/// Check if an expression contains any primed sub-expression.
fn expr_contains_prime(expr: &Expr) -> bool {
    match expr {
        Expr::Prime(_) => true,
        _ => {
            let mut found = false;
            visit_expr_children(expr, |child| {
                if expr_contains_prime(child) {
                    found = true;
                }
            });
            found
        }
    }
}

/// Collect the top-level disjuncts from the Next operator body.
/// Follows operator references one level deep.
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
    if depth > 10 {
        out.push(expr);
        return;
    }
    match expr {
        Expr::Or(lhs, rhs) => {
            collect_disjuncts_inner(&lhs.node, ops, out, depth);
            collect_disjuncts_inner(&rhs.node, ops, out, depth);
        }
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

/// Visit direct child expressions of an Expr node.
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
            invariants: Vec::new(),
        };
    }

    let source = match std::fs::read_to_string(&config_path_buf) {
        Ok(s) => s,
        Err(_) => {
            return ConfigInfo {
                init: Some("Init".to_string()),
                next: Some("Next".to_string()),
                invariants: Vec::new(),
            };
        }
    };

    match tla_check::Config::parse(&source) {
        Ok(config) => ConfigInfo {
            init: config.init.clone(),
            next: config.next.clone(),
            invariants: config.invariants.clone(),
        },
        Err(_) => ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: Vec::new(),
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
// Output formatting -- Human
// ---------------------------------------------------------------------------

fn print_human(file_path: &str, source: &str, result: &WitnessResult) {
    let analysis = &result.analysis;

    println!(
        "\x1b[1mWitness analysis: {}\x1b[0m (module `{}`)\n",
        file_path, analysis.module_name
    );

    // Structure summary
    println!("  Target:       `{}`", analysis.target);
    println!(
        "  Target found: {}",
        if analysis.target_found { "yes" } else { "NO" }
    );
    if let Some(info) = &analysis.target_info {
        let kind = if info.is_predicate {
            "state predicate"
        } else if info.is_action {
            "action"
        } else {
            "operator"
        };
        println!(
            "  Target type:  {} ({} parameter(s))",
            kind, info.param_count
        );
    }
    println!("  Init:         `{}`{}", analysis.init_name, if analysis.has_init { "" } else { " (NOT FOUND)" });
    println!("  Next:         `{}`{}", analysis.next_name, if analysis.has_next { "" } else { " (NOT FOUND)" });
    println!("  Variables:    {}", analysis.variable_count);
    println!("  Operators:    {}", analysis.operator_count);
    println!("  Max depth:    {}", analysis.max_depth);
    println!("  Count:        {}", analysis.requested_count);
    println!();

    // References to target
    if !analysis.references_to_target.is_empty() {
        println!("\x1b[1mOperators referencing `{}`:\x1b[0m", analysis.target);
        for oref in &analysis.references_to_target {
            let kind = if oref.direct { "direct" } else { "transitive" };
            println!("  {} -> {} ({})", oref.from, oref.to, kind);
        }
        println!();
    }

    // Target dependencies
    let direct_deps: Vec<_> = analysis
        .target_dependencies
        .iter()
        .filter(|r| r.direct)
        .collect();
    if !direct_deps.is_empty() {
        println!(
            "\x1b[1m`{}` depends on:\x1b[0m",
            analysis.target
        );
        for oref in &direct_deps {
            println!("  -> {}", oref.to);
        }
        println!();
    }

    // Relevant actions
    if !analysis.relevant_actions.is_empty() {
        println!("\x1b[1mRelevant actions (from `{}`):\x1b[0m", analysis.next_name);
        for action in &analysis.relevant_actions {
            println!("  - {action}");
        }
        println!();
    }

    // Search notes
    if !analysis.search_notes.is_empty() {
        println!("\x1b[1mSearch notes:\x1b[0m");
        for note in &analysis.search_notes {
            println!("  * {note}");
        }
        println!();
    }

    // Status
    let status_color = match result.status.as_str() {
        "analysis_complete" => "\x1b[32m",
        "target_not_found" => "\x1b[31m",
        _ => "\x1b[33m",
    };
    println!("{status_color}{}\x1b[0m", result.message);

    // Source location for target
    if let Some(info) = &analysis.target_info {
        let starts = line_starts(source);
        let (line, col) = offset_to_line_col(info.span.start, &starts);
        println!("  --> {file_path}:{line}:{col}");
    }

    // Hint for full BFS
    if analysis.target_found && analysis.has_init && analysis.has_next {
        println!();
        println!(
            "\x1b[2mTip: Full witness trace generation via BFS will be available in a\n\
             future release. For now, use `tla2 check {} --config <cfg>` and inspect\n\
             the state graph.\x1b[0m",
            file_path
        );
    }
}

// ---------------------------------------------------------------------------
// Output formatting -- JSON
// ---------------------------------------------------------------------------

fn print_json(result: &WitnessResult) -> Result<()> {
    let output = serde_json::json!({
        "file": result.file,
        "status": result.status,
        "message": result.message,
        "analysis": {
            "module": result.analysis.module_name,
            "target": result.analysis.target,
            "target_found": result.analysis.target_found,
            "target_info": result.analysis.target_info,
            "init": result.analysis.init_name,
            "next": result.analysis.next_name,
            "has_init": result.analysis.has_init,
            "has_next": result.analysis.has_next,
            "variable_count": result.analysis.variable_count,
            "operator_count": result.analysis.operator_count,
            "max_depth": result.analysis.max_depth,
            "requested_count": result.analysis.requested_count,
            "references_to_target": result.analysis.references_to_target,
            "target_dependencies": result.analysis.target_dependencies,
            "relevant_actions": result.analysis.relevant_actions,
            "search_notes": result.analysis.search_notes,
        },
        "traces": result.traces,
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

    fn default_cfg() -> ConfigInfo {
        ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: Vec::new(),
        }
    }

    // -- Target resolution ---------------------------------------------------

    #[test]
    fn test_target_found_for_existing_operator() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "TypeOK", 10, 1);
        assert!(analysis.target_found);
        assert!(analysis.target_info.is_some());
        let info = analysis.target_info.as_ref().unwrap();
        assert!(info.is_predicate);
        assert!(!info.is_action);
        assert_eq!(info.param_count, 0);
    }

    #[test]
    fn test_target_not_found_for_missing_operator() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "TypeOK", 10, 1);
        assert!(!analysis.target_found);
        assert!(analysis.target_info.is_none());
    }

    #[test]
    fn test_action_target_identified() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Increment == x' = x + 1
Next == Increment
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "Increment", 10, 1);
        assert!(analysis.target_found);
        let info = analysis.target_info.as_ref().unwrap();
        assert!(info.is_action);
        assert!(!info.is_predicate);
    }

    // -- Dependency graph ----------------------------------------------------

    #[test]
    fn test_dependency_graph_direct_refs() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
Safety == TypeOK
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "TypeOK", 10, 1);
        assert!(
            analysis
                .references_to_target
                .iter()
                .any(|r| r.from == "Safety" && r.direct),
            "Safety should directly reference TypeOK"
        );
    }

    #[test]
    fn test_target_dependencies_resolved() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y
Helper == x + y
Invariant == Helper > 0
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "Invariant", 10, 1);
        assert!(
            analysis
                .target_dependencies
                .iter()
                .any(|r| r.to == "Helper" && r.direct),
            "Invariant should depend on Helper"
        );
    }

    #[test]
    fn test_transitive_dependency() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
A == x > 0
B == A
C == B
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "C", 10, 1);
        // C -> B -> A (transitive)
        let deps: Vec<&str> = analysis
            .target_dependencies
            .iter()
            .map(|r| r.to.as_str())
            .collect();
        assert!(deps.contains(&"B"), "C should depend on B");
        assert!(deps.contains(&"A"), "C should transitively depend on A");
    }

    // -- Relevant actions ----------------------------------------------------

    #[test]
    fn test_relevant_actions_identified() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
IncX == x' = x + 1 /\ UNCHANGED y
IncY == y' = y + 1 /\ UNCHANGED x
Next == IncX \/ IncY
TypeOK == x \in Nat /\ y \in Nat
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "TypeOK", 10, 1);
        // Both actions modify variables referenced by TypeOK
        assert!(
            !analysis.relevant_actions.is_empty(),
            "should identify relevant actions"
        );
    }

    // -- Search notes --------------------------------------------------------

    #[test]
    fn test_search_notes_state_predicate() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "TypeOK", 10, 1);
        assert!(
            analysis
                .search_notes
                .iter()
                .any(|n| n.contains("state predicate")),
            "should note TypeOK is a state predicate"
        );
    }

    #[test]
    fn test_search_notes_invariant_hint() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
===="#,
        );
        let cfg = ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["TypeOK".to_string()],
        };
        let analysis = analyze_witness_feasibility(&module, &cfg, "TypeOK", 10, 1);
        assert!(
            analysis
                .search_notes
                .iter()
                .any(|n| n.contains("INVARIANT")),
            "should note TypeOK is an invariant"
        );
    }

    #[test]
    fn test_search_notes_missing_init() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Next == x' = x + 1
TypeOK == x \in Nat
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "TypeOK", 10, 1);
        assert!(
            analysis
                .search_notes
                .iter()
                .any(|n| n.contains("No Init")),
            "should note missing Init"
        );
    }

    // -- Module structure ----------------------------------------------------

    #[test]
    fn test_variable_count() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y, z
Init == x = 0 /\ y = 0 /\ z = 0
Next == x' = x /\ y' = y /\ z' = z
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "Init", 10, 1);
        assert_eq!(analysis.variable_count, 3);
    }

    #[test]
    fn test_operator_count() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
Safety == TypeOK
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "TypeOK", 10, 1);
        assert_eq!(analysis.operator_count, 4); // Init, Next, TypeOK, Safety
    }

    // -- Expression helpers --------------------------------------------------

    #[test]
    fn test_expr_contains_prime_positive() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        // Next contains priming
        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                if op.name.node == "Next" {
                    assert!(expr_contains_prime(&op.body.node));
                }
                if op.name.node == "Init" {
                    assert!(!expr_contains_prime(&op.body.node));
                }
            }
        }
    }

    // -- BFS reachability ----------------------------------------------------

    #[test]
    fn test_can_reach_direct() {
        let mut graph = DepGraph::new();
        graph.insert("A".to_string(), ["B".to_string()].into_iter().collect());
        graph.insert("B".to_string(), HashSet::new());
        assert!(can_reach(&graph, "A", "B"));
        assert!(!can_reach(&graph, "B", "A"));
    }

    #[test]
    fn test_can_reach_transitive() {
        let mut graph = DepGraph::new();
        graph.insert("A".to_string(), ["B".to_string()].into_iter().collect());
        graph.insert("B".to_string(), ["C".to_string()].into_iter().collect());
        graph.insert("C".to_string(), HashSet::new());
        assert!(can_reach(&graph, "A", "C"));
        assert!(!can_reach(&graph, "C", "A"));
    }

    #[test]
    fn test_can_reach_cycle_terminates() {
        let mut graph = DepGraph::new();
        graph.insert("A".to_string(), ["B".to_string()].into_iter().collect());
        graph.insert("B".to_string(), ["A".to_string()].into_iter().collect());
        // Should terminate even with a cycle, returning false for unreachable target
        assert!(!can_reach(&graph, "A", "C"));
    }

    // -- offset_to_line_col --------------------------------------------------

    #[test]
    fn test_offset_to_line_col_basic() {
        let source = "line1\nline2\nline3\n";
        let starts = line_starts(source);
        assert_eq!(offset_to_line_col(0, &starts), (1, 1));
        assert_eq!(offset_to_line_col(6, &starts), (2, 1));
        assert_eq!(offset_to_line_col(8, &starts), (2, 3));
    }

    // -- Enum equality -------------------------------------------------------

    #[test]
    fn test_format_enum_equality() {
        assert_eq!(WitnessOutputFormat::Human, WitnessOutputFormat::Human);
        assert_ne!(WitnessOutputFormat::Human, WitnessOutputFormat::Json);
    }

    // -- Status messages -----------------------------------------------------

    #[test]
    fn test_status_message_target_not_found() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "Bogus", 10, 1);
        let msg = build_status_message(&analysis, "target_not_found");
        assert!(msg.contains("Bogus"));
        assert!(msg.contains("not found"));
    }

    #[test]
    fn test_status_message_analysis_complete() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TypeOK == x \in Nat
===="#,
        );
        let analysis = analyze_witness_feasibility(&module, &default_cfg(), "TypeOK", 10, 1);
        let msg = build_status_message(&analysis, "analysis_complete");
        assert!(msg.contains("TypeOK"));
        assert!(msg.contains("complete"));
    }

    // -- collect_all_idents --------------------------------------------------

    #[test]
    fn test_collect_all_idents_from_conjunction() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y
===="#,
        );
        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                if op.name.node == "Init" {
                    let idents = collect_all_idents(&op.body.node);
                    assert!(idents.contains("x"), "should find x in Init body");
                    assert!(idents.contains("y"), "should find y in Init body");
                }
            }
        }
    }
}
