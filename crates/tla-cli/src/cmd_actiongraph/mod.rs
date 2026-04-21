// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 action-graph` -- action dependency and conflict analysis for TLA+ specifications.
//!
//! Analyzes the Next-state relation's disjuncts (actions) to build an action dependency
//! graph showing which actions enable/disable, conflict with, or are independent of each
//! other. Independent actions are candidates for partial-order reduction (POR) ample sets.
//!
//! # Analysis phases
//!
//! 1. **Parse** the TLA+ spec and config to identify the Next operator.
//! 2. **Decompose** Next into its top-level disjuncts (actions).
//! 3. **Analyze** each action for variable reads (guard/enabling condition),
//!    variable writes (primed assignments), and UNCHANGED declarations.
//! 4. **Build** inter-action relationships: conflict, dependency, independence.
//! 5. **Detect** cycles in the dependency graph (potential livelock patterns).
//! 6. **Output** in human-readable, JSON, or DOT format.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{Expr, ExprLabel, Module, OperatorDef, Unit};
use tla_core::{
    lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId, SyntaxNode,
};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Output format for the action graph command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ActionGraphOutputFormat {
    Human,
    Json,
    Dot,
}

/// Entry point for `tla2 action-graph`.
pub(crate) fn cmd_action_graph(
    file: &Path,
    config: Option<&Path>,
    format: ActionGraphOutputFormat,
) -> Result<()> {
    let source = read_source(file)?;

    // Parse source into CST.
    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diag = parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diag.eprint(&file_path, &source);
        }
        bail!(
            "action-graph aborted: {} parse error(s)",
            parse_result.errors.len()
        );
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

    // Lower CST -> AST.
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
            "action-graph aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("action-graph: lowering produced no module")?;

    // Resolve config to find the Next operator name.
    let next_name = resolve_next_name(file, config);

    // Collect all state variables declared in the module.
    let state_vars = collect_state_variables(&module);

    // Build an operator lookup table for inline expansion.
    let op_table = build_operator_table(&module);

    // Decompose the Next operator into individual actions.
    let actions = decompose_next(&module, &next_name, &op_table);
    if actions.is_empty() {
        bail!(
            "action-graph: no actions found (operator `{next_name}` not found or has no disjuncts)"
        );
    }

    // Analyze each action's variable reads, writes, and unchanged sets.
    let analyzed: Vec<AnalyzedAction> = actions
        .iter()
        .map(|a| analyze_action(a, &state_vars, &op_table))
        .collect();

    // Build inter-action relationships.
    let graph = build_action_graph(&analyzed, &state_vars);

    // Output.
    let file_path = file.display().to_string();
    match format {
        ActionGraphOutputFormat::Human => emit_human(&file_path, &analyzed, &graph, &state_vars),
        ActionGraphOutputFormat::Json => emit_json(&file_path, &analyzed, &graph, &state_vars)?,
        ActionGraphOutputFormat::Dot => emit_dot(&file_path, &analyzed, &graph),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Core data types
// ---------------------------------------------------------------------------

/// A named action extracted from the Next-state relation.
struct RawAction {
    /// Name of the action (label, operator name, or synthesized index).
    name: String,
    /// The expression body of this action.
    body: Expr,
}

/// An action with analyzed variable usage.
struct AnalyzedAction {
    /// Display name for this action.
    name: String,
    /// Variables read in guards / enabling conditions (unprimed references).
    reads: BTreeSet<String>,
    /// Variables written (primed assignments).
    writes: BTreeSet<String>,
    /// Variables declared UNCHANGED.
    unchanged: BTreeSet<String>,
}

/// Inter-action relationship type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum RelationKind {
    /// Two actions write the same variable.
    Conflict,
    /// Action A writes a variable that action B reads.
    Dependency,
}

/// A directed edge in the action graph.
#[derive(Debug, Clone)]
struct ActionEdge {
    from: usize,
    to: usize,
    kind: RelationKind,
    /// The variables that caused this relationship.
    shared_vars: BTreeSet<String>,
}

/// The complete action graph analysis result.
struct ActionGraph {
    /// Directed edges (dependency: from writes what to reads; conflict: bidirectional).
    edges: Vec<ActionEdge>,
    /// Pairs of actions that are fully independent (no shared variables).
    independent_pairs: Vec<(usize, usize)>,
    /// Cycles detected in the dependency subgraph.
    cycles: Vec<Vec<usize>>,
    /// For each variable, which actions write it.
    var_writers: BTreeMap<String, Vec<usize>>,
    /// For each variable, which actions read it.
    var_readers: BTreeMap<String, Vec<usize>>,
}

// ---------------------------------------------------------------------------
// Config resolution
// ---------------------------------------------------------------------------

/// Resolve the Next operator name from the config file, defaulting to "Next".
fn resolve_next_name(file: &Path, config_path: Option<&Path>) -> String {
    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    if !config_path_buf.exists() {
        return "Next".to_string();
    }

    let source = match std::fs::read_to_string(&config_path_buf) {
        Ok(s) => s,
        Err(_) => return "Next".to_string(),
    };

    match tla_check::Config::parse(&source) {
        Ok(config) => config.next.unwrap_or_else(|| "Next".to_string()),
        Err(_) => "Next".to_string(),
    }
}

// ---------------------------------------------------------------------------
// State variable collection
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

// ---------------------------------------------------------------------------
// Operator table for inline expansion
// ---------------------------------------------------------------------------

/// Builds a name -> OperatorDef lookup for resolving operator references.
fn build_operator_table(module: &Module) -> HashMap<String, OperatorDef> {
    let mut table = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            table.insert(op.name.node.clone(), op.clone());
        }
    }
    table
}

// ---------------------------------------------------------------------------
// Next decomposition into disjuncts
// ---------------------------------------------------------------------------

/// Decompose the Next operator into its top-level disjuncts (actions).
///
/// The decomposition follows TLA+ convention:
/// - `Next == A \/ B \/ C` yields actions A, B, C.
/// - If a disjunct is a bare operator reference `Apply(Ident(name), [])`,
///   we expand one level to get the action body and use the operator name.
/// - Labels (`P0:: expr`) provide explicit action names.
/// - Existential quantifiers wrapping disjunctions are expanded.
fn decompose_next(
    module: &Module,
    next_name: &str,
    op_table: &HashMap<String, OperatorDef>,
) -> Vec<RawAction> {
    // Find the Next operator definition.
    let next_op = module.units.iter().find_map(|u| match &u.node {
        Unit::Operator(op) if op.name.node == next_name => Some(op),
        _ => None,
    });

    let next_op = match next_op {
        Some(op) => op,
        None => return Vec::new(),
    };

    let mut actions = Vec::new();
    collect_disjuncts(&next_op.body.node, op_table, &mut actions, 0);

    // If no disjuncts found, treat the whole Next body as a single action.
    if actions.is_empty() {
        actions.push(RawAction {
            name: next_name.to_string(),
            body: next_op.body.node.clone(),
        });
    }

    actions
}

/// Recursively collect disjuncts from an expression.
///
/// `depth` prevents unbounded expansion of nested operator references.
fn collect_disjuncts(
    expr: &Expr,
    op_table: &HashMap<String, OperatorDef>,
    actions: &mut Vec<RawAction>,
    depth: usize,
) {
    const MAX_EXPAND_DEPTH: usize = 8;

    match expr {
        // A \/ B: split into sub-disjuncts.
        Expr::Or(lhs, rhs) => {
            collect_disjuncts(&lhs.node, op_table, actions, depth);
            collect_disjuncts(&rhs.node, op_table, actions, depth);
        }

        // Labels provide explicit action names.
        Expr::Label(ExprLabel { name, body }) => {
            // Check if the label body is itself a disjunction.
            if is_disjunction(&body.node) {
                collect_disjuncts(&body.node, op_table, actions, depth);
            } else {
                actions.push(RawAction {
                    name: name.node.clone(),
                    body: body.node.clone(),
                });
            }
        }

        // \E x \in S : body — common pattern for parameterized actions.
        // We name the action "Exists_<index>" and keep the full body.
        Expr::Exists(_, body) => {
            if is_disjunction(&body.node) {
                collect_disjuncts(&body.node, op_table, actions, depth);
            } else {
                let idx = actions.len();
                actions.push(RawAction {
                    name: format!("Exists_{idx}"),
                    body: expr.clone(),
                });
            }
        }

        // Bare operator application with no arguments: Op or Op()
        // Expand to the operator body to extract its name.
        Expr::Apply(func, args) if args.is_empty() && depth < MAX_EXPAND_DEPTH => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &func.node {
                if let Some(op_def) = op_table.get(name.as_str()) {
                    if op_def.params.is_empty() {
                        // Check if the operator body is a disjunction — if so,
                        // expand it so we get finer-grained actions.
                        if is_disjunction(&op_def.body.node) {
                            collect_disjuncts(
                                &op_def.body.node,
                                op_table,
                                actions,
                                depth + 1,
                            );
                        } else {
                            actions.push(RawAction {
                                name: name.clone(),
                                body: op_def.body.node.clone(),
                            });
                        }
                        return;
                    }
                }
            }
            // Fallthrough: non-expandable application.
            let idx = actions.len();
            actions.push(RawAction {
                name: format!("Action_{idx}"),
                body: expr.clone(),
            });
        }

        // Ident reference without Apply wrapper — also a common pattern.
        Expr::Ident(name, _) if depth < MAX_EXPAND_DEPTH => {
            if let Some(op_def) = op_table.get(name.as_str()) {
                if op_def.params.is_empty() {
                    if is_disjunction(&op_def.body.node) {
                        collect_disjuncts(&op_def.body.node, op_table, actions, depth + 1);
                    } else {
                        actions.push(RawAction {
                            name: name.clone(),
                            body: op_def.body.node.clone(),
                        });
                    }
                    return;
                }
            }
            actions.push(RawAction {
                name: name.clone(),
                body: expr.clone(),
            });
        }

        // Any other expression is a leaf action.
        _ => {
            let idx = actions.len();
            actions.push(RawAction {
                name: format!("Action_{idx}"),
                body: expr.clone(),
            });
        }
    }
}

/// Returns true if the expression is a top-level disjunction.
fn is_disjunction(expr: &Expr) -> bool {
    matches!(expr, Expr::Or(_, _))
}

// ---------------------------------------------------------------------------
// Variable usage analysis per action
// ---------------------------------------------------------------------------

/// Analyze a single action to determine its read, write, and unchanged variable sets.
fn analyze_action(
    action: &RawAction,
    state_vars: &[String],
    op_table: &HashMap<String, OperatorDef>,
) -> AnalyzedAction {
    let var_set: HashSet<&str> = state_vars.iter().map(|s| s.as_str()).collect();
    let mut collector = VarCollector {
        reads: BTreeSet::new(),
        writes: BTreeSet::new(),
        unchanged: BTreeSet::new(),
        state_vars: &var_set,
        in_prime: false,
        in_unchanged: false,
        bound_names: Vec::new(),
        op_table,
        visited_ops: HashSet::new(),
    };
    collector.visit(&action.body);

    AnalyzedAction {
        name: action.name.clone(),
        reads: collector.reads,
        writes: collector.writes,
        unchanged: collector.unchanged,
    }
}

/// AST visitor that collects variable reads, writes, and UNCHANGED declarations.
struct VarCollector<'a> {
    reads: BTreeSet<String>,
    writes: BTreeSet<String>,
    unchanged: BTreeSet<String>,
    state_vars: &'a HashSet<&'a str>,
    in_prime: bool,
    in_unchanged: bool,
    bound_names: Vec<String>,
    op_table: &'a HashMap<String, OperatorDef>,
    /// Prevents infinite recursion in RECURSIVE operators.
    visited_ops: HashSet<String>,
}

impl<'a> VarCollector<'a> {
    fn visit(&mut self, expr: &Expr) {
        match expr {
            // State variable reference (pre-resolved).
            Expr::StateVar(name, _, _) => {
                if self.state_vars.contains(name.as_str())
                    && !self.is_bound(name)
                {
                    if self.in_prime {
                        self.writes.insert(name.clone());
                    } else if self.in_unchanged {
                        self.unchanged.insert(name.clone());
                    } else {
                        self.reads.insert(name.clone());
                    }
                }
            }

            // Identifier reference (may be a state variable before resolution).
            Expr::Ident(name, _) => {
                if self.state_vars.contains(name.as_str())
                    && !self.is_bound(name)
                {
                    if self.in_prime {
                        self.writes.insert(name.clone());
                    } else if self.in_unchanged {
                        self.unchanged.insert(name.clone());
                    } else {
                        self.reads.insert(name.clone());
                    }
                }
            }

            // Prime: x' — marks enclosed variable references as writes.
            Expr::Prime(inner) => {
                let was_prime = self.in_prime;
                self.in_prime = true;
                self.visit(&inner.node);
                self.in_prime = was_prime;
            }

            // UNCHANGED <<x, y, z>> or UNCHANGED var.
            Expr::Unchanged(inner) => {
                let was_unchanged = self.in_unchanged;
                self.in_unchanged = true;
                self.visit_unchanged_body(&inner.node);
                self.in_unchanged = was_unchanged;
            }

            // Quantifiers: introduce bound variables to avoid false positives.
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                for bv in bounds {
                    if let Some(d) = &bv.domain {
                        self.visit(&d.node);
                    }
                    self.bound_names.push(bv.name.node.clone());
                }
                self.visit(&body.node);
                for _ in bounds {
                    self.bound_names.pop();
                }
            }

            // CHOOSE x \in S : P
            Expr::Choose(bv, body) => {
                if let Some(d) = &bv.domain {
                    self.visit(&d.node);
                }
                self.bound_names.push(bv.name.node.clone());
                self.visit(&body.node);
                self.bound_names.pop();
            }

            // Set builder / function def introduce bound variables.
            Expr::SetBuilder(body, bounds) | Expr::FuncDef(bounds, body) => {
                for bv in bounds {
                    if let Some(d) = &bv.domain {
                        self.visit(&d.node);
                    }
                    self.bound_names.push(bv.name.node.clone());
                }
                self.visit(&body.node);
                for _ in bounds {
                    self.bound_names.pop();
                }
            }

            // Set filter: {x \in S : P}
            Expr::SetFilter(bv, body) => {
                if let Some(d) = &bv.domain {
                    self.visit(&d.node);
                }
                self.bound_names.push(bv.name.node.clone());
                self.visit(&body.node);
                self.bound_names.pop();
            }

            // LET definitions introduce local names.
            Expr::Let(defs, body) => {
                for def in defs {
                    self.visit(&def.body.node);
                    self.bound_names.push(def.name.node.clone());
                }
                self.visit(&body.node);
                for _ in defs {
                    self.bound_names.pop();
                }
            }

            // Lambda introduces bound variable names.
            Expr::Lambda(params, body) => {
                for p in params {
                    self.bound_names.push(p.node.clone());
                }
                self.visit(&body.node);
                for _ in params {
                    self.bound_names.pop();
                }
            }

            // Operator application — expand zero-arity operators one level.
            Expr::Apply(func, args) => {
                // Visit arguments first (they may contain variable refs).
                for arg in args {
                    self.visit(&arg.node);
                }
                // If it is a zero-arity call to a known operator, inline its body.
                if args.is_empty() {
                    if let Expr::Ident(name, _) = &func.node {
                        if let Some(op_def) = self.op_table.get(name.as_str()) {
                            if op_def.params.is_empty()
                                && !self.visited_ops.contains(name.as_str())
                            {
                                self.visited_ops.insert(name.clone());
                                self.visit(&op_def.body.node);
                                return;
                            }
                        }
                    }
                }
                // Visit the function expression itself.
                self.visit(&func.node);
            }

            // Labels: unwrap and visit body.
            Expr::Label(label) => {
                self.visit(&label.body.node);
            }

            // SubstIn: visit the body (substitutions are handled at eval time).
            Expr::SubstIn(_, body) => {
                self.visit(&body.node);
            }

            // IF-THEN-ELSE: condition is a guard (read), branches may write.
            Expr::If(cond, then_, else_) => {
                self.visit(&cond.node);
                self.visit(&then_.node);
                self.visit(&else_.node);
            }

            // CASE: guards are reads, bodies may write.
            Expr::Case(arms, other) => {
                for arm in arms {
                    self.visit(&arm.guard.node);
                    self.visit(&arm.body.node);
                }
                if let Some(o) = other {
                    self.visit(&o.node);
                }
            }

            // All other expressions: structural traversal.
            _ => {
                visit_expr_children(expr, |child| self.visit(child));
            }
        }
    }

    /// Visit the body of an UNCHANGED expression to extract variable names.
    ///
    /// UNCHANGED <<x, y, z>> produces a Tuple of variable references.
    /// UNCHANGED x produces a single variable reference.
    fn visit_unchanged_body(&mut self, expr: &Expr) {
        match expr {
            Expr::Tuple(elems) => {
                for elem in elems {
                    self.visit_unchanged_body(&elem.node);
                }
            }
            Expr::StateVar(name, _, _) | Expr::Ident(name, _) => {
                if self.state_vars.contains(name.as_str()) && !self.is_bound(name) {
                    self.unchanged.insert(name.clone());
                }
            }
            _ => {
                // Fallback: treat as a normal expression in unchanged context.
                self.visit(expr);
            }
        }
    }

    /// Check if a name is bound by a quantifier or LET definition.
    fn is_bound(&self, name: &str) -> bool {
        self.bound_names.iter().any(|b| b == name)
    }
}

// ---------------------------------------------------------------------------
// Expression visitor helper (structural child traversal)
// ---------------------------------------------------------------------------

/// Visit all direct child expressions of an Expr node, calling `f` on each.
/// This mirrors the visitor in cmd_stats to ensure complete coverage.
fn visit_expr_children(expr: &Expr, mut f: impl FnMut(&Expr)) {
    match expr {
        // Leaves — no children.
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_)
        | Expr::InstanceExpr(_, _) => {}

        // Unary.
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

        // Binary.
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

        // Apply.
        Expr::Apply(func, args) => {
            f(&func.node);
            for arg in args {
                f(&arg.node);
            }
        }

        // Lambda.
        Expr::Lambda(_, body) => {
            f(&body.node);
        }

        // Label.
        Expr::Label(label) => {
            f(&label.body.node);
        }

        // ModuleRef.
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

        // Quantifiers.
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

        // Collections.
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

        // Records.
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, val) in fields {
                f(&val.node);
            }
        }

        Expr::RecordAccess(base, _) => {
            f(&base.node);
        }

        // Except.
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

        // Control.
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
// Action graph construction
// ---------------------------------------------------------------------------

/// Build the action graph from analyzed actions.
///
/// Relationships:
/// - **Conflict**: actions i and j both write the same variable.
/// - **Dependency**: action i writes a variable that action j reads.
/// - **Independence**: actions i and j share no variables at all (POR candidates).
fn build_action_graph(actions: &[AnalyzedAction], state_vars: &[String]) -> ActionGraph {
    let n = actions.len();
    let mut edges = Vec::new();
    let mut independent_pairs = Vec::new();

    // Build per-variable writer/reader indexes.
    let mut var_writers: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    let mut var_readers: BTreeMap<String, Vec<usize>> = BTreeMap::new();

    for (i, action) in actions.iter().enumerate() {
        for var in &action.writes {
            var_writers.entry(var.clone()).or_default().push(i);
        }
        // UNCHANGED variables are effectively writes (they constrain the successor state).
        for var in &action.unchanged {
            var_writers.entry(var.clone()).or_default().push(i);
        }
        for var in &action.reads {
            var_readers.entry(var.clone()).or_default().push(i);
        }
    }

    // Build adjacency sets for conflict and dependency edges.
    // Use sets to avoid duplicate edges.
    let mut conflict_pairs: HashSet<(usize, usize)> = HashSet::new();
    let mut dep_edges: HashSet<(usize, usize)> = HashSet::new();

    // Conflicts: both actions write the same variable.
    for var in state_vars {
        if let Some(writers) = var_writers.get(var) {
            for (wi, &i) in writers.iter().enumerate() {
                for &j in &writers[wi + 1..] {
                    let key = if i < j { (i, j) } else { (j, i) };
                    if conflict_pairs.insert(key) {
                        let mut shared = BTreeSet::new();
                        shared.insert(var.clone());
                        edges.push(ActionEdge {
                            from: key.0,
                            to: key.1,
                            kind: RelationKind::Conflict,
                            shared_vars: shared,
                        });
                    } else {
                        // Add the variable to the existing conflict edge.
                        for edge in edges.iter_mut().rev() {
                            if edge.from == key.0
                                && edge.to == key.1
                                && edge.kind == RelationKind::Conflict
                            {
                                edge.shared_vars.insert(var.clone());
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    // Dependencies: action i writes what action j reads (directed).
    for var in state_vars {
        let writers = match var_writers.get(var) {
            Some(w) => w,
            None => continue,
        };
        let readers = match var_readers.get(var) {
            Some(r) => r,
            None => continue,
        };

        for &writer in writers {
            for &reader in readers {
                if writer == reader {
                    continue;
                }
                if dep_edges.insert((writer, reader)) {
                    let mut shared = BTreeSet::new();
                    shared.insert(var.clone());
                    edges.push(ActionEdge {
                        from: writer,
                        to: reader,
                        kind: RelationKind::Dependency,
                        shared_vars: shared,
                    });
                } else {
                    // Add the variable to the existing dependency edge.
                    for edge in edges.iter_mut().rev() {
                        if edge.from == writer
                            && edge.to == reader
                            && edge.kind == RelationKind::Dependency
                        {
                            edge.shared_vars.insert(var.clone());
                            break;
                        }
                    }
                }
            }
        }
    }

    // Independence: pairs with no shared variables at all.
    for i in 0..n {
        for j in (i + 1)..n {
            let a = &actions[i];
            let b = &actions[j];

            let a_all_vars: BTreeSet<&String> =
                a.reads.iter().chain(&a.writes).chain(&a.unchanged).collect();
            let b_all_vars: BTreeSet<&String> =
                b.reads.iter().chain(&b.writes).chain(&b.unchanged).collect();

            let has_overlap = a_all_vars.iter().any(|v| b_all_vars.contains(v));
            if !has_overlap {
                independent_pairs.push((i, j));
            }
        }
    }

    // Cycle detection on the dependency subgraph.
    let cycles = detect_dependency_cycles(n, &edges);

    ActionGraph {
        edges,
        independent_pairs,
        cycles,
        var_writers,
        var_readers,
    }
}

// ---------------------------------------------------------------------------
// Cycle detection (DFS-based)
// ---------------------------------------------------------------------------

/// Detect cycles in the dependency subgraph using iterative DFS with coloring.
///
/// Returns cycles as sequences of action indices. Only dependency edges are
/// considered (conflicts are symmetric and don't form meaningful cycles).
fn detect_dependency_cycles(num_actions: usize, edges: &[ActionEdge]) -> Vec<Vec<usize>> {
    // Build adjacency list from dependency edges only.
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); num_actions];
    for edge in edges {
        if edge.kind == RelationKind::Dependency {
            adj[edge.from].push(edge.to);
        }
    }

    let mut cycles = Vec::new();

    // Standard 3-color DFS cycle detection.
    // White=0, Gray=1, Black=2
    let mut color = vec![0u8; num_actions];
    let mut parent = vec![usize::MAX; num_actions];

    for start in 0..num_actions {
        if color[start] != 0 {
            continue;
        }

        let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
        color[start] = 1;

        while let Some((node, neighbor_idx)) = stack.last_mut() {
            let node = *node;
            if *neighbor_idx < adj[node].len() {
                let next = adj[node][*neighbor_idx];
                *neighbor_idx += 1;

                if color[next] == 0 {
                    // Unvisited: push onto DFS stack.
                    color[next] = 1;
                    parent[next] = node;
                    stack.push((next, 0));
                } else if color[next] == 1 {
                    // Back edge: found a cycle. Reconstruct it.
                    let mut cycle = vec![next];
                    let mut cur = node;
                    while cur != next && cur != usize::MAX {
                        cycle.push(cur);
                        cur = parent[cur];
                    }
                    cycle.reverse();
                    // Only keep short cycles (limit to avoid combinatorial explosion).
                    if cycle.len() <= 10 {
                        cycles.push(cycle);
                    }
                    // Limit total cycles reported.
                    if cycles.len() >= 50 {
                        return cycles;
                    }
                }
                // Gray or black with no new cycle: continue.
            } else {
                // Done with this node: mark black and pop.
                color[node] = 2;
                stack.pop();
            }
        }
    }

    cycles
}

// ---------------------------------------------------------------------------
// Output: Human-readable
// ---------------------------------------------------------------------------

fn emit_human(
    file_path: &str,
    actions: &[AnalyzedAction],
    graph: &ActionGraph,
    state_vars: &[String],
) {
    println!("Action Dependency Graph: {file_path}");
    println!("{}", "=".repeat(64));

    // State variables summary.
    println!();
    println!("  State Variables ({}):", state_vars.len());
    if state_vars.is_empty() {
        println!("    (none)");
    } else {
        println!("    {}", state_vars.join(", "));
    }

    // Per-action summary.
    println!();
    println!("  Actions ({}):", actions.len());
    println!("  {}", "-".repeat(58));
    for (i, action) in actions.iter().enumerate() {
        println!();
        println!("  [{i}] {}", action.name);
        if !action.reads.is_empty() {
            let vars: Vec<&str> = action.reads.iter().map(|s| s.as_str()).collect();
            println!("      Reads:     {}", vars.join(", "));
        }
        if !action.writes.is_empty() {
            let vars: Vec<&str> = action.writes.iter().map(|s| s.as_str()).collect();
            println!("      Writes:    {}", vars.join(", "));
        }
        if !action.unchanged.is_empty() {
            let vars: Vec<&str> = action.unchanged.iter().map(|s| s.as_str()).collect();
            println!("      Unchanged: {}", vars.join(", "));
        }
        if action.reads.is_empty() && action.writes.is_empty() && action.unchanged.is_empty() {
            println!("      (no variable references detected)");
        }
    }

    // Conflict edges.
    let conflicts: Vec<&ActionEdge> = graph
        .edges
        .iter()
        .filter(|e| e.kind == RelationKind::Conflict)
        .collect();
    println!();
    println!("  Conflicts ({}):", conflicts.len());
    println!("  {}", "-".repeat(58));
    if conflicts.is_empty() {
        println!("    (none)");
    } else {
        for edge in &conflicts {
            let vars: Vec<&str> = edge.shared_vars.iter().map(|s| s.as_str()).collect();
            println!(
                "    {} <-> {} : write-write on {{{}}}",
                actions[edge.from].name,
                actions[edge.to].name,
                vars.join(", ")
            );
        }
    }

    // Dependency edges.
    let deps: Vec<&ActionEdge> = graph
        .edges
        .iter()
        .filter(|e| e.kind == RelationKind::Dependency)
        .collect();
    println!();
    println!("  Dependencies ({}):", deps.len());
    println!("  {}", "-".repeat(58));
    if deps.is_empty() {
        println!("    (none)");
    } else {
        for edge in &deps {
            let vars: Vec<&str> = edge.shared_vars.iter().map(|s| s.as_str()).collect();
            println!(
                "    {} --> {} : writes {{{}}} that it reads",
                actions[edge.from].name,
                actions[edge.to].name,
                vars.join(", ")
            );
        }
    }

    // Independent pairs (POR candidates).
    println!();
    println!(
        "  Independent Pairs ({}) [POR ample set candidates]:",
        graph.independent_pairs.len()
    );
    println!("  {}", "-".repeat(58));
    if graph.independent_pairs.is_empty() {
        println!("    (none -- all action pairs share at least one variable)");
    } else {
        for (i, j) in &graph.independent_pairs {
            println!("    {} <=> {}", actions[*i].name, actions[*j].name);
        }
    }

    // Cycles (potential livelock).
    println!();
    println!(
        "  Dependency Cycles ({}) [potential livelock]:",
        graph.cycles.len()
    );
    println!("  {}", "-".repeat(58));
    if graph.cycles.is_empty() {
        println!("    (none -- dependency graph is acyclic)");
    } else {
        for (ci, cycle) in graph.cycles.iter().enumerate() {
            let names: Vec<&str> = cycle.iter().map(|&idx| actions[idx].name.as_str()).collect();
            println!("    Cycle {ci}: {} -> {}", names.join(" -> "), names[0]);
        }
    }

    // Variable coverage summary.
    println!();
    println!("  Variable Coverage:");
    println!("  {}", "-".repeat(58));
    for var in state_vars {
        let writers = graph
            .var_writers
            .get(var)
            .map(|v| v.len())
            .unwrap_or(0);
        let readers = graph
            .var_readers
            .get(var)
            .map(|v| v.len())
            .unwrap_or(0);
        let writer_names: Vec<&str> = graph
            .var_writers
            .get(var)
            .map(|idxs| idxs.iter().map(|&i| actions[i].name.as_str()).collect())
            .unwrap_or_default();
        let reader_names: Vec<&str> = graph
            .var_readers
            .get(var)
            .map(|idxs| idxs.iter().map(|&i| actions[i].name.as_str()).collect())
            .unwrap_or_default();

        println!("    {var}:");
        println!(
            "      Writers ({writers}): {}",
            if writer_names.is_empty() {
                "(none)".to_string()
            } else {
                writer_names.join(", ")
            }
        );
        println!(
            "      Readers ({readers}): {}",
            if reader_names.is_empty() {
                "(none)".to_string()
            } else {
                reader_names.join(", ")
            }
        );
    }

    println!();
}

// ---------------------------------------------------------------------------
// Output: JSON
// ---------------------------------------------------------------------------

fn emit_json(
    file_path: &str,
    actions: &[AnalyzedAction],
    graph: &ActionGraph,
    state_vars: &[String],
) -> Result<()> {
    let actions_json: Vec<serde_json::Value> = actions
        .iter()
        .enumerate()
        .map(|(i, a)| {
            serde_json::json!({
                "index": i,
                "name": a.name,
                "reads": a.reads.iter().collect::<Vec<_>>(),
                "writes": a.writes.iter().collect::<Vec<_>>(),
                "unchanged": a.unchanged.iter().collect::<Vec<_>>(),
            })
        })
        .collect();

    let edges_json: Vec<serde_json::Value> = graph
        .edges
        .iter()
        .map(|e| {
            let kind_str = match e.kind {
                RelationKind::Conflict => "conflict",
                RelationKind::Dependency => "dependency",
            };
            serde_json::json!({
                "from": e.from,
                "from_name": actions[e.from].name,
                "to": e.to,
                "to_name": actions[e.to].name,
                "kind": kind_str,
                "shared_vars": e.shared_vars.iter().collect::<Vec<_>>(),
            })
        })
        .collect();

    let independent_json: Vec<serde_json::Value> = graph
        .independent_pairs
        .iter()
        .map(|(i, j)| {
            serde_json::json!({
                "action_a": *i,
                "name_a": actions[*i].name,
                "action_b": *j,
                "name_b": actions[*j].name,
            })
        })
        .collect();

    let cycles_json: Vec<serde_json::Value> = graph
        .cycles
        .iter()
        .map(|cycle| {
            let names: Vec<&str> = cycle.iter().map(|&idx| actions[idx].name.as_str()).collect();
            serde_json::json!({
                "indices": cycle,
                "names": names,
            })
        })
        .collect();

    let var_coverage: Vec<serde_json::Value> = state_vars
        .iter()
        .map(|var| {
            let writer_names: Vec<&str> = graph
                .var_writers
                .get(var)
                .map(|idxs| idxs.iter().map(|&i| actions[i].name.as_str()).collect())
                .unwrap_or_default();
            let reader_names: Vec<&str> = graph
                .var_readers
                .get(var)
                .map(|idxs| idxs.iter().map(|&i| actions[i].name.as_str()).collect())
                .unwrap_or_default();
            serde_json::json!({
                "variable": var,
                "writers": writer_names,
                "readers": reader_names,
            })
        })
        .collect();

    let output = serde_json::json!({
        "file": file_path,
        "state_variables": state_vars,
        "actions": actions_json,
        "edges": edges_json,
        "independent_pairs": independent_json,
        "cycles": cycles_json,
        "variable_coverage": var_coverage,
        "summary": {
            "num_actions": actions.len(),
            "num_state_variables": state_vars.len(),
            "num_conflicts": graph.edges.iter().filter(|e| e.kind == RelationKind::Conflict).count(),
            "num_dependencies": graph.edges.iter().filter(|e| e.kind == RelationKind::Dependency).count(),
            "num_independent_pairs": graph.independent_pairs.len(),
            "num_cycles": graph.cycles.len(),
        },
    });

    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}

// ---------------------------------------------------------------------------
// Output: DOT (Graphviz)
// ---------------------------------------------------------------------------

fn emit_dot(file_path: &str, actions: &[AnalyzedAction], graph: &ActionGraph) {
    println!("// Action dependency graph for {file_path}");
    println!("// Generated by tla2 action-graph");
    println!("digraph action_graph {{");
    println!("    rankdir=LR;");
    println!("    node [shape=box, style=filled, fontname=\"Helvetica\"];");
    println!();

    // Emit action nodes with tooltips showing variable usage.
    for (i, action) in actions.iter().enumerate() {
        let reads_str = if action.reads.is_empty() {
            String::new()
        } else {
            format!(
                "reads: {{{}}}",
                action
                    .reads
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let writes_str = if action.writes.is_empty() {
            String::new()
        } else {
            format!(
                "writes: {{{}}}",
                action
                    .writes
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let unchanged_str = if action.unchanged.is_empty() {
            String::new()
        } else {
            format!(
                "unchanged: {{{}}}",
                action
                    .unchanged
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };

        let tooltip_parts: Vec<&str> = [
            reads_str.as_str(),
            writes_str.as_str(),
            unchanged_str.as_str(),
        ]
        .iter()
        .filter(|s| !s.is_empty())
        .copied()
        .collect();
        let tooltip = if tooltip_parts.is_empty() {
            "(no variables)".to_string()
        } else {
            tooltip_parts.join("\\n")
        };

        let color = if action.writes.is_empty() && action.unchanged.is_empty() {
            "#d4edda" // Green-ish: read-only action
        } else if action.reads.is_empty() {
            "#fff3cd" // Yellow-ish: write-only action
        } else {
            "#cce5ff" // Blue-ish: read-write action
        };

        let escaped_name = dot_escape(&action.name);
        println!(
            "    a{i} [label=\"{escaped_name}\", fillcolor=\"{color}\", tooltip=\"{tooltip}\"];",
        );
    }

    println!();

    // Emit conflict edges (red, undirected via dir=none).
    let mut emitted_conflicts = HashSet::new();
    for edge in &graph.edges {
        if edge.kind == RelationKind::Conflict {
            let key = if edge.from < edge.to {
                (edge.from, edge.to)
            } else {
                (edge.to, edge.from)
            };
            if emitted_conflicts.insert(key) {
                let vars: Vec<&str> = edge.shared_vars.iter().map(|s| s.as_str()).collect();
                let label = vars.join(", ");
                println!(
                    "    a{} -> a{} [color=\"#dc3545\", style=bold, dir=none, \
                     label=\"{}\", fontcolor=\"#dc3545\", fontsize=9];",
                    key.0, key.1, label
                );
            }
        }
    }

    // Emit dependency edges (blue, directed).
    for edge in &graph.edges {
        if edge.kind == RelationKind::Dependency {
            let vars: Vec<&str> = edge.shared_vars.iter().map(|s| s.as_str()).collect();
            let label = vars.join(", ");
            println!(
                "    a{} -> a{} [color=\"#007bff\", label=\"{}\", \
                 fontcolor=\"#007bff\", fontsize=9];",
                edge.from, edge.to, label
            );
        }
    }

    // Emit independence edges (green, dashed, undirected).
    if !graph.independent_pairs.is_empty() {
        println!();
        println!("    // Independent pairs (POR candidates)");
        for (i, j) in &graph.independent_pairs {
            println!(
                "    a{i} -> a{j} [color=\"#28a745\", style=dashed, dir=none, \
                 constraint=false];",
            );
        }
    }

    // Legend subgraph.
    println!();
    println!("    subgraph cluster_legend {{");
    println!("        label=\"Legend\";");
    println!("        style=dashed;");
    println!("        fontsize=10;");
    println!(
        "        l1 [shape=plaintext, label=\"Red (bold): write-write conflict\"];"
    );
    println!(
        "        l2 [shape=plaintext, label=\"Blue (arrow): write-read dependency\"];"
    );
    println!(
        "        l3 [shape=plaintext, label=\"Green (dashed): independent (POR)\"];"
    );
    println!("        l1 -> l2 -> l3 [style=invis];");
    println!("    }}");

    println!("}}");
}

/// Escape a string for use in DOT labels.
fn dot_escape(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
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
    fn test_decompose_simple_disjunction() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
A == x' = x + 1 /\ UNCHANGED y
B == y' = y + 1 /\ UNCHANGED x
Next == A \/ B
===="#,
        );
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        assert_eq!(actions.len(), 2, "expected 2 actions from A \\/ B");
        assert_eq!(actions[0].name, "A");
        assert_eq!(actions[1].name, "B");
    }

    #[test]
    fn test_decompose_three_disjuncts() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = 1 \/ x' = 2 \/ x' = 3
===="#,
        );
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        assert_eq!(actions.len(), 3, "expected 3 inline disjuncts");
    }

    #[test]
    fn test_analyze_reads_writes_unchanged() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y, z
Init == x = 0 /\ y = 0 /\ z = 0
A == x' = y + 1 /\ UNCHANGED <<y, z>>
Next == A
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        assert_eq!(actions.len(), 1);

        let analyzed = analyze_action(&actions[0], &state_vars, &op_table);
        assert_eq!(analyzed.name, "A");
        assert!(
            analyzed.reads.contains("y"),
            "A reads y in guard: {:?}",
            analyzed.reads
        );
        assert!(
            analyzed.writes.contains("x"),
            "A writes x: {:?}",
            analyzed.writes
        );
        assert!(
            analyzed.unchanged.contains("y"),
            "A has y unchanged: {:?}",
            analyzed.unchanged
        );
        assert!(
            analyzed.unchanged.contains("z"),
            "A has z unchanged: {:?}",
            analyzed.unchanged
        );
    }

    #[test]
    fn test_conflict_detection() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
A == x' = 1 /\ y' = 0
B == x' = 2 /\ y' = 1
Next == A \/ B
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        let analyzed: Vec<AnalyzedAction> = actions
            .iter()
            .map(|a| analyze_action(a, &state_vars, &op_table))
            .collect();
        let graph = build_action_graph(&analyzed, &state_vars);

        let conflicts: Vec<&ActionEdge> = graph
            .edges
            .iter()
            .filter(|e| e.kind == RelationKind::Conflict)
            .collect();
        assert!(
            !conflicts.is_empty(),
            "A and B both write x and y, should have conflicts"
        );
    }

    #[test]
    fn test_independence_detection() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
A == x' = x + 1 /\ UNCHANGED y
B == y' = y + 1 /\ UNCHANGED x
Next == A \/ B
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        let analyzed: Vec<AnalyzedAction> = actions
            .iter()
            .map(|a| analyze_action(a, &state_vars, &op_table))
            .collect();
        let graph = build_action_graph(&analyzed, &state_vars);

        // A writes x, reads x, UNCHANGED y
        // B writes y, reads y, UNCHANGED x
        // They are NOT independent because A UNCHANGED y overlaps with B UNCHANGED x...
        // Actually: A touches {x(rw), y(unchanged)}, B touches {y(rw), x(unchanged)}.
        // Both touch x and y via writes/unchanged, so they are NOT independent.
        assert!(
            graph.independent_pairs.is_empty(),
            "A touches y (unchanged) and B touches x (unchanged), so no independence"
        );
    }

    #[test]
    fn test_true_independence() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
A == x' = x + 1
B == y' = y + 1
Next == A \/ B
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        let analyzed: Vec<AnalyzedAction> = actions
            .iter()
            .map(|a| analyze_action(a, &state_vars, &op_table))
            .collect();
        let graph = build_action_graph(&analyzed, &state_vars);

        // A only touches x. B only touches y. No UNCHANGED clauses.
        // They are truly independent.
        assert_eq!(
            graph.independent_pairs.len(),
            1,
            "A and B should be independent: A touches only x, B touches only y"
        );
    }

    #[test]
    fn test_dependency_detection() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
A == x' = x + 1
B == y' = x
Next == A \/ B
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        let analyzed: Vec<AnalyzedAction> = actions
            .iter()
            .map(|a| analyze_action(a, &state_vars, &op_table))
            .collect();
        let graph = build_action_graph(&analyzed, &state_vars);

        let deps: Vec<&ActionEdge> = graph
            .edges
            .iter()
            .filter(|e| e.kind == RelationKind::Dependency)
            .collect();
        // A writes x, B reads x => dependency from A to B.
        assert!(
            deps.iter().any(|e| e.from == 0 && e.to == 1),
            "expected dependency from A (writes x) to B (reads x)"
        );
    }

    #[test]
    fn test_cycle_detection() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
A == x' = y
B == y' = x
Next == A \/ B
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        let analyzed: Vec<AnalyzedAction> = actions
            .iter()
            .map(|a| analyze_action(a, &state_vars, &op_table))
            .collect();
        let graph = build_action_graph(&analyzed, &state_vars);

        // A writes x, reads y. B writes y, reads x.
        // Dependency: A->B (A writes x, B reads x) and B->A (B writes y, A reads y).
        // This forms a cycle.
        assert!(
            !graph.cycles.is_empty(),
            "expected a cycle between A and B"
        );
    }

    #[test]
    fn test_empty_next() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
===="#,
        );
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        assert!(actions.is_empty(), "no Next operator should yield no actions");
    }

    #[test]
    fn test_existential_quantifier_wrapping() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
A == x' = 1
B == x' = 2
Next == \E n \in {1, 2} : (A \/ B)
===="#,
        );
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        // The exists wraps a disjunction, so we should get A and B.
        assert_eq!(actions.len(), 2, "expected 2 actions from exists-wrapped disjunction");
    }

    #[test]
    fn test_bound_variable_not_counted_as_state_var() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == \E n \in {1, 2, 3} : x' = n
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        assert_eq!(actions.len(), 1);

        let analyzed = analyze_action(&actions[0], &state_vars, &op_table);
        assert!(
            analyzed.writes.contains("x"),
            "should detect x as written"
        );
        // 'n' is bound by \E, should NOT appear as a state variable reference.
        assert!(
            !analyzed.reads.contains("n"),
            "bound variable n should not be in reads"
        );
        assert!(
            !analyzed.writes.contains("n"),
            "bound variable n should not be in writes"
        );
    }

    #[test]
    fn test_dot_escape() {
        assert_eq!(dot_escape("hello"), "hello");
        assert_eq!(dot_escape("a\"b"), "a\\\"b");
        assert_eq!(dot_escape("a\\b"), "a\\\\b");
    }

    #[test]
    fn test_single_action_no_disjunction() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        assert_eq!(actions.len(), 1, "single Next body should be one action");
    }

    #[test]
    fn test_variable_coverage_map() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y, z
Init == x = 0 /\ y = 0 /\ z = 0
A == x' = y + 1 /\ UNCHANGED <<y, z>>
B == y' = z + 1 /\ UNCHANGED <<x, z>>
Next == A \/ B
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        let analyzed: Vec<AnalyzedAction> = actions
            .iter()
            .map(|a| analyze_action(a, &state_vars, &op_table))
            .collect();
        let graph = build_action_graph(&analyzed, &state_vars);

        // x: written by A (direct write + B has UNCHANGED x)
        assert!(
            graph.var_writers.get("x").map(|v| v.len()).unwrap_or(0) >= 1,
            "x should have at least 1 writer"
        );
        // y: read by A, written by B, unchanged by A
        assert!(
            graph.var_readers.get("y").map(|v| v.len()).unwrap_or(0) >= 1,
            "y should have at least 1 reader"
        );
    }
}
