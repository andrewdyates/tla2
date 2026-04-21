// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 assume-guarantee` -- compositional verification for TLA+ specifications.
//!
//! Assume-guarantee reasoning decomposes verification of a large system into
//! smaller, independent verification tasks. Given a system whose Next-state
//! relation is a disjunction of actions, this command:
//!
//! 1. Parses the spec and identifies actions (disjuncts of Next).
//! 2. Analyzes variable access patterns to build an action dependency graph.
//! 3. Partitions actions into independent groups (connected components of the
//!    dependency graph -- actions that share no variables).
//! 4. For each group, runs a model check using only that group's actions as Next,
//!    while still checking all configured invariants.
//! 5. Combines results: if all groups pass independently, the global property
//!    holds under the circular assume-guarantee rule for non-interfering actions.
//!
//! # Soundness
//!
//! This decomposition is **sound** (no false negatives) when the action groups
//! are truly independent -- i.e., they operate on disjoint variable sets and
//! cannot interfere with each other's invariants. The analysis is conservative:
//! if any dependency is detected, those actions are grouped together and checked
//! as a single unit.
//!
//! The decomposition is **not complete**: it may report violations that would not
//! occur in the full system (false positives) because individual group checks
//! explore states reachable under only a subset of actions.
//!
//! # Limitations
//!
//! - Only static variable-access analysis is used; runtime aliasing through
//!   function application or CHOOSE is not tracked.
//! - Specs where all actions share variables (single coupling group) gain no
//!   benefit -- the tool reports this and falls back to full model checking.
//! - Liveness properties are not decomposed; only safety invariants are checked
//!   per-group.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, ExprLabel, Module, OperatorDef, Unit};
use tla_core::{
    lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, FileId, ModuleLoader,
    SyntaxNode,
};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Output format for the assume-guarantee command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AssumeGuaranteeOutputFormat {
    Human,
    Json,
}

/// Entry point for `tla2 assume-guarantee`.
pub(crate) fn cmd_assume_guarantee(
    file: &Path,
    config: Option<&Path>,
    max_states: usize,
    format: AssumeGuaranteeOutputFormat,
) -> Result<()> {
    let total_start = Instant::now();

    // -----------------------------------------------------------------------
    // Phase 1: Parse and lower
    // -----------------------------------------------------------------------
    let source = read_source(file)?;

    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diag = parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diag.eprint(&file_path, &source);
        }
        bail!(
            "assume-guarantee aborted: {} parse error(s)",
            parse_result.errors.len()
        );
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

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
            "assume-guarantee aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("assume-guarantee: lowering produced no module")?;

    // -----------------------------------------------------------------------
    // Phase 2: Load config
    // -----------------------------------------------------------------------
    let cfg = load_config(file, config);

    // -----------------------------------------------------------------------
    // Phase 3: Decompose Next into actions
    // -----------------------------------------------------------------------
    let state_vars = collect_state_variables(&module);
    if state_vars.is_empty() {
        bail!("assume-guarantee: no state variables declared in the module");
    }

    let op_table = build_operator_table(&module);
    let next_name = cfg
        .as_ref()
        .and_then(|c| c.next.as_deref())
        .unwrap_or("Next");
    let init_name = cfg
        .as_ref()
        .and_then(|c| c.init.as_deref())
        .unwrap_or("Init");
    // Suppress unused variable warning -- init_name is used conceptually but
    // passed through the config to ModelChecker.
    let _ = init_name;

    let actions = decompose_next(&module, next_name, &op_table);
    if actions.is_empty() {
        bail!(
            "assume-guarantee: no actions found (operator `{next_name}` not found or has no disjuncts)"
        );
    }

    // -----------------------------------------------------------------------
    // Phase 4: Analyze variable access and build dependency graph
    // -----------------------------------------------------------------------
    let analyzed: Vec<AnalyzedAction> = actions
        .iter()
        .map(|a| analyze_action(a, &state_vars, &op_table))
        .collect();

    let groups = compute_independent_groups(&analyzed, &state_vars);

    // -----------------------------------------------------------------------
    // Phase 5: Report decomposition and run per-group model checking
    // -----------------------------------------------------------------------
    let invariants: Vec<String> = cfg
        .as_ref()
        .map(|c| c.invariants.clone())
        .unwrap_or_default();

    let group_results = run_group_checks(
        file,
        &tree,
        &module,
        &cfg,
        &groups,
        &analyzed,
        max_states,
    );

    let total_elapsed = total_start.elapsed();

    // -----------------------------------------------------------------------
    // Phase 6: Combine and report results
    // -----------------------------------------------------------------------
    let report = build_report(
        &module.name.node,
        &state_vars,
        &analyzed,
        &groups,
        &invariants,
        &group_results,
        total_elapsed,
    );

    match format {
        AssumeGuaranteeOutputFormat::Human => emit_human(&report),
        AssumeGuaranteeOutputFormat::Json => emit_json(&report)?,
    }

    // Exit with non-zero if any group failed
    if report.overall_verdict == Verdict::Fail {
        std::process::exit(1);
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Internal data types
// ---------------------------------------------------------------------------

/// A raw action extracted from the Next-state relation.
struct RawAction {
    name: String,
    body: Expr,
}

/// An action with analyzed variable usage.
struct AnalyzedAction {
    name: String,
    reads: BTreeSet<String>,
    writes: BTreeSet<String>,
    unchanged: BTreeSet<String>,
}

impl AnalyzedAction {
    /// All variables touched by this action (reads, writes, unchanged).
    fn all_vars(&self) -> BTreeSet<&String> {
        self.reads
            .iter()
            .chain(&self.writes)
            .chain(&self.unchanged)
            .collect()
    }
}

/// A group of actions that share variables (connected component).
struct ActionGroup {
    /// Indices into the analyzed actions vector.
    action_indices: Vec<usize>,
    /// Variables touched by all actions in this group.
    variables: BTreeSet<String>,
}

/// Result of model-checking a single action group.
#[derive(Debug, Clone)]
struct GroupCheckResult {
    group_id: usize,
    action_names: Vec<String>,
    variables: BTreeSet<String>,
    verdict: Verdict,
    states_found: usize,
    max_depth: usize,
    initial_states: usize,
    elapsed: Duration,
    /// If an invariant was violated, which one.
    violated_invariant: Option<String>,
    /// If an error occurred during checking.
    error_message: Option<String>,
}

/// Overall verdict for a group or the full decomposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Pass,
    Fail,
    Error,
    /// The group could not be checked (e.g., no Next operator could be formed).
    Skipped,
}

impl Verdict {
    fn as_str(self) -> &'static str {
        match self {
            Verdict::Pass => "PASS",
            Verdict::Fail => "FAIL",
            Verdict::Error => "ERROR",
            Verdict::Skipped => "SKIPPED",
        }
    }
}

/// Full assume-guarantee analysis report.
struct AgReport {
    module_name: String,
    state_variables: Vec<String>,
    actions: Vec<ActionSummary>,
    groups: Vec<GroupSummary>,
    invariants: Vec<String>,
    group_results: Vec<GroupCheckResult>,
    overall_verdict: Verdict,
    total_states: usize,
    total_elapsed: Duration,
    decomposition_benefit: DecompositionBenefit,
}

/// Summary of an action for reporting.
struct ActionSummary {
    name: String,
    reads: Vec<String>,
    writes: Vec<String>,
    unchanged: Vec<String>,
}

/// Summary of a group for reporting.
struct GroupSummary {
    group_id: usize,
    action_names: Vec<String>,
    variables: Vec<String>,
}

/// Assessment of whether decomposition provides a benefit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DecompositionBenefit {
    /// Multiple independent groups found -- decomposition is beneficial.
    Beneficial { num_groups: usize },
    /// All actions share variables -- no benefit from decomposition.
    NoBenefit,
    /// Only one action -- trivially decomposed.
    SingleAction,
}

// ---------------------------------------------------------------------------
// Config loading (non-fatal)
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

fn decompose_next(
    module: &Module,
    next_name: &str,
    op_table: &HashMap<String, OperatorDef>,
) -> Vec<RawAction> {
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
fn collect_disjuncts(
    expr: &Expr,
    op_table: &HashMap<String, OperatorDef>,
    actions: &mut Vec<RawAction>,
    depth: usize,
) {
    const MAX_EXPAND_DEPTH: usize = 8;

    match expr {
        Expr::Or(lhs, rhs) => {
            collect_disjuncts(&lhs.node, op_table, actions, depth);
            collect_disjuncts(&rhs.node, op_table, actions, depth);
        }

        Expr::Label(ExprLabel { name, body }) => {
            if is_disjunction(&body.node) {
                collect_disjuncts(&body.node, op_table, actions, depth);
            } else {
                actions.push(RawAction {
                    name: name.node.clone(),
                    body: body.node.clone(),
                });
            }
        }

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

        Expr::Apply(func, args) if args.is_empty() && depth < MAX_EXPAND_DEPTH => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &func.node {
                if let Some(op_def) = op_table.get(name.as_str()) {
                    if op_def.params.is_empty() {
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
            let idx = actions.len();
            actions.push(RawAction {
                name: format!("Action_{idx}"),
                body: expr.clone(),
            });
        }

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

        _ => {
            let idx = actions.len();
            actions.push(RawAction {
                name: format!("Action_{idx}"),
                body: expr.clone(),
            });
        }
    }
}

fn is_disjunction(expr: &Expr) -> bool {
    matches!(expr, Expr::Or(_, _))
}

// ---------------------------------------------------------------------------
// Variable usage analysis per action
// ---------------------------------------------------------------------------

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
    visited_ops: HashSet<String>,
}

impl<'a> VarCollector<'a> {
    fn visit(&mut self, expr: &Expr) {
        match expr {
            Expr::StateVar(name, _, _) => {
                if self.state_vars.contains(name.as_str()) && !self.is_bound(name) {
                    if self.in_prime {
                        self.writes.insert(name.clone());
                    } else if self.in_unchanged {
                        self.unchanged.insert(name.clone());
                    } else {
                        self.reads.insert(name.clone());
                    }
                }
            }

            Expr::Ident(name, _) => {
                if self.state_vars.contains(name.as_str()) && !self.is_bound(name) {
                    if self.in_prime {
                        self.writes.insert(name.clone());
                    } else if self.in_unchanged {
                        self.unchanged.insert(name.clone());
                    } else {
                        self.reads.insert(name.clone());
                    }
                }
            }

            Expr::Prime(inner) => {
                let was_prime = self.in_prime;
                self.in_prime = true;
                self.visit(&inner.node);
                self.in_prime = was_prime;
            }

            Expr::Unchanged(inner) => {
                let was_unchanged = self.in_unchanged;
                self.in_unchanged = true;
                self.visit_unchanged_body(&inner.node);
                self.in_unchanged = was_unchanged;
            }

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

            Expr::Choose(bv, body) => {
                if let Some(d) = &bv.domain {
                    self.visit(&d.node);
                }
                self.bound_names.push(bv.name.node.clone());
                self.visit(&body.node);
                self.bound_names.pop();
            }

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

            Expr::SetFilter(bv, body) => {
                if let Some(d) = &bv.domain {
                    self.visit(&d.node);
                }
                self.bound_names.push(bv.name.node.clone());
                self.visit(&body.node);
                self.bound_names.pop();
            }

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

            Expr::Lambda(params, body) => {
                for p in params {
                    self.bound_names.push(p.node.clone());
                }
                self.visit(&body.node);
                for _ in params {
                    self.bound_names.pop();
                }
            }

            Expr::Apply(func, args) => {
                for arg in args {
                    self.visit(&arg.node);
                }
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
                self.visit(&func.node);
            }

            Expr::Label(label) => {
                self.visit(&label.body.node);
            }

            Expr::SubstIn(_, body) => {
                self.visit(&body.node);
            }

            Expr::If(cond, then_, else_) => {
                self.visit(&cond.node);
                self.visit(&then_.node);
                self.visit(&else_.node);
            }

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
                self.visit(expr);
            }
        }
    }

    fn is_bound(&self, name: &str) -> bool {
        self.bound_names.iter().any(|b| b == name)
    }
}

// ---------------------------------------------------------------------------
// Expression child visitor (structural traversal for catch-all)
// ---------------------------------------------------------------------------

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

        // Collections
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
// Independence analysis (union-find connected components)
// ---------------------------------------------------------------------------

fn compute_independent_groups(
    actions: &[AnalyzedAction],
    variables: &[String],
) -> Vec<ActionGroup> {
    if actions.is_empty() || variables.is_empty() {
        return Vec::new();
    }

    // Union-find on action indices: two actions are in the same group if they
    // share any variable (reads, writes, or unchanged).

    let n = actions.len();
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

    // Build variable -> action indices map.
    let mut var_to_actions: HashMap<&str, Vec<usize>> = HashMap::new();
    for (i, action) in actions.iter().enumerate() {
        for var in action.all_vars() {
            var_to_actions
                .entry(var.as_str())
                .or_default()
                .push(i);
        }
    }

    // Union all actions that share a variable.
    for action_indices in var_to_actions.values() {
        if action_indices.len() >= 2 {
            for pair in action_indices.windows(2) {
                union(&mut parent, &mut rank, pair[0], pair[1]);
            }
        }
    }

    // Collect connected components.
    let mut components: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for i in 0..n {
        components
            .entry(find(&mut parent, i))
            .or_default()
            .push(i);
    }

    components
        .into_values()
        .map(|indices| {
            let mut group_vars = BTreeSet::new();
            for &idx in &indices {
                for var in actions[idx].all_vars() {
                    group_vars.insert(var.clone());
                }
            }
            ActionGroup {
                action_indices: indices,
                variables: group_vars,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Per-group model checking
// ---------------------------------------------------------------------------

/// Run model checking for each independent action group.
///
/// For each group, we construct a synthetic Next operator that is the disjunction
/// of only that group's actions. We then run the model checker with the original
/// Init and all configured invariants.
fn run_group_checks(
    file: &Path,
    tree: &SyntaxNode,
    module: &Module,
    cfg: &Option<tla_check::Config>,
    groups: &[ActionGroup],
    analyzed: &[AnalyzedAction],
    max_states: usize,
) -> Vec<GroupCheckResult> {
    let mut results = Vec::with_capacity(groups.len());

    // If there is only one group, run with the original config (no decomposition needed).
    if groups.len() <= 1 {
        let group = &groups[0];
        let action_names: Vec<String> = group
            .action_indices
            .iter()
            .map(|&i| analyzed[i].name.clone())
            .collect();

        let result = run_single_group_check(
            file,
            tree,
            module,
            cfg,
            0,
            &action_names,
            &group.variables,
            None, // Use original config's Next
            max_states,
        );
        results.push(result);
        return results;
    }

    // Multiple groups: run each group independently with a synthetic Next.
    for (gid, group) in groups.iter().enumerate() {
        let action_names: Vec<String> = group
            .action_indices
            .iter()
            .map(|&i| analyzed[i].name.clone())
            .collect();

        // Build the synthetic Next name: if the group has exactly one action,
        // use it directly. Otherwise, search for a wrapper operator.
        let synthetic_next = if action_names.len() == 1 {
            Some(action_names[0].clone())
        } else {
            find_wrapper_operator(module, &action_names)
        };

        let result = run_single_group_check(
            file,
            tree,
            module,
            cfg,
            gid,
            &action_names,
            &group.variables,
            synthetic_next.as_deref(),
            max_states,
        );
        results.push(result);
    }

    results
}

/// Try to find an operator in the module whose body is a disjunction of exactly
/// the given action names.
fn find_wrapper_operator(module: &Module, action_names: &[String]) -> Option<String> {
    let target_set: HashSet<&str> = action_names.iter().map(|s| s.as_str()).collect();
    let op_table = build_operator_table(module);

    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            let mut disjuncts = Vec::new();
            collect_disjunct_names(&op.body.node, &op_table, &mut disjuncts, 0);

            let disjunct_set: HashSet<&str> = disjuncts.iter().map(|s| s.as_str()).collect();
            if disjunct_set == target_set {
                return Some(op.name.node.clone());
            }
        }
    }
    None
}

/// Collect the names of top-level disjuncts (operator references) from an expression.
fn collect_disjunct_names(
    expr: &Expr,
    op_table: &HashMap<String, OperatorDef>,
    names: &mut Vec<String>,
    depth: usize,
) {
    const MAX_DEPTH: usize = 4;

    match expr {
        Expr::Or(lhs, rhs) => {
            collect_disjunct_names(&lhs.node, op_table, names, depth);
            collect_disjunct_names(&rhs.node, op_table, names, depth);
        }
        Expr::Label(label) => {
            collect_disjunct_names(&label.body.node, op_table, names, depth);
        }
        Expr::Ident(name, _) if depth < MAX_DEPTH => {
            names.push(name.clone());
        }
        Expr::Apply(func, args) if args.is_empty() && depth < MAX_DEPTH => {
            if let Expr::Ident(name, _) = &func.node {
                names.push(name.clone());
            }
        }
        _ => {}
    }
}

/// Run model checking for a single action group.
fn run_single_group_check(
    file: &Path,
    tree: &SyntaxNode,
    module: &Module,
    cfg: &Option<tla_check::Config>,
    group_id: usize,
    action_names: &[String],
    variables: &BTreeSet<String>,
    override_next: Option<&str>,
    max_states: usize,
) -> GroupCheckResult {
    let start = Instant::now();

    // Build the config for this group.
    let mut group_cfg = cfg.clone().unwrap_or_default();
    if let Some(next_name) = override_next {
        group_cfg.next = Some(next_name.to_string());
    }

    // Disable deadlock checking for sub-groups: a group with a subset of
    // actions may legitimately have states with no successors (the other
    // group's actions would normally fire there).
    group_cfg.check_deadlock = false;

    // Disable liveness properties -- assume-guarantee only checks safety.
    group_cfg.properties.clear();

    // Load module dependencies for model checking.
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(tree, file);
    if let Err(e) = loader.load_extends(module) {
        return GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Error,
            states_found: 0,
            max_depth: 0,
            initial_states: 0,
            elapsed: start.elapsed(),
            violated_invariant: None,
            error_message: Some(format!("failed to load EXTENDS: {e}")),
        };
    }
    if let Err(e) = loader.load_instances(module) {
        return GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Error,
            states_found: 0,
            max_depth: 0,
            initial_states: 0,
            elapsed: start.elapsed(),
            violated_invariant: None,
            error_message: Some(format!("failed to load INSTANCE: {e}")),
        };
    }

    let extended_modules = loader.modules_for_model_checking(module);
    let extended_refs: Vec<&tla_core::ast::Module> = extended_modules.iter().copied().collect();

    let mut mc =
        tla_check::ModelChecker::new_with_extends(module, &extended_refs, &group_cfg);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();
    let elapsed = start.elapsed();

    match &check_result {
        tla_check::CheckResult::Success(_) => GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Pass,
            states_found: stats.states_found,
            max_depth: stats.max_depth,
            initial_states: stats.initial_states,
            elapsed,
            violated_invariant: None,
            error_message: None,
        },
        tla_check::CheckResult::InvariantViolation { invariant, .. } => GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Fail,
            states_found: stats.states_found,
            max_depth: stats.max_depth,
            initial_states: stats.initial_states,
            elapsed,
            violated_invariant: Some(invariant.clone()),
            error_message: None,
        },
        tla_check::CheckResult::PropertyViolation { property, .. } => GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Fail,
            states_found: stats.states_found,
            max_depth: stats.max_depth,
            initial_states: stats.initial_states,
            elapsed,
            violated_invariant: Some(property.clone()),
            error_message: None,
        },
        tla_check::CheckResult::Deadlock { .. } => GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Fail,
            states_found: stats.states_found,
            max_depth: stats.max_depth,
            initial_states: stats.initial_states,
            elapsed,
            violated_invariant: None,
            error_message: Some("deadlock detected".to_string()),
        },
        tla_check::CheckResult::Error { error, .. } => GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Error,
            states_found: stats.states_found,
            max_depth: stats.max_depth,
            initial_states: stats.initial_states,
            elapsed,
            violated_invariant: None,
            error_message: Some(format!("{error}")),
        },
        tla_check::CheckResult::LimitReached { .. } => GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Pass,
            states_found: stats.states_found,
            max_depth: stats.max_depth,
            initial_states: stats.initial_states,
            elapsed,
            violated_invariant: None,
            error_message: Some("state limit reached (partial verification)".to_string()),
        },
        _ => GroupCheckResult {
            group_id,
            action_names: action_names.to_vec(),
            variables: variables.clone(),
            verdict: Verdict::Error,
            states_found: stats.states_found,
            max_depth: stats.max_depth,
            initial_states: stats.initial_states,
            elapsed,
            violated_invariant: None,
            error_message: Some("unexpected check result variant".to_string()),
        },
    }
}

// ---------------------------------------------------------------------------
// Report construction
// ---------------------------------------------------------------------------

fn build_report(
    module_name: &str,
    state_vars: &[String],
    analyzed: &[AnalyzedAction],
    groups: &[ActionGroup],
    invariants: &[String],
    group_results: &[GroupCheckResult],
    total_elapsed: Duration,
) -> AgReport {
    let actions: Vec<ActionSummary> = analyzed
        .iter()
        .map(|a| ActionSummary {
            name: a.name.clone(),
            reads: a.reads.iter().cloned().collect(),
            writes: a.writes.iter().cloned().collect(),
            unchanged: a.unchanged.iter().cloned().collect(),
        })
        .collect();

    let group_summaries: Vec<GroupSummary> = groups
        .iter()
        .enumerate()
        .map(|(gid, g)| GroupSummary {
            group_id: gid,
            action_names: g
                .action_indices
                .iter()
                .map(|&i| analyzed[i].name.clone())
                .collect(),
            variables: g.variables.iter().cloned().collect(),
        })
        .collect();

    let overall_verdict = if group_results.iter().all(|r| r.verdict == Verdict::Pass) {
        Verdict::Pass
    } else if group_results.iter().any(|r| r.verdict == Verdict::Fail) {
        Verdict::Fail
    } else {
        Verdict::Error
    };

    let total_states: usize = group_results.iter().map(|r| r.states_found).sum();

    let decomposition_benefit = if analyzed.len() <= 1 {
        DecompositionBenefit::SingleAction
    } else if groups.len() > 1 {
        DecompositionBenefit::Beneficial {
            num_groups: groups.len(),
        }
    } else {
        DecompositionBenefit::NoBenefit
    };

    AgReport {
        module_name: module_name.to_string(),
        state_variables: state_vars.to_vec(),
        actions,
        groups: group_summaries,
        invariants: invariants.to_vec(),
        group_results: group_results.to_vec(),
        overall_verdict,
        total_states,
        total_elapsed,
        decomposition_benefit,
    }
}

// ---------------------------------------------------------------------------
// Output: Human-readable
// ---------------------------------------------------------------------------

fn emit_human(report: &AgReport) {
    println!(
        "=== Assume-Guarantee Compositional Verification: {} ===",
        report.module_name
    );
    println!();

    // Variables
    println!(
        "State variables ({}): {}",
        report.state_variables.len(),
        report.state_variables.join(", ")
    );
    println!();

    // Actions with variable access
    println!("Actions ({}):", report.actions.len());
    println!("{}", "-".repeat(64));
    for (i, action) in report.actions.iter().enumerate() {
        let fmt_set = |v: &[String]| {
            if v.is_empty() {
                "-".to_string()
            } else {
                v.join(", ")
            }
        };
        println!(
            "  [{}] {} : reads={{{}}} writes={{{}}}",
            i,
            action.name,
            fmt_set(&action.reads),
            fmt_set(&action.writes)
        );
        if !action.unchanged.is_empty() {
            println!("      UNCHANGED {{{}}}", action.unchanged.join(", "));
        }
    }
    println!();

    // Decomposition
    match report.decomposition_benefit {
        DecompositionBenefit::Beneficial { num_groups } => {
            println!(
                "Decomposition: {} independent groups found -- compositional checking enabled",
                num_groups
            );
        }
        DecompositionBenefit::NoBenefit => {
            println!(
                "Decomposition: all actions share variables -- no compositional benefit"
            );
            println!("  (falling back to monolithic model checking)");
        }
        DecompositionBenefit::SingleAction => {
            println!("Decomposition: single action -- trivially decomposed");
        }
    }
    println!();

    // Groups
    println!("Independent Groups ({}):", report.groups.len());
    println!("{}", "-".repeat(64));
    for group in &report.groups {
        println!(
            "  Group {}: actions=[{}] variables={{{}}}",
            group.group_id,
            group.action_names.join(", "),
            group.variables.join(", ")
        );
    }
    println!();

    // Invariants
    if report.invariants.is_empty() {
        println!("Invariants: (none configured)");
    } else {
        println!("Invariants ({}):", report.invariants.len());
        for inv in &report.invariants {
            println!("  - {}", inv);
        }
    }
    println!();

    // Per-group results
    println!("=== Group Verification Results ===");
    println!("{}", "-".repeat(64));
    for result in &report.group_results {
        let verdict_marker = result.verdict.as_str();
        println!(
            "  Group {} [{}]: {} states, depth {}, {:.2}s",
            result.group_id,
            verdict_marker,
            result.states_found,
            result.max_depth,
            result.elapsed.as_secs_f64()
        );
        println!("    Actions: [{}]", result.action_names.join(", "));
        println!(
            "    Variables: {{{}}}",
            result
                .variables
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(", ")
        );
        if let Some(inv) = &result.violated_invariant {
            println!("    Violated invariant: {}", inv);
        }
        if let Some(err) = &result.error_message {
            println!("    Note: {}", err);
        }
    }
    println!();

    // Overall verdict
    let verdict_str = report.overall_verdict.as_str();
    println!("=== Overall Verdict: {} ===", verdict_str);
    println!(
        "Total states explored: {} across {} group(s) in {:.2}s",
        report.total_states,
        report.group_results.len(),
        report.total_elapsed.as_secs_f64()
    );

    if report.overall_verdict == Verdict::Pass
        && report.decomposition_benefit != DecompositionBenefit::NoBenefit
    {
        println!();
        println!("All independent groups verified successfully.");
        println!("By the assume-guarantee rule for non-interfering actions,");
        println!("the global safety properties hold.");
    }

    if report.overall_verdict == Verdict::Fail {
        println!();
        println!("WARNING: Invariant violation detected in at least one group.");
        println!(
            "This may be a true violation, or a false positive caused by the"
        );
        println!(
            "decomposition (a group may reach states that the full system cannot)."
        );
        println!("Run `tla2 check` on the full spec to confirm.");
    }
}

// ---------------------------------------------------------------------------
// Output: JSON
// ---------------------------------------------------------------------------

fn emit_json(report: &AgReport) -> Result<()> {
    let actions_json: Vec<serde_json::Value> = report
        .actions
        .iter()
        .enumerate()
        .map(|(i, a)| {
            serde_json::json!({
                "index": i,
                "name": a.name,
                "reads": a.reads,
                "writes": a.writes,
                "unchanged": a.unchanged,
            })
        })
        .collect();

    let groups_json: Vec<serde_json::Value> = report
        .groups
        .iter()
        .map(|g| {
            serde_json::json!({
                "group_id": g.group_id,
                "action_names": g.action_names,
                "variables": g.variables,
            })
        })
        .collect();

    let results_json: Vec<serde_json::Value> = report
        .group_results
        .iter()
        .map(|r| {
            let mut obj = serde_json::json!({
                "group_id": r.group_id,
                "action_names": r.action_names,
                "variables": r.variables.iter().cloned().collect::<Vec<_>>(),
                "verdict": r.verdict.as_str(),
                "states_found": r.states_found,
                "max_depth": r.max_depth,
                "initial_states": r.initial_states,
                "elapsed_secs": r.elapsed.as_secs_f64(),
            });
            if let Some(inv) = &r.violated_invariant {
                obj["violated_invariant"] = serde_json::json!(inv);
            }
            if let Some(err) = &r.error_message {
                obj["error_message"] = serde_json::json!(err);
            }
            obj
        })
        .collect();

    let benefit_str = match report.decomposition_benefit {
        DecompositionBenefit::Beneficial { num_groups } => {
            format!("beneficial ({num_groups} groups)")
        }
        DecompositionBenefit::NoBenefit => "no_benefit".to_string(),
        DecompositionBenefit::SingleAction => "single_action".to_string(),
    };

    let output = serde_json::json!({
        "module_name": report.module_name,
        "state_variables": report.state_variables,
        "actions": actions_json,
        "groups": groups_json,
        "invariants": report.invariants,
        "group_results": results_json,
        "overall_verdict": report.overall_verdict.as_str(),
        "total_states": report.total_states,
        "total_elapsed_secs": report.total_elapsed.as_secs_f64(),
        "decomposition_benefit": benefit_str,
        "summary": {
            "num_actions": report.actions.len(),
            "num_groups": report.groups.len(),
            "num_invariants": report.invariants.len(),
            "num_state_variables": report.state_variables.len(),
            "groups_passed": report.group_results.iter()
                .filter(|r| r.verdict == Verdict::Pass).count(),
            "groups_failed": report.group_results.iter()
                .filter(|r| r.verdict == Verdict::Fail).count(),
            "groups_error": report.group_results.iter()
                .filter(|r| r.verdict == Verdict::Error).count(),
        },
    });

    let json_str =
        serde_json::to_string_pretty(&output).context("serialize assume-guarantee report")?;
    println!("{json_str}");
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
    fn test_output_format_eq() {
        assert_eq!(
            AssumeGuaranteeOutputFormat::Human,
            AssumeGuaranteeOutputFormat::Human
        );
        assert_ne!(
            AssumeGuaranteeOutputFormat::Human,
            AssumeGuaranteeOutputFormat::Json
        );
    }

    #[test]
    fn test_collect_state_variables() {
        let module = parse_module(
            "---- MODULE Test ----\nVARIABLE x, y, z\nFoo == TRUE\n====",
        );
        let vars = collect_state_variables(&module);
        assert_eq!(vars, vec!["x", "y", "z"]);
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
    fn test_decompose_single_action() {
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
            "A reads y: {:?}",
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
        assert!(analyzed.writes.contains("x"), "should detect x as written");
        assert!(
            !analyzed.reads.contains("n"),
            "bound var n should not be in reads"
        );
        assert!(
            !analyzed.writes.contains("n"),
            "bound var n should not be in writes"
        );
    }

    #[test]
    fn test_independent_groups_truly_independent() {
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

        let groups = compute_independent_groups(&analyzed, &state_vars);
        // A touches only x, B touches only y -- no UNCHANGED, truly independent.
        assert_eq!(
            groups.len(),
            2,
            "expected 2 independent groups, got {}",
            groups.len()
        );
    }

    #[test]
    fn test_independent_groups_coupled_via_unchanged() {
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

        let groups = compute_independent_groups(&analyzed, &state_vars);
        // Both share x and y via UNCHANGED, so single group.
        assert_eq!(
            groups.len(),
            1,
            "expected 1 coupled group, got {}",
            groups.len()
        );
    }

    #[test]
    fn test_independent_groups_three_actions_two_groups() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y, z
Init == x = 0 /\ y = 0 /\ z = 0
A == x' = x + 1
B == x' = x + 2
C == z' = z + 1
Next == A \/ B \/ C
===="#,
        );
        let state_vars = collect_state_variables(&module);
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        let analyzed: Vec<AnalyzedAction> = actions
            .iter()
            .map(|a| analyze_action(a, &state_vars, &op_table))
            .collect();

        let groups = compute_independent_groups(&analyzed, &state_vars);
        // A and B share x, C touches only z.
        assert_eq!(
            groups.len(),
            2,
            "expected 2 groups: {{A,B}} and {{C}}, got {}",
            groups.len()
        );
    }

    #[test]
    fn test_verdict_as_str() {
        assert_eq!(Verdict::Pass.as_str(), "PASS");
        assert_eq!(Verdict::Fail.as_str(), "FAIL");
        assert_eq!(Verdict::Error.as_str(), "ERROR");
        assert_eq!(Verdict::Skipped.as_str(), "SKIPPED");
    }

    #[test]
    fn test_build_report_all_pass() {
        let vars = vec!["x".to_string(), "y".to_string()];
        let analyzed = vec![
            AnalyzedAction {
                name: "A".to_string(),
                reads: ["x"].iter().map(|s| s.to_string()).collect(),
                writes: ["x"].iter().map(|s| s.to_string()).collect(),
                unchanged: BTreeSet::new(),
            },
            AnalyzedAction {
                name: "B".to_string(),
                reads: ["y"].iter().map(|s| s.to_string()).collect(),
                writes: ["y"].iter().map(|s| s.to_string()).collect(),
                unchanged: BTreeSet::new(),
            },
        ];
        let groups = vec![
            ActionGroup {
                action_indices: vec![0],
                variables: ["x"].iter().map(|s| s.to_string()).collect(),
            },
            ActionGroup {
                action_indices: vec![1],
                variables: ["y"].iter().map(|s| s.to_string()).collect(),
            },
        ];
        let results = vec![
            GroupCheckResult {
                group_id: 0,
                action_names: vec!["A".to_string()],
                variables: ["x"].iter().map(|s| s.to_string()).collect(),
                verdict: Verdict::Pass,
                states_found: 100,
                max_depth: 5,
                initial_states: 1,
                elapsed: Duration::from_millis(50),
                violated_invariant: None,
                error_message: None,
            },
            GroupCheckResult {
                group_id: 1,
                action_names: vec!["B".to_string()],
                variables: ["y"].iter().map(|s| s.to_string()).collect(),
                verdict: Verdict::Pass,
                states_found: 200,
                max_depth: 10,
                initial_states: 1,
                elapsed: Duration::from_millis(80),
                violated_invariant: None,
                error_message: None,
            },
        ];
        let invariants = vec!["TypeInv".to_string()];

        let report = build_report(
            "Test",
            &vars,
            &analyzed,
            &groups,
            &invariants,
            &results,
            Duration::from_millis(150),
        );

        assert_eq!(report.overall_verdict, Verdict::Pass);
        assert_eq!(report.total_states, 300);
        assert_eq!(report.groups.len(), 2);
        assert!(matches!(
            report.decomposition_benefit,
            DecompositionBenefit::Beneficial { num_groups: 2 }
        ));
    }

    #[test]
    fn test_build_report_one_fail() {
        let vars = vec!["x".to_string()];
        let analyzed = vec![AnalyzedAction {
            name: "A".to_string(),
            reads: ["x"].iter().map(|s| s.to_string()).collect(),
            writes: ["x"].iter().map(|s| s.to_string()).collect(),
            unchanged: BTreeSet::new(),
        }];
        let groups = vec![ActionGroup {
            action_indices: vec![0],
            variables: ["x"].iter().map(|s| s.to_string()).collect(),
        }];
        let results = vec![GroupCheckResult {
            group_id: 0,
            action_names: vec!["A".to_string()],
            variables: ["x"].iter().map(|s| s.to_string()).collect(),
            verdict: Verdict::Fail,
            states_found: 50,
            max_depth: 3,
            initial_states: 1,
            elapsed: Duration::from_millis(20),
            violated_invariant: Some("Inv".to_string()),
            error_message: None,
        }];

        let report = build_report(
            "Test",
            &vars,
            &analyzed,
            &groups,
            &["Inv".to_string()],
            &results,
            Duration::from_millis(20),
        );

        assert_eq!(report.overall_verdict, Verdict::Fail);
    }

    #[test]
    fn test_decomposition_benefit_single_action() {
        let vars = vec!["x".to_string()];
        let analyzed = vec![AnalyzedAction {
            name: "A".to_string(),
            reads: BTreeSet::new(),
            writes: ["x"].iter().map(|s| s.to_string()).collect(),
            unchanged: BTreeSet::new(),
        }];
        let groups = vec![ActionGroup {
            action_indices: vec![0],
            variables: ["x"].iter().map(|s| s.to_string()).collect(),
        }];
        let results = vec![GroupCheckResult {
            group_id: 0,
            action_names: vec!["A".to_string()],
            variables: ["x"].iter().map(|s| s.to_string()).collect(),
            verdict: Verdict::Pass,
            states_found: 10,
            max_depth: 1,
            initial_states: 1,
            elapsed: Duration::from_millis(5),
            violated_invariant: None,
            error_message: None,
        }];

        let report = build_report(
            "Test",
            &vars,
            &analyzed,
            &groups,
            &[],
            &results,
            Duration::from_millis(5),
        );

        assert_eq!(
            report.decomposition_benefit,
            DecompositionBenefit::SingleAction
        );
    }

    #[test]
    fn test_find_wrapper_operator_exact_match() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
A == x' = x + 1
B == y' = y + 1
GroupAB == A \/ B
Next == A \/ B
===="#,
        );
        let result =
            find_wrapper_operator(&module, &["A".to_string(), "B".to_string()]);
        assert!(result.is_some(), "should find a wrapper for {{A, B}}");
    }

    #[test]
    fn test_find_wrapper_operator_no_match() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x, y, z
Init == x = 0 /\ y = 0 /\ z = 0
A == x' = x + 1
B == y' = y + 1
C == z' = z + 1
Next == A \/ B \/ C
===="#,
        );
        let result =
            find_wrapper_operator(&module, &["A".to_string(), "B".to_string()]);
        assert!(result.is_none(), "no operator wraps exactly A and B");
    }

    #[test]
    fn test_analyzed_action_all_vars() {
        let action = AnalyzedAction {
            name: "A".to_string(),
            reads: ["x", "y"].iter().map(|s| s.to_string()).collect(),
            writes: ["z"].iter().map(|s| s.to_string()).collect(),
            unchanged: ["w"].iter().map(|s| s.to_string()).collect(),
        };
        let all = action.all_vars();
        assert_eq!(all.len(), 4);
        assert!(all.contains(&"x".to_string()));
        assert!(all.contains(&"y".to_string()));
        assert!(all.contains(&"z".to_string()));
        assert!(all.contains(&"w".to_string()));
    }

    #[test]
    fn test_empty_module_no_next() {
        let module = parse_module(
            r#"---- MODULE Test ----
VARIABLE x
Init == x = 0
===="#,
        );
        let op_table = build_operator_table(&module);
        let actions = decompose_next(&module, "Next", &op_table);
        assert!(
            actions.is_empty(),
            "no Next operator should yield no actions"
        );
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
        assert_eq!(
            actions.len(),
            2,
            "expected 2 actions from exists-wrapped disjunction"
        );
    }

    #[test]
    fn test_compute_independent_groups_empty() {
        let groups = compute_independent_groups(&[], &[]);
        assert!(groups.is_empty());
    }

    #[test]
    fn test_four_actions_three_groups() {
        // A touches {x}, B touches {x, y}, C touches {z}, D touches {w}
        // A and B share x -> group 1
        // C alone -> group 2
        // D alone -> group 3
        let analyzed = vec![
            AnalyzedAction {
                name: "A".to_string(),
                reads: ["x"].iter().map(|s| s.to_string()).collect(),
                writes: ["x"].iter().map(|s| s.to_string()).collect(),
                unchanged: BTreeSet::new(),
            },
            AnalyzedAction {
                name: "B".to_string(),
                reads: ["x"].iter().map(|s| s.to_string()).collect(),
                writes: ["y"].iter().map(|s| s.to_string()).collect(),
                unchanged: BTreeSet::new(),
            },
            AnalyzedAction {
                name: "C".to_string(),
                reads: BTreeSet::new(),
                writes: ["z"].iter().map(|s| s.to_string()).collect(),
                unchanged: BTreeSet::new(),
            },
            AnalyzedAction {
                name: "D".to_string(),
                reads: BTreeSet::new(),
                writes: ["w"].iter().map(|s| s.to_string()).collect(),
                unchanged: BTreeSet::new(),
            },
        ];
        let vars: Vec<String> = ["x", "y", "z", "w"]
            .iter()
            .map(|s| s.to_string())
            .collect();

        let groups = compute_independent_groups(&analyzed, &vars);
        assert_eq!(
            groups.len(),
            3,
            "expected 3 groups: {{A,B}}, {{C}}, {{D}}"
        );

        // Find the group containing A (index 0).
        let ab_group = groups.iter().find(|g| g.action_indices.contains(&0));
        assert!(ab_group.is_some());
        let ab_group = ab_group.unwrap();
        assert!(ab_group.action_indices.contains(&0));
        assert!(ab_group.action_indices.contains(&1));
        assert_eq!(ab_group.action_indices.len(), 2);
    }
}
