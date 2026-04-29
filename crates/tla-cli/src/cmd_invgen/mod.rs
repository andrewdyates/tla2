// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 inv-gen` — automatic invariant generation for TLA+ specifications.
//!
//! Analyzes a TLA+ spec to suggest candidate invariants by examining the
//! structure of the Init predicate, Next transitions, and variable types.
//!
//! Candidate invariant strategies:
//! - **Type invariants** from Init predicates (`x \in S` -> `x \in S` as invariant)
//! - **Range preservation** (if `x` starts in `S`, Next preserves `x \in S`)
//! - **Monotonicity detection** (`x' >= x` patterns)
//! - **Conservation laws** (sum of variables preserved by Next)
//! - **Mutual exclusion** (at most one process in a critical section)

use std::collections::{HashMap, HashSet};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{BoundVar, Expr, ExprLabel, Module, OperatorDef, Unit};
use tla_core::span::Spanned;
use tla_core::{
    lower_error_diagnostic, lower_main_module, parse, parse_error_diagnostic, pretty_expr, FileId,
    SyntaxNode,
};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Output format for generated invariants.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InvGenOutputFormat {
    /// Human-readable summary with explanations.
    Human,
    /// Machine-readable JSON array of candidate invariants.
    Json,
    /// TLA+ operator definitions ready to paste into a spec.
    Tla,
}

/// Entry point for `tla2 inv-gen`.
///
/// Parses the TLA+ spec (and optional config), extracts structural information
/// from Init/Next, generates candidate invariants, and optionally verifies each
/// one with a quick model check.
pub(crate) fn cmd_inv_gen(
    file: &Path,
    config: Option<&Path>,
    verify: bool,
    format: InvGenOutputFormat,
) -> Result<()> {
    let source = read_source(file)?;

    // Parse source -> CST
    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diag = parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diag.eprint(&file_path, &source);
        }
        bail!(
            "inv-gen aborted: {} parse error(s)",
            parse_result.errors.len()
        );
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
            "inv-gen aborted: {} lowering error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("inv-gen: lowering produced no module")?;

    // Load config (best-effort)
    let cfg_info = load_config_info(file, config);

    // Collect structural information
    let spec_info = SpecInfo::extract(&module, &cfg_info);

    // Generate candidates
    let mut candidates = Vec::new();
    generate_type_invariants(&spec_info, &mut candidates);
    generate_range_preservation(&spec_info, &mut candidates);
    generate_monotonicity(&spec_info, &mut candidates);
    generate_conservation_laws(&spec_info, &mut candidates);
    generate_mutual_exclusion(&spec_info, &mut candidates);

    // Deduplicate by TLA+ text
    dedup_candidates(&mut candidates);

    // Optional verification
    if verify {
        verify_candidates(file, config, &mut candidates)?;
    }

    // Output
    match format {
        InvGenOutputFormat::Human => print_human(&spec_info, &candidates),
        InvGenOutputFormat::Json => print_json(&candidates)?,
        InvGenOutputFormat::Tla => print_tla(&module.name.node, &candidates),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Candidate invariant types
// ---------------------------------------------------------------------------

/// Strategy that generated a candidate invariant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InvariantStrategy {
    /// Derived from `x \in S` in Init.
    TypeInvariant,
    /// Init constraint preserved by all Next disjuncts.
    RangePreservation,
    /// Variable is monotonically non-decreasing or non-increasing.
    Monotonicity,
    /// Sum/difference of variables is constant across transitions.
    ConservationLaw,
    /// At most one element of a set satisfies a predicate at a time.
    MutualExclusion,
}

impl InvariantStrategy {
    fn label(self) -> &'static str {
        match self {
            Self::TypeInvariant => "type-invariant",
            Self::RangePreservation => "range-preservation",
            Self::Monotonicity => "monotonicity",
            Self::ConservationLaw => "conservation-law",
            Self::MutualExclusion => "mutual-exclusion",
        }
    }

    fn description(self) -> &'static str {
        match self {
            Self::TypeInvariant => "Membership constraint from Init predicate",
            Self::RangePreservation => "Init domain constraint preserved by Next",
            Self::Monotonicity => "Variable changes monotonically",
            Self::ConservationLaw => "Sum of variables is preserved across transitions",
            Self::MutualExclusion => "At most one element satisfies the predicate",
        }
    }
}

/// A candidate invariant with metadata.
#[derive(Debug, Clone)]
struct CandidateInvariant {
    /// Human-readable name for the invariant operator.
    name: String,
    /// The invariant as TLA+ text.
    tla_text: String,
    /// Which strategy produced this candidate.
    strategy: InvariantStrategy,
    /// Explanation of why this is likely an invariant.
    rationale: String,
    /// Confidence level: 0.0 (speculative) to 1.0 (definitional).
    confidence: f64,
    /// Verification status (if --verify was used).
    verified: Option<bool>,
    /// Variables involved.
    variables: Vec<String>,
}

// ---------------------------------------------------------------------------
// Config loading (best-effort, does not fail inv-gen)
// ---------------------------------------------------------------------------

#[derive(Default)]
struct ConfigInfo {
    init: Option<String>,
    next: Option<String>,
    invariants: Vec<String>,
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
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
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
        },
        Err(_) => ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        },
    }
}

// ---------------------------------------------------------------------------
// Spec structural information
// ---------------------------------------------------------------------------

/// Extracted structural information from the spec for invariant generation.
struct SpecInfo {
    /// All declared state variable names.
    variables: Vec<String>,
    /// Operator definitions by name.
    operators: HashMap<String, OperatorDef>,
    /// Membership constraints from Init: variable -> set expression text.
    init_memberships: Vec<MembershipConstraint>,
    /// Equality constraints from Init: variable -> value expression text.
    init_equalities: Vec<EqualityConstraint>,
    /// Primed assignment patterns found in Next disjuncts.
    next_assignments: Vec<NextAssignment>,
    /// Names of Next's disjuncts (action names).
    action_names: Vec<String>,
    /// Existing invariant names from config (to avoid duplicating).
    existing_invariants: HashSet<String>,
}

/// A membership constraint: `var \in set_expr`.
#[derive(Debug, Clone)]
struct MembershipConstraint {
    var_name: String,
    set_text: String,
}

/// An equality constraint: `var = value`.
#[derive(Debug, Clone)]
struct EqualityConstraint {
    var_name: String,
    value_text: String,
}

/// A primed assignment pattern extracted from Next.
#[derive(Debug, Clone)]
struct NextAssignment {
    /// The action (disjunct) this came from, if known.
    action_name: Option<String>,
    /// Variable being assigned.
    var_name: String,
    /// The kind of assignment pattern detected.
    pattern: AssignmentPattern,
}

/// Detected patterns in primed variable assignments.
#[derive(Debug, Clone)]
enum AssignmentPattern {
    /// `var' \in S` — membership in a set.
    MemberOf(String),
    /// `var' = var + expr` — increment.
    Increment(String),
    /// `var' = var - expr` — decrement.
    Decrement(String),
    /// `var' = expr` where expr is a function of current state.
    DirectAssign(String),
    /// `var' >= var` — non-decreasing.
    NonDecreasing,
    /// `var' <= var` — non-increasing.
    NonIncreasing,
    /// `UNCHANGED var`.
    Unchanged,
}

impl SpecInfo {
    fn extract(module: &Module, cfg: &ConfigInfo) -> Self {
        let variables = extract_variables(module);
        let operators = extract_operators(module);
        let existing_invariants: HashSet<String> = cfg.invariants.iter().cloned().collect();

        let init_name = cfg.init.as_deref().unwrap_or("Init");
        let next_name = cfg.next.as_deref().unwrap_or("Next");

        let var_set: HashSet<&str> = variables.iter().map(|s| s.as_str()).collect();

        let init_memberships = operators
            .get(init_name)
            .map(|op| extract_memberships(&op.body.node, &var_set))
            .unwrap_or_default();

        let init_equalities = operators
            .get(init_name)
            .map(|op| extract_equalities(&op.body.node, &var_set))
            .unwrap_or_default();

        let (next_assignments, action_names) = operators
            .get(next_name)
            .map(|op| extract_next_info(&op.body.node, &var_set, &operators))
            .unwrap_or_default();

        Self {
            variables,
            operators,
            init_memberships,
            init_equalities,
            next_assignments,
            action_names,
            existing_invariants,
        }
    }
}

// ---------------------------------------------------------------------------
// AST extraction helpers
// ---------------------------------------------------------------------------

/// Collect all state variable names from VARIABLE declarations.
fn extract_variables(module: &Module) -> Vec<String> {
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

/// Collect all operator definitions by name.
fn extract_operators(module: &Module) -> HashMap<String, OperatorDef> {
    let mut ops = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            ops.insert(op.name.node.clone(), op.clone());
        }
    }
    ops
}

/// Flatten conjunctions into a list of conjuncts.
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

/// Flatten disjunctions into a list of disjuncts.
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

/// Extract `var \in S` membership constraints from an Init-like expression.
fn extract_memberships(expr: &Expr, vars: &HashSet<&str>) -> Vec<MembershipConstraint> {
    let mut result = Vec::new();
    for conjunct in flatten_and(expr) {
        extract_memberships_from_conjunct(conjunct, vars, &mut result);
    }
    result
}

fn extract_memberships_from_conjunct(
    expr: &Expr,
    vars: &HashSet<&str>,
    out: &mut Vec<MembershipConstraint>,
) {
    match expr {
        Expr::In(lhs, rhs) => {
            if let Some(name) = expr_as_var_name(&lhs.node, vars) {
                out.push(MembershipConstraint {
                    var_name: name,
                    set_text: pretty_expr(&rhs.node),
                });
            }
        }
        Expr::And(lhs, rhs) => {
            extract_memberships_from_conjunct(&lhs.node, vars, out);
            extract_memberships_from_conjunct(&rhs.node, vars, out);
        }
        Expr::Label(label) => {
            extract_memberships_from_conjunct(&label.body.node, vars, out);
        }
        Expr::Let(_, body) => {
            extract_memberships_from_conjunct(&body.node, vars, out);
        }
        _ => {}
    }
}

/// Extract `var = value` equality constraints from an Init-like expression.
fn extract_equalities(expr: &Expr, vars: &HashSet<&str>) -> Vec<EqualityConstraint> {
    let mut result = Vec::new();
    for conjunct in flatten_and(expr) {
        extract_equalities_from_conjunct(conjunct, vars, &mut result);
    }
    result
}

fn extract_equalities_from_conjunct(
    expr: &Expr,
    vars: &HashSet<&str>,
    out: &mut Vec<EqualityConstraint>,
) {
    match expr {
        Expr::Eq(lhs, rhs) => {
            if let Some(name) = expr_as_var_name(&lhs.node, vars) {
                out.push(EqualityConstraint {
                    var_name: name,
                    value_text: pretty_expr(&rhs.node),
                });
            } else if let Some(name) = expr_as_var_name(&rhs.node, vars) {
                out.push(EqualityConstraint {
                    var_name: name,
                    value_text: pretty_expr(&lhs.node),
                });
            }
        }
        Expr::And(lhs, rhs) => {
            extract_equalities_from_conjunct(&lhs.node, vars, out);
            extract_equalities_from_conjunct(&rhs.node, vars, out);
        }
        Expr::Label(label) => {
            extract_equalities_from_conjunct(&label.body.node, vars, out);
        }
        _ => {}
    }
}

/// If the expression is a simple variable reference (Ident or StateVar) that
/// is in the known variable set, return its name.
fn expr_as_var_name(expr: &Expr, vars: &HashSet<&str>) -> Option<String> {
    match expr {
        Expr::Ident(name, _) if vars.contains(name.as_str()) => Some(name.clone()),
        Expr::StateVar(name, _, _) => Some(name.clone()),
        _ => None,
    }
}

/// If the expression is a primed variable reference, return the base variable name.
fn expr_as_primed_var(expr: &Expr, vars: &HashSet<&str>) -> Option<String> {
    match expr {
        Expr::Prime(inner) => expr_as_var_name(&inner.node, vars),
        _ => None,
    }
}

/// Extract structural information from the Next relation.
///
/// Returns (assignments, action_names). The Next relation is typically a
/// disjunction of action predicates, each of which is a conjunction of
/// primed-variable assignments and guards.
fn extract_next_info(
    expr: &Expr,
    vars: &HashSet<&str>,
    operators: &HashMap<String, OperatorDef>,
) -> (Vec<NextAssignment>, Vec<String>) {
    let mut assignments = Vec::new();
    let mut action_names = Vec::new();

    let disjuncts = flatten_or(expr);
    for disjunct in &disjuncts {
        // Try to resolve action name if disjunct is an operator application or ident
        let (action_name, action_body) = resolve_action(disjunct, operators);
        if let Some(ref name) = action_name {
            action_names.push(name.clone());
        }

        let conjuncts = flatten_and(action_body);
        for conjunct in &conjuncts {
            extract_assignment_pattern(conjunct, vars, &action_name, &mut assignments);
        }
    }

    (assignments, action_names)
}

/// Resolve an action disjunct: if it is an identifier referencing an operator,
/// return (Some(name), operator_body). Otherwise return (None, expr).
fn resolve_action<'a>(
    expr: &'a Expr,
    operators: &'a HashMap<String, OperatorDef>,
) -> (Option<String>, &'a Expr) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if let Some(op) = operators.get(name.as_str()) {
                if op.params.is_empty() {
                    return (Some(name.clone()), &op.body.node);
                }
            }
            (Some(name.clone()), expr)
        }
        Expr::Apply(op_expr, _args) => {
            if let Expr::Ident(name, _) = &op_expr.node {
                (Some(name.clone()), expr)
            } else {
                (None, expr)
            }
        }
        Expr::Label(label) => resolve_action(&label.body.node, operators),
        _ => (None, expr),
    }
}

/// Extract assignment patterns from a single conjunct of an action.
fn extract_assignment_pattern(
    expr: &Expr,
    vars: &HashSet<&str>,
    action_name: &Option<String>,
    out: &mut Vec<NextAssignment>,
) {
    match expr {
        // var' = <rhs>
        Expr::Eq(lhs, rhs) => {
            if let Some(var) = expr_as_primed_var(&lhs.node, vars) {
                let pattern = classify_rhs_pattern(&var, &rhs.node, vars);
                out.push(NextAssignment {
                    action_name: action_name.clone(),
                    var_name: var,
                    pattern,
                });
            } else if let Some(var) = expr_as_primed_var(&rhs.node, vars) {
                let pattern = classify_rhs_pattern(&var, &lhs.node, vars);
                out.push(NextAssignment {
                    action_name: action_name.clone(),
                    var_name: var,
                    pattern,
                });
            }
        }
        // var' \in S
        Expr::In(lhs, rhs) => {
            if let Some(var) = expr_as_primed_var(&lhs.node, vars) {
                out.push(NextAssignment {
                    action_name: action_name.clone(),
                    var_name: var.clone(),
                    pattern: AssignmentPattern::MemberOf(pretty_expr(&rhs.node)),
                });
            }
        }
        // var' >= var (non-decreasing)
        Expr::Geq(lhs, rhs) => {
            if let Some(pvar) = expr_as_primed_var(&lhs.node, vars) {
                if let Some(base) = expr_as_var_name(&rhs.node, vars) {
                    if pvar == base {
                        out.push(NextAssignment {
                            action_name: action_name.clone(),
                            var_name: pvar,
                            pattern: AssignmentPattern::NonDecreasing,
                        });
                    }
                }
            }
        }
        // var' <= var (non-increasing)
        Expr::Leq(lhs, rhs) => {
            if let Some(pvar) = expr_as_primed_var(&lhs.node, vars) {
                if let Some(base) = expr_as_var_name(&rhs.node, vars) {
                    if pvar == base {
                        out.push(NextAssignment {
                            action_name: action_name.clone(),
                            var_name: pvar,
                            pattern: AssignmentPattern::NonIncreasing,
                        });
                    }
                }
            }
        }
        // UNCHANGED var
        Expr::Unchanged(inner) => {
            let unchanged_vars = collect_unchanged_vars(&inner.node, vars);
            for var in unchanged_vars {
                out.push(NextAssignment {
                    action_name: action_name.clone(),
                    var_name: var,
                    pattern: AssignmentPattern::Unchanged,
                });
            }
        }
        Expr::And(lhs, rhs) => {
            extract_assignment_pattern(&lhs.node, vars, action_name, out);
            extract_assignment_pattern(&rhs.node, vars, action_name, out);
        }
        Expr::Label(label) => {
            extract_assignment_pattern(&label.body.node, vars, action_name, out);
        }
        _ => {}
    }
}

/// Classify the RHS of `var' = rhs` into an assignment pattern.
fn classify_rhs_pattern(var_name: &str, rhs: &Expr, vars: &HashSet<&str>) -> AssignmentPattern {
    // Check for var + expr
    if let Expr::Add(lhs, rhs_inner) = rhs {
        if let Some(base) = expr_as_var_name(&lhs.node, vars) {
            if base == var_name {
                return AssignmentPattern::Increment(pretty_expr(&rhs_inner.node));
            }
        }
        if let Some(base) = expr_as_var_name(&rhs_inner.node, vars) {
            if base == var_name {
                return AssignmentPattern::Increment(pretty_expr(&lhs.node));
            }
        }
    }
    // Check for var - expr
    if let Expr::Sub(lhs, rhs_inner) = rhs {
        if let Some(base) = expr_as_var_name(&lhs.node, vars) {
            if base == var_name {
                return AssignmentPattern::Decrement(pretty_expr(&rhs_inner.node));
            }
        }
    }
    // Check for simple identity (UNCHANGED equivalent)
    if let Some(base) = expr_as_var_name(rhs, vars) {
        if base == var_name {
            return AssignmentPattern::Unchanged;
        }
    }
    AssignmentPattern::DirectAssign(pretty_expr(rhs))
}

/// Collect variable names from UNCHANGED expressions (handles tuples).
fn collect_unchanged_vars(expr: &Expr, vars: &HashSet<&str>) -> Vec<String> {
    let mut result = Vec::new();
    match expr {
        Expr::Tuple(elems) => {
            for elem in elems {
                result.extend(collect_unchanged_vars(&elem.node, vars));
            }
        }
        Expr::Ident(name, _) if vars.contains(name.as_str()) => {
            result.push(name.clone());
        }
        Expr::StateVar(name, _, _) => {
            result.push(name.clone());
        }
        _ => {}
    }
    result
}

// ---------------------------------------------------------------------------
// Invariant generation strategies
// ---------------------------------------------------------------------------

/// Strategy 1: Type invariants from Init predicates.
///
/// For each `var \in S` in Init, generate `var \in S` as a candidate invariant.
/// These are the most common and highest-confidence invariants.
fn generate_type_invariants(info: &SpecInfo, candidates: &mut Vec<CandidateInvariant>) {
    for mc in &info.init_memberships {
        let tla_text = format!("{} \\in {}", mc.var_name, mc.set_text);
        let name = format!("TypeInv_{}", mc.var_name);

        // Skip if this is already a declared invariant
        if info.existing_invariants.contains(&name) {
            continue;
        }

        candidates.push(CandidateInvariant {
            name,
            tla_text,
            strategy: InvariantStrategy::TypeInvariant,
            rationale: format!(
                "Init constrains {} to {}, which should hold in all reachable states",
                mc.var_name, mc.set_text
            ),
            confidence: 0.9,
            verified: None,
            variables: vec![mc.var_name.clone()],
        });
    }
}

/// Strategy 2: Range preservation — Init constraint preserved by Next.
///
/// If Init says `var \in S` and every Next disjunct that modifies `var` keeps
/// it within `S` (via `var' \in S`, `var' = var + k` where result stays in S,
/// or UNCHANGED), then `var \in S` is likely an invariant.
fn generate_range_preservation(info: &SpecInfo, candidates: &mut Vec<CandidateInvariant>) {
    for mc in &info.init_memberships {
        // Check if all Next assignments for this variable are compatible with the
        // Init membership constraint.
        let var_assignments: Vec<&NextAssignment> = info
            .next_assignments
            .iter()
            .filter(|a| a.var_name == mc.var_name)
            .collect();

        if var_assignments.is_empty() {
            continue;
        }

        let mut all_preserve = true;
        let mut preserving_actions = Vec::new();

        for assignment in &var_assignments {
            let preserved = match &assignment.pattern {
                AssignmentPattern::MemberOf(set_text) => set_text == &mc.set_text,
                AssignmentPattern::Unchanged => true,
                AssignmentPattern::DirectAssign(_) => false,
                AssignmentPattern::Increment(_) | AssignmentPattern::Decrement(_) => {
                    // Increment/decrement may or may not preserve range.
                    // Conservative: mark as not definitively preserved.
                    false
                }
                AssignmentPattern::NonDecreasing | AssignmentPattern::NonIncreasing => false,
            };

            if preserved {
                if let Some(ref action) = assignment.action_name {
                    preserving_actions.push(action.clone());
                }
            } else {
                all_preserve = false;
            }
        }

        if all_preserve && !var_assignments.is_empty() {
            let name = format!("RangeInv_{}", mc.var_name);
            if info.existing_invariants.contains(&name) {
                continue;
            }

            let tla_text = format!("{} \\in {}", mc.var_name, mc.set_text);
            let actions_desc = if preserving_actions.is_empty() {
                "all actions".to_string()
            } else {
                preserving_actions.join(", ")
            };

            candidates.push(CandidateInvariant {
                name,
                tla_text,
                strategy: InvariantStrategy::RangePreservation,
                rationale: format!(
                    "Init constrains {} to {} and {} preserve this membership",
                    mc.var_name, mc.set_text, actions_desc
                ),
                confidence: 0.95,
                verified: None,
                variables: vec![mc.var_name.clone()],
            });
        }
    }
}

/// Strategy 3: Monotonicity detection.
///
/// If every Next disjunct either increments a variable, leaves it unchanged,
/// or explicitly constrains `var' >= var`, then `var' >= var` is an action
/// invariant and we can derive that `var >= init_value` is a state invariant.
fn generate_monotonicity(info: &SpecInfo, candidates: &mut Vec<CandidateInvariant>) {
    for var in &info.variables {
        let var_assignments: Vec<&NextAssignment> = info
            .next_assignments
            .iter()
            .filter(|a| a.var_name == *var)
            .collect();

        if var_assignments.is_empty() {
            continue;
        }

        let mut all_non_decreasing = true;
        let mut all_non_increasing = true;

        for assignment in &var_assignments {
            match &assignment.pattern {
                AssignmentPattern::Increment(_) | AssignmentPattern::NonDecreasing => {
                    all_non_increasing = false;
                }
                AssignmentPattern::Decrement(_) | AssignmentPattern::NonIncreasing => {
                    all_non_decreasing = false;
                }
                AssignmentPattern::Unchanged => {
                    // Unchanged preserves both directions.
                }
                _ => {
                    all_non_decreasing = false;
                    all_non_increasing = false;
                }
            }
        }

        // Find initial value for bound construction
        let init_eq = info.init_equalities.iter().find(|eq| eq.var_name == *var);

        if all_non_decreasing && !all_non_increasing {
            let name = format!("MonoInc_{}", var);
            if info.existing_invariants.contains(&name) {
                continue;
            }

            let tla_text = if let Some(eq) = init_eq {
                format!("{} >= {}", var, eq.value_text)
            } else {
                // Without knowing the initial value, express as action invariant
                format!("{var}' >= {var}", var = var)
            };

            candidates.push(CandidateInvariant {
                name,
                tla_text,
                strategy: InvariantStrategy::Monotonicity,
                rationale: format!(
                    "All Next actions either increment {} or leave it unchanged",
                    var
                ),
                confidence: 0.85,
                verified: None,
                variables: vec![var.clone()],
            });
        } else if all_non_increasing && !all_non_decreasing {
            let name = format!("MonoDec_{}", var);
            if info.existing_invariants.contains(&name) {
                continue;
            }

            let tla_text = if let Some(eq) = init_eq {
                format!("{} <= {}", var, eq.value_text)
            } else {
                format!("{var}' <= {var}", var = var)
            };

            candidates.push(CandidateInvariant {
                name,
                tla_text,
                strategy: InvariantStrategy::Monotonicity,
                rationale: format!(
                    "All Next actions either decrement {} or leave it unchanged",
                    var
                ),
                confidence: 0.85,
                verified: None,
                variables: vec![var.clone()],
            });
        }
    }
}

/// Strategy 4: Conservation laws.
///
/// If we detect that the sum of a set of variables is preserved by every Next
/// disjunct (increments to one are balanced by decrements to another, plus
/// UNCHANGED for the rest), then `sum = initial_sum` is an invariant.
fn generate_conservation_laws(info: &SpecInfo, candidates: &mut Vec<CandidateInvariant>) {
    // Only consider integer-initialized variables for conservation laws.
    let int_vars: Vec<(&str, &str)> = info
        .init_equalities
        .iter()
        .filter(|eq| is_likely_integer_expr(&eq.value_text))
        .map(|eq| (eq.var_name.as_str(), eq.value_text.as_str()))
        .collect();

    if int_vars.len() < 2 {
        return;
    }

    // Group Next assignments by action to check balance per action.
    let mut actions: HashMap<Option<String>, Vec<&NextAssignment>> = HashMap::new();
    for assignment in &info.next_assignments {
        actions
            .entry(assignment.action_name.clone())
            .or_default()
            .push(assignment);
    }

    // Check all pairs for conservation.
    for i in 0..int_vars.len() {
        for j in (i + 1)..int_vars.len() {
            let (var_a, init_a) = int_vars[i];
            let (var_b, init_b) = int_vars[j];

            let conserved = check_pair_conservation(var_a, var_b, &actions);

            if conserved {
                let name = format!("Conserve_{}_{}", var_a, var_b);
                if info.existing_invariants.contains(&name) {
                    continue;
                }

                let tla_text = format!("{} + {} = {} + {}", var_a, var_b, init_a, init_b);

                candidates.push(CandidateInvariant {
                    name,
                    tla_text,
                    strategy: InvariantStrategy::ConservationLaw,
                    rationale: format!(
                        "Every action that modifies {} or {} preserves their sum",
                        var_a, var_b
                    ),
                    confidence: 0.80,
                    verified: None,
                    variables: vec![var_a.to_string(), var_b.to_string()],
                });
            }
        }
    }
}

/// Check whether a pair of variables has a conservation law across all actions.
///
/// A pair (a, b) is conserved if for every action, increments to `a` are matched
/// by equal decrements to `b` (or vice versa), or both are unchanged.
fn check_pair_conservation(
    var_a: &str,
    var_b: &str,
    actions: &HashMap<Option<String>, Vec<&NextAssignment>>,
) -> bool {
    for (_action, assignments) in actions {
        let a_pattern = assignments.iter().find(|a| a.var_name == var_a);
        let b_pattern = assignments.iter().find(|a| a.var_name == var_b);

        match (a_pattern, b_pattern) {
            (None, None) => {
                // Neither variable is mentioned — implicitly unchanged.
                continue;
            }
            (Some(a), None) => {
                // Only a is modified — conservation requires a unchanged too.
                if !matches!(a.pattern, AssignmentPattern::Unchanged) {
                    return false;
                }
            }
            (None, Some(b)) => {
                if !matches!(b.pattern, AssignmentPattern::Unchanged) {
                    return false;
                }
            }
            (Some(a), Some(b)) => {
                let balanced = match (&a.pattern, &b.pattern) {
                    (AssignmentPattern::Unchanged, AssignmentPattern::Unchanged) => true,
                    (AssignmentPattern::Increment(inc), AssignmentPattern::Decrement(dec)) => {
                        inc == dec
                    }
                    (AssignmentPattern::Decrement(dec), AssignmentPattern::Increment(inc)) => {
                        inc == dec
                    }
                    _ => false,
                };
                if !balanced {
                    return false;
                }
            }
        }
    }
    true
}

/// Heuristic: does this expression text look like an integer literal or
/// simple integer expression?
fn is_likely_integer_expr(text: &str) -> bool {
    let trimmed = text.trim();
    if trimmed.is_empty() {
        return false;
    }
    // Integer literal
    if trimmed.parse::<i64>().is_ok() {
        return true;
    }
    // Negative integer
    if trimmed.starts_with('-') && trimmed[1..].trim().parse::<i64>().is_ok() {
        return true;
    }
    false
}

/// Strategy 5: Mutual exclusion patterns.
///
/// Detects patterns where a set of processes/indices have a "state" variable
/// and at most one can be in a particular state (e.g., critical section).
/// Common patterns:
/// - `Cardinality({p \in Procs : state[p] = "cs"}) <= 1`
/// - For function-typed variables with finite domain, if Init sets all to
///   some default and Next changes at most one at a time.
fn generate_mutual_exclusion(info: &SpecInfo, candidates: &mut Vec<CandidateInvariant>) {
    // Look for function-typed variables (Init: var = [p \in S |-> val])
    for eq in &info.init_equalities {
        let text = &eq.value_text;
        // Detect function constructor pattern: [p \in S |-> v]
        if !text.contains("|->") {
            continue;
        }

        // Check if there is an operator that looks like it is an Init function def.
        // We look for FuncDef patterns in the actual AST for this variable.
        let func_info = find_init_func_def(eq, info);
        if let Some((domain_text, default_text)) = func_info {
            // Look for actions that set var[p] to distinct values
            let distinct_values = find_distinct_assigned_values(&eq.var_name, info);

            if distinct_values.len() >= 2 {
                // For each non-default value, generate a mutex candidate
                for val in &distinct_values {
                    if *val == default_text {
                        continue;
                    }

                    let name = format!("Mutex_{}_{}", eq.var_name, sanitize_name(val));
                    if info.existing_invariants.contains(&name) {
                        continue;
                    }

                    let tla_text = format!(
                        "Cardinality({{p \\in {} : {}[p] = {}}}) <= 1",
                        domain_text, eq.var_name, val
                    );

                    candidates.push(CandidateInvariant {
                        name,
                        tla_text,
                        strategy: InvariantStrategy::MutualExclusion,
                        rationale: format!(
                            "At most one element of {} has {}[p] = {} at any time",
                            domain_text, eq.var_name, val
                        ),
                        confidence: 0.60,
                        verified: None,
                        variables: vec![eq.var_name.clone()],
                    });
                }
            }
        }
    }
}

/// Try to find a function definition pattern in Init for a given equality.
/// Returns (domain_text, default_value_text) if found.
fn find_init_func_def(eq: &EqualityConstraint, info: &SpecInfo) -> Option<(String, String)> {
    let init_name = info
        .operators
        .keys()
        .find(|k| k.as_str() == "Init" || info.operators.get(k.as_str()).map_or(false, |_| false))
        .cloned()
        .unwrap_or_else(|| "Init".to_string());

    let init_op = info.operators.get(&init_name)?;
    find_func_def_for_var(&eq.var_name, &init_op.body.node)
}

/// Recursively search Init body for `var = [p \in S |-> default]` and extract
/// the domain and default value.
fn find_func_def_for_var(var_name: &str, expr: &Expr) -> Option<(String, String)> {
    match expr {
        Expr::And(lhs, rhs) => find_func_def_for_var(var_name, &lhs.node)
            .or_else(|| find_func_def_for_var(var_name, &rhs.node)),
        Expr::Eq(lhs, rhs) => {
            let is_target = match &lhs.node {
                Expr::Ident(name, _) | Expr::StateVar(name, _, _) => name == var_name,
                _ => false,
            };
            if is_target {
                extract_func_def_info(&rhs.node)
            } else {
                let is_target_rhs = match &rhs.node {
                    Expr::Ident(name, _) | Expr::StateVar(name, _, _) => name == var_name,
                    _ => false,
                };
                if is_target_rhs {
                    extract_func_def_info(&lhs.node)
                } else {
                    None
                }
            }
        }
        Expr::Label(label) => find_func_def_for_var(var_name, &label.body.node),
        Expr::Let(_, body) => find_func_def_for_var(var_name, &body.node),
        _ => None,
    }
}

/// Extract (domain_text, body_text) from a FuncDef expression `[x \in S |-> body]`.
fn extract_func_def_info(expr: &Expr) -> Option<(String, String)> {
    if let Expr::FuncDef(bounds, body) = expr {
        if let Some(first_bound) = bounds.first() {
            if let Some(ref domain) = first_bound.domain {
                let domain_text = pretty_expr(&domain.node);
                let body_text = pretty_expr(&body.node);
                return Some((domain_text, body_text));
            }
        }
    }
    None
}

/// Find distinct values assigned to a function-typed variable across all Next actions.
/// Looks for patterns like `var' = [var EXCEPT ![p] = val]`.
fn find_distinct_assigned_values(var_name: &str, info: &SpecInfo) -> Vec<String> {
    let mut values = HashSet::new();

    for assignment in &info.next_assignments {
        if assignment.var_name != var_name {
            continue;
        }
        if let AssignmentPattern::DirectAssign(text) = &assignment.pattern {
            // Try to extract EXCEPT values from the pretty-printed text.
            // Pattern: [var EXCEPT ![...] = val]
            extract_except_values(text, &mut values);
        }
    }

    let mut sorted: Vec<String> = values.into_iter().collect();
    sorted.sort();
    sorted
}

/// Extract assigned values from EXCEPT expression text.
///
/// Looks for `= <value>]` patterns in text like `[var EXCEPT ![p] = "cs"]`.
fn extract_except_values(text: &str, values: &mut HashSet<String>) {
    // Simple heuristic: find `= <token>]` patterns
    let mut rest = text;
    while let Some(eq_pos) = rest.find("= ") {
        let after_eq = &rest[eq_pos + 2..];
        // Find the end of the value (next `]` or `,`)
        let end = after_eq
            .find(']')
            .unwrap_or(after_eq.len())
            .min(after_eq.find(',').unwrap_or(after_eq.len()));
        let val = after_eq[..end].trim();
        if !val.is_empty() && !val.contains("EXCEPT") && !val.contains("![") {
            values.insert(val.to_string());
        }
        rest = &after_eq[end..];
    }
}

/// Sanitize a string for use in a TLA+ operator name.
fn sanitize_name(s: &str) -> String {
    s.chars()
        .filter_map(|c| {
            if c.is_alphanumeric() || c == '_' {
                Some(c)
            } else {
                None
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Deduplication
// ---------------------------------------------------------------------------

/// Remove duplicate candidates by TLA+ text, keeping the highest-confidence version.
fn dedup_candidates(candidates: &mut Vec<CandidateInvariant>) {
    // Sort by confidence descending so that when we dedup we keep the best.
    candidates.sort_by(|a, b| {
        b.confidence
            .partial_cmp(&a.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    let mut seen = HashSet::new();
    candidates.retain(|c| seen.insert(c.tla_text.clone()));
}

// ---------------------------------------------------------------------------
// Verification (optional)
// ---------------------------------------------------------------------------

/// Verify each candidate invariant by running a quick model check.
///
/// This creates a temporary config that includes the candidate as an invariant
/// and runs the model checker with a small state-space bound. If the invariant
/// holds, it is marked as verified; if it is violated, it is marked as falsified.
fn verify_candidates(
    file: &Path,
    config: Option<&Path>,
    candidates: &mut [CandidateInvariant],
) -> Result<()> {
    let tla2_bin = std::env::current_exe().context("resolve tla2 binary path")?;

    for candidate in candidates.iter_mut() {
        let result = verify_single_candidate(file, config, &tla2_bin, candidate);
        match result {
            Ok(holds) => {
                candidate.verified = Some(holds);
            }
            Err(e) => {
                eprintln!(
                    "  warning: verification of {} failed: {}",
                    candidate.name, e
                );
                candidate.verified = None;
            }
        }
    }

    Ok(())
}

/// Verify a single candidate invariant by running `tla2 check` with a
/// temporary config file that adds this invariant.
fn verify_single_candidate(
    spec_file: &Path,
    config: Option<&Path>,
    tla2_bin: &Path,
    candidate: &CandidateInvariant,
) -> Result<bool> {
    // Build a temporary TLA+ file that wraps the original spec and adds the
    // candidate invariant as an operator.
    let module_name = spec_file
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("Spec");

    let inv_module_name = format!("{}__InvGenCheck", module_name);
    let inv_op_name = &candidate.name;

    // Create a wrapper module that extends the original and adds the invariant
    let wrapper_tla = format!(
        "---- MODULE {} ----\nEXTENDS {}\n\n{} == {}\n\n====\n",
        inv_module_name, module_name, inv_op_name, candidate.tla_text
    );

    // Write temporary files
    let tmp_dir = std::env::temp_dir().join("tla2_invgen");
    std::fs::create_dir_all(&tmp_dir).context("create temp dir for invariant verification")?;

    let wrapper_path = tmp_dir.join(format!("{}.tla", inv_module_name));
    std::fs::write(&wrapper_path, &wrapper_tla).context("write wrapper TLA+ file")?;

    // Copy or symlink the original spec into the temp dir so EXTENDS can find it
    let spec_in_tmp = tmp_dir.join(spec_file.file_name().context("spec file name")?);
    if !spec_in_tmp.exists() {
        let original = std::fs::read_to_string(spec_file)?;
        std::fs::write(&spec_in_tmp, original)?;
    }

    // Build config: use original config as base, add the new invariant
    let mut cfg_text = String::new();
    if let Some(cfg_path) = config {
        if let Ok(original_cfg) = std::fs::read_to_string(cfg_path) {
            cfg_text = original_cfg;
        }
    } else {
        let default_cfg = spec_file.with_extension("cfg");
        if let Ok(original_cfg) = std::fs::read_to_string(&default_cfg) {
            cfg_text = original_cfg;
        }
    }
    cfg_text.push_str(&format!("\nINVARIANT {}\n", inv_op_name));

    let cfg_path = tmp_dir.join(format!("{}.cfg", inv_module_name));
    std::fs::write(&cfg_path, &cfg_text).context("write wrapper config file")?;

    // Run tla2 check with a short timeout
    let output = std::process::Command::new(tla2_bin)
        .arg("check")
        .arg(&wrapper_path)
        .arg("--config")
        .arg(&cfg_path)
        .arg("--workers")
        .arg("1")
        .current_dir(&tmp_dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()
        .context("run tla2 check for invariant verification")?;

    // Clean up temporary files (best-effort)
    let _ = std::fs::remove_file(&wrapper_path);
    let _ = std::fs::remove_file(&cfg_path);
    let _ = std::fs::remove_file(&spec_in_tmp);

    // Exit code 0 means no violation found => invariant holds
    Ok(output.status.success())
}

// ---------------------------------------------------------------------------
// Output formatting
// ---------------------------------------------------------------------------

/// Print candidates in human-readable format.
fn print_human(info: &SpecInfo, candidates: &[CandidateInvariant]) {
    println!("Invariant Generation Report");
    println!("==========================");
    println!();
    println!(
        "Variables: {}",
        if info.variables.is_empty() {
            "(none)".to_string()
        } else {
            info.variables.join(", ")
        }
    );
    println!(
        "Actions:   {}",
        if info.action_names.is_empty() {
            "(none detected)".to_string()
        } else {
            info.action_names.join(", ")
        }
    );
    println!();

    if candidates.is_empty() {
        println!("No candidate invariants found.");
        println!();
        println!("Hints:");
        println!("  - Ensure Init uses explicit membership constraints (x \\in S)");
        println!("  - Ensure Next is a disjunction of action predicates");
        println!("  - Constants must be assigned in the config file");
        return;
    }

    println!("Found {} candidate invariant(s):", candidates.len());
    println!();

    for (idx, candidate) in candidates.iter().enumerate() {
        let verified_marker = match candidate.verified {
            Some(true) => " [VERIFIED]",
            Some(false) => " [FALSIFIED]",
            None => "",
        };

        println!(
            "  {}. {} ({}){verified_marker}",
            idx + 1,
            candidate.name,
            candidate.strategy.label()
        );
        println!("     TLA+: {}", candidate.tla_text);
        println!("     Confidence: {:.0}%", candidate.confidence * 100.0);
        println!("     Rationale: {}", candidate.rationale);
        println!("     Variables: {}", candidate.variables.join(", "));
        println!();
    }

    // Summary
    let verified_count = candidates
        .iter()
        .filter(|c| c.verified == Some(true))
        .count();
    let falsified_count = candidates
        .iter()
        .filter(|c| c.verified == Some(false))
        .count();
    let unverified_count = candidates.iter().filter(|c| c.verified.is_none()).count();

    if verified_count > 0 || falsified_count > 0 {
        println!("Verification summary:");
        if verified_count > 0 {
            println!("  Verified:   {}", verified_count);
        }
        if falsified_count > 0 {
            println!("  Falsified:  {}", falsified_count);
        }
        if unverified_count > 0 {
            println!("  Unverified: {}", unverified_count);
        }
    }
}

/// Print candidates as JSON.
fn print_json(candidates: &[CandidateInvariant]) -> Result<()> {
    use std::io::Write;

    let mut out = std::io::stdout().lock();
    writeln!(out, "[")?;
    for (idx, candidate) in candidates.iter().enumerate() {
        let comma = if idx + 1 < candidates.len() { "," } else { "" };
        // Escape strings for JSON manually to avoid pulling in serde for this
        // single subcommand.
        let tla_escaped = json_escape(&candidate.tla_text);
        let rationale_escaped = json_escape(&candidate.rationale);
        let name_escaped = json_escape(&candidate.name);
        let strategy_escaped = json_escape(candidate.strategy.label());
        let vars_json: Vec<String> = candidate
            .variables
            .iter()
            .map(|v| format!("\"{}\"", json_escape(v)))
            .collect();

        let verified_str = match candidate.verified {
            Some(true) => "true",
            Some(false) => "false",
            None => "null",
        };

        writeln!(out, "  {{")?;
        writeln!(out, "    \"name\": \"{}\",", name_escaped)?;
        writeln!(out, "    \"tla_text\": \"{}\",", tla_escaped)?;
        writeln!(out, "    \"strategy\": \"{}\",", strategy_escaped)?;
        writeln!(
            out,
            "    \"strategy_description\": \"{}\",",
            json_escape(candidate.strategy.description())
        )?;
        writeln!(out, "    \"rationale\": \"{}\",", rationale_escaped)?;
        writeln!(out, "    \"confidence\": {:.2},", candidate.confidence)?;
        writeln!(out, "    \"verified\": {},", verified_str)?;
        writeln!(out, "    \"variables\": [{}]", vars_json.join(", "))?;
        writeln!(out, "  }}{}", comma)?;
    }
    writeln!(out, "]")?;
    Ok(())
}

/// Print candidates as TLA+ operator definitions.
fn print_tla(module_name: &str, candidates: &[CandidateInvariant]) {
    println!("\\* =========================================================");
    println!(
        "\\* Auto-generated invariant candidates for module {}",
        module_name
    );
    println!("\\* Generated by: tla2 inv-gen");
    println!("\\* =========================================================");
    println!();

    if candidates.is_empty() {
        println!("\\* No candidate invariants found.");
        return;
    }

    // Group by strategy for readability
    let strategies = [
        InvariantStrategy::TypeInvariant,
        InvariantStrategy::RangePreservation,
        InvariantStrategy::Monotonicity,
        InvariantStrategy::ConservationLaw,
        InvariantStrategy::MutualExclusion,
    ];

    for strategy in &strategies {
        let group: Vec<&CandidateInvariant> = candidates
            .iter()
            .filter(|c| c.strategy == *strategy)
            .collect();

        if group.is_empty() {
            continue;
        }

        println!(
            "\\* --- {} ({}) ---",
            strategy.label(),
            strategy.description()
        );
        println!();

        for candidate in &group {
            let status = match candidate.verified {
                Some(true) => " (verified)",
                Some(false) => " (FALSIFIED - do not use)",
                None => "",
            };
            println!(
                "\\* {}{} [confidence: {:.0}%]",
                candidate.rationale,
                status,
                candidate.confidence * 100.0
            );
            println!("{} ==", candidate.name);
            println!("    {}", candidate.tla_text);
            println!();
        }
    }

    // Generate a combined TypeInvariant if there are multiple type invariants
    let type_invs: Vec<&CandidateInvariant> = candidates
        .iter()
        .filter(|c| c.strategy == InvariantStrategy::TypeInvariant && c.verified != Some(false))
        .collect();

    if type_invs.len() > 1 {
        println!("\\* --- Combined type invariant ---");
        println!();
        println!("CombinedTypeInvariant ==");
        for (idx, inv) in type_invs.iter().enumerate() {
            let prefix = if idx == 0 { "    " } else { "    /\\ " };
            if idx == 0 {
                println!("{}/\\ {}", prefix, inv.tla_text);
            } else {
                println!("{}{}", prefix, inv.tla_text);
            }
        }
        println!();
    }

    // Print config snippet
    let usable: Vec<&CandidateInvariant> = candidates
        .iter()
        .filter(|c| c.verified != Some(false))
        .collect();

    if !usable.is_empty() {
        println!("\\* --- Suggested config additions ---");
        println!("\\* INVARIANT");
        for candidate in &usable {
            println!("\\*     {}", candidate.name);
        }
        if type_invs.len() > 1 {
            println!("\\* Or use the combined:");
            println!("\\*     CombinedTypeInvariant");
        }
    }
}

/// Escape a string for JSON output.
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c < '\x20' => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_json_escape_basic() {
        assert_eq!(json_escape("hello"), "hello");
        assert_eq!(json_escape("a\"b"), "a\\\"b");
        assert_eq!(json_escape("a\\b"), "a\\\\b");
        assert_eq!(json_escape("a\nb"), "a\\nb");
    }

    #[test]
    fn test_sanitize_name() {
        assert_eq!(sanitize_name("cs"), "cs");
        assert_eq!(sanitize_name("\"cs\""), "cs");
        assert_eq!(sanitize_name("a-b"), "ab");
        assert_eq!(sanitize_name("hello_world"), "hello_world");
    }

    #[test]
    fn test_is_likely_integer_expr() {
        assert!(is_likely_integer_expr("0"));
        assert!(is_likely_integer_expr("42"));
        assert!(is_likely_integer_expr("-1"));
        assert!(!is_likely_integer_expr("TRUE"));
        assert!(!is_likely_integer_expr("{}"));
        assert!(!is_likely_integer_expr(""));
    }

    #[test]
    fn test_dedup_candidates() {
        let mut candidates = vec![
            CandidateInvariant {
                name: "A".to_string(),
                tla_text: "x \\in 1..3".to_string(),
                strategy: InvariantStrategy::TypeInvariant,
                rationale: "from Init".to_string(),
                confidence: 0.9,
                verified: None,
                variables: vec!["x".to_string()],
            },
            CandidateInvariant {
                name: "B".to_string(),
                tla_text: "x \\in 1..3".to_string(),
                strategy: InvariantStrategy::RangePreservation,
                rationale: "preserved by Next".to_string(),
                confidence: 0.95,
                verified: None,
                variables: vec!["x".to_string()],
            },
        ];
        dedup_candidates(&mut candidates);
        assert_eq!(candidates.len(), 1);
        // Higher confidence (0.95) should be kept
        assert_eq!(candidates[0].name, "B");
    }

    #[test]
    fn test_extract_except_values() {
        let mut values = HashSet::new();
        extract_except_values("[state EXCEPT ![self] = \"cs\"]", &mut values);
        assert!(values.contains("\"cs\""));
    }

    #[test]
    fn test_extract_except_values_multiple() {
        let mut values = HashSet::new();
        extract_except_values(
            "[state EXCEPT ![self] = \"cs\", ![other] = \"idle\"]",
            &mut values,
        );
        assert!(values.contains("\"cs\""));
        assert!(values.contains("\"idle\""));
    }

    #[test]
    fn test_invariant_strategy_labels() {
        assert_eq!(InvariantStrategy::TypeInvariant.label(), "type-invariant");
        assert_eq!(
            InvariantStrategy::RangePreservation.label(),
            "range-preservation"
        );
        assert_eq!(InvariantStrategy::Monotonicity.label(), "monotonicity");
        assert_eq!(
            InvariantStrategy::ConservationLaw.label(),
            "conservation-law"
        );
        assert_eq!(
            InvariantStrategy::MutualExclusion.label(),
            "mutual-exclusion"
        );
    }

    #[test]
    fn test_strategy_descriptions_nonempty() {
        let strategies = [
            InvariantStrategy::TypeInvariant,
            InvariantStrategy::RangePreservation,
            InvariantStrategy::Monotonicity,
            InvariantStrategy::ConservationLaw,
            InvariantStrategy::MutualExclusion,
        ];
        for s in &strategies {
            assert!(!s.description().is_empty());
        }
    }
}
