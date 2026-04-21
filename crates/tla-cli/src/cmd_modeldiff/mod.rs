// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 model-diff` -- structural comparison of two TLA+ specifications.
//!
//! Parses both spec versions (old and new TLA+ files), compares module-level
//! declarations, performs structural AST comparison on operator bodies, builds
//! a dependency graph to identify transitive impact on invariants and
//! properties, and produces either human-readable colored output or structured
//! JSON.
//!
//! # Change categories
//!
//! Each declaration-level item is classified as:
//! - **Added** -- present in new but absent in old
//! - **Removed** -- present in old but absent in new
//! - **Modified** -- present in both but structurally different body
//!
//! For modified operators, a structural diff of the AST expression tree is
//! computed, yielding fine-grained change descriptions (e.g. "guard condition
//! changed", "new conjunct added").
//!
//! # Impact analysis
//!
//! A call-graph is built from the new spec. For every changed (added/removed/
//! modified) operator, transitive dependents are computed. When any transitive
//! dependent is an invariant or property (from `.cfg`), it is reported in the
//! impact section so the user knows which verification obligations may need
//! re-checking.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{
    BoundVar, CaseArm, ConstantDecl, ExceptPathElement, ExceptSpec, Expr, Module, OperatorDef,
    Substitution, Unit,
};
use tla_core::{lower_main_module, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the model-diff command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ModelDiffOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Compare two TLA+ specifications structurally, reporting declaration-level
/// changes, structural expression diffs, and transitive impact analysis on
/// invariants and properties.
pub(crate) fn cmd_model_diff(
    old_file: &Path,
    new_file: &Path,
    format: ModelDiffOutputFormat,
) -> Result<()> {
    // 1. Parse and lower both specs.
    let old_module = parse_and_lower(old_file)?;
    let new_module = parse_and_lower(new_file)?;

    let old_source = read_source(old_file)?;
    let new_source = read_source(new_file)?;

    // 2. Collect declarations from both modules.
    let old_decls = ModuleDecls::extract(&old_module, &old_source);
    let new_decls = ModuleDecls::extract(&new_module, &new_source);

    // 3. Compute diffs for each declaration category.
    let var_diff = diff_string_sets(&old_decls.variables, &new_decls.variables);
    let const_diff = diff_string_sets(&old_decls.constants, &new_decls.constants);
    let extends_diff = diff_string_sets(&old_decls.extends, &new_decls.extends);
    let op_diff = diff_operators(&old_decls, &new_decls, &old_source, &new_source);

    // 4. Load invariants/properties from config files.
    let old_config = load_config(old_file);
    let new_config = load_config(new_file);
    let inv_diff = diff_config_list(
        old_config.as_ref().map(|c| &c.invariants),
        new_config.as_ref().map(|c| &c.invariants),
    );
    let prop_diff = diff_config_list(
        old_config.as_ref().map(|c| &c.properties),
        new_config.as_ref().map(|c| &c.properties),
    );

    // 5. Build dependency graph from the *new* spec and compute impact.
    let call_graph = build_call_graph(&new_module);
    let reverse_graph = reverse_call_graph(&call_graph);
    let new_invariants: BTreeSet<String> = new_config
        .as_ref()
        .map(|c| c.invariants.iter().cloned().collect())
        .unwrap_or_default();
    let new_properties: BTreeSet<String> = new_config
        .as_ref()
        .map(|c| c.properties.iter().cloned().collect())
        .unwrap_or_default();

    let changed_ops: BTreeSet<String> = op_diff
        .added
        .iter()
        .map(|o| o.name.clone())
        .chain(op_diff.removed.iter().map(|o| o.name.clone()))
        .chain(op_diff.modified.iter().map(|o| o.name.clone()))
        .collect();

    let impact =
        compute_impact(&changed_ops, &reverse_graph, &new_invariants, &new_properties);

    // 6. Assemble full diff report.
    let report = ModelDiffReport {
        old_file: old_file.display().to_string(),
        new_file: new_file.display().to_string(),
        extends: extends_diff,
        variables: var_diff,
        constants: const_diff,
        operators: op_diff,
        invariants: inv_diff,
        properties: prop_diff,
        impact,
    };

    // 7. Emit output.
    match format {
        ModelDiffOutputFormat::Human => print_human(&report),
        ModelDiffOutputFormat::Json => print_json(&report),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Internal data structures
// ---------------------------------------------------------------------------

/// Extracted declarations from a single module.
struct ModuleDecls {
    variables: BTreeSet<String>,
    constants: BTreeSet<String>,
    extends: BTreeSet<String>,
    operators: BTreeMap<String, OperatorSnapshot>,
}

/// Snapshot of an operator definition, enough for comparison.
struct OperatorSnapshot {
    params: Vec<String>,
    body_pretty: String,
    line: usize,
    local: bool,
    contains_prime: bool,
}

impl ModuleDecls {
    fn extract(module: &Module, source: &str) -> Self {
        let mut variables = BTreeSet::new();
        let mut constants = BTreeSet::new();
        let mut operators = BTreeMap::new();

        for unit in &module.units {
            match &unit.node {
                Unit::Variable(decls) => {
                    for decl in decls {
                        variables.insert(decl.node.clone());
                    }
                }
                Unit::Constant(decls) => {
                    for decl in decls {
                        constants.insert(format_constant_decl(decl));
                    }
                }
                Unit::Operator(def) => {
                    let params: Vec<String> =
                        def.params.iter().map(|p| p.name.node.clone()).collect();
                    let body_pretty = pretty_expr(&def.body.node);
                    let line = line_of(source, def.name.span.start);
                    operators.insert(
                        def.name.node.clone(),
                        OperatorSnapshot {
                            params,
                            body_pretty,
                            line,
                            local: def.local,
                            contains_prime: def.contains_prime,
                        },
                    );
                }
                _ => {}
            }
        }

        let extends = module
            .extends
            .iter()
            .map(|s| s.node.clone())
            .collect();

        ModuleDecls {
            variables,
            constants,
            extends,
            operators,
        }
    }
}

// ---------------------------------------------------------------------------
// Diff result structures (serializable for JSON output)
// ---------------------------------------------------------------------------

#[derive(Debug, serde::Serialize)]
struct ModelDiffReport {
    old_file: String,
    new_file: String,
    extends: StringSetDiff,
    variables: StringSetDiff,
    constants: StringSetDiff,
    operators: OperatorsDiff,
    invariants: StringSetDiff,
    properties: StringSetDiff,
    impact: ImpactReport,
}

#[derive(Debug, Default, serde::Serialize)]
struct StringSetDiff {
    added: Vec<String>,
    removed: Vec<String>,
}

#[derive(Debug, Default, serde::Serialize)]
struct OperatorsDiff {
    added: Vec<OpSummary>,
    removed: Vec<OpSummary>,
    modified: Vec<ModifiedOp>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    signature_changed: Vec<SignatureChange>,
}

#[derive(Debug, serde::Serialize)]
struct OpSummary {
    name: String,
    line: usize,
    arity: usize,
    local: bool,
}

#[derive(Debug, serde::Serialize)]
struct ModifiedOp {
    name: String,
    old_line: usize,
    new_line: usize,
    structural_changes: Vec<StructuralChange>,
    old_body: String,
    new_body: String,
}

#[derive(Debug, serde::Serialize)]
struct SignatureChange {
    name: String,
    old_params: Vec<String>,
    new_params: Vec<String>,
}

/// A fine-grained structural change description.
#[derive(Debug, Clone, serde::Serialize)]
struct StructuralChange {
    kind: ChangeKind,
    description: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    path: Option<String>,
}

#[derive(Debug, Clone, serde::Serialize)]
#[serde(rename_all = "snake_case")]
enum ChangeKind {
    /// The top-level expression type changed (e.g. And -> Or).
    ExprTypeChanged,
    /// A conjunct was added or removed.
    ConjunctChanged,
    /// A disjunct was added or removed.
    DisjunctChanged,
    /// An IF-THEN-ELSE condition changed.
    GuardChanged,
    /// An IF-THEN-ELSE branch changed.
    BranchChanged,
    /// A quantifier bound domain changed.
    BoundDomainChanged,
    /// A quantifier body changed.
    QuantifierBodyChanged,
    /// A literal value changed.
    LiteralChanged,
    /// A sub-expression changed (catch-all for deeper structural diff).
    SubExprChanged,
    /// Operator application arguments changed.
    ArgumentsChanged,
    /// A LET definition changed.
    LetDefChanged,
    /// A CASE arm changed.
    CaseArmChanged,
    /// A record field changed.
    RecordFieldChanged,
    /// A set element changed.
    SetElementChanged,
    /// Parameters changed.
    ParametersChanged,
}

#[derive(Debug, Default, serde::Serialize)]
struct ImpactReport {
    /// Operators whose changes transitively affect invariants.
    affected_invariants: Vec<ImpactEntry>,
    /// Operators whose changes transitively affect properties.
    affected_properties: Vec<ImpactEntry>,
    /// All transitively affected operators (beyond the directly changed ones).
    transitive_dependents: Vec<String>,
}

#[derive(Debug, serde::Serialize)]
struct ImpactEntry {
    /// The invariant or property name.
    name: String,
    /// Which changed operators cause this impact (direct or transitive).
    caused_by: Vec<String>,
}

impl ModelDiffReport {
    fn is_empty(&self) -> bool {
        self.extends.added.is_empty()
            && self.extends.removed.is_empty()
            && self.variables.added.is_empty()
            && self.variables.removed.is_empty()
            && self.constants.added.is_empty()
            && self.constants.removed.is_empty()
            && self.operators.added.is_empty()
            && self.operators.removed.is_empty()
            && self.operators.modified.is_empty()
            && self.operators.signature_changed.is_empty()
            && self.invariants.added.is_empty()
            && self.invariants.removed.is_empty()
            && self.properties.added.is_empty()
            && self.properties.removed.is_empty()
    }

    fn total_changes(&self) -> usize {
        self.extends.added.len()
            + self.extends.removed.len()
            + self.variables.added.len()
            + self.variables.removed.len()
            + self.constants.added.len()
            + self.constants.removed.len()
            + self.operators.added.len()
            + self.operators.removed.len()
            + self.operators.modified.len()
            + self.operators.signature_changed.len()
            + self.invariants.added.len()
            + self.invariants.removed.len()
            + self.properties.added.len()
            + self.properties.removed.len()
    }
}

// ---------------------------------------------------------------------------
// Parse + lower helper
// ---------------------------------------------------------------------------

fn parse_and_lower(file: &Path) -> Result<Module> {
    let source = read_source(file)?;
    let parse_result = tla_core::parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diagnostic =
                tla_core::parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "parse failed for {}: {} error(s)",
            file.display(),
            parse_result.errors.len()
        );
    }
    let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lower failed for {}: {} error(s)",
            file.display(),
            result.errors.len()
        );
    }
    result
        .module
        .context(format!("lower produced no module for {}", file.display()))
}

// ---------------------------------------------------------------------------
// Utility functions
// ---------------------------------------------------------------------------

/// Compute 1-indexed line number from byte offset within source text.
fn line_of(source: &str, byte_offset: u32) -> usize {
    let offset = byte_offset as usize;
    let clamped = offset.min(source.len());
    source[..clamped].bytes().filter(|&b| b == b'\n').count() + 1
}

fn format_constant_decl(decl: &ConstantDecl) -> String {
    match decl.arity {
        Some(arity) if arity > 0 => {
            let underscores: Vec<&str> = (0..arity).map(|_| "_").collect();
            format!("{}({})", decl.name.node, underscores.join(", "))
        }
        _ => decl.name.node.clone(),
    }
}

/// Load a `.cfg` file for a spec, returning None if not found or unparseable.
fn load_config(spec_file: &Path) -> Option<tla_check::Config> {
    let mut cfg_path = spec_file.to_path_buf();
    cfg_path.set_extension("cfg");
    let source = std::fs::read_to_string(&cfg_path).ok()?;
    tla_check::Config::parse(&source).ok()
}

// ---------------------------------------------------------------------------
// Set-level diffs
// ---------------------------------------------------------------------------

fn diff_string_sets(old: &BTreeSet<String>, new: &BTreeSet<String>) -> StringSetDiff {
    StringSetDiff {
        added: new.difference(old).cloned().collect(),
        removed: old.difference(new).cloned().collect(),
    }
}

fn diff_config_list(
    old: Option<&Vec<String>>,
    new: Option<&Vec<String>>,
) -> StringSetDiff {
    let empty = Vec::new();
    let old_set: BTreeSet<String> = old.unwrap_or(&empty).iter().cloned().collect();
    let new_set: BTreeSet<String> = new.unwrap_or(&empty).iter().cloned().collect();
    diff_string_sets(&old_set, &new_set)
}

// ---------------------------------------------------------------------------
// Operator-level diff
// ---------------------------------------------------------------------------

fn diff_operators(
    old_decls: &ModuleDecls,
    new_decls: &ModuleDecls,
    old_source: &str,
    new_source: &str,
) -> OperatorsDiff {
    let mut added = Vec::new();
    let mut removed = Vec::new();
    let mut modified = Vec::new();
    let mut signature_changed = Vec::new();

    // Find added and modified operators.
    for (name, new_snap) in &new_decls.operators {
        match old_decls.operators.get(name) {
            None => {
                added.push(OpSummary {
                    name: name.clone(),
                    line: new_snap.line,
                    arity: new_snap.params.len(),
                    local: new_snap.local,
                });
            }
            Some(old_snap) => {
                // Check signature changes.
                if old_snap.params != new_snap.params {
                    signature_changed.push(SignatureChange {
                        name: name.clone(),
                        old_params: old_snap.params.clone(),
                        new_params: new_snap.params.clone(),
                    });
                }
                // Check body changes.
                if old_snap.body_pretty != new_snap.body_pretty {
                    // Get the original AST nodes for structural comparison.
                    let old_def = find_operator_def_by_name(old_source, name);
                    let new_def = find_operator_def_by_name(new_source, name);

                    let structural_changes = match (old_def, new_def) {
                        (Some(old_ast), Some(new_ast)) => {
                            structural_expr_diff(&old_ast.body.node, &new_ast.body.node, "")
                        }
                        _ => {
                            vec![StructuralChange {
                                kind: ChangeKind::SubExprChanged,
                                description: "body changed (AST not available for \
                                              structural diff)"
                                    .to_string(),
                                path: None,
                            }]
                        }
                    };

                    modified.push(ModifiedOp {
                        name: name.clone(),
                        old_line: old_snap.line,
                        new_line: new_snap.line,
                        structural_changes,
                        old_body: old_snap.body_pretty.clone(),
                        new_body: new_snap.body_pretty.clone(),
                    });
                }
            }
        }
    }

    // Find removed operators.
    for (name, old_snap) in &old_decls.operators {
        if !new_decls.operators.contains_key(name) {
            removed.push(OpSummary {
                name: name.clone(),
                line: old_snap.line,
                arity: old_snap.params.len(),
                local: old_snap.local,
            });
        }
    }

    OperatorsDiff {
        added,
        removed,
        modified,
        signature_changed,
    }
}

/// Parse+lower a source string, then find an operator by name.
/// Returns the OperatorDef if found. This re-parses per call but is only used
/// for modified operators (typically a small number).
fn find_operator_def_by_name(source: &str, name: &str) -> Option<OperatorDef> {
    let parse_result = tla_core::parse(source);
    if !parse_result.errors.is_empty() {
        return None;
    }
    let tree = tla_core::SyntaxNode::new_root(parse_result.green_node);
    let result = lower_main_module(FileId(0), &tree, None);
    let module = result.module?;
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            if def.name.node == name {
                return Some(def.clone());
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Structural AST expression diff
// ---------------------------------------------------------------------------

/// Structurally compare two AST expressions, producing a list of fine-grained
/// change descriptions. The `path` parameter tracks the location in the
/// expression tree for reporting (e.g. "lhs", "rhs", "then-branch").
fn structural_expr_diff(old: &Expr, new: &Expr, path: &str) -> Vec<StructuralChange> {
    // Unwrap labels transparently.
    let old = unwrap_label(old);
    let new = unwrap_label(new);

    // Fast path: if pretty-printed forms are identical, no changes.
    if pretty_expr(old) == pretty_expr(new) {
        return Vec::new();
    }

    let path_opt = if path.is_empty() {
        None
    } else {
        Some(path.to_string())
    };

    // If the top-level expression type differs, report that and stop recursing.
    if std::mem::discriminant(old) != std::mem::discriminant(new) {
        return vec![StructuralChange {
            kind: ChangeKind::ExprTypeChanged,
            description: format!(
                "expression type changed from {} to {}",
                expr_kind_name(old),
                expr_kind_name(new)
            ),
            path: path_opt,
        }];
    }

    // Same discriminant: recurse into sub-expressions.
    match (old, new) {
        // --- Logic binary operators ---
        (Expr::And(oa, ob), Expr::And(na, nb)) => {
            diff_binary_children("conjunct", ChangeKind::ConjunctChanged, oa, ob, na, nb, path)
        }
        (Expr::Or(oa, ob), Expr::Or(na, nb)) => {
            diff_binary_children("disjunct", ChangeKind::DisjunctChanged, oa, ob, na, nb, path)
        }
        (Expr::Implies(oa, ob), Expr::Implies(na, nb))
        | (Expr::Equiv(oa, ob), Expr::Equiv(na, nb)) => {
            diff_binary_children(
                "operand",
                ChangeKind::SubExprChanged,
                oa,
                ob,
                na,
                nb,
                path,
            )
        }

        // --- Comparison / arithmetic binary operators ---
        (Expr::Eq(oa, ob), Expr::Eq(na, nb))
        | (Expr::Neq(oa, ob), Expr::Neq(na, nb))
        | (Expr::Lt(oa, ob), Expr::Lt(na, nb))
        | (Expr::Leq(oa, ob), Expr::Leq(na, nb))
        | (Expr::Gt(oa, ob), Expr::Gt(na, nb))
        | (Expr::Geq(oa, ob), Expr::Geq(na, nb))
        | (Expr::In(oa, ob), Expr::In(na, nb))
        | (Expr::NotIn(oa, ob), Expr::NotIn(na, nb))
        | (Expr::Subseteq(oa, ob), Expr::Subseteq(na, nb))
        | (Expr::Union(oa, ob), Expr::Union(na, nb))
        | (Expr::Intersect(oa, ob), Expr::Intersect(na, nb))
        | (Expr::SetMinus(oa, ob), Expr::SetMinus(na, nb))
        | (Expr::FuncSet(oa, ob), Expr::FuncSet(na, nb))
        | (Expr::Add(oa, ob), Expr::Add(na, nb))
        | (Expr::Sub(oa, ob), Expr::Sub(na, nb))
        | (Expr::Mul(oa, ob), Expr::Mul(na, nb))
        | (Expr::Div(oa, ob), Expr::Div(na, nb))
        | (Expr::IntDiv(oa, ob), Expr::IntDiv(na, nb))
        | (Expr::Mod(oa, ob), Expr::Mod(na, nb))
        | (Expr::Pow(oa, ob), Expr::Pow(na, nb))
        | (Expr::Range(oa, ob), Expr::Range(na, nb))
        | (Expr::LeadsTo(oa, ob), Expr::LeadsTo(na, nb))
        | (Expr::WeakFair(oa, ob), Expr::WeakFair(na, nb))
        | (Expr::StrongFair(oa, ob), Expr::StrongFair(na, nb)) => {
            diff_binary_children(
                "operand",
                ChangeKind::SubExprChanged,
                oa,
                ob,
                na,
                nb,
                path,
            )
        }

        // --- Unary operators ---
        (Expr::Not(oi), Expr::Not(ni))
        | (Expr::Neg(oi), Expr::Neg(ni))
        | (Expr::Prime(oi), Expr::Prime(ni))
        | (Expr::Powerset(oi), Expr::Powerset(ni))
        | (Expr::BigUnion(oi), Expr::BigUnion(ni))
        | (Expr::Domain(oi), Expr::Domain(ni))
        | (Expr::Always(oi), Expr::Always(ni))
        | (Expr::Eventually(oi), Expr::Eventually(ni))
        | (Expr::Enabled(oi), Expr::Enabled(ni))
        | (Expr::Unchanged(oi), Expr::Unchanged(ni)) => {
            structural_expr_diff(&oi.node, &ni.node, &child_path(path, "inner"))
        }

        // --- IF-THEN-ELSE ---
        (Expr::If(oc, ot, oe), Expr::If(nc, nt, ne)) => {
            let mut changes = Vec::new();
            let cond_changes = structural_expr_diff(
                &oc.node,
                &nc.node,
                &child_path(path, "condition"),
            );
            if !cond_changes.is_empty() {
                changes.push(StructuralChange {
                    kind: ChangeKind::GuardChanged,
                    description: "IF condition changed".to_string(),
                    path: Some(child_path(path, "condition")),
                });
                changes.extend(cond_changes);
            }
            let then_changes = structural_expr_diff(
                &ot.node,
                &nt.node,
                &child_path(path, "then"),
            );
            if !then_changes.is_empty() {
                changes.push(StructuralChange {
                    kind: ChangeKind::BranchChanged,
                    description: "THEN branch changed".to_string(),
                    path: Some(child_path(path, "then")),
                });
                changes.extend(then_changes);
            }
            let else_changes = structural_expr_diff(
                &oe.node,
                &ne.node,
                &child_path(path, "else"),
            );
            if !else_changes.is_empty() {
                changes.push(StructuralChange {
                    kind: ChangeKind::BranchChanged,
                    description: "ELSE branch changed".to_string(),
                    path: Some(child_path(path, "else")),
                });
                changes.extend(else_changes);
            }
            changes
        }

        // --- Quantifiers ---
        (Expr::Forall(ob, obody), Expr::Forall(nb, nbody))
        | (Expr::Exists(ob, obody), Expr::Exists(nb, nbody)) => {
            diff_quantifier(ob, &obody.node, nb, &nbody.node, path)
        }

        // --- CHOOSE ---
        (Expr::Choose(obv, obody), Expr::Choose(nbv, nbody)) => {
            let mut changes = Vec::new();
            changes.extend(diff_bound_var_domain(obv, nbv, path));
            changes.extend(structural_expr_diff(
                &obody.node,
                &nbody.node,
                &child_path(path, "body"),
            ));
            changes
        }

        // --- LET-IN ---
        (Expr::Let(odefs, obody), Expr::Let(ndefs, nbody)) => {
            diff_let_in(odefs, &obody.node, ndefs, &nbody.node, path)
        }

        // --- CASE ---
        (Expr::Case(oarms, oother), Expr::Case(narms, nother)) => {
            diff_case(oarms, oother.as_deref(), narms, nother.as_deref(), path)
        }

        // --- Apply ---
        (Expr::Apply(oop, oargs), Expr::Apply(nop, nargs)) => {
            let mut changes = Vec::new();
            changes.extend(structural_expr_diff(
                &oop.node,
                &nop.node,
                &child_path(path, "operator"),
            ));
            changes.extend(diff_expr_lists(
                oargs,
                nargs,
                ChangeKind::ArgumentsChanged,
                "argument",
                path,
            ));
            changes
        }

        // --- FuncApply ---
        (Expr::FuncApply(of, oarg), Expr::FuncApply(nf, narg)) => {
            let mut changes = Vec::new();
            changes.extend(structural_expr_diff(
                &of.node,
                &nf.node,
                &child_path(path, "function"),
            ));
            changes.extend(structural_expr_diff(
                &oarg.node,
                &narg.node,
                &child_path(path, "argument"),
            ));
            changes
        }

        // --- Set enumeration ---
        (Expr::SetEnum(oelems), Expr::SetEnum(nelems)) => diff_expr_lists(
            oelems,
            nelems,
            ChangeKind::SetElementChanged,
            "set element",
            path,
        ),

        // --- Tuple ---
        (Expr::Tuple(oelems), Expr::Tuple(nelems)) => diff_expr_lists(
            oelems,
            nelems,
            ChangeKind::SubExprChanged,
            "tuple element",
            path,
        ),

        // --- Times (Cartesian product) ---
        (Expr::Times(oelems), Expr::Times(nelems)) => diff_expr_lists(
            oelems,
            nelems,
            ChangeKind::SubExprChanged,
            "cross-product component",
            path,
        ),

        // --- Record ---
        (Expr::Record(ofields), Expr::Record(nfields)) => {
            diff_record_fields(ofields, nfields, path)
        }

        // --- RecordSet ---
        (Expr::RecordSet(ofields), Expr::RecordSet(nfields)) => {
            diff_record_fields(ofields, nfields, path)
        }

        // --- RecordAccess ---
        (Expr::RecordAccess(obase, ofield), Expr::RecordAccess(nbase, nfield)) => {
            let mut changes = Vec::new();
            if ofield.name.node != nfield.name.node {
                changes.push(StructuralChange {
                    kind: ChangeKind::RecordFieldChanged,
                    description: format!(
                        "field name changed from .{} to .{}",
                        ofield.name.node, nfield.name.node
                    ),
                    path: path_opt,
                });
            }
            changes.extend(structural_expr_diff(
                &obase.node,
                &nbase.node,
                &child_path(path, "base"),
            ));
            changes
        }

        // --- SetBuilder ---
        (Expr::SetBuilder(obody, obounds), Expr::SetBuilder(nbody, nbounds)) => {
            let mut changes = Vec::new();
            changes.extend(diff_bound_vars(obounds, nbounds, path));
            changes.extend(structural_expr_diff(
                &obody.node,
                &nbody.node,
                &child_path(path, "map-expr"),
            ));
            changes
        }

        // --- SetFilter ---
        (Expr::SetFilter(obv, obody), Expr::SetFilter(nbv, nbody)) => {
            let mut changes = Vec::new();
            changes.extend(diff_bound_var_domain(obv, nbv, path));
            changes.extend(structural_expr_diff(
                &obody.node,
                &nbody.node,
                &child_path(path, "predicate"),
            ));
            changes
        }

        // --- FuncDef ---
        (Expr::FuncDef(obounds, obody), Expr::FuncDef(nbounds, nbody)) => {
            let mut changes = Vec::new();
            changes.extend(diff_bound_vars(obounds, nbounds, path));
            changes.extend(structural_expr_diff(
                &obody.node,
                &nbody.node,
                &child_path(path, "func-body"),
            ));
            changes
        }

        // --- Except ---
        (Expr::Except(obase, ospecs), Expr::Except(nbase, nspecs)) => {
            let mut changes = Vec::new();
            changes.extend(structural_expr_diff(
                &obase.node,
                &nbase.node,
                &child_path(path, "except-base"),
            ));
            let min_len = ospecs.len().min(nspecs.len());
            for i in 0..min_len {
                changes.extend(diff_except_spec(&ospecs[i], &nspecs[i], path, i));
            }
            if ospecs.len() != nspecs.len() {
                changes.push(StructuralChange {
                    kind: ChangeKind::SubExprChanged,
                    description: format!(
                        "EXCEPT spec count changed from {} to {}",
                        ospecs.len(),
                        nspecs.len()
                    ),
                    path: path_opt.clone(),
                });
            }
            changes
        }

        // --- Lambda ---
        (Expr::Lambda(oparams, obody), Expr::Lambda(nparams, nbody)) => {
            let mut changes = Vec::new();
            let old_names: Vec<&str> = oparams.iter().map(|p| p.node.as_str()).collect();
            let new_names: Vec<&str> = nparams.iter().map(|p| p.node.as_str()).collect();
            if old_names != new_names {
                changes.push(StructuralChange {
                    kind: ChangeKind::ParametersChanged,
                    description: format!(
                        "lambda parameters changed from ({}) to ({})",
                        old_names.join(", "),
                        new_names.join(", ")
                    ),
                    path: path_opt.clone(),
                });
            }
            changes.extend(structural_expr_diff(
                &obody.node,
                &nbody.node,
                &child_path(path, "lambda-body"),
            ));
            changes
        }

        // --- SubstIn ---
        (Expr::SubstIn(_, obody), Expr::SubstIn(_, nbody)) => {
            structural_expr_diff(&obody.node, &nbody.node, &child_path(path, "subst-body"))
        }

        // --- ModuleRef ---
        (
            Expr::ModuleRef(_, oname, oargs),
            Expr::ModuleRef(_, nname, nargs),
        ) => {
            let mut changes = Vec::new();
            if oname != nname {
                changes.push(StructuralChange {
                    kind: ChangeKind::SubExprChanged,
                    description: format!(
                        "module reference operator changed from {} to {}",
                        oname, nname
                    ),
                    path: path_opt.clone(),
                });
            }
            changes.extend(diff_expr_lists(
                oargs,
                nargs,
                ChangeKind::ArgumentsChanged,
                "module-ref argument",
                path,
            ));
            changes
        }

        // --- Literals ---
        (Expr::Bool(ob), Expr::Bool(nb)) if ob != nb => {
            vec![StructuralChange {
                kind: ChangeKind::LiteralChanged,
                description: format!("boolean literal changed from {ob} to {nb}"),
                path: path_opt,
            }]
        }
        (Expr::Int(oi), Expr::Int(ni)) if oi != ni => {
            vec![StructuralChange {
                kind: ChangeKind::LiteralChanged,
                description: format!("integer literal changed from {oi} to {ni}"),
                path: path_opt,
            }]
        }
        (Expr::String(os), Expr::String(ns)) if os != ns => {
            vec![StructuralChange {
                kind: ChangeKind::LiteralChanged,
                description: format!(
                    "string literal changed from \"{}\" to \"{}\"",
                    os, ns
                ),
                path: path_opt,
            }]
        }

        // --- Ident / StateVar ---
        (Expr::Ident(oname, _), Expr::Ident(nname, _)) if oname != nname => {
            vec![StructuralChange {
                kind: ChangeKind::SubExprChanged,
                description: format!("identifier changed from {oname} to {nname}"),
                path: path_opt,
            }]
        }
        (Expr::StateVar(oname, _, _), Expr::StateVar(nname, _, _)) if oname != nname => {
            vec![StructuralChange {
                kind: ChangeKind::SubExprChanged,
                description: format!("state variable changed from {oname} to {nname}"),
                path: path_opt,
            }]
        }
        (Expr::OpRef(oname), Expr::OpRef(nname)) if oname != nname => {
            vec![StructuralChange {
                kind: ChangeKind::SubExprChanged,
                description: format!("operator reference changed from {oname} to {nname}"),
                path: path_opt,
            }]
        }

        // --- InstanceExpr ---
        (Expr::InstanceExpr(omod, osubs), Expr::InstanceExpr(nmod, nsubs)) => {
            let mut changes = Vec::new();
            if omod != nmod {
                changes.push(StructuralChange {
                    kind: ChangeKind::SubExprChanged,
                    description: format!(
                        "INSTANCE module changed from {omod} to {nmod}"
                    ),
                    path: path_opt.clone(),
                });
            }
            changes.extend(diff_substitutions(osubs, nsubs, path));
            changes
        }

        // Catch-all: same discriminant but not matched above (e.g. identical
        // literals). The top-level pretty-print check already confirmed
        // they differ, so produce a generic diff.
        _ => {
            vec![StructuralChange {
                kind: ChangeKind::SubExprChanged,
                description: format!(
                    "{} expression changed",
                    expr_kind_name(old)
                ),
                path: path_opt,
            }]
        }
    }
}

// ---------------------------------------------------------------------------
// Structural diff helpers
// ---------------------------------------------------------------------------

fn unwrap_label(expr: &Expr) -> &Expr {
    match expr {
        Expr::Label(label) => unwrap_label(&label.body.node),
        other => other,
    }
}

fn child_path(parent: &str, child: &str) -> String {
    if parent.is_empty() {
        child.to_string()
    } else {
        format!("{parent}.{child}")
    }
}

fn expr_kind_name(expr: &Expr) -> &'static str {
    match expr {
        Expr::Bool(_) => "Bool",
        Expr::Int(_) => "Int",
        Expr::String(_) => "String",
        Expr::Ident(_, _) => "Ident",
        Expr::StateVar(_, _, _) => "StateVar",
        Expr::Apply(_, _) => "Apply",
        Expr::OpRef(_) => "OpRef",
        Expr::ModuleRef(_, _, _) => "ModuleRef",
        Expr::InstanceExpr(_, _) => "InstanceExpr",
        Expr::Lambda(_, _) => "Lambda",
        Expr::Label(_) => "Label",
        Expr::And(_, _) => "And",
        Expr::Or(_, _) => "Or",
        Expr::Not(_) => "Not",
        Expr::Implies(_, _) => "Implies",
        Expr::Equiv(_, _) => "Equiv",
        Expr::Forall(_, _) => "Forall",
        Expr::Exists(_, _) => "Exists",
        Expr::Choose(_, _) => "Choose",
        Expr::SetEnum(_) => "SetEnum",
        Expr::SetBuilder(_, _) => "SetBuilder",
        Expr::SetFilter(_, _) => "SetFilter",
        Expr::In(_, _) => "In",
        Expr::NotIn(_, _) => "NotIn",
        Expr::Subseteq(_, _) => "Subseteq",
        Expr::Union(_, _) => "Union",
        Expr::Intersect(_, _) => "Intersect",
        Expr::SetMinus(_, _) => "SetMinus",
        Expr::Powerset(_) => "Powerset",
        Expr::BigUnion(_) => "BigUnion",
        Expr::FuncDef(_, _) => "FuncDef",
        Expr::FuncApply(_, _) => "FuncApply",
        Expr::Domain(_) => "Domain",
        Expr::Except(_, _) => "Except",
        Expr::FuncSet(_, _) => "FuncSet",
        Expr::Record(_) => "Record",
        Expr::RecordAccess(_, _) => "RecordAccess",
        Expr::RecordSet(_) => "RecordSet",
        Expr::Tuple(_) => "Tuple",
        Expr::Times(_) => "Times",
        Expr::Prime(_) => "Prime",
        Expr::Always(_) => "Always",
        Expr::Eventually(_) => "Eventually",
        Expr::LeadsTo(_, _) => "LeadsTo",
        Expr::WeakFair(_, _) => "WeakFair",
        Expr::StrongFair(_, _) => "StrongFair",
        Expr::Enabled(_) => "Enabled",
        Expr::Unchanged(_) => "Unchanged",
        Expr::If(_, _, _) => "If",
        Expr::Case(_, _) => "Case",
        Expr::Let(_, _) => "Let",
        Expr::SubstIn(_, _) => "SubstIn",
        Expr::Eq(_, _) => "Eq",
        Expr::Neq(_, _) => "Neq",
        Expr::Lt(_, _) => "Lt",
        Expr::Leq(_, _) => "Leq",
        Expr::Gt(_, _) => "Gt",
        Expr::Geq(_, _) => "Geq",
        Expr::Add(_, _) => "Add",
        Expr::Sub(_, _) => "Sub",
        Expr::Mul(_, _) => "Mul",
        Expr::Div(_, _) => "Div",
        Expr::IntDiv(_, _) => "IntDiv",
        Expr::Mod(_, _) => "Mod",
        Expr::Pow(_, _) => "Pow",
        Expr::Neg(_) => "Neg",
        Expr::Range(_, _) => "Range",
    }
}

/// Diff two binary sub-expressions (e.g. both sides of /\ or \/).
fn diff_binary_children(
    child_label: &str,
    kind: ChangeKind,
    old_a: &tla_core::Spanned<Expr>,
    old_b: &tla_core::Spanned<Expr>,
    new_a: &tla_core::Spanned<Expr>,
    new_b: &tla_core::Spanned<Expr>,
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    let lhs_changes = structural_expr_diff(
        &old_a.node,
        &new_a.node,
        &child_path(path, &format!("{child_label}.lhs")),
    );
    if !lhs_changes.is_empty() {
        changes.push(StructuralChange {
            kind: kind.clone(),
            description: format!("left {child_label} changed"),
            path: Some(child_path(path, &format!("{child_label}.lhs"))),
        });
        changes.extend(lhs_changes);
    }
    let rhs_changes = structural_expr_diff(
        &old_b.node,
        &new_b.node,
        &child_path(path, &format!("{child_label}.rhs")),
    );
    if !rhs_changes.is_empty() {
        changes.push(StructuralChange {
            kind: kind.clone(),
            description: format!("right {child_label} changed"),
            path: Some(child_path(path, &format!("{child_label}.rhs"))),
        });
        changes.extend(rhs_changes);
    }
    changes
}

/// Diff expression lists (e.g. Apply arguments, SetEnum elements).
fn diff_expr_lists(
    old_list: &[tla_core::Spanned<Expr>],
    new_list: &[tla_core::Spanned<Expr>],
    kind: ChangeKind,
    label: &str,
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    let min_len = old_list.len().min(new_list.len());
    for i in 0..min_len {
        let child_changes = structural_expr_diff(
            &old_list[i].node,
            &new_list[i].node,
            &child_path(path, &format!("{label}[{i}]")),
        );
        changes.extend(child_changes);
    }
    if old_list.len() != new_list.len() {
        changes.push(StructuralChange {
            kind,
            description: format!(
                "{label} count changed from {} to {}",
                old_list.len(),
                new_list.len()
            ),
            path: if path.is_empty() {
                None
            } else {
                Some(path.to_string())
            },
        });
    }
    changes
}

/// Diff record/record-set fields.
fn diff_record_fields(
    old_fields: &[(tla_core::Spanned<String>, tla_core::Spanned<Expr>)],
    new_fields: &[(tla_core::Spanned<String>, tla_core::Spanned<Expr>)],
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    let old_map: BTreeMap<&str, &Expr> = old_fields
        .iter()
        .map(|(k, v)| (k.node.as_str(), &v.node))
        .collect();
    let new_map: BTreeMap<&str, &Expr> = new_fields
        .iter()
        .map(|(k, v)| (k.node.as_str(), &v.node))
        .collect();

    for (name, new_val) in &new_map {
        match old_map.get(name) {
            None => {
                changes.push(StructuralChange {
                    kind: ChangeKind::RecordFieldChanged,
                    description: format!("field '{name}' added"),
                    path: Some(child_path(path, name)),
                });
            }
            Some(old_val) => {
                changes.extend(structural_expr_diff(
                    old_val,
                    new_val,
                    &child_path(path, name),
                ));
            }
        }
    }
    for name in old_map.keys() {
        if !new_map.contains_key(name) {
            changes.push(StructuralChange {
                kind: ChangeKind::RecordFieldChanged,
                description: format!("field '{name}' removed"),
                path: Some(child_path(path, name)),
            });
        }
    }
    changes
}

/// Diff quantifier bounds and body.
fn diff_quantifier(
    old_bounds: &[BoundVar],
    old_body: &Expr,
    new_bounds: &[BoundVar],
    new_body: &Expr,
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    changes.extend(diff_bound_vars(old_bounds, new_bounds, path));
    let body_changes = structural_expr_diff(
        old_body,
        new_body,
        &child_path(path, "body"),
    );
    if !body_changes.is_empty() {
        changes.push(StructuralChange {
            kind: ChangeKind::QuantifierBodyChanged,
            description: "quantifier body changed".to_string(),
            path: Some(child_path(path, "body")),
        });
        changes.extend(body_changes);
    }
    changes
}

/// Diff bound variable lists (domains and names).
fn diff_bound_vars(
    old_bounds: &[BoundVar],
    new_bounds: &[BoundVar],
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    let min_len = old_bounds.len().min(new_bounds.len());
    for i in 0..min_len {
        changes.extend(diff_bound_var_domain(
            &old_bounds[i],
            &new_bounds[i],
            path,
        ));
    }
    if old_bounds.len() != new_bounds.len() {
        changes.push(StructuralChange {
            kind: ChangeKind::BoundDomainChanged,
            description: format!(
                "bound variable count changed from {} to {}",
                old_bounds.len(),
                new_bounds.len()
            ),
            path: if path.is_empty() {
                None
            } else {
                Some(path.to_string())
            },
        });
    }
    changes
}

/// Diff a single bound variable's domain.
fn diff_bound_var_domain(
    old_bv: &BoundVar,
    new_bv: &BoundVar,
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    if old_bv.name.node != new_bv.name.node {
        changes.push(StructuralChange {
            kind: ChangeKind::BoundDomainChanged,
            description: format!(
                "bound variable name changed from {} to {}",
                old_bv.name.node, new_bv.name.node
            ),
            path: if path.is_empty() {
                None
            } else {
                Some(path.to_string())
            },
        });
    }
    match (&old_bv.domain, &new_bv.domain) {
        (Some(od), Some(nd)) => {
            let domain_changes = structural_expr_diff(
                &od.node,
                &nd.node,
                &child_path(path, "domain"),
            );
            if !domain_changes.is_empty() {
                changes.push(StructuralChange {
                    kind: ChangeKind::BoundDomainChanged,
                    description: format!(
                        "domain of bound variable '{}' changed",
                        new_bv.name.node
                    ),
                    path: Some(child_path(path, "domain")),
                });
                changes.extend(domain_changes);
            }
        }
        (None, Some(_)) => {
            changes.push(StructuralChange {
                kind: ChangeKind::BoundDomainChanged,
                description: format!(
                    "domain added for bound variable '{}'",
                    new_bv.name.node
                ),
                path: Some(child_path(path, "domain")),
            });
        }
        (Some(_), None) => {
            changes.push(StructuralChange {
                kind: ChangeKind::BoundDomainChanged,
                description: format!(
                    "domain removed for bound variable '{}'",
                    old_bv.name.node
                ),
                path: Some(child_path(path, "domain")),
            });
        }
        (None, None) => {}
    }
    changes
}

/// Diff LET-IN definitions and body.
fn diff_let_in(
    old_defs: &[OperatorDef],
    old_body: &Expr,
    new_defs: &[OperatorDef],
    new_body: &Expr,
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();

    // Index definitions by name.
    let old_map: BTreeMap<&str, &OperatorDef> =
        old_defs.iter().map(|d| (d.name.node.as_str(), d)).collect();
    let new_map: BTreeMap<&str, &OperatorDef> =
        new_defs.iter().map(|d| (d.name.node.as_str(), d)).collect();

    for (name, new_def) in &new_map {
        match old_map.get(name) {
            None => {
                changes.push(StructuralChange {
                    kind: ChangeKind::LetDefChanged,
                    description: format!("LET definition '{name}' added"),
                    path: Some(child_path(path, &format!("let.{name}"))),
                });
            }
            Some(old_def) => {
                let def_changes = structural_expr_diff(
                    &old_def.body.node,
                    &new_def.body.node,
                    &child_path(path, &format!("let.{name}")),
                );
                if !def_changes.is_empty() {
                    changes.push(StructuralChange {
                        kind: ChangeKind::LetDefChanged,
                        description: format!("LET definition '{name}' body changed"),
                        path: Some(child_path(path, &format!("let.{name}"))),
                    });
                    changes.extend(def_changes);
                }
            }
        }
    }
    for name in old_map.keys() {
        if !new_map.contains_key(name) {
            changes.push(StructuralChange {
                kind: ChangeKind::LetDefChanged,
                description: format!("LET definition '{name}' removed"),
                path: Some(child_path(path, &format!("let.{name}"))),
            });
        }
    }

    // Diff the IN body.
    changes.extend(structural_expr_diff(
        old_body,
        new_body,
        &child_path(path, "in-body"),
    ));
    changes
}

/// Diff CASE arms and OTHER clause.
fn diff_case(
    old_arms: &[CaseArm],
    old_other: Option<&tla_core::Spanned<Expr>>,
    new_arms: &[CaseArm],
    new_other: Option<&tla_core::Spanned<Expr>>,
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    let min_len = old_arms.len().min(new_arms.len());
    for i in 0..min_len {
        let guard_changes = structural_expr_diff(
            &old_arms[i].guard.node,
            &new_arms[i].guard.node,
            &child_path(path, &format!("case[{i}].guard")),
        );
        if !guard_changes.is_empty() {
            changes.push(StructuralChange {
                kind: ChangeKind::CaseArmChanged,
                description: format!("CASE arm {i} guard changed"),
                path: Some(child_path(path, &format!("case[{i}].guard"))),
            });
            changes.extend(guard_changes);
        }
        let body_changes = structural_expr_diff(
            &old_arms[i].body.node,
            &new_arms[i].body.node,
            &child_path(path, &format!("case[{i}].body")),
        );
        if !body_changes.is_empty() {
            changes.push(StructuralChange {
                kind: ChangeKind::CaseArmChanged,
                description: format!("CASE arm {i} body changed"),
                path: Some(child_path(path, &format!("case[{i}].body"))),
            });
            changes.extend(body_changes);
        }
    }
    if old_arms.len() != new_arms.len() {
        changes.push(StructuralChange {
            kind: ChangeKind::CaseArmChanged,
            description: format!(
                "CASE arm count changed from {} to {}",
                old_arms.len(),
                new_arms.len()
            ),
            path: if path.is_empty() {
                None
            } else {
                Some(path.to_string())
            },
        });
    }

    // Diff OTHER clause.
    match (old_other, new_other) {
        (Some(oe), Some(ne)) => {
            let other_changes = structural_expr_diff(
                &oe.node,
                &ne.node,
                &child_path(path, "case.other"),
            );
            if !other_changes.is_empty() {
                changes.push(StructuralChange {
                    kind: ChangeKind::CaseArmChanged,
                    description: "CASE OTHER clause changed".to_string(),
                    path: Some(child_path(path, "case.other")),
                });
                changes.extend(other_changes);
            }
        }
        (None, Some(_)) => {
            changes.push(StructuralChange {
                kind: ChangeKind::CaseArmChanged,
                description: "CASE OTHER clause added".to_string(),
                path: Some(child_path(path, "case.other")),
            });
        }
        (Some(_), None) => {
            changes.push(StructuralChange {
                kind: ChangeKind::CaseArmChanged,
                description: "CASE OTHER clause removed".to_string(),
                path: Some(child_path(path, "case.other")),
            });
        }
        (None, None) => {}
    }
    changes
}

/// Diff EXCEPT specs.
fn diff_except_spec(
    old_spec: &ExceptSpec,
    new_spec: &ExceptSpec,
    path: &str,
    index: usize,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    let spec_path = child_path(path, &format!("except[{index}]"));

    // Diff paths.
    let min_path_len = old_spec.path.len().min(new_spec.path.len());
    for i in 0..min_path_len {
        match (&old_spec.path[i], &new_spec.path[i]) {
            (ExceptPathElement::Index(oi), ExceptPathElement::Index(ni)) => {
                changes.extend(structural_expr_diff(
                    &oi.node,
                    &ni.node,
                    &child_path(&spec_path, &format!("path[{i}]")),
                ));
            }
            (ExceptPathElement::Field(of), ExceptPathElement::Field(nf)) => {
                if of.name.node != nf.name.node {
                    changes.push(StructuralChange {
                        kind: ChangeKind::SubExprChanged,
                        description: format!(
                            "EXCEPT path field changed from .{} to .{}",
                            of.name.node, nf.name.node
                        ),
                        path: Some(child_path(&spec_path, &format!("path[{i}]"))),
                    });
                }
            }
            _ => {
                changes.push(StructuralChange {
                    kind: ChangeKind::SubExprChanged,
                    description: format!("EXCEPT path element {i} type changed"),
                    path: Some(child_path(&spec_path, &format!("path[{i}]"))),
                });
            }
        }
    }
    if old_spec.path.len() != new_spec.path.len() {
        changes.push(StructuralChange {
            kind: ChangeKind::SubExprChanged,
            description: format!(
                "EXCEPT path length changed from {} to {}",
                old_spec.path.len(),
                new_spec.path.len()
            ),
            path: Some(spec_path.clone()),
        });
    }

    // Diff value.
    changes.extend(structural_expr_diff(
        &old_spec.value.node,
        &new_spec.value.node,
        &child_path(&spec_path, "value"),
    ));

    changes
}

/// Diff INSTANCE substitutions.
fn diff_substitutions(
    old_subs: &[Substitution],
    new_subs: &[Substitution],
    path: &str,
) -> Vec<StructuralChange> {
    let mut changes = Vec::new();
    let old_map: BTreeMap<&str, &Expr> = old_subs
        .iter()
        .map(|s| (s.from.node.as_str(), &s.to.node))
        .collect();
    let new_map: BTreeMap<&str, &Expr> = new_subs
        .iter()
        .map(|s| (s.from.node.as_str(), &s.to.node))
        .collect();

    for (name, new_expr) in &new_map {
        match old_map.get(name) {
            None => {
                changes.push(StructuralChange {
                    kind: ChangeKind::SubExprChanged,
                    description: format!("substitution '{name}' added"),
                    path: Some(child_path(path, &format!("subst.{name}"))),
                });
            }
            Some(old_expr) => {
                changes.extend(structural_expr_diff(
                    old_expr,
                    new_expr,
                    &child_path(path, &format!("subst.{name}")),
                ));
            }
        }
    }
    for name in old_map.keys() {
        if !new_map.contains_key(name) {
            changes.push(StructuralChange {
                kind: ChangeKind::SubExprChanged,
                description: format!("substitution '{name}' removed"),
                path: Some(child_path(path, &format!("subst.{name}"))),
            });
        }
    }
    changes
}

// ---------------------------------------------------------------------------
// Call graph construction (for impact analysis)
// ---------------------------------------------------------------------------

/// Build a forward call graph: operator name -> set of operator names it calls.
fn build_call_graph(module: &Module) -> BTreeMap<String, BTreeSet<String>> {
    let variables: BTreeSet<String> = collect_all_variables(module);
    let mut graph = BTreeMap::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let mut collector = RefCollector {
                variables: &variables,
                refs: BTreeSet::new(),
            };
            collector.visit_expr(&def.body.node);
            graph.insert(def.name.node.clone(), collector.refs);
        }
    }
    graph
}

fn collect_all_variables(module: &Module) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for decl in decls {
                vars.insert(decl.node.clone());
            }
        }
    }
    vars
}

/// Build reverse call graph: operator name -> set of operators that call it.
fn reverse_call_graph(
    forward: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut reverse: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (caller, callees) in forward {
        for callee in callees {
            reverse
                .entry(callee.clone())
                .or_default()
                .insert(caller.clone());
        }
    }
    reverse
}

/// Minimal expression reference collector: collects operator references
/// (identifiers that are not bound variables and not state variables).
struct RefCollector<'a> {
    variables: &'a BTreeSet<String>,
    refs: BTreeSet<String>,
}

impl<'a> RefCollector<'a> {
    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Ident(name, _) => {
                if !self.variables.contains(name) {
                    self.refs.insert(name.clone());
                }
            }
            Expr::StateVar(_, _, _) => {}
            Expr::Apply(op, args) => {
                self.visit_expr(&op.node);
                for arg in args {
                    self.visit_expr(&arg.node);
                }
            }
            Expr::ModuleRef(_, name, args) => {
                self.refs.insert(name.clone());
                for arg in args {
                    self.visit_expr(&arg.node);
                }
            }
            Expr::OpRef(name) => {
                self.refs.insert(name.clone());
            }
            Expr::And(a, b)
            | Expr::Or(a, b)
            | Expr::Implies(a, b)
            | Expr::Equiv(a, b)
            | Expr::Eq(a, b)
            | Expr::Neq(a, b)
            | Expr::Lt(a, b)
            | Expr::Leq(a, b)
            | Expr::Gt(a, b)
            | Expr::Geq(a, b)
            | Expr::In(a, b)
            | Expr::NotIn(a, b)
            | Expr::Subseteq(a, b)
            | Expr::Union(a, b)
            | Expr::Intersect(a, b)
            | Expr::SetMinus(a, b)
            | Expr::FuncSet(a, b)
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
            | Expr::StrongFair(a, b) => {
                self.visit_expr(&a.node);
                self.visit_expr(&b.node);
            }
            Expr::Not(inner)
            | Expr::Neg(inner)
            | Expr::Prime(inner)
            | Expr::Powerset(inner)
            | Expr::BigUnion(inner)
            | Expr::Domain(inner)
            | Expr::Always(inner)
            | Expr::Eventually(inner)
            | Expr::Enabled(inner)
            | Expr::Unchanged(inner) => {
                self.visit_expr(&inner.node);
            }
            Expr::If(cond, then_e, else_e) => {
                self.visit_expr(&cond.node);
                self.visit_expr(&then_e.node);
                self.visit_expr(&else_e.node);
            }
            Expr::Case(arms, other) => {
                for arm in arms {
                    self.visit_expr(&arm.guard.node);
                    self.visit_expr(&arm.body.node);
                }
                if let Some(other) = other {
                    self.visit_expr(&other.node);
                }
            }
            Expr::Let(defs, body) => {
                for def in defs {
                    self.visit_expr(&def.body.node);
                }
                self.visit_expr(&body.node);
            }
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                for bv in bounds {
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(&domain.node);
                    }
                }
                self.visit_expr(&body.node);
            }
            Expr::Choose(bv, body) => {
                if let Some(ref domain) = bv.domain {
                    self.visit_expr(&domain.node);
                }
                self.visit_expr(&body.node);
            }
            Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
                for e in elems {
                    self.visit_expr(&e.node);
                }
            }
            Expr::SetBuilder(body, bounds) => {
                for bv in bounds {
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(&domain.node);
                    }
                }
                self.visit_expr(&body.node);
            }
            Expr::SetFilter(bv, body) => {
                if let Some(ref domain) = bv.domain {
                    self.visit_expr(&domain.node);
                }
                self.visit_expr(&body.node);
            }
            Expr::FuncDef(bounds, body) => {
                for bv in bounds {
                    if let Some(ref domain) = bv.domain {
                        self.visit_expr(&domain.node);
                    }
                }
                self.visit_expr(&body.node);
            }
            Expr::FuncApply(f, arg) => {
                self.visit_expr(&f.node);
                self.visit_expr(&arg.node);
            }
            Expr::Except(base, specs) => {
                self.visit_expr(&base.node);
                for spec in specs {
                    for path_elem in &spec.path {
                        if let ExceptPathElement::Index(idx) = path_elem {
                            self.visit_expr(&idx.node);
                        }
                    }
                    self.visit_expr(&spec.value.node);
                }
            }
            Expr::Record(fields) | Expr::RecordSet(fields) => {
                for (_, val) in fields {
                    self.visit_expr(&val.node);
                }
            }
            Expr::RecordAccess(base, _) => {
                self.visit_expr(&base.node);
            }
            Expr::Lambda(_, body) => {
                self.visit_expr(&body.node);
            }
            Expr::Label(label) => {
                self.visit_expr(&label.body.node);
            }
            Expr::SubstIn(_, body) => {
                self.visit_expr(&body.node);
            }
            Expr::InstanceExpr(_, _) => {}
            Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Impact analysis
// ---------------------------------------------------------------------------

/// Compute which invariants and properties are transitively affected by the
/// changed operators, using BFS on the reverse call graph.
fn compute_impact(
    changed_ops: &BTreeSet<String>,
    reverse_graph: &BTreeMap<String, BTreeSet<String>>,
    invariants: &BTreeSet<String>,
    properties: &BTreeSet<String>,
) -> ImpactReport {
    // BFS from each changed operator to find all transitive dependents.
    let mut all_affected: BTreeSet<String> = BTreeSet::new();
    // Map: affected operator -> which changed ops caused it.
    let mut caused_by: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    for changed in changed_ops {
        let mut visited: BTreeSet<String> = BTreeSet::new();
        let mut queue: VecDeque<String> = VecDeque::new();
        queue.push_back(changed.clone());
        visited.insert(changed.clone());

        while let Some(current) = queue.pop_front() {
            all_affected.insert(current.clone());
            caused_by
                .entry(current.clone())
                .or_default()
                .insert(changed.clone());

            if let Some(callers) = reverse_graph.get(&current) {
                for caller in callers {
                    if visited.insert(caller.clone()) {
                        queue.push_back(caller.clone());
                    }
                }
            }
        }
    }

    // Build impact entries for invariants and properties.
    let affected_invariants: Vec<ImpactEntry> = invariants
        .iter()
        .filter(|inv| all_affected.contains(inv.as_str()))
        .map(|inv| ImpactEntry {
            name: inv.clone(),
            caused_by: caused_by
                .get(inv.as_str())
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default(),
        })
        .collect();

    let affected_properties: Vec<ImpactEntry> = properties
        .iter()
        .filter(|prop| all_affected.contains(prop.as_str()))
        .map(|prop| ImpactEntry {
            name: prop.clone(),
            caused_by: caused_by
                .get(prop.as_str())
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default(),
        })
        .collect();

    // Transitive dependents beyond the directly changed ops.
    let transitive_dependents: Vec<String> = all_affected
        .difference(changed_ops)
        .cloned()
        .collect();

    ImpactReport {
        affected_invariants,
        affected_properties,
        transitive_dependents,
    }
}

// ---------------------------------------------------------------------------
// Human-readable output
// ---------------------------------------------------------------------------

/// ANSI color codes.
const GREEN: &str = "\x1b[32m";
const RED: &str = "\x1b[31m";
const YELLOW: &str = "\x1b[33m";
const CYAN: &str = "\x1b[36m";
const BOLD: &str = "\x1b[1m";
const DIM: &str = "\x1b[2m";
const RESET: &str = "\x1b[0m";

fn print_human(report: &ModelDiffReport) {
    if report.is_empty() {
        println!("No structural differences found between the specifications.");
        return;
    }

    println!(
        "{BOLD}Model Diff: {} vs {}{RESET}",
        report.old_file, report.new_file
    );
    println!(
        "{DIM}{} total change(s) detected{RESET}",
        report.total_changes()
    );
    println!();

    // --- EXTENDS ---
    print_string_set_section("EXTENDS", &report.extends);

    // --- VARIABLES ---
    print_string_set_section("VARIABLES", &report.variables);

    // --- CONSTANTS ---
    print_string_set_section("CONSTANTS", &report.constants);

    // --- OPERATORS ---
    print_operators_section(&report.operators);

    // --- INVARIANTS ---
    print_string_set_section("INVARIANTS (from .cfg)", &report.invariants);

    // --- PROPERTIES ---
    print_string_set_section("PROPERTIES (from .cfg)", &report.properties);

    // --- IMPACT ---
    print_impact_section(&report.impact);
}

fn print_string_set_section(title: &str, diff: &StringSetDiff) {
    if diff.added.is_empty() && diff.removed.is_empty() {
        return;
    }
    println!("{BOLD}{title}:{RESET}");
    for name in &diff.added {
        println!("  {GREEN}+ {name}{RESET}");
    }
    for name in &diff.removed {
        println!("  {RED}- {name}{RESET}");
    }
    println!();
}

fn print_operators_section(ops: &OperatorsDiff) {
    let has_changes = !ops.added.is_empty()
        || !ops.removed.is_empty()
        || !ops.modified.is_empty()
        || !ops.signature_changed.is_empty();

    if !has_changes {
        return;
    }

    println!("{BOLD}OPERATORS:{RESET}");

    for op in &ops.added {
        let locality = if op.local { " (LOCAL)" } else { "" };
        println!(
            "  {GREEN}+ {:<24}{RESET} line {}, arity {}{}",
            op.name, op.line, op.arity, locality
        );
    }

    for op in &ops.removed {
        let locality = if op.local { " (LOCAL)" } else { "" };
        println!(
            "  {RED}- {:<24}{RESET} was line {}, arity {}{}",
            op.name, op.line, op.arity, locality
        );
    }

    for sig in &ops.signature_changed {
        println!(
            "  {YELLOW}~ {:<24}{RESET} signature: ({}) -> ({})",
            sig.name,
            sig.old_params.join(", "),
            sig.new_params.join(", ")
        );
    }

    for op in &ops.modified {
        println!(
            "  {YELLOW}~ {:<24}{RESET} modified (line {} -> {})",
            op.name, op.old_line, op.new_line
        );

        // Print structural change summary.
        for change in &op.structural_changes {
            let path_str = change
                .path
                .as_deref()
                .map(|p| format!(" [{p}]"))
                .unwrap_or_default();
            println!(
                "      {DIM}{}{RESET}{path_str}",
                change.description
            );
        }

        // Print line-level diff of the pretty-printed body.
        print_body_diff(&op.old_body, &op.new_body);
    }
    println!();
}

fn print_body_diff(old_body: &str, new_body: &str) {
    let old_lines: Vec<&str> = old_body.lines().collect();
    let new_lines: Vec<&str> = new_body.lines().collect();

    let lcs = compute_lcs(&old_lines, &new_lines);
    let mut oi = 0usize;
    let mut ni = 0usize;
    let mut li = 0usize;

    while oi < old_lines.len() || ni < new_lines.len() {
        if li < lcs.len()
            && oi < old_lines.len()
            && ni < new_lines.len()
            && old_lines[oi] == lcs[li]
            && new_lines[ni] == lcs[li]
        {
            println!("        {}", old_lines[oi]);
            oi += 1;
            ni += 1;
            li += 1;
        } else if li < lcs.len() && ni < new_lines.len() && new_lines[ni] == lcs[li] {
            println!("      {RED}- {}{RESET}", old_lines[oi]);
            oi += 1;
        } else if li < lcs.len() && oi < old_lines.len() && old_lines[oi] == lcs[li] {
            println!("      {GREEN}+ {}{RESET}", new_lines[ni]);
            ni += 1;
        } else {
            if oi < old_lines.len() {
                println!("      {RED}- {}{RESET}", old_lines[oi]);
                oi += 1;
            }
            if ni < new_lines.len() {
                println!("      {GREEN}+ {}{RESET}", new_lines[ni]);
                ni += 1;
            }
        }
    }
}

/// Compute the longest common subsequence of two string slices.
fn compute_lcs<'a>(a: &[&'a str], b: &[&'a str]) -> Vec<&'a str> {
    let m = a.len();
    let n = b.len();
    let mut dp = vec![vec![0u32; n + 1]; m + 1];
    for i in 1..=m {
        for j in 1..=n {
            if a[i - 1] == b[j - 1] {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
            }
        }
    }
    let mut result = Vec::with_capacity(dp[m][n] as usize);
    let mut i = m;
    let mut j = n;
    while i > 0 && j > 0 {
        if a[i - 1] == b[j - 1] {
            result.push(a[i - 1]);
            i -= 1;
            j -= 1;
        } else if dp[i - 1][j] >= dp[i][j - 1] {
            i -= 1;
        } else {
            j -= 1;
        }
    }
    result.reverse();
    result
}

fn print_impact_section(impact: &ImpactReport) {
    let has_impact = !impact.affected_invariants.is_empty()
        || !impact.affected_properties.is_empty()
        || !impact.transitive_dependents.is_empty();

    if !has_impact {
        return;
    }

    println!("{BOLD}IMPACT ANALYSIS:{RESET}");

    if !impact.affected_invariants.is_empty() {
        println!("  {CYAN}Affected invariants:{RESET}");
        for entry in &impact.affected_invariants {
            println!(
                "    {YELLOW}! {}{RESET} (caused by: {})",
                entry.name,
                entry.caused_by.join(", ")
            );
        }
    }

    if !impact.affected_properties.is_empty() {
        println!("  {CYAN}Affected properties:{RESET}");
        for entry in &impact.affected_properties {
            println!(
                "    {YELLOW}! {}{RESET} (caused by: {})",
                entry.name,
                entry.caused_by.join(", ")
            );
        }
    }

    if !impact.transitive_dependents.is_empty() {
        println!(
            "  {DIM}Transitively affected operators ({}):{RESET}",
            impact.transitive_dependents.len()
        );
        for name in &impact.transitive_dependents {
            println!("    {DIM}{name}{RESET}");
        }
    }
    println!();
}

// ---------------------------------------------------------------------------
// JSON output
// ---------------------------------------------------------------------------

fn print_json(report: &ModelDiffReport) {
    let json =
        serde_json::to_string_pretty(report).expect("invariant: ModelDiffReport is serializable");
    println!("{json}");
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::ast::ExprLabel;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_line_of_basic() {
        let source = "line1\nline2\nline3\n";
        assert_eq!(line_of(source, 0), 1);
        assert_eq!(line_of(source, 6), 2);
        assert_eq!(line_of(source, 12), 3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_line_of_past_end() {
        let source = "abc";
        assert_eq!(line_of(source, 100), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_constant_decl_simple() {
        let decl = ConstantDecl {
            name: tla_core::Spanned::dummy("N".to_string()),
            arity: None,
        };
        assert_eq!(format_constant_decl(&decl), "N");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_constant_decl_arity() {
        let decl = ConstantDecl {
            name: tla_core::Spanned::dummy("F".to_string()),
            arity: Some(3),
        };
        assert_eq!(format_constant_decl(&decl), "F(_, _, _)");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_diff_string_sets_identical() {
        let a: BTreeSet<String> = ["x", "y"].iter().map(|s| s.to_string()).collect();
        let diff = diff_string_sets(&a, &a);
        assert!(diff.added.is_empty());
        assert!(diff.removed.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_diff_string_sets_add_remove() {
        let old: BTreeSet<String> = ["a", "b"].iter().map(|s| s.to_string()).collect();
        let new: BTreeSet<String> = ["b", "c"].iter().map(|s| s.to_string()).collect();
        let diff = diff_string_sets(&old, &new);
        assert_eq!(diff.added, vec!["c"]);
        assert_eq!(diff.removed, vec!["a"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compute_lcs_identical() {
        let a = vec!["a", "b", "c"];
        let b = vec!["a", "b", "c"];
        assert_eq!(compute_lcs(&a, &b), vec!["a", "b", "c"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compute_lcs_disjoint() {
        let a = vec!["a", "b"];
        let b = vec!["c", "d"];
        let result: Vec<&str> = compute_lcs(&a, &b);
        assert!(result.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compute_lcs_insertion() {
        let a = vec!["a", "c"];
        let b = vec!["a", "b", "c"];
        assert_eq!(compute_lcs(&a, &b), vec!["a", "c"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expr_kind_name_coverage() {
        // Verify a few representative variants return the right names.
        let e_bool = Expr::Bool(true);
        assert_eq!(expr_kind_name(&e_bool), "Bool");

        let e_ident = Expr::Ident("x".to_string(), tla_core::NameId::INVALID);
        assert_eq!(expr_kind_name(&e_ident), "Ident");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_reverse_call_graph() {
        let mut forward = BTreeMap::new();
        let mut a_calls = BTreeSet::new();
        a_calls.insert("B".to_string());
        a_calls.insert("C".to_string());
        forward.insert("A".to_string(), a_calls);

        let mut b_calls = BTreeSet::new();
        b_calls.insert("C".to_string());
        forward.insert("B".to_string(), b_calls);

        let reverse = reverse_call_graph(&forward);
        assert!(reverse.get("C").expect("C should have callers").contains("A"));
        assert!(reverse.get("C").expect("C should have callers").contains("B"));
        assert!(reverse.get("B").expect("B should have callers").contains("A"));
        assert!(reverse.get("A").is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_impact_analysis_transitive() {
        let mut reverse = BTreeMap::new();
        // C is called by B, B is called by Inv (an invariant).
        let mut c_callers = BTreeSet::new();
        c_callers.insert("B".to_string());
        reverse.insert("C".to_string(), c_callers);

        let mut b_callers = BTreeSet::new();
        b_callers.insert("Inv".to_string());
        reverse.insert("B".to_string(), b_callers);

        let mut changed = BTreeSet::new();
        changed.insert("C".to_string());

        let mut invariants = BTreeSet::new();
        invariants.insert("Inv".to_string());

        let properties = BTreeSet::new();

        let impact = compute_impact(&changed, &reverse, &invariants, &properties);
        assert_eq!(impact.affected_invariants.len(), 1);
        assert_eq!(impact.affected_invariants[0].name, "Inv");
        assert!(impact.affected_invariants[0].caused_by.contains(&"C".to_string()));
        assert!(impact.transitive_dependents.contains(&"B".to_string()));
        assert!(impact.transitive_dependents.contains(&"Inv".to_string()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_unwrap_label() {
        let inner = Expr::Bool(true);
        let label = Expr::Label(ExprLabel {
            name: tla_core::Spanned::dummy("lbl".to_string()),
            body: Box::new(tla_core::Spanned::dummy(inner.clone())),
        });
        assert!(matches!(unwrap_label(&label), Expr::Bool(true)));
        assert!(matches!(unwrap_label(&inner), Expr::Bool(true)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_child_path_empty_parent() {
        assert_eq!(child_path("", "child"), "child");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_child_path_nested() {
        assert_eq!(child_path("a.b", "c"), "a.b.c");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_report_is_empty_default() {
        let report = ModelDiffReport {
            old_file: "a.tla".to_string(),
            new_file: "b.tla".to_string(),
            extends: StringSetDiff::default(),
            variables: StringSetDiff::default(),
            constants: StringSetDiff::default(),
            operators: OperatorsDiff::default(),
            invariants: StringSetDiff::default(),
            properties: StringSetDiff::default(),
            impact: ImpactReport::default(),
        };
        assert!(report.is_empty());
        assert_eq!(report.total_changes(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_report_total_changes() {
        let report = ModelDiffReport {
            old_file: "a.tla".to_string(),
            new_file: "b.tla".to_string(),
            extends: StringSetDiff {
                added: vec!["Naturals".to_string()],
                removed: vec![],
            },
            variables: StringSetDiff {
                added: vec!["x".to_string(), "y".to_string()],
                removed: vec!["z".to_string()],
            },
            constants: StringSetDiff::default(),
            operators: OperatorsDiff {
                added: vec![OpSummary {
                    name: "Op".to_string(),
                    line: 1,
                    arity: 0,
                    local: false,
                }],
                removed: vec![],
                modified: vec![],
                signature_changed: vec![],
            },
            invariants: StringSetDiff::default(),
            properties: StringSetDiff::default(),
            impact: ImpactReport::default(),
        };
        assert!(!report.is_empty());
        // 1 extends added + 2 variables added + 1 variable removed + 1 operator added = 5
        assert_eq!(report.total_changes(), 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_structural_diff_same_expr() {
        let expr = Expr::Bool(true);
        let changes = structural_expr_diff(&expr, &expr, "");
        assert!(changes.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_structural_diff_type_change() {
        let old = Expr::Bool(true);
        let new = Expr::Int(num_bigint::BigInt::from(42));
        let changes = structural_expr_diff(&old, &new, "");
        assert_eq!(changes.len(), 1);
        assert!(matches!(changes[0].kind, ChangeKind::ExprTypeChanged));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_structural_diff_literal_change() {
        let old = Expr::Bool(true);
        let new = Expr::Bool(false);
        let changes = structural_expr_diff(&old, &new, "");
        assert_eq!(changes.len(), 1);
        assert!(matches!(changes[0].kind, ChangeKind::LiteralChanged));
        assert!(changes[0].description.contains("true"));
        assert!(changes[0].description.contains("false"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_json_serialization_roundtrip() {
        let report = ModelDiffReport {
            old_file: "old.tla".to_string(),
            new_file: "new.tla".to_string(),
            extends: StringSetDiff::default(),
            variables: StringSetDiff {
                added: vec!["x".to_string()],
                removed: vec![],
            },
            constants: StringSetDiff::default(),
            operators: OperatorsDiff::default(),
            invariants: StringSetDiff::default(),
            properties: StringSetDiff::default(),
            impact: ImpactReport::default(),
        };
        let json = serde_json::to_string_pretty(&report)
            .expect("should serialize");
        assert!(json.contains("\"x\""));
        assert!(json.contains("old.tla"));
        assert!(json.contains("new.tla"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_diff_config_list_both_none() {
        let diff = diff_config_list(None, None);
        assert!(diff.added.is_empty());
        assert!(diff.removed.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_diff_config_list_add_invariant() {
        let old: Vec<String> = vec!["A".to_string()];
        let new: Vec<String> = vec!["A".to_string(), "B".to_string()];
        let diff = diff_config_list(Some(&old), Some(&new));
        assert_eq!(diff.added, vec!["B"]);
        assert!(diff.removed.is_empty());
    }
}
