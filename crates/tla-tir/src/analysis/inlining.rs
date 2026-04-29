// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared TIR-level inlining pass for JIT and codegen consumers.
//!
//! Identifies small, non-recursive leaf functions in a [`TirModule`] and
//! inlines their bodies at call sites, replacing parameter references with
//! argument expressions. This eliminates call overhead for both the JIT
//! compiler and the code generator without either backend needing to
//! implement its own inlining logic.
//!
//! **Leaf function**: a function whose body contains no `Apply` calls to
//! other user-defined operators in the module. Built-in operators and
//! lambda applications are not considered calls for this purpose.
//!
//! Part of #3931.

use crate::lower::{TirModule, TirOperator};
use crate::nodes::{
    TirBoundVar, TirCaseArm, TirExceptPathElement, TirExceptSpec, TirExpr, TirLetDef,
    TirModuleRefSegment, TirOperatorRef,
};
use rustc_hash::{FxHashMap, FxHashSet};
use tla_core::{NameId, Spanned};

/// Configuration for the inlining pass.
#[derive(Debug, Clone)]
pub struct InliningConfig {
    /// Maximum number of TIR expression nodes in a function body for it
    /// to be considered an inline candidate. Functions larger than this
    /// threshold are never inlined.
    pub max_inline_size: usize,
}

impl Default for InliningConfig {
    fn default() -> Self {
        Self {
            max_inline_size: 20,
        }
    }
}

/// Statistics collected during an inlining pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InliningStats {
    /// Number of distinct functions whose bodies were inlined at least once.
    pub functions_inlined: usize,
    /// Total number of call sites that were replaced with inlined bodies.
    pub call_sites_replaced: usize,
}

/// Run the inlining pass on a `TirModule`, modifying operator bodies in place.
///
/// Returns statistics about what was inlined. The pass:
/// 1. Identifies inline candidates: non-recursive leaf operators within the
///    size threshold.
/// 2. Walks every operator body, replacing `Apply` nodes that target a
///    candidate with the candidate's body (after parameter substitution).
///
/// Candidates are not themselves mutated (they remain in the module for
/// any direct references), only call sites in other operators are rewritten.
#[must_use]
pub fn inline_functions(module: &mut TirModule, config: &InliningConfig) -> InliningStats {
    // Build the set of all user-defined operator NameIds in this module.
    let all_op_names: FxHashSet<NameId> = module.operators.iter().map(|op| op.name_id).collect();

    // Phase 1: identify inline candidates.
    let candidates: FxHashMap<NameId, &TirOperator> = module
        .operators
        .iter()
        .filter(|op| is_inline_candidate(op, config, &all_op_names))
        .map(|op| (op.name_id, op))
        .collect();

    if candidates.is_empty() {
        return InliningStats::default();
    }

    // Phase 2: clone candidate bodies and param lists (to avoid borrowing module
    // while mutating it).
    let candidate_data: FxHashMap<NameId, (Vec<String>, Spanned<TirExpr>)> = candidates
        .iter()
        .map(|(&id, op)| (id, (op.params.clone(), op.body.clone())))
        .collect();

    // Phase 3: walk every operator body and replace call sites, tracking
    // which candidates were actually inlined.
    let mut inlined_ids: FxHashSet<NameId> = FxHashSet::default();
    let mut total_replaced = 0usize;

    for op in &mut module.operators {
        let mut local_replaced = 0usize;
        op.body = inline_in_expr(
            op.body.clone(),
            &candidate_data,
            &mut local_replaced,
            &mut inlined_ids,
        );
        total_replaced += local_replaced;
    }

    InliningStats {
        functions_inlined: inlined_ids.len(),
        call_sites_replaced: total_replaced,
    }
}

/// Determine whether an operator is an inline candidate.
fn is_inline_candidate(
    op: &TirOperator,
    config: &InliningConfig,
    all_op_names: &FxHashSet<NameId>,
) -> bool {
    // Must not be recursive.
    if op.is_recursive {
        return false;
    }

    // Must have parameters (zero-arity operators are just constants,
    // not worth the complexity of inlining).
    // Actually, zero-arity operators CAN benefit from inlining if they
    // are referenced via Apply nodes. But in TLA+ TIR, zero-arity
    // operators are typically referenced as Name/OperatorRef, not Apply.
    // Keep it simple: require at least one parameter.
    if op.params.is_empty() {
        return false;
    }

    // Must be within size threshold.
    let size = count_nodes(&op.body);
    if size > config.max_inline_size {
        return false;
    }

    // Must be a leaf: no calls to other user-defined operators.
    !has_user_calls(&op.body, all_op_names, op.name_id)
}

/// Count the number of TIR expression nodes in a tree.
fn count_nodes(expr: &Spanned<TirExpr>) -> usize {
    let mut count = 1usize;
    visit_children(&expr.node, &mut |child| {
        count += count_nodes(child);
    });
    count
}

/// Check whether an expression tree contains calls to any user-defined
/// operator (other than the operator itself, which is handled by the
/// `is_recursive` flag).
fn has_user_calls(
    expr: &Spanned<TirExpr>,
    all_op_names: &FxHashSet<NameId>,
    self_id: NameId,
) -> bool {
    match &expr.node {
        TirExpr::Apply { op, args } => {
            // Check if op is a Name referencing a user-defined operator.
            if let TirExpr::Name(name_ref) = &op.node {
                if name_ref.name_id != self_id && all_op_names.contains(&name_ref.name_id) {
                    return true;
                }
            }
            // Also check for OperatorRef targeting a user op.
            if let TirExpr::OperatorRef(op_ref) = &op.node {
                if op_ref.path.is_empty() && all_op_names.contains(&op_ref.operator_id) {
                    return true;
                }
            }
            // Recurse into children.
            if has_user_calls(op, all_op_names, self_id) {
                return true;
            }
            args.iter()
                .any(|a| has_user_calls(a, all_op_names, self_id))
        }
        _ => {
            let mut found = false;
            visit_children(&expr.node, &mut |child| {
                if !found && has_user_calls(child, all_op_names, self_id) {
                    found = true;
                }
            });
            found
        }
    }
}

/// Walk an expression tree, replacing eligible `Apply` nodes with inlined bodies.
fn inline_in_expr(
    expr: Spanned<TirExpr>,
    candidates: &FxHashMap<NameId, (Vec<String>, Spanned<TirExpr>)>,
    replaced_count: &mut usize,
    inlined_ids: &mut FxHashSet<NameId>,
) -> Spanned<TirExpr> {
    let span = expr.span;
    match expr.node {
        TirExpr::Apply { op, args } => {
            // Check if op targets an inline candidate.
            let target_id = match &op.node {
                TirExpr::Name(name_ref) => Some(name_ref.name_id),
                _ => None,
            };

            if let Some(id) = target_id {
                if let Some((params, body)) = candidates.get(&id) {
                    if params.len() == args.len() {
                        // Inline: substitute parameters with (recursively inlined) arguments.
                        let inlined_args: Vec<Spanned<TirExpr>> = args
                            .into_iter()
                            .map(|a| inline_in_expr(a, candidates, replaced_count, inlined_ids))
                            .collect();

                        let param_map: FxHashMap<&str, &Spanned<TirExpr>> = params
                            .iter()
                            .zip(inlined_args.iter())
                            .map(|(p, a)| (p.as_str(), a))
                            .collect();

                        *replaced_count += 1;
                        inlined_ids.insert(id);
                        return substitute_params(body.clone(), &param_map, span);
                    }
                }
            }

            // Not a candidate: recurse into children.
            let new_op = Box::new(inline_in_expr(*op, candidates, replaced_count, inlined_ids));
            let new_args = args
                .into_iter()
                .map(|a| inline_in_expr(a, candidates, replaced_count, inlined_ids))
                .collect();
            Spanned {
                node: TirExpr::Apply {
                    op: new_op,
                    args: new_args,
                },
                span,
            }
        }
        other => {
            // Recursively transform all children.
            let node = map_children_owned(other, candidates, replaced_count, inlined_ids);
            Spanned { node, span }
        }
    }
}

/// Substitute parameter references in a cloned body with argument expressions.
///
/// Parameters in TIR are `TirExpr::Name` nodes with `TirNameKind::Ident` whose
/// name matches a parameter string. We replace those with the corresponding
/// argument expression. The call-site span is used for the outer wrapper to
/// preserve debug location information.
fn substitute_params(
    body: Spanned<TirExpr>,
    param_map: &FxHashMap<&str, &Spanned<TirExpr>>,
    call_span: tla_core::span::Span,
) -> Spanned<TirExpr> {
    let node = substitute_node(body.node, body.span, param_map);
    Spanned {
        node,
        span: call_span,
    }
}

fn substitute_node(
    node: TirExpr,
    _span: tla_core::span::Span,
    param_map: &FxHashMap<&str, &Spanned<TirExpr>>,
) -> TirExpr {
    match node {
        TirExpr::Name(ref name_ref) => {
            if let Some(replacement) = param_map.get(name_ref.name.as_str()) {
                return (*replacement).clone().node;
            }
            node
        }
        TirExpr::ArithBinOp { left, op, right } => TirExpr::ArithBinOp {
            left: Box::new(substitute_spanned(*left, param_map)),
            op,
            right: Box::new(substitute_spanned(*right, param_map)),
        },
        TirExpr::ArithNeg(inner) => {
            TirExpr::ArithNeg(Box::new(substitute_spanned(*inner, param_map)))
        }
        TirExpr::BoolBinOp { left, op, right } => TirExpr::BoolBinOp {
            left: Box::new(substitute_spanned(*left, param_map)),
            op,
            right: Box::new(substitute_spanned(*right, param_map)),
        },
        TirExpr::BoolNot(inner) => {
            TirExpr::BoolNot(Box::new(substitute_spanned(*inner, param_map)))
        }
        TirExpr::Cmp { left, op, right } => TirExpr::Cmp {
            left: Box::new(substitute_spanned(*left, param_map)),
            op,
            right: Box::new(substitute_spanned(*right, param_map)),
        },
        TirExpr::In { elem, set } => TirExpr::In {
            elem: Box::new(substitute_spanned(*elem, param_map)),
            set: Box::new(substitute_spanned(*set, param_map)),
        },
        TirExpr::Subseteq { left, right } => TirExpr::Subseteq {
            left: Box::new(substitute_spanned(*left, param_map)),
            right: Box::new(substitute_spanned(*right, param_map)),
        },
        TirExpr::If { cond, then_, else_ } => TirExpr::If {
            cond: Box::new(substitute_spanned(*cond, param_map)),
            then_: Box::new(substitute_spanned(*then_, param_map)),
            else_: Box::new(substitute_spanned(*else_, param_map)),
        },
        TirExpr::Let { defs, body } => TirExpr::Let {
            defs: defs
                .into_iter()
                .map(|def| substitute_let_def(def, param_map))
                .collect(),
            body: Box::new(substitute_spanned(*body, param_map)),
        },
        TirExpr::Case { arms, other } => TirExpr::Case {
            arms: arms
                .into_iter()
                .map(|arm| TirCaseArm {
                    guard: substitute_spanned(arm.guard, param_map),
                    body: substitute_spanned(arm.body, param_map),
                })
                .collect(),
            other: other.map(|o| Box::new(substitute_spanned(*o, param_map))),
        },
        TirExpr::Forall { vars, body } => TirExpr::Forall {
            vars: vars
                .into_iter()
                .map(|v| substitute_bound_var(v, param_map))
                .collect(),
            body: Box::new(substitute_spanned(*body, param_map)),
        },
        TirExpr::Exists { vars, body } => TirExpr::Exists {
            vars: vars
                .into_iter()
                .map(|v| substitute_bound_var(v, param_map))
                .collect(),
            body: Box::new(substitute_spanned(*body, param_map)),
        },
        TirExpr::Choose { var, body } => TirExpr::Choose {
            var: substitute_bound_var(var, param_map),
            body: Box::new(substitute_spanned(*body, param_map)),
        },
        TirExpr::SetEnum(elems) => TirExpr::SetEnum(
            elems
                .into_iter()
                .map(|e| substitute_spanned(e, param_map))
                .collect(),
        ),
        TirExpr::SetFilter { var, body } => TirExpr::SetFilter {
            var: substitute_bound_var(var, param_map),
            body: Box::new(substitute_spanned(*body, param_map)),
        },
        TirExpr::SetBuilder { body, vars } => TirExpr::SetBuilder {
            body: Box::new(substitute_spanned(*body, param_map)),
            vars: vars
                .into_iter()
                .map(|v| substitute_bound_var(v, param_map))
                .collect(),
        },
        TirExpr::SetBinOp { left, op, right } => TirExpr::SetBinOp {
            left: Box::new(substitute_spanned(*left, param_map)),
            op,
            right: Box::new(substitute_spanned(*right, param_map)),
        },
        TirExpr::Powerset(inner) => {
            TirExpr::Powerset(Box::new(substitute_spanned(*inner, param_map)))
        }
        TirExpr::BigUnion(inner) => {
            TirExpr::BigUnion(Box::new(substitute_spanned(*inner, param_map)))
        }
        TirExpr::KSubset { base, k } => TirExpr::KSubset {
            base: Box::new(substitute_spanned(*base, param_map)),
            k: Box::new(substitute_spanned(*k, param_map)),
        },
        TirExpr::FuncDef { vars, body } => TirExpr::FuncDef {
            vars: vars
                .into_iter()
                .map(|v| substitute_bound_var(v, param_map))
                .collect(),
            body: Box::new(substitute_spanned(*body, param_map)),
        },
        TirExpr::FuncApply { func, arg } => TirExpr::FuncApply {
            func: Box::new(substitute_spanned(*func, param_map)),
            arg: Box::new(substitute_spanned(*arg, param_map)),
        },
        TirExpr::FuncSet { domain, range } => TirExpr::FuncSet {
            domain: Box::new(substitute_spanned(*domain, param_map)),
            range: Box::new(substitute_spanned(*range, param_map)),
        },
        TirExpr::Domain(inner) => TirExpr::Domain(Box::new(substitute_spanned(*inner, param_map))),
        TirExpr::Record(fields) => TirExpr::Record(
            fields
                .into_iter()
                .map(|(f, e)| (f, substitute_spanned(e, param_map)))
                .collect(),
        ),
        TirExpr::RecordSet(fields) => TirExpr::RecordSet(
            fields
                .into_iter()
                .map(|(f, e)| (f, substitute_spanned(e, param_map)))
                .collect(),
        ),
        TirExpr::Tuple(elems) => TirExpr::Tuple(
            elems
                .into_iter()
                .map(|e| substitute_spanned(e, param_map))
                .collect(),
        ),
        TirExpr::Times(elems) => TirExpr::Times(
            elems
                .into_iter()
                .map(|e| substitute_spanned(e, param_map))
                .collect(),
        ),
        TirExpr::RecordAccess { record, field } => TirExpr::RecordAccess {
            record: Box::new(substitute_spanned(*record, param_map)),
            field,
        },
        TirExpr::Except { base, specs } => TirExpr::Except {
            base: Box::new(substitute_spanned(*base, param_map)),
            specs: specs
                .into_iter()
                .map(|spec| substitute_except_spec(spec, param_map))
                .collect(),
        },
        TirExpr::Range { lo, hi } => TirExpr::Range {
            lo: Box::new(substitute_spanned(*lo, param_map)),
            hi: Box::new(substitute_spanned(*hi, param_map)),
        },
        TirExpr::Unchanged(inner) => {
            TirExpr::Unchanged(Box::new(substitute_spanned(*inner, param_map)))
        }
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => TirExpr::ActionSubscript {
            kind,
            action: Box::new(substitute_spanned(*action, param_map)),
            subscript: Box::new(substitute_spanned(*subscript, param_map)),
        },
        TirExpr::Always(inner) => TirExpr::Always(Box::new(substitute_spanned(*inner, param_map))),
        TirExpr::Eventually(inner) => {
            TirExpr::Eventually(Box::new(substitute_spanned(*inner, param_map)))
        }
        TirExpr::Prime(inner) => TirExpr::Prime(Box::new(substitute_spanned(*inner, param_map))),
        TirExpr::Apply { op, args } => TirExpr::Apply {
            op: Box::new(substitute_spanned(*op, param_map)),
            args: args
                .into_iter()
                .map(|a| substitute_spanned(a, param_map))
                .collect(),
        },
        TirExpr::Lambda {
            params,
            body,
            ast_body,
        } => TirExpr::Lambda {
            params,
            body: Box::new(substitute_spanned(*body, param_map)),
            ast_body,
        },
        TirExpr::Label { name, body } => TirExpr::Label {
            name,
            body: Box::new(substitute_spanned(*body, param_map)),
        },
        TirExpr::LeadsTo { left, right } => TirExpr::LeadsTo {
            left: Box::new(substitute_spanned(*left, param_map)),
            right: Box::new(substitute_spanned(*right, param_map)),
        },
        TirExpr::WeakFair { vars, action } => TirExpr::WeakFair {
            vars: Box::new(substitute_spanned(*vars, param_map)),
            action: Box::new(substitute_spanned(*action, param_map)),
        },
        TirExpr::StrongFair { vars, action } => TirExpr::StrongFair {
            vars: Box::new(substitute_spanned(*vars, param_map)),
            action: Box::new(substitute_spanned(*action, param_map)),
        },
        TirExpr::Enabled(inner) => {
            TirExpr::Enabled(Box::new(substitute_spanned(*inner, param_map)))
        }
        TirExpr::OperatorRef(op_ref) => TirExpr::OperatorRef(TirOperatorRef {
            path: op_ref
                .path
                .into_iter()
                .map(|seg| TirModuleRefSegment {
                    name: seg.name,
                    name_id: seg.name_id,
                    args: seg
                        .args
                        .into_iter()
                        .map(|a| substitute_spanned(a, param_map))
                        .collect(),
                })
                .collect(),
            operator: op_ref.operator,
            operator_id: op_ref.operator_id,
            args: op_ref
                .args
                .into_iter()
                .map(|a| substitute_spanned(a, param_map))
                .collect(),
        }),
        // Leaves with no children to substitute.
        TirExpr::Const { .. } | TirExpr::ExceptAt | TirExpr::OpRef(_) => node,
    }
}

fn substitute_spanned(
    expr: Spanned<TirExpr>,
    param_map: &FxHashMap<&str, &Spanned<TirExpr>>,
) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = substitute_node(expr.node, span, param_map);
    Spanned { node, span }
}

fn substitute_let_def(def: TirLetDef, param_map: &FxHashMap<&str, &Spanned<TirExpr>>) -> TirLetDef {
    TirLetDef {
        name: def.name,
        name_id: def.name_id,
        params: def.params,
        body: substitute_spanned(def.body, param_map),
    }
}

fn substitute_bound_var(
    var: TirBoundVar,
    param_map: &FxHashMap<&str, &Spanned<TirExpr>>,
) -> TirBoundVar {
    TirBoundVar {
        name: var.name,
        name_id: var.name_id,
        domain: var
            .domain
            .map(|d| Box::new(substitute_spanned(*d, param_map))),
        pattern: var.pattern,
    }
}

fn substitute_except_spec(
    spec: TirExceptSpec,
    param_map: &FxHashMap<&str, &Spanned<TirExpr>>,
) -> TirExceptSpec {
    TirExceptSpec {
        path: spec
            .path
            .into_iter()
            .map(|elem| match elem {
                TirExceptPathElement::Index(idx) => {
                    TirExceptPathElement::Index(Box::new(substitute_spanned(*idx, param_map)))
                }
                TirExceptPathElement::Field(f) => TirExceptPathElement::Field(f),
            })
            .collect(),
        value: substitute_spanned(spec.value, param_map),
    }
}

// --- Child visitor and mapper helpers ---

/// Visit all direct child expressions of a TIR node.
fn visit_children<F: FnMut(&Spanned<TirExpr>)>(node: &TirExpr, f: &mut F) {
    match node {
        TirExpr::Const { .. } | TirExpr::ExceptAt | TirExpr::OpRef(_) => {}
        TirExpr::Name(_) => {}
        TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::Subseteq { left, right }
        | TirExpr::In {
            elem: left,
            set: right,
        }
        | TirExpr::FuncSet {
            domain: left,
            range: right,
        }
        | TirExpr::FuncApply {
            func: left,
            arg: right,
        }
        | TirExpr::Range {
            lo: left,
            hi: right,
        }
        | TirExpr::LeadsTo { left, right }
        | TirExpr::KSubset {
            base: left,
            k: right,
        } => {
            f(left);
            f(right);
        }
        TirExpr::WeakFair { vars, action } | TirExpr::StrongFair { vars, action } => {
            f(vars);
            f(action);
        }
        TirExpr::ArithNeg(inner)
        | TirExpr::BoolNot(inner)
        | TirExpr::Unchanged(inner)
        | TirExpr::Always(inner)
        | TirExpr::Eventually(inner)
        | TirExpr::Enabled(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner)
        | TirExpr::Prime(inner) => f(inner),
        TirExpr::ActionSubscript {
            action, subscript, ..
        } => {
            f(action);
            f(subscript);
        }
        TirExpr::RecordAccess { record, .. } => f(record),
        TirExpr::If { cond, then_, else_ } => {
            f(cond);
            f(then_);
            f(else_);
        }
        TirExpr::Forall { vars, body } | TirExpr::Exists { vars, body } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    f(d);
                }
            }
            f(body);
        }
        TirExpr::Choose { var, body } => {
            if let Some(d) = &var.domain {
                f(d);
            }
            f(body);
        }
        TirExpr::SetEnum(elems) | TirExpr::Tuple(elems) | TirExpr::Times(elems) => {
            for e in elems {
                f(e);
            }
        }
        TirExpr::SetFilter { var, body } => {
            if let Some(d) = &var.domain {
                f(d);
            }
            f(body);
        }
        TirExpr::SetBuilder { body, vars } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    f(d);
                }
            }
            f(body);
        }
        TirExpr::FuncDef { vars, body } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    f(d);
                }
            }
            f(body);
        }
        TirExpr::Record(fields) | TirExpr::RecordSet(fields) => {
            for (_, e) in fields {
                f(e);
            }
        }
        TirExpr::Except { base, specs } => {
            f(base);
            for spec in specs {
                for elem in &spec.path {
                    if let TirExceptPathElement::Index(idx) = elem {
                        f(idx);
                    }
                }
                f(&spec.value);
            }
        }
        TirExpr::Let { defs, body } => {
            for def in defs {
                f(&def.body);
            }
            f(body);
        }
        TirExpr::Case { arms, other } => {
            for arm in arms {
                f(&arm.guard);
                f(&arm.body);
            }
            if let Some(o) = other {
                f(o);
            }
        }
        TirExpr::Apply { op, args } => {
            f(op);
            for a in args {
                f(a);
            }
        }
        TirExpr::Lambda { body, .. } => f(body),
        TirExpr::Label { body, .. } => f(body),
        TirExpr::OperatorRef(op_ref) => {
            for seg in &op_ref.path {
                for a in &seg.args {
                    f(a);
                }
            }
            for a in &op_ref.args {
                f(a);
            }
        }
    }
}

/// Map all children of a TIR node through the inline transformation, returning
/// a new owned node. This handles every variant except `Apply` (which is
/// handled specially in `inline_in_expr`).
fn map_children_owned(
    node: TirExpr,
    candidates: &FxHashMap<NameId, (Vec<String>, Spanned<TirExpr>)>,
    replaced_count: &mut usize,
    inlined_ids: &mut FxHashSet<NameId>,
) -> TirExpr {
    match node {
        TirExpr::Const { .. } | TirExpr::Name(_) | TirExpr::ExceptAt | TirExpr::OpRef(_) => node,
        TirExpr::ArithBinOp { left, op, right } => TirExpr::ArithBinOp {
            left: Box::new(inline_in_expr(
                *left,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            op,
            right: Box::new(inline_in_expr(
                *right,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::ArithNeg(inner) => TirExpr::ArithNeg(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::BoolBinOp { left, op, right } => TirExpr::BoolBinOp {
            left: Box::new(inline_in_expr(
                *left,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            op,
            right: Box::new(inline_in_expr(
                *right,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::BoolNot(inner) => TirExpr::BoolNot(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::Cmp { left, op, right } => TirExpr::Cmp {
            left: Box::new(inline_in_expr(
                *left,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            op,
            right: Box::new(inline_in_expr(
                *right,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::In { elem, set } => TirExpr::In {
            elem: Box::new(inline_in_expr(
                *elem,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            set: Box::new(inline_in_expr(
                *set,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Subseteq { left, right } => TirExpr::Subseteq {
            left: Box::new(inline_in_expr(
                *left,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            right: Box::new(inline_in_expr(
                *right,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Unchanged(inner) => TirExpr::Unchanged(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => TirExpr::ActionSubscript {
            kind,
            action: Box::new(inline_in_expr(
                *action,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            subscript: Box::new(inline_in_expr(
                *subscript,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Always(inner) => TirExpr::Always(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::Eventually(inner) => TirExpr::Eventually(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::Enabled(inner) => TirExpr::Enabled(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::RecordAccess { record, field } => TirExpr::RecordAccess {
            record: Box::new(inline_in_expr(
                *record,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            field,
        },
        TirExpr::Except { base, specs } => TirExpr::Except {
            base: Box::new(inline_in_expr(
                *base,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            specs: specs
                .into_iter()
                .map(|spec| inline_except_spec(spec, candidates, replaced_count, inlined_ids))
                .collect(),
        },
        TirExpr::Range { lo, hi } => TirExpr::Range {
            lo: Box::new(inline_in_expr(*lo, candidates, replaced_count, inlined_ids)),
            hi: Box::new(inline_in_expr(*hi, candidates, replaced_count, inlined_ids)),
        },
        TirExpr::If { cond, then_, else_ } => TirExpr::If {
            cond: Box::new(inline_in_expr(
                *cond,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            then_: Box::new(inline_in_expr(
                *then_,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            else_: Box::new(inline_in_expr(
                *else_,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Forall { vars, body } => TirExpr::Forall {
            vars: vars
                .into_iter()
                .map(|v| inline_bound_var(v, candidates, replaced_count, inlined_ids))
                .collect(),
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Exists { vars, body } => TirExpr::Exists {
            vars: vars
                .into_iter()
                .map(|v| inline_bound_var(v, candidates, replaced_count, inlined_ids))
                .collect(),
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Choose { var, body } => TirExpr::Choose {
            var: inline_bound_var(var, candidates, replaced_count, inlined_ids),
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::SetEnum(elems) => TirExpr::SetEnum(
            elems
                .into_iter()
                .map(|e| inline_in_expr(e, candidates, replaced_count, inlined_ids))
                .collect(),
        ),
        TirExpr::SetFilter { var, body } => TirExpr::SetFilter {
            var: inline_bound_var(var, candidates, replaced_count, inlined_ids),
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::SetBuilder { body, vars } => TirExpr::SetBuilder {
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            vars: vars
                .into_iter()
                .map(|v| inline_bound_var(v, candidates, replaced_count, inlined_ids))
                .collect(),
        },
        TirExpr::SetBinOp { left, op, right } => TirExpr::SetBinOp {
            left: Box::new(inline_in_expr(
                *left,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            op,
            right: Box::new(inline_in_expr(
                *right,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Powerset(inner) => TirExpr::Powerset(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::BigUnion(inner) => TirExpr::BigUnion(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::KSubset { base, k } => TirExpr::KSubset {
            base: Box::new(inline_in_expr(
                *base,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            k: Box::new(inline_in_expr(*k, candidates, replaced_count, inlined_ids)),
        },
        TirExpr::FuncDef { vars, body } => TirExpr::FuncDef {
            vars: vars
                .into_iter()
                .map(|v| inline_bound_var(v, candidates, replaced_count, inlined_ids))
                .collect(),
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::FuncApply { func, arg } => TirExpr::FuncApply {
            func: Box::new(inline_in_expr(
                *func,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            arg: Box::new(inline_in_expr(
                *arg,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::FuncSet { domain, range } => TirExpr::FuncSet {
            domain: Box::new(inline_in_expr(
                *domain,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            range: Box::new(inline_in_expr(
                *range,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Domain(inner) => TirExpr::Domain(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::Record(fields) => TirExpr::Record(
            fields
                .into_iter()
                .map(|(f, e)| {
                    (
                        f,
                        inline_in_expr(e, candidates, replaced_count, inlined_ids),
                    )
                })
                .collect(),
        ),
        TirExpr::RecordSet(fields) => TirExpr::RecordSet(
            fields
                .into_iter()
                .map(|(f, e)| {
                    (
                        f,
                        inline_in_expr(e, candidates, replaced_count, inlined_ids),
                    )
                })
                .collect(),
        ),
        TirExpr::Tuple(elems) => TirExpr::Tuple(
            elems
                .into_iter()
                .map(|e| inline_in_expr(e, candidates, replaced_count, inlined_ids))
                .collect(),
        ),
        TirExpr::Times(elems) => TirExpr::Times(
            elems
                .into_iter()
                .map(|e| inline_in_expr(e, candidates, replaced_count, inlined_ids))
                .collect(),
        ),
        TirExpr::Let { defs, body } => TirExpr::Let {
            defs: defs
                .into_iter()
                .map(|def| inline_let_def(def, candidates, replaced_count, inlined_ids))
                .collect(),
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::Case { arms, other } => TirExpr::Case {
            arms: arms
                .into_iter()
                .map(|arm| TirCaseArm {
                    guard: inline_in_expr(arm.guard, candidates, replaced_count, inlined_ids),
                    body: inline_in_expr(arm.body, candidates, replaced_count, inlined_ids),
                })
                .collect(),
            other: other
                .map(|o| Box::new(inline_in_expr(*o, candidates, replaced_count, inlined_ids))),
        },
        TirExpr::Prime(inner) => TirExpr::Prime(Box::new(inline_in_expr(
            *inner,
            candidates,
            replaced_count,
            inlined_ids,
        ))),
        TirExpr::Apply { op, args } => {
            // This shouldn't be reached (handled in inline_in_expr), but be safe.
            TirExpr::Apply {
                op: Box::new(inline_in_expr(*op, candidates, replaced_count, inlined_ids)),
                args: args
                    .into_iter()
                    .map(|a| inline_in_expr(a, candidates, replaced_count, inlined_ids))
                    .collect(),
            }
        }
        TirExpr::Lambda {
            params,
            body,
            ast_body,
        } => TirExpr::Lambda {
            params,
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            ast_body,
        },
        TirExpr::Label { name, body } => TirExpr::Label {
            name,
            body: Box::new(inline_in_expr(
                *body,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::LeadsTo { left, right } => TirExpr::LeadsTo {
            left: Box::new(inline_in_expr(
                *left,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            right: Box::new(inline_in_expr(
                *right,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::WeakFair { vars, action } => TirExpr::WeakFair {
            vars: Box::new(inline_in_expr(
                *vars,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            action: Box::new(inline_in_expr(
                *action,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::StrongFair { vars, action } => TirExpr::StrongFair {
            vars: Box::new(inline_in_expr(
                *vars,
                candidates,
                replaced_count,
                inlined_ids,
            )),
            action: Box::new(inline_in_expr(
                *action,
                candidates,
                replaced_count,
                inlined_ids,
            )),
        },
        TirExpr::OperatorRef(op_ref) => TirExpr::OperatorRef(TirOperatorRef {
            path: op_ref
                .path
                .into_iter()
                .map(|seg| TirModuleRefSegment {
                    name: seg.name,
                    name_id: seg.name_id,
                    args: seg
                        .args
                        .into_iter()
                        .map(|a| inline_in_expr(a, candidates, replaced_count, inlined_ids))
                        .collect(),
                })
                .collect(),
            operator: op_ref.operator,
            operator_id: op_ref.operator_id,
            args: op_ref
                .args
                .into_iter()
                .map(|a| inline_in_expr(a, candidates, replaced_count, inlined_ids))
                .collect(),
        }),
    }
}

fn inline_bound_var(
    var: TirBoundVar,
    candidates: &FxHashMap<NameId, (Vec<String>, Spanned<TirExpr>)>,
    replaced_count: &mut usize,
    inlined_ids: &mut FxHashSet<NameId>,
) -> TirBoundVar {
    TirBoundVar {
        name: var.name,
        name_id: var.name_id,
        domain: var
            .domain
            .map(|d| Box::new(inline_in_expr(*d, candidates, replaced_count, inlined_ids))),
        pattern: var.pattern,
    }
}

fn inline_let_def(
    def: TirLetDef,
    candidates: &FxHashMap<NameId, (Vec<String>, Spanned<TirExpr>)>,
    replaced_count: &mut usize,
    inlined_ids: &mut FxHashSet<NameId>,
) -> TirLetDef {
    TirLetDef {
        name: def.name,
        name_id: def.name_id,
        params: def.params,
        body: inline_in_expr(def.body, candidates, replaced_count, inlined_ids),
    }
}

fn inline_except_spec(
    spec: TirExceptSpec,
    candidates: &FxHashMap<NameId, (Vec<String>, Spanned<TirExpr>)>,
    replaced_count: &mut usize,
    inlined_ids: &mut FxHashSet<NameId>,
) -> TirExceptSpec {
    TirExceptSpec {
        path: spec
            .path
            .into_iter()
            .map(|elem| match elem {
                TirExceptPathElement::Index(idx) => TirExceptPathElement::Index(Box::new(
                    inline_in_expr(*idx, candidates, replaced_count, inlined_ids),
                )),
                TirExceptPathElement::Field(f) => TirExceptPathElement::Field(f),
            })
            .collect(),
        value: inline_in_expr(spec.value, candidates, replaced_count, inlined_ids),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nodes::*;
    use crate::types::TirType;
    use tla_core::intern_name;
    use tla_core::span::{FileId, Span};
    use tla_value::Value;

    fn span() -> Span {
        Span::new(FileId(0), 0, 0)
    }

    fn spanned(expr: TirExpr) -> Spanned<TirExpr> {
        Spanned::new(expr, span())
    }

    fn int_const(n: i64) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::int(n),
            ty: TirType::Int,
        })
    }

    fn name_ident(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::Ident,
            ty: TirType::Dyn,
        }))
    }

    fn make_operator(name: &str, params: Vec<&str>, body: Spanned<TirExpr>) -> TirOperator {
        TirOperator {
            name: name.to_string(),
            name_id: intern_name(name),
            params: params.into_iter().map(String::from).collect(),
            is_recursive: false,
            body,
        }
    }

    /// Double(x) == x + x
    fn double_operator() -> TirOperator {
        make_operator(
            "Double",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            }),
        )
    }

    /// Main == Double(5)
    fn main_calls_double() -> TirOperator {
        TirOperator {
            name: "Main".to_string(),
            name_id: intern_name("Main"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Double")),
                args: vec![int_const(5)],
            }),
        }
    }

    #[test]
    fn test_inline_simple_call() {
        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double_operator(), main_calls_double()],
        };

        let config = InliningConfig::default();
        let stats = inline_functions(&mut module, &config);

        assert_eq!(stats.call_sites_replaced, 1);
        assert_eq!(stats.functions_inlined, 1);

        // Main's body should now be 5 + 5, not Apply(Double, [5]).
        let main_op = &module.operators[1];
        match &main_op.body.node {
            TirExpr::ArithBinOp {
                left, op, right, ..
            } => {
                assert_eq!(*op, TirArithOp::Add);
                // Both sides should be the constant 5 (substituted for x).
                match (&left.node, &right.node) {
                    (TirExpr::Const { value: lv, .. }, TirExpr::Const { value: rv, .. }) => {
                        assert_eq!(*lv, Value::int(5));
                        assert_eq!(*rv, Value::int(5));
                    }
                    _ => panic!(
                        "expected Const nodes after inlining, got {:?}",
                        main_op.body
                    ),
                }
            }
            _ => panic!("expected ArithBinOp after inlining, got {:?}", main_op.body),
        }
    }

    #[test]
    fn test_no_inline_recursive() {
        let mut fib = make_operator(
            "Fib",
            vec!["n"],
            // Simplified: just Fib(n) to mark it recursive.
            spanned(TirExpr::Apply {
                op: Box::new(name_ident("Fib")),
                args: vec![name_ident("n")],
            }),
        );
        fib.is_recursive = true;

        let caller = TirOperator {
            name: "Main".to_string(),
            name_id: intern_name("Main"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Fib")),
                args: vec![int_const(10)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![fib, caller],
        };

        let stats = inline_functions(&mut module, &InliningConfig::default());

        assert_eq!(stats.call_sites_replaced, 0);
        assert_eq!(stats.functions_inlined, 0);

        // Main body should still be Apply.
        assert!(matches!(
            module.operators[1].body.node,
            TirExpr::Apply { .. }
        ));
    }

    #[test]
    fn test_no_inline_too_large() {
        // Build a body that exceeds the threshold.
        let big_body = spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            })),
            op: TirArithOp::Mul,
            right: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Sub,
                right: Box::new(name_ident("x")),
            })),
        });

        let big_op = make_operator("Big", vec!["x"], big_body);
        let caller = TirOperator {
            name: "Main".to_string(),
            name_id: intern_name("Main"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Big")),
                args: vec![int_const(1)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![big_op, caller],
        };

        // Use a tiny threshold.
        let config = InliningConfig { max_inline_size: 3 };
        let stats = inline_functions(&mut module, &config);

        assert_eq!(stats.call_sites_replaced, 0);
    }

    #[test]
    fn test_no_inline_non_leaf() {
        // Inner(x) == x + 1
        let inner = make_operator(
            "Inner",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(int_const(1)),
            }),
        );

        // Outer(y) == Inner(y) + 2 — calls Inner, so NOT a leaf.
        let outer = make_operator(
            "Outer",
            vec!["y"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Apply {
                    op: Box::new(name_ident("Inner")),
                    args: vec![name_ident("y")],
                })),
                op: TirArithOp::Add,
                right: Box::new(int_const(2)),
            }),
        );

        let main = TirOperator {
            name: "Main".to_string(),
            name_id: intern_name("Main"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Outer")),
                args: vec![int_const(10)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![inner, outer, main],
        };

        let stats = inline_functions(&mut module, &InliningConfig::default());

        // Inner IS a leaf and small, so it should be inlined into Outer.
        // Outer is NOT a leaf (calls Inner), so it should NOT be inlined into Main.
        // After inlining Inner into Outer:
        //   Outer's body: (y + 1) + 2  (the call to Inner(y) is replaced)
        //   Main's body: still Apply(Outer, [10])
        assert_eq!(stats.call_sites_replaced, 1);
        assert_eq!(stats.functions_inlined, 1);

        // Check Main is still an Apply (Outer was not inlined).
        assert!(
            matches!(module.operators[2].body.node, TirExpr::Apply { .. }),
            "Main should still have Apply since Outer is not a leaf"
        );

        // Check Outer's body was inlined (Inner's body substituted).
        match &module.operators[1].body.node {
            TirExpr::ArithBinOp { left, .. } => {
                // left should now be (y + 1), not Apply(Inner, [y]).
                assert!(
                    matches!(left.node, TirExpr::ArithBinOp { .. }),
                    "Inner call should have been inlined into Outer"
                );
            }
            _ => panic!("Outer body should still be ArithBinOp"),
        }
    }

    #[test]
    fn test_no_inline_zero_arity() {
        let constant_op = make_operator("N", vec![], int_const(42));

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![constant_op],
        };

        let stats = inline_functions(&mut module, &InliningConfig::default());
        assert_eq!(stats.call_sites_replaced, 0);
    }

    #[test]
    fn test_inline_multiple_call_sites() {
        // Double(x) == x + x
        let double = double_operator();

        // Main == Double(3) + Double(7)
        let main = TirOperator {
            name: "Main".to_string(),
            name_id: intern_name("Main"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Apply {
                    op: Box::new(name_ident("Double")),
                    args: vec![int_const(3)],
                })),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Apply {
                    op: Box::new(name_ident("Double")),
                    args: vec![int_const(7)],
                })),
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double, main],
        };

        let stats = inline_functions(&mut module, &InliningConfig::default());

        assert_eq!(stats.call_sites_replaced, 2);
        assert_eq!(stats.functions_inlined, 1);

        // Main body: (3 + 3) + (7 + 7)
        match &module.operators[1].body.node {
            TirExpr::ArithBinOp { left, right, .. } => {
                assert!(matches!(left.node, TirExpr::ArithBinOp { .. }));
                assert!(matches!(right.node, TirExpr::ArithBinOp { .. }));
            }
            _ => panic!("expected nested ArithBinOp"),
        }
    }

    #[test]
    fn test_inline_multi_param() {
        // Add(a, b) == a + b
        let add = make_operator(
            "Add",
            vec!["a", "b"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("a")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("b")),
            }),
        );

        // Main == Add(3, 4)
        let main = TirOperator {
            name: "Main".to_string(),
            name_id: intern_name("Main"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Add")),
                args: vec![int_const(3), int_const(4)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![add, main],
        };

        let stats = inline_functions(&mut module, &InliningConfig::default());
        assert_eq!(stats.call_sites_replaced, 1);

        // Main body: 3 + 4
        match &module.operators[1].body.node {
            TirExpr::ArithBinOp { left, right, op } => {
                assert_eq!(*op, TirArithOp::Add);
                assert!(matches!(left.node, TirExpr::Const { .. }));
                assert!(matches!(right.node, TirExpr::Const { .. }));
            }
            _ => panic!("expected ArithBinOp after inlining Add"),
        }
    }

    #[test]
    fn test_count_nodes() {
        // Leaf: 1 node.
        assert_eq!(count_nodes(&int_const(0)), 1);

        // x + y: 3 nodes (ArithBinOp + 2 Name).
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(name_ident("x")),
            op: TirArithOp::Add,
            right: Box::new(name_ident("y")),
        });
        assert_eq!(count_nodes(&expr), 3);
    }

    #[test]
    fn test_empty_module() {
        let mut module = TirModule {
            name: "Empty".to_string(),
            operators: vec![],
        };
        let stats = inline_functions(&mut module, &InliningConfig::default());
        assert_eq!(stats, InliningStats::default());
    }

    #[test]
    fn test_config_default() {
        let config = InliningConfig::default();
        assert_eq!(config.max_inline_size, 20);
    }

    #[test]
    fn test_inline_with_if_body() {
        // Max(a, b) == IF a > b THEN a ELSE b
        let max_op = make_operator(
            "Max",
            vec!["a", "b"],
            spanned(TirExpr::If {
                cond: Box::new(spanned(TirExpr::Cmp {
                    left: Box::new(name_ident("a")),
                    op: TirCmpOp::Gt,
                    right: Box::new(name_ident("b")),
                })),
                then_: Box::new(name_ident("a")),
                else_: Box::new(name_ident("b")),
            }),
        );

        // Main == Max(10, 20)
        let main = TirOperator {
            name: "Main".to_string(),
            name_id: intern_name("Main"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Max")),
                args: vec![int_const(10), int_const(20)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![max_op, main],
        };

        let stats = inline_functions(&mut module, &InliningConfig::default());
        assert_eq!(stats.call_sites_replaced, 1);

        // Main body: IF 10 > 20 THEN 10 ELSE 20
        match &module.operators[1].body.node {
            TirExpr::If { cond, then_, else_ } => {
                // cond should be Cmp with constants.
                assert!(matches!(cond.node, TirExpr::Cmp { .. }));
                // then_ and else_ should be constants.
                assert!(matches!(then_.node, TirExpr::Const { .. }));
                assert!(matches!(else_.node, TirExpr::Const { .. }));
            }
            _ => panic!("expected If after inlining Max"),
        }
    }
}
