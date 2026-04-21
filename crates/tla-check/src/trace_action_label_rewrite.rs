// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace-validation helpers for constraining action labels via AST rewrites.
//!
//! v1 rewrite backend (design docs in `designs/`):
//! - Detect an action disjunct `E` from `Next` (via `detect_actions`).
//! - Conjoin equality constraints for trace-provided params inside the outer `\E` scopes of `E`.
//! - Evaluate the rewritten predicate over `(s, s')`.
//!
//! This module currently provides binder discovery + structured errors for the case where a trace
//! param key cannot be bound to a unique outer `\E` witness variable.

use std::fmt;

use crate::coverage::{DetectedAction, DetectedActionId};
use crate::trace_action_label_mapping::OperatorRef;
use tla_core::ast::{BoundPattern, Expr, ModuleTarget};
use tla_core::pretty_expr;
use tla_core::{Span, Spanned};

/// A `\E` bound variable site (name + span) extracted from an action expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundVarSite {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ActionLabelParamBindErrorKind {
    /// A mapping param key does not appear among the outer `\E` binders of the detected action.
    MissingBinder { param: String },
    /// A mapping param key matches multiple distinct outer `\E` binders (shadowing/reuse).
    AmbiguousBinder {
        param: String,
        matches: Vec<BoundVarSite>,
    },
    /// A mapping param key didn't match an outer binder name, and no safe operator callsite exists.
    MissingCallsite { param: String },
    /// A mapping param key didn't match an outer binder name, and multiple safe callsites exist.
    AmbiguousCallsite { param: String, callsites: Vec<Span> },
    /// A mapping param key didn't match an outer binder name, and the callsite arg is unsupported.
    UnsupportedCallsiteArg {
        param: String,
        /// 0-based formal index in the mapped operator (and callsite arg position).
        position: usize,
        arg: String,
        arg_span: Span,
    },
}

/// A structured error for rewrite-backend parameter binding failures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActionLabelParamBindError {
    pub label: String,
    pub operator_raw: String,
    pub action_name: String,
    pub action_id: DetectedActionId,
    pub action_span: Span,
    pub outer_binders: Vec<BoundVarSite>,
    pub kind: ActionLabelParamBindErrorKind,
}

impl ActionLabelParamBindError {
    pub fn suggestion_text(&self) -> &'static str {
        "v1 limitation: trace param keys must match the mapped operator's formal parameter names; \
each formal must either be (1) an outer `\\E` witness variable name in the detected action, or \
(2) passed at the operator callsite as a simple identifier bound by an outer `\\E` witness binder"
    }
}

impl fmt::Display for ActionLabelParamBindError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let span = &self.action_span;
        let mut binder_names: Vec<&str> =
            self.outer_binders.iter().map(|b| b.name.as_str()).collect();
        binder_names.sort_unstable();
        binder_names.dedup();

        let action_id_suffix = format!(" (id={})", self.action_id);

        match &self.kind {
            ActionLabelParamBindErrorKind::MissingBinder { param } => {
                write!(
                    f,
                    "action label {} (operator {}) cannot bind param {:?}: no outer `\\E` binder named {:?} in action {}{} (file {}, bytes {}-{}); available binders: {:?}. hint: {}",
                    self.label,
                    self.operator_raw,
                    param,
                    param,
                    self.action_name,
                    action_id_suffix,
                    span.file.0,
                    span.start,
                    span.end,
                    binder_names,
                    self.suggestion_text(),
                )
            }
            ActionLabelParamBindErrorKind::AmbiguousBinder { param, matches } => {
                write!(
                    f,
                    "action label {} (operator {}) cannot bind param {:?}: multiple outer `\\E` binders named {:?} in action {}{} (file {}, bytes {}-{}); matching binders at spans {:?}; available binders: {:?}. hint: {}",
                    self.label,
                    self.operator_raw,
                    param,
                    param,
                    self.action_name,
                    action_id_suffix,
                    span.file.0,
                    span.start,
                    span.end,
                    matches.iter().map(|m| m.span).collect::<Vec<_>>(),
                    binder_names,
                    self.suggestion_text(),
                )
            }
            ActionLabelParamBindErrorKind::MissingCallsite { param } => {
                write!(
                    f,
                    "action label {} (operator {}) cannot bind param {:?}: no safe callsite for operator {:?} in action {}{} (file {}, bytes {}-{}); available binders: {:?}. hint: {}",
                    self.label,
                    self.operator_raw,
                    param,
                    self.operator_raw,
                    self.action_name,
                    action_id_suffix,
                    span.file.0,
                    span.start,
                    span.end,
                    binder_names,
                    self.suggestion_text(),
                )
            }
            ActionLabelParamBindErrorKind::AmbiguousCallsite { param, callsites } => {
                write!(
                    f,
                    "action label {} (operator {}) cannot bind param {:?}: multiple safe callsites for operator {:?} in action {}{} (file {}, bytes {}-{}); callsites at spans {:?}; available binders: {:?}. hint: {}",
                    self.label,
                    self.operator_raw,
                    param,
                    self.operator_raw,
                    self.action_name,
                    action_id_suffix,
                    span.file.0,
                    span.start,
                    span.end,
                    callsites,
                    binder_names,
                    self.suggestion_text(),
                )
            }
            ActionLabelParamBindErrorKind::UnsupportedCallsiteArg {
                param,
                position,
                arg,
                arg_span,
            } => {
                write!(
                    f,
                    "action label {} (operator {}) cannot bind param {:?}: callsite arg {} is unsupported (expected an outer `\\E`-bound identifier), got {:?} (file {}, bytes {}-{}); available binders: {:?}. hint: {}",
                    self.label,
                    self.operator_raw,
                    param,
                    position + 1,
                    arg,
                    arg_span.file.0,
                    arg_span.start,
                    arg_span.end,
                    binder_names,
                    self.suggestion_text(),
                )
            }
        }
    }
}

impl std::error::Error for ActionLabelParamBindError {}

/// Extract `\E` binder sites along the outer wrapper spine of an action expression.
///
/// `detect_actions` preserves `LET` wrappers around disjuncts, so an action expression may start
/// with `LET ... IN (\E ...)`. For rewrite-backend param binding, treat `LET` as transparent and
/// collect all `\E` binders encountered along the outer `LET`/`\E` spine, stopping at the first
/// non-`LET` / non-`\E` node.
///
/// For pattern binders like `\E <<x, y>> \in S`, collect the pattern variables (`x`, `y`) rather
/// than the synthetic internal binder name (`<<x, y>>`).
pub fn outer_exists_binder_sites(expr: &Spanned<Expr>) -> Vec<BoundVarSite> {
    let mut sites = Vec::new();
    let mut cur = expr;
    loop {
        match &cur.node {
            Expr::Let(_, body) => {
                cur = body.as_ref();
            }
            Expr::Exists(bounds, body) => {
                for b in bounds {
                    match &b.pattern {
                        // For tuple/pattern binders, the evaluator binds pattern variables, not
                        // `b.name` (which is synthetic for tuple patterns).
                        Some(BoundPattern::Var(v)) => sites.push(BoundVarSite {
                            name: v.node.clone(),
                            span: v.span,
                        }),
                        Some(BoundPattern::Tuple(vars)) => {
                            sites.extend(vars.iter().map(|v| BoundVarSite {
                                name: v.node.clone(),
                                span: v.span,
                            }));
                        }
                        None => sites.push(BoundVarSite {
                            name: b.name.node.clone(),
                            span: b.name.span,
                        }),
                    }
                }
                cur = body.as_ref();
            }
            _ => break,
        }
    }
    sites
}

#[derive(Debug, Clone)]
struct SafeCallsite {
    span: Span,
    args: Vec<Spanned<Expr>>,
}

fn operator_ref_from_raw(operator_raw: &str) -> OperatorRef {
    let trimmed = operator_raw.trim();
    if let Some((target, name)) = trimmed.split_once('!') {
        OperatorRef::ModuleRef {
            target: target.to_string(),
            name: name.to_string(),
        }
    } else {
        OperatorRef::Unqualified {
            name: trimmed.to_string(),
        }
    }
}

fn peel_outer_let_exists(expr: &Spanned<Expr>) -> &Spanned<Expr> {
    let mut cur = expr;
    loop {
        match &cur.node {
            Expr::Let(_, body) => cur = body.as_ref(),
            Expr::Exists(_, body) => cur = body.as_ref(),
            _ => return cur,
        }
    }
}

fn operator_matches_apply(operator: &OperatorRef, op_expr: &Expr) -> bool {
    match (operator, op_expr) {
        (OperatorRef::Unqualified { name }, Expr::Ident(op_name, _)) => name == op_name,
        _ => false,
    }
}

fn operator_matches_module_ref(operator: &OperatorRef, module: &ModuleTarget, name: &str) -> bool {
    let ModuleTarget::Named(module_name) = module else {
        return false;
    };
    match operator {
        OperatorRef::ModuleRef { target, name: op } => target == module_name && op == name,
        _ => false,
    }
}

fn collect_safe_callsites(
    expr: &Spanned<Expr>,
    operator: &OperatorRef,
    out: &mut Vec<SafeCallsite>,
) {
    match &expr.node {
        Expr::And(a, b) => {
            collect_safe_callsites(a, operator, out);
            collect_safe_callsites(b, operator, out);
        }
        Expr::Apply(op, args) => {
            if operator_matches_apply(operator, &op.node) {
                out.push(SafeCallsite {
                    span: expr.span,
                    args: args.clone(),
                });
            }
        }
        Expr::ModuleRef(module, name, args) => {
            if operator_matches_module_ref(operator, module, name) {
                out.push(SafeCallsite {
                    span: expr.span,
                    args: args.clone(),
                });
            }
        }
        // v1 scope boundaries for safe callsite discovery.
        Expr::Let(_, _) | Expr::Exists(_, _) | Expr::Forall(_, _) => {}
        _ => {}
    }
}

fn find_safe_callsites(expr: &Spanned<Expr>, operator: &OperatorRef) -> Vec<SafeCallsite> {
    let body = peel_outer_let_exists(expr);
    let mut out = Vec::new();
    collect_safe_callsites(body, operator, &mut out);
    out
}

/// Resolve mapping param keys to unique outer `\E` binder sites for the rewrite backend.
///
/// Returns the binder sites in the same order as `param_keys`.
#[allow(clippy::result_large_err)]
pub fn resolve_param_binders_for_rewrite(
    label: &str,
    operator_raw: &str,
    action: &DetectedAction,
    param_keys: &[String],
) -> Result<Vec<BoundVarSite>, ActionLabelParamBindError> {
    let operator = operator_ref_from_raw(operator_raw);
    let action_id = action.id;
    let outer_binders = outer_exists_binder_sites(&action.expr);

    let mut resolved = Vec::with_capacity(param_keys.len());
    let mut safe_callsites: Option<Vec<SafeCallsite>> = None;

    for (position, key) in param_keys.iter().enumerate() {
        let matches: Vec<BoundVarSite> = outer_binders
            .iter()
            .filter(|b| b.name == *key)
            .cloned()
            .collect();

        match matches.len() {
            0 => {}
            1 => resolved.push(matches[0].clone()),
            _ => {
                return Err(ActionLabelParamBindError {
                    label: label.to_string(),
                    operator_raw: operator_raw.to_string(),
                    action_name: action.name.clone(),
                    action_id,
                    action_span: action.expr.span,
                    outer_binders,
                    kind: ActionLabelParamBindErrorKind::AmbiguousBinder {
                        param: key.clone(),
                        matches,
                    },
                });
            }
        }

        if matches.is_empty() {
            let callsites =
                safe_callsites.get_or_insert_with(|| find_safe_callsites(&action.expr, &operator));
            match callsites.len() {
                0 => {
                    return Err(ActionLabelParamBindError {
                        label: label.to_string(),
                        operator_raw: operator_raw.to_string(),
                        action_name: action.name.clone(),
                        action_id,
                        action_span: action.expr.span,
                        outer_binders,
                        kind: ActionLabelParamBindErrorKind::MissingCallsite { param: key.clone() },
                    });
                }
                1 => {
                    let callsite = &callsites[0];
                    let Some(arg) = callsite.args.get(position) else {
                        return Err(ActionLabelParamBindError {
                            label: label.to_string(),
                            operator_raw: operator_raw.to_string(),
                            action_name: action.name.clone(),
                            action_id,
                            action_span: action.expr.span,
                            outer_binders,
                            kind: ActionLabelParamBindErrorKind::UnsupportedCallsiteArg {
                                param: key.clone(),
                                position,
                                arg: format!(
                                    "<missing arg {} of {}>",
                                    position + 1,
                                    param_keys.len()
                                ),
                                arg_span: callsite.span,
                            },
                        });
                    };

                    let Expr::Ident(arg_name, _) = &arg.node else {
                        return Err(ActionLabelParamBindError {
                            label: label.to_string(),
                            operator_raw: operator_raw.to_string(),
                            action_name: action.name.clone(),
                            action_id,
                            action_span: action.expr.span,
                            outer_binders,
                            kind: ActionLabelParamBindErrorKind::UnsupportedCallsiteArg {
                                param: key.clone(),
                                position,
                                arg: pretty_expr(&arg.node),
                                arg_span: arg.span,
                            },
                        });
                    };

                    let binder_matches: Vec<BoundVarSite> = outer_binders
                        .iter()
                        .filter(|b| b.name == *arg_name)
                        .cloned()
                        .collect();
                    match binder_matches.len() {
                        0 => {
                            return Err(ActionLabelParamBindError {
                                label: label.to_string(),
                                operator_raw: operator_raw.to_string(),
                                action_name: action.name.clone(),
                                action_id,
                                action_span: action.expr.span,
                                outer_binders,
                                kind: ActionLabelParamBindErrorKind::UnsupportedCallsiteArg {
                                    param: key.clone(),
                                    position,
                                    arg: arg_name.clone(),
                                    arg_span: arg.span,
                                },
                            });
                        }
                        1 => resolved.push(binder_matches[0].clone()),
                        _ => {
                            return Err(ActionLabelParamBindError {
                                label: label.to_string(),
                                operator_raw: operator_raw.to_string(),
                                action_name: action.name.clone(),
                                action_id,
                                action_span: action.expr.span,
                                outer_binders,
                                kind: ActionLabelParamBindErrorKind::AmbiguousBinder {
                                    param: key.clone(),
                                    matches: binder_matches,
                                },
                            });
                        }
                    }
                }
                _ => {
                    return Err(ActionLabelParamBindError {
                        label: label.to_string(),
                        operator_raw: operator_raw.to_string(),
                        action_name: action.name.clone(),
                        action_id,
                        action_span: action.expr.span,
                        outer_binders,
                        kind: ActionLabelParamBindErrorKind::AmbiguousCallsite {
                            param: key.clone(),
                            callsites: callsites.iter().map(|c| c.span).collect(),
                        },
                    });
                }
            }
        }
    }

    Ok(resolved)
}
