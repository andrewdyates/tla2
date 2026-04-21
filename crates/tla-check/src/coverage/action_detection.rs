// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fmt;
use tla_core::ast::{BoundVar, Expr, OperatorDef};
use tla_core::{Span, Spanned};

/// Stable identifier for a detected Next disjunct.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DetectedActionId {
    pub span: Span,
}

impl DetectedActionId {
    #[must_use]
    pub const fn new(span: Span) -> Self {
        Self { span }
    }
}

impl fmt::Display for DetectedActionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}-{}",
            self.span.file.0, self.span.start, self.span.end
        )
    }
}

/// Detected action from Next relation analysis
#[derive(Debug, Clone)]
pub struct DetectedAction {
    /// Stable identifier for this detected action.
    pub id: DetectedActionId,
    /// Name of the action.
    pub name: String,
    /// The expression for this action (disjunct of Next).
    pub expr: Spanned<Expr>,
}

/// Analyze the Next relation to detect top-level action disjuncts.
///
/// Looks for patterns like:
/// - `Action1 \/ Action2 \/ Action3`
/// - `\E p \in S : action(p)`
/// - Named operator references
///
/// Returns list of detected actions with their names and expressions.
pub fn detect_actions(next_def: &OperatorDef) -> Vec<DetectedAction> {
    let mut actions = Vec::new();
    let mut counter = 0;
    let ctx = ActionContext::default();
    detect_actions_rec(&next_def.body, &ctx, &mut actions, &mut counter);
    actions
}

#[derive(Debug, Clone, Default)]
struct ActionContext {
    guards: Vec<Spanned<Expr>>,
    wrappers: Vec<ActionWrapper>,
}

#[derive(Debug, Clone)]
enum ActionWrapper {
    Exists(Vec<BoundVar>),
    Let(Vec<OperatorDef>),
}

fn detect_actions_rec(
    expr: &Spanned<Expr>,
    ctx: &ActionContext,
    actions: &mut Vec<DetectedAction>,
    counter: &mut usize,
) {
    match &expr.node {
        // Disjunction: each branch is a separate action
        Expr::Or(a, b) => {
            detect_actions_rec(a, ctx, actions, counter);
            detect_actions_rec(b, ctx, actions, counter);
        }

        Expr::Exists(bounds, body) => {
            // Preserve the EXISTS context so each detected action remains well-scoped.
            let mut next_ctx = ctx.clone();
            next_ctx
                .wrappers
                .push(ActionWrapper::Exists(bounds.clone()));
            detect_actions_rec(body, &next_ctx, actions, counter);
        }

        // LET wrapper - transparent for splitting, but must be preserved for evaluation parity.
        Expr::Let(defs, body) => {
            let mut next_ctx = ctx.clone();
            next_ctx.wrappers.push(ActionWrapper::Let(defs.clone()));
            detect_actions_rec(body, &next_ctx, actions, counter);
        }

        // IF expression - each branch is a different action, guarded by the condition.
        Expr::If(cond, then_branch, else_branch) => {
            let cond_expr = (**cond).clone();

            // THEN branch: cond /\ action
            let mut then_ctx = ctx.clone();
            then_ctx.guards.push(cond_expr.clone());
            detect_actions_rec(then_branch, &then_ctx, actions, counter);

            // ELSE branch: ~cond /\ action
            let mut else_ctx = ctx.clone();
            let not_cond = Spanned::new(Expr::Not(Box::new(cond_expr.clone())), cond_expr.span);
            else_ctx.guards.push(not_cond);
            detect_actions_rec(else_branch, &else_ctx, actions, counter);
        }

        // Named operator reference - this is an action
        Expr::Ident(name, _) => {
            push_detected_action(actions, name.clone(), expr.clone(), ctx);
        }

        // Applied operator - use the operator name as action name
        Expr::Apply(op, _args) => {
            let name = extract_action_name_from_expr(&op.node).unwrap_or_else(|| {
                *counter += 1;
                format!("Action_{}", counter)
            });
            push_detected_action(actions, name, expr.clone(), ctx);
        }

        // Module-qualified reference
        Expr::ModuleRef(module, op, _args) => {
            push_detected_action(actions, format!("{}!{}", module, op), expr.clone(), ctx);
        }

        // Conjunction at top level - this is a single complex action
        Expr::And(_, _) => {
            // Try to extract a name from the conjunction
            let name = try_extract_name_from_conjunction(expr).unwrap_or_else(|| {
                *counter += 1;
                format!("Action_{}", counter)
            });
            push_detected_action(actions, name, expr.clone(), ctx);
        }

        // Any other expression is treated as a single action
        _ => {
            *counter += 1;
            push_detected_action(actions, format!("Action_{}", counter), expr.clone(), ctx);
        }
    }
}

fn push_detected_action(
    actions: &mut Vec<DetectedAction>,
    name: String,
    expr: Spanned<Expr>,
    ctx: &ActionContext,
) {
    let expr = apply_action_context(expr, ctx);
    actions.push(DetectedAction {
        id: DetectedActionId::new(expr.span),
        name,
        expr,
    });
}

fn apply_action_context(mut expr: Spanned<Expr>, ctx: &ActionContext) -> Spanned<Expr> {
    // Conjoin guards first (so they remain inside any EXISTS wrappers).
    for guard in &ctx.guards {
        let span = merged_span(guard.span, expr.span);
        expr = Spanned::new(Expr::And(Box::new(guard.clone()), Box::new(expr)), span);
    }

    // Wrap from inner to outer.
    for wrapper in ctx.wrappers.iter().rev() {
        let span = expr.span;
        expr = match wrapper {
            ActionWrapper::Exists(bounds) => {
                Spanned::new(Expr::Exists(bounds.clone(), Box::new(expr)), span)
            }
            ActionWrapper::Let(defs) => Spanned::new(Expr::Let(defs.clone(), Box::new(expr)), span),
        };
    }

    expr
}

fn merged_span(a: Span, b: Span) -> Span {
    if a.file == b.file {
        a.merge(b)
    } else {
        // Best-effort for synthesized expressions that combine multiple files/modules.
        Span::dummy()
    }
}

/// Extract action name from an expression (for Apply nodes)
fn extract_action_name_from_expr(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Ident(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// Try to extract a meaningful name from a conjunction (e.g., name from first conjunct)
fn try_extract_name_from_conjunction(expr: &Spanned<Expr>) -> Option<String> {
    match &expr.node {
        Expr::And(a, _b) => {
            // Try the left side first
            if let Some(name) = try_extract_name_from_conjunction(a) {
                return Some(name);
            }
            // Could try right side but usually left is the "name"
            None
        }
        Expr::Ident(name, _) => Some(name.clone()),
        Expr::Apply(op, _) => extract_action_name_from_expr(&op.node),
        _ => None,
    }
}
