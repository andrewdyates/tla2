// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Record, tuple, and control-flow expression lowering.

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_core::{
    lower_binary_with_left, lower_expr, lower_expr_from_children_after_keyword,
};
use super::module_items::lower_operator_def;
use crate::ast::{CaseArm, Expr};
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};
use num_bigint::BigInt;

use crate::name_intern::NameId;
/// Lower record expression [a |-> 1, b |-> 2]
pub(super) fn lower_record_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut fields = Vec::new();

    for child in node.children() {
        if child.kind() == SyntaxKind::RecordField {
            if let Some((name, value)) = lower_record_field(ctx, &child) {
                fields.push((name, value));
            }
        }
    }

    Some(Expr::Record(fields))
}

/// Lower record field
fn lower_record_field(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<(Spanned<String>, Spanned<Expr>)> {
    let mut name: Option<Spanned<String>> = None;
    let mut value: Option<Spanned<Expr>> = None;
    let mut saw_mapsto = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind == SyntaxKind::MapsTo || kind == SyntaxKind::Colon {
                    saw_mapsto = true;
                    continue;
                }
                if kind == SyntaxKind::Ident && name.is_none() && !saw_mapsto {
                    let span = ctx.token_span(&token);
                    name = Some(Spanned::new(token.text().to_string(), span));
                } else if saw_mapsto && value.is_none() {
                    // Value token
                    let expr = match kind {
                        SyntaxKind::Number => token.text().parse::<BigInt>().ok().map(Expr::Int),
                        SyntaxKind::Ident => {
                            Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                        }
                        SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                        SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                        SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                        // BOOLEAN is a keyword that represents the set {TRUE, FALSE}
                        // In record set context [field: BOOLEAN], it should be treated as identifier
                        SyntaxKind::BooleanKw => {
                            Some(Expr::Ident("BOOLEAN".to_string(), NameId::INVALID))
                        }
                        _ => None,
                    };
                    if let Some(e) = expr {
                        let span = ctx.token_span(&token);
                        value = Some(Spanned::new(e, span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if value.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        value = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    Some((name?, value?))
}

/// Lower record access r.field
pub(super) fn lower_record_access_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut record: Option<Spanned<Expr>> = None;
    let mut field: Option<Spanned<String>> = None;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::Ident {
                    let span = ctx.token_span(&token);
                    if record.is_none() {
                        record = Some(Spanned::new(
                            Expr::Ident(token.text().to_string(), NameId::INVALID),
                            span,
                        ));
                    } else {
                        field = Some(Spanned::new(token.text().to_string(), span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if record.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        record = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    Some(Expr::RecordAccess(Box::new(record?), field?.into()))
}

/// Lower record set [a : S, b : T]
pub(super) fn lower_record_set_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut fields = Vec::new();

    for child in node.children() {
        if child.kind() == SyntaxKind::RecordField {
            if let Some((name, value)) = lower_record_field(ctx, &child) {
                fields.push((name, value));
            }
        }
    }

    Some(Expr::RecordSet(fields))
}

/// Lower tuple expression <<a, b, c>>
pub(super) fn lower_tuple_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut elements = Vec::new();

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let expr = match token.kind() {
                    SyntaxKind::Number => token.text().parse::<BigInt>().ok().map(Expr::Int),
                    SyntaxKind::Ident => {
                        Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                    }
                    SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                    SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                    SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                    // BOOLEAN is a built-in set identifier
                    SyntaxKind::BooleanKw => {
                        Some(Expr::Ident("BOOLEAN".to_string(), NameId::INVALID))
                    }
                    _ => None,
                };
                if let Some(e) = expr {
                    let span = ctx.token_span(&token);
                    elements.push(Spanned::new(e, span));
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.span(&child_node);
                    elements.push(Spanned::new(expr, span));
                }
            }
        }
    }

    Some(Expr::Tuple(elements))
}

/// Lower IF-THEN-ELSE expression
pub(super) fn lower_if_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut cond: Option<Spanned<Expr>> = None;
    let mut then_: Option<Spanned<Expr>> = None;
    let mut else_: Option<Spanned<Expr>> = None;
    let mut state = 0; // 0=cond, 1=then, 2=else

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                // Handle keywords that set the IF/THEN/ELSE state
                if kind == SyntaxKind::IfKw {
                    state = 0;
                    continue;
                }
                if kind == SyntaxKind::ThenKw {
                    state = 1;
                    continue;
                }
                if kind == SyntaxKind::ElseKw {
                    state = 2;
                    continue;
                }
                // Try to make expression from token
                let expr = match kind {
                    SyntaxKind::Ident => {
                        Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                    }
                    SyntaxKind::At => Some(Expr::Ident("@".to_string(), NameId::INVALID)),
                    SyntaxKind::Number => token.text().parse::<BigInt>().ok().map(Expr::Int),
                    SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                    SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                    SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                    _ => None,
                };
                if let Some(e) = expr {
                    let span = ctx.token_span(&token);
                    match state {
                        0 => cond = Some(Spanned::new(e, span)),
                        1 => then_ = Some(Spanned::new(e, span)),
                        2 => else_ = Some(Spanned::new(e, span)),
                        _ => {}
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                // Handle BinaryExpr specially to combine with existing cond
                if child_node.kind() == SyntaxKind::BinaryExpr && state == 0 {
                    if let Some(left) = cond.take() {
                        if let Some(combined) = lower_binary_with_left(ctx, &child_node, left) {
                            cond = Some(combined);
                        }
                    } else if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        cond = Some(Spanned::new(expr, span));
                    }
                } else if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.span(&child_node);
                    match state {
                        0 => cond = Some(Spanned::new(expr, span)),
                        1 => then_ = Some(Spanned::new(expr, span)),
                        2 => else_ = Some(Spanned::new(expr, span)),
                        _ => {}
                    }
                }
            }
        }
    }

    Some(Expr::If(
        Box::new(cond?),
        Box::new(then_?),
        Box::new(else_?),
    ))
}

/// Lower CASE expression
pub(super) fn lower_case_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut arms = Vec::new();
    let mut default: Option<Spanned<Expr>> = None;

    let mut in_other = false;
    let mut saw_other_arrow = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::CaseArm {
                    if let Some(arm) = lower_case_arm(ctx, &child_node) {
                        arms.push(arm);
                    }
                    continue;
                }

                if in_other && saw_other_arrow && default.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        default = Some(Spanned::new(expr, span));
                    }
                }
            }
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind.is_trivia() {
                    continue;
                }

                if kind == SyntaxKind::OtherKw {
                    in_other = true;
                    saw_other_arrow = false;
                    continue;
                }
                if !in_other || default.is_some() {
                    continue;
                }
                if kind == SyntaxKind::Arrow {
                    saw_other_arrow = true;
                    continue;
                }
                if !saw_other_arrow {
                    continue;
                }

                let expr = match kind {
                    SyntaxKind::Ident => {
                        Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                    }
                    SyntaxKind::Number => token.text().parse::<BigInt>().ok().map(Expr::Int),
                    SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                    SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                    SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                    SyntaxKind::BooleanKw => {
                        Some(Expr::Ident("BOOLEAN".to_string(), NameId::INVALID))
                    }
                    _ => None,
                };

                if let Some(e) = expr {
                    let span = ctx.token_span(&token);
                    default = Some(Spanned::new(e, span));
                }
            }
        }
    }

    Some(Expr::Case(arms, default.map(Box::new)))
}

/// Lower case arm
fn lower_case_arm(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<CaseArm> {
    let mut guard: Option<Spanned<Expr>> = None;
    let mut body: Option<Spanned<Expr>> = None;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                // Skip Arrow and trivia
                if kind == SyntaxKind::Arrow || kind.is_trivia() {
                    continue;
                }
                // Handle leaf tokens as expressions
                let expr = match kind {
                    SyntaxKind::Ident => {
                        Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                    }
                    SyntaxKind::Number => token.text().parse::<BigInt>().ok().map(Expr::Int),
                    SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                    SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                    SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                    _ => None,
                };
                if let Some(e) = expr {
                    let span = ctx.token_span(&token);
                    if guard.is_none() {
                        guard = Some(Spanned::new(e, span));
                    } else if body.is_none() {
                        body = Some(Spanned::new(e, span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.span(&child_node);
                    if guard.is_none() {
                        guard = Some(Spanned::new(expr, span));
                    } else if body.is_none() {
                        body = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    Some(CaseArm {
        guard: guard?,
        body: body?,
    })
}

/// Lower LET-IN expression
///
/// Standard form: `LET Op == e IN body` lowers to `Let([Op], body)`.
/// Apalache extension: `LET Op == e` (no IN) lowers to `Let([Op], Op)` where
/// the implicit body is a reference to the last defined operator.
pub(super) fn lower_let_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut defs = Vec::new();

    for child in node.children() {
        if child.kind() == SyntaxKind::OperatorDef {
            if let Some(def) = lower_operator_def(ctx, &child) {
                defs.push(def);
            }
        }
    }

    // The parser doesn't always wrap the `IN <expr>` body in an expression node, so use the
    // token/node scanning helper to reliably lower the body expression.
    let body = lower_expr_from_children_after_keyword(ctx, node, SyntaxKind::InKw)
        .or_else(|| {
            // Apalache extension: LET without IN.
            // The implicit body is a reference to the last defined operator.
            if let Some(last_def) = defs.last() {
                let name = last_def.name.node.clone();
                let span = last_def.name.span;
                Some(Spanned::new(
                    Expr::Ident(name, NameId::INVALID),
                    span,
                ))
            } else {
                None
            }
        })?;

    Some(Expr::Let(defs, Box::new(body)))
}
