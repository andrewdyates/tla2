// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Binary expression lowering: `lower_binary_expr` and `lower_binary_with_left`.

use super::children::lower_apply_args;
use super::lower_expr;
use super::lower_token_to_expr;
use crate::ast::Expr;
use crate::lower::ctx::LowerCtx;
use crate::lower::expr_operator_map::stdlib_keyword_to_name;
use crate::lower::module_items::make_apply_expr;
use crate::lower::operators::{is_binary_op, make_binary_expr};
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

/// Lower a BinaryExpr node given its left operand (which is a sibling in the CST)
pub(in crate::lower) fn lower_binary_with_left(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
    left: Spanned<Expr>,
) -> Option<Spanned<Expr>> {
    let mut op: Option<SyntaxKind> = None;
    let mut right: Option<Spanned<Expr>> = None;
    // Track pending identifier that might be followed by ApplyExpr
    let mut pending_ident: Option<Spanned<Expr>> = None;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if is_binary_op(kind) && op.is_none() {
                    // Don't flush pending_ident to right - it's part of the left operand
                    // which was already passed as a parameter
                    pending_ident = None;
                    op = Some(kind);
                // Handle stdlib keyword tokens (Len, Head, etc.) which precede ApplyExpr
                // Only process these AFTER we've seen the operator
                } else if op.is_some() {
                    if let Some(op_name) = stdlib_keyword_to_name(kind) {
                        // Flush any existing pending ident first
                        if let Some(ident) = pending_ident.take() {
                            right = Some(ident);
                        }
                        let span = ctx.token_span(&token);
                        pending_ident =
                            Some(Spanned::new(Expr::Ident(op_name, NameId::INVALID), span));
                    } else if right.is_none() {
                        if let Some(e) = lower_token_to_expr(kind, token.text(), false) {
                            let span = ctx.token_span(&token);
                            // For identifiers, keep pending in case ApplyExpr follows
                            if matches!(e, Expr::Ident(_, NameId::INVALID)) {
                                pending_ident = Some(Spanned::new(e, span));
                            } else {
                                right = Some(Spanned::new(e, span));
                            }
                        }
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                // Only process nodes for the RHS after we've seen the operator
                if op.is_none() {
                    continue;
                }

                // Check for ApplyExpr following an identifier
                if child_node.kind() == SyntaxKind::ApplyExpr {
                    if let Some(ident) = pending_ident.take() {
                        // Combine identifier with ApplyExpr args (handles WF_/SF_ identifiers)
                        let args = lower_apply_args(ctx, &child_node);
                        let span = ctx.tight_span(&child_node);
                        right = Some(Spanned::new(make_apply_expr(ident, args), span));
                        continue;
                    }
                }

                // Flush pending_ident if we're seeing a non-ApplyExpr node
                if let Some(ident) = pending_ident.take() {
                    right = Some(ident);
                }

                // Check for nested BinaryExpr
                if child_node.kind() == SyntaxKind::BinaryExpr {
                    if let Some(r) = right.take() {
                        // We have left and op, combine with right, then process nested
                        if let Some(op_kind) = op {
                            let combined = make_binary_expr(op_kind, false, left.clone(), r);
                            let span = ctx.tight_span(node);
                            let new_left = Spanned::new(combined, span);
                            return lower_binary_with_left(ctx, &child_node, new_left);
                        }
                    } else if let Some(r) = lower_expr(ctx, &child_node) {
                        let span = ctx.preserved_expr_span(&child_node);
                        right = Some(Spanned::new(r, span));
                    }
                } else if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.preserved_expr_span(&child_node);
                    if right.is_none() {
                        right = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    // Flush any pending identifier
    if let Some(ident) = pending_ident.take() {
        right = Some(ident);
    }

    // Combine left, op, right
    let op = op?;
    let right = right?;
    let combined = make_binary_expr(op, false, left, right);
    let span = ctx.span(node);
    Some(Spanned::new(combined, span))
}

/// Lower binary expression
pub(in crate::lower) fn lower_binary_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut exprs = Vec::new();
    let mut op: Option<SyntaxKind> = None;
    // Track pending identifier that might be followed by ApplyExpr
    let mut pending_ident: Option<Spanned<Expr>> = None;
    // Track underscore-prefixed identifiers like `_msgs`
    let mut pending_underscore = false;
    // Track parenthesized operators like (+), (-), etc.
    // In TLA+, (op) is a user-definable operator distinct from op.
    let mut saw_lparen = false;
    let mut op_is_parenthesized = false;
    // Track whether we've seen an operand (node) yet.
    // Operators BEFORE any operand are "bullets" (leading markers in bullet lists).
    let mut saw_operand = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind == SyntaxKind::LParen {
                    saw_lparen = true;
                    continue;
                }
                if kind == SyntaxKind::RParen {
                    continue;
                }
                if kind == SyntaxKind::Underscore {
                    if let Some(ident) = pending_ident.take() {
                        exprs.push(ident);
                        saw_operand = true;
                    }
                    pending_underscore = true;
                    saw_lparen = false;
                    continue;
                }
                if is_binary_op(kind) {
                    if let Some(ident) = pending_ident.take() {
                        exprs.push(ident);
                        saw_operand = true;
                    }
                    pending_underscore = false;
                    let is_prefix_binary =
                        matches!(kind, SyntaxKind::WeakFairKw | SyntaxKind::StrongFairKw);
                    if op.is_none() && (saw_operand || is_prefix_binary) {
                        op_is_parenthesized = saw_lparen;
                        op = Some(kind);
                    }
                    saw_lparen = false;
                } else if let Some(op_name) = stdlib_keyword_to_name(kind) {
                    if let Some(ident) = pending_ident.take() {
                        exprs.push(ident);
                    }
                    let span = ctx.token_span(&token);
                    pending_ident = Some(Spanned::new(Expr::Ident(op_name, NameId::INVALID), span));
                    pending_underscore = false;
                } else if let Some(expr) =
                    lower_token_to_expr(kind, token.text(), pending_underscore)
                {
                    if let Some(ident) = pending_ident.take() {
                        exprs.push(ident);
                    }
                    pending_underscore = false;
                    let span = ctx.token_span(&token);

                    // For identifiers, keep pending in case ApplyExpr follows
                    if matches!(expr, Expr::Ident(_, NameId::INVALID)) {
                        pending_ident = Some(Spanned::new(expr, span));
                    } else {
                        exprs.push(Spanned::new(expr, span));
                        saw_operand = true;
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::ApplyExpr {
                    if let Some(ident) = pending_ident.take() {
                        let args = lower_apply_args(ctx, &child_node);
                        let span = ctx.span(&child_node);
                        exprs.push(Spanned::new(make_apply_expr(ident, args), span));
                        saw_operand = true;
                        continue;
                    }
                }

                if let Some(ident) = pending_ident.take() {
                    exprs.push(ident);
                    saw_operand = true;
                }

                if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.span(&child_node);
                    exprs.push(Spanned::new(expr, span));
                    saw_operand = true;
                }
            }
        }
    }

    // Flush any remaining pending identifier
    if let Some(ident) = pending_ident.take() {
        exprs.push(ident);
    }

    if exprs.len() < 2 || op.is_none() {
        return exprs.into_iter().next().map(|s| s.node);
    }

    let op = op?;
    let left = exprs.remove(0);
    let right = exprs.remove(0);

    Some(make_binary_expr(op, op_is_parenthesized, left, right))
}
