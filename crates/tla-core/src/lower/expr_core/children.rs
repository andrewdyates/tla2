// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Children-based expression lowering: handles fragmented CST expressions
//! like `Ident("a"), BinaryExpr("+", Ident("b"))`.

use super::binary::lower_binary_with_left;
use super::lower_expr;
use super::lower_token_to_expr;
use crate::ast::Expr;
use crate::lower::ctx::LowerCtx;
use crate::lower::expr_operator_map::stdlib_keyword_to_name;
use crate::lower::module_items::make_apply_expr;
use crate::lower::operators::{is_binary_op, lower_arg_list};
use crate::name_intern::NameId;
use crate::span::{Span, Spanned};
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

/// Lower expression from a sequence of children.
pub(in crate::lower) enum ExprStart {
    AfterDefEq,
    AfterKeyword(SyntaxKind),
}

pub(in crate::lower) fn lower_expr_from_children_start(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
    start: ExprStart,
) -> Option<Spanned<Expr>> {
    let mut result: Option<Spanned<Expr>> = None;
    let mut in_expr = false;
    let mut pending_stdlib_op: Option<(String, Span)> = None;
    let mut pending_underscore = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();

                if !in_expr {
                    match start {
                        ExprStart::AfterDefEq => {
                            if kind == SyntaxKind::DefEqOp || kind == SyntaxKind::TriangleEqOp {
                                in_expr = true;
                            }
                        }
                        ExprStart::AfterKeyword(start_kind) => {
                            if kind == start_kind {
                                in_expr = true;
                            }
                        }
                    }
                    continue;
                }

                if kind.is_trivia() || is_binary_op(kind) {
                    continue;
                }

                if kind == SyntaxKind::Underscore {
                    pending_underscore = true;
                    continue;
                }

                if let Some(op_name) = stdlib_keyword_to_name(kind) {
                    let span = ctx.token_span(&token);
                    pending_stdlib_op = Some((op_name, span));
                    pending_underscore = false;
                    continue;
                }

                if let Some(e) = lower_token_to_expr(kind, token.text(), pending_underscore) {
                    pending_underscore = false;
                    let span = ctx.token_span(&token);
                    result = Some(Spanned::new(e, span));
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if !in_expr {
                    continue;
                }

                if child_node.kind() == SyntaxKind::Proof {
                    break;
                }

                if child_node.kind() == SyntaxKind::BinaryExpr {
                    if let Some(left) = result.take() {
                        if let Some(combined) = lower_binary_with_left(ctx, &child_node, left) {
                            result = Some(combined);
                        }
                    } else if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.preserved_expr_span(&child_node);
                        result = Some(Spanned::new(expr, span));
                    }
                } else if child_node.kind() == SyntaxKind::ApplyExpr {
                    if let Some((op_name, op_span)) = pending_stdlib_op.take() {
                        let args = lower_apply_args(ctx, &child_node);
                        let op_expr = Spanned::new(Expr::Ident(op_name, NameId::INVALID), op_span);
                        let span = ctx.preserved_expr_span(&child_node);
                        result = Some(Spanned::new(Expr::Apply(Box::new(op_expr), args), span));
                    } else if let Some(prev) = result.take() {
                        let args = lower_apply_args(ctx, &child_node);
                        let span = ctx.preserved_expr_span(&child_node);
                        result = Some(Spanned::new(make_apply_expr(prev, args), span));
                    } else if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.preserved_expr_span(&child_node);
                        result = Some(Spanned::new(expr, span));
                    }
                } else if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.preserved_expr_span(&child_node);
                    result = Some(Spanned::new(expr, span));
                }
            }
        }
    }

    result
}

pub(in crate::lower) fn lower_expr_from_children(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<Spanned<Expr>> {
    lower_expr_from_children_start(ctx, node, ExprStart::AfterDefEq)
}

pub(in crate::lower) fn lower_expr_from_children_after_keyword(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
    keyword: SyntaxKind,
) -> Option<Spanned<Expr>> {
    lower_expr_from_children_start(ctx, node, ExprStart::AfterKeyword(keyword))
}

/// Lower args from ApplyExpr node (extracts from ArgList child)
pub(in crate::lower) fn lower_apply_args(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Vec<Spanned<Expr>> {
    for child in node.children() {
        if child.kind() == SyntaxKind::ArgList {
            return lower_arg_list(ctx, &child);
        }
    }
    Vec::new()
}
