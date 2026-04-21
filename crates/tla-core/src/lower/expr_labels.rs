// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lowering for labeled subexpressions (`P0:: expr`).

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_core::lower_expr;
use crate::ast::{Expr, ExprLabel};
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

pub(super) fn lower_label_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut name: Option<Spanned<String>> = None;
    let mut body: Option<Spanned<Expr>> = None;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::Ident && name.is_none() {
                    let span = ctx.token_span(&token);
                    name = Some(Spanned::new(token.text().to_string(), span));
                } else if name.is_some() && body.is_none() {
                    // Part of #3125: When the label body is a bare token (e.g.,
                    // `RealInv:: Inv`), the CST contains the body as a token,
                    // not a child node. Lower leaf tokens to expressions here,
                    // matching the same token kinds handled by lower_expr.
                    let span = ctx.token_span(&token);
                    let expr = match token.kind() {
                        SyntaxKind::Ident => {
                            Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                        }
                        SyntaxKind::Number => token.text().parse().ok().map(Expr::Int),
                        SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                        SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                        SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                        SyntaxKind::BooleanKw => {
                            Some(Expr::Ident("BOOLEAN".to_string(), NameId::INVALID))
                        }
                        SyntaxKind::At => Some(Expr::Ident("@".to_string(), NameId::INVALID)),
                        _ => None,
                    };
                    if let Some(e) = expr {
                        body = Some(Spanned::new(e, span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if body.is_none() {
                    let expr = lower_expr(ctx, &child_node)?;
                    body = Some(Spanned::new(expr, ctx.span(&child_node)));
                }
            }
        }
    }

    Some(Expr::Label(ExprLabel {
        name: name?,
        body: Box::new(body?),
    }))
}
