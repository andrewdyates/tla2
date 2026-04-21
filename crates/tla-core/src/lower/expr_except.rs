// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EXCEPT expression lowering.

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_core::{lower_expr, lower_expr_from_children_after_keyword};
use crate::ast::{ExceptPathElement, ExceptSpec, Expr};
use crate::name_intern::NameId;
use crate::span::{Span, Spanned};
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

/// Lower EXCEPT expression
pub(super) fn lower_except_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut base: Option<Spanned<Expr>> = None;
    let mut specs = Vec::new();
    let mut pending_underscore = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if base.is_some() {
                    continue;
                }
                match token.kind() {
                    SyntaxKind::Underscore => {
                        pending_underscore = true;
                    }
                    SyntaxKind::Ident => {
                        let span = ctx.token_span(&token);
                        let name = if pending_underscore {
                            pending_underscore = false;
                            format!("_{}", token.text())
                        } else {
                            token.text().to_string()
                        };
                        base = Some(Spanned::new(Expr::Ident(name, NameId::INVALID), span));
                    }
                    // @ is used inside EXCEPT specs to refer to the old value
                    SyntaxKind::At => {
                        let span = ctx.token_span(&token);
                        base = Some(Spanned::new(
                            Expr::Ident("@".to_string(), NameId::INVALID),
                            span,
                        ));
                    }
                    _ => {}
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::ExceptSpec {
                    if let Some(spec) = lower_except_spec(ctx, &child_node) {
                        specs.push(spec);
                    }
                } else if base.is_none() {
                    // First expression node becomes the base
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        base = Some(Spanned::new(expr, span));
                    }
                } else {
                    // Base already set - apply postfix chain operations
                    apply_postfix_to_base(&mut base, ctx, &child_node);
                }
            }
        }
    }

    Some(Expr::Except(Box::new(base?), specs))
}

/// Apply a postfix operation (record access, function application, etc.) to an
/// existing base expression. Handles chained postfix ops in EXCEPT expressions
/// like `node[r].insts[1]`.
fn apply_postfix_to_base(
    base: &mut Option<Spanned<Expr>>,
    ctx: &mut LowerCtx,
    child_node: &SyntaxNode,
) {
    let span = ctx.span(child_node);
    match child_node.kind() {
        SyntaxKind::RecordAccessExpr => {
            if let Some(field) = extract_field_from_partial_record_access(ctx, child_node) {
                let current_base = base.take().expect("caller guarantees base is Some");
                *base = Some(Spanned::new(
                    Expr::RecordAccess(Box::new(current_base), field.into()),
                    span,
                ));
            }
        }
        SyntaxKind::FuncApplyExpr => {
            let args = extract_args_from_partial_func_apply(ctx, child_node);
            if let Some(current_base) = base.take() {
                let mut result = current_base;
                for arg in args {
                    result = Spanned::new(Expr::FuncApply(Box::new(result), Box::new(arg)), span);
                }
                *base = Some(result);
            }
        }
        _ => {
            if let Some(expr) = lower_expr(ctx, child_node) {
                *base = Some(Spanned::new(expr, span));
            }
        }
    }
}

/// Extract just the field name from a partial RecordAccessExpr (one without a base)
fn extract_field_from_partial_record_access(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<Spanned<String>> {
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::Ident {
                let span = ctx.token_span(&token);
                return Some(Spanned::new(token.text().to_string(), span));
            }
        }
    }
    None
}

/// Extract just the args from a partial FuncApplyExpr (one without a base)
fn extract_args_from_partial_func_apply(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Vec<Spanned<Expr>> {
    let mut args = Vec::new();

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let span = ctx.token_span(&token);
                let expr = match token.kind() {
                    SyntaxKind::Ident => {
                        Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                    }
                    SyntaxKind::Number => token
                        .text()
                        .parse::<num_bigint::BigInt>()
                        .ok()
                        .map(Expr::Int),
                    SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                    SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                    SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                    _ => None,
                };
                if let Some(e) = expr {
                    args.push(Spanned::new(e, span));
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.span(&child_node);
                    args.push(Spanned::new(expr, span));
                }
            }
        }
    }

    args
}

/// Lower EXCEPT spec
fn lower_except_spec(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<ExceptSpec> {
    let mut path = Vec::new();
    let mut in_path = true;
    let mut after_dot = false; // Track if we just saw a dot (next ident is a field)
    let mut in_bracket = false; // Track if we're inside a bracket group
    let mut bracket_indices: Vec<Spanned<Expr>> = Vec::new(); // Collect indices within a bracket
    let mut bracket_start_span: Option<Span> = None;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                match token.kind() {
                    SyntaxKind::LBracket if in_path => {
                        in_bracket = true;
                        bracket_indices.clear();
                        bracket_start_span = Some(ctx.token_span(&token));
                    }
                    SyntaxKind::RBracket if in_bracket => {
                        // Close the bracket - create index element(s)
                        if bracket_indices.len() == 1 {
                            // Single index
                            path.push(ExceptPathElement::Index(bracket_indices.remove(0)));
                        } else if bracket_indices.len() > 1 {
                            // Multiple indices - create a tuple for multi-arg functions
                            let exprs: Vec<Spanned<Expr>> = std::mem::take(&mut bracket_indices);
                            let start =
                                bracket_start_span.unwrap_or_else(|| ctx.token_span(&token));
                            let end = ctx.token_span(&token);
                            let combined_span = Span::new(start.file, start.start, end.end);
                            let tuple_expr = Expr::Tuple(exprs);
                            path.push(ExceptPathElement::Index(Spanned::new(
                                tuple_expr,
                                combined_span,
                            )));
                        }
                        in_bracket = false;
                        bracket_start_span = None;
                    }
                    SyntaxKind::Comma if in_bracket => {
                        // Just a separator, continue collecting
                    }
                    SyntaxKind::Dot => {
                        // Next ident is a field
                        after_dot = true;
                    }
                    SyntaxKind::Ident if in_path && after_dot => {
                        // After a dot, this is a field access
                        let span = ctx.token_span(&token);
                        let name = Spanned::new(token.text().to_string(), span);
                        path.push(ExceptPathElement::Field(name.into()));
                        after_dot = false;
                    }
                    SyntaxKind::Ident if in_path => {
                        // Not after a dot - this is a variable reference in an index position
                        // e.g., ![self] where self is a variable
                        let span = ctx.token_span(&token);
                        let expr = Expr::Ident(token.text().to_string(), NameId::INVALID);
                        if in_bracket {
                            bracket_indices.push(Spanned::new(expr, span));
                        } else {
                            path.push(ExceptPathElement::Index(Spanned::new(expr, span)));
                        }
                    }
                    SyntaxKind::EqOp | SyntaxKind::DefEqOp => {
                        // SANY accepts both = and == in EXCEPT specs
                        in_path = false;
                    }
                    // Handle literal number tokens (parser doesn't wrap them in nodes)
                    SyntaxKind::Number => {
                        let span = ctx.token_span(&token);
                        let n = token
                            .text()
                            .parse::<num_bigint::BigInt>()
                            .unwrap_or_default();
                        let expr = Expr::Int(n);
                        if in_path {
                            if in_bracket {
                                bracket_indices.push(Spanned::new(expr, span));
                            } else {
                                path.push(ExceptPathElement::Index(Spanned::new(expr, span)));
                            }
                        }
                    }
                    // Handle literal string tokens
                    SyntaxKind::String => {
                        let span = ctx.token_span(&token);
                        let expr = Expr::String(unescape_tla_string(token.text()));
                        if in_path {
                            if in_bracket {
                                bracket_indices.push(Spanned::new(expr, span));
                            } else {
                                path.push(ExceptPathElement::Index(Spanned::new(expr, span)));
                            }
                        }
                    }
                    // Handle boolean keywords
                    SyntaxKind::TrueKw => {
                        let span = ctx.token_span(&token);
                        let expr = Expr::Bool(true);
                        if in_path {
                            if in_bracket {
                                bracket_indices.push(Spanned::new(expr, span));
                            } else {
                                path.push(ExceptPathElement::Index(Spanned::new(expr, span)));
                            }
                        }
                    }
                    SyntaxKind::FalseKw => {
                        let span = ctx.token_span(&token);
                        let expr = Expr::Bool(false);
                        if in_path {
                            if in_bracket {
                                bracket_indices.push(Spanned::new(expr, span));
                            } else {
                                path.push(ExceptPathElement::Index(Spanned::new(expr, span)));
                            }
                        }
                    }
                    _ => {}
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if in_path {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        if in_bracket {
                            bracket_indices.push(Spanned::new(expr, span));
                        } else {
                            path.push(ExceptPathElement::Index(Spanned::new(expr, span)));
                        }
                    }
                }
            }
        }
    }

    // Lower the value expression as a full TLA+ expression after the '=' or '=='.
    // This is essential for specs that use `@` and infix operators (e.g., `@ \\cup {x}`).
    // SANY accepts both `=` and `==` in EXCEPT specs.
    let value = lower_expr_from_children_after_keyword(ctx, node, SyntaxKind::EqOp)
        .or_else(|| lower_expr_from_children_after_keyword(ctx, node, SyntaxKind::DefEqOp))?;

    Some(ExceptSpec { path, value })
}
