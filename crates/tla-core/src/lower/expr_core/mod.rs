// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core expression lowering: dispatch hub, leaf expressions, operator params.

mod binary;
mod children;

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_except::lower_except_expr;
use super::expr_labels::lower_label_expr;
use super::expr_modules_subscripts::{
    lower_instance_expr, lower_module_ref_expr, lower_subscript_expr,
};
use super::expr_quantifiers::{lower_choose_expr, lower_quant_expr};
use super::expr_records_tuples::{
    lower_case_expr, lower_if_expr, lower_let_expr, lower_record_access_expr, lower_record_expr,
    lower_record_set_expr, lower_tuple_expr,
};
use super::expr_sets_funcs::{
    lower_func_apply_expr, lower_func_def_expr, lower_func_set_expr, lower_set_builder_expr,
    lower_set_enum_expr, lower_set_filter_expr,
};
use super::operators::{lower_apply_expr, lower_lambda_expr, lower_unary_expr};
use crate::ast::{Expr, OpParam};
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};
use num_bigint::BigInt;

// Re-exports for backward compatibility: callers use `super::expr_core::*`
pub(in crate::lower) use super::expr_operator_map::{
    make_apply_binary, operator_token_to_name, stdlib_keyword_to_name,
};
pub(in crate::lower) use binary::{lower_binary_expr, lower_binary_with_left};
pub(in crate::lower) use children::{
    lower_apply_args, lower_expr_from_children, lower_expr_from_children_after_keyword,
};

/// Convert a leaf token to an Expr. Shared by all leaf-matching sites.
pub(super) fn lower_token_to_expr(
    kind: SyntaxKind,
    text: &str,
    pending_underscore: bool,
) -> Option<Expr> {
    match kind {
        SyntaxKind::Ident => {
            if pending_underscore {
                Some(Expr::Ident(format!("_{text}"), NameId::INVALID))
            } else {
                Some(Expr::Ident(text.to_string(), NameId::INVALID))
            }
        }
        SyntaxKind::At => Some(Expr::Ident("@".to_string(), NameId::INVALID)),
        SyntaxKind::Number => text.parse::<BigInt>().ok().map(Expr::Int),
        SyntaxKind::String => Some(Expr::String(unescape_tla_string(text))),
        SyntaxKind::TrueKw => Some(Expr::Bool(true)),
        SyntaxKind::FalseKw => Some(Expr::Bool(false)),
        SyntaxKind::BooleanKw => Some(Expr::Ident("BOOLEAN".to_string(), NameId::INVALID)),
        _ => None,
    }
}

/// Lower an operator parameter
pub(in crate::lower) fn lower_operator_param(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<OpParam> {
    let mut name: Option<Spanned<String>> = None;
    let mut arity = 0;

    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            match token.kind() {
                SyntaxKind::Ident if name.is_none() => {
                    let span = ctx.token_span(&token);
                    name = Some(Spanned::new(token.text().to_string(), span));
                }
                SyntaxKind::Underscore => {
                    arity += 1;
                }
                _ => {}
            }
        }
    }

    Some(OpParam { name: name?, arity })
}

// =============================================================================
// Expression Lowering
// =============================================================================

/// Lower an expression node to AST Expr
pub(in crate::lower) fn lower_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    match node.kind() {
        // Literals - handled specially
        SyntaxKind::TrueKw => Some(Expr::Bool(true)),
        SyntaxKind::FalseKw => Some(Expr::Bool(false)),

        // Composite expressions
        SyntaxKind::ParenExpr => lower_paren_expr(ctx, node),
        SyntaxKind::BinaryExpr => lower_binary_expr(ctx, node),
        SyntaxKind::UnaryExpr => lower_unary_expr(ctx, node),
        SyntaxKind::ApplyExpr => lower_apply_expr(ctx, node),
        SyntaxKind::LambdaExpr => lower_lambda_expr(ctx, node),
        SyntaxKind::QuantExpr => lower_quant_expr(ctx, node),
        SyntaxKind::ChooseExpr => lower_choose_expr(ctx, node),
        SyntaxKind::SetEnumExpr => lower_set_enum_expr(ctx, node),
        SyntaxKind::SetBuilderExpr => lower_set_builder_expr(ctx, node),
        SyntaxKind::SetFilterExpr => lower_set_filter_expr(ctx, node),
        SyntaxKind::FuncDefExpr => lower_func_def_expr(ctx, node),
        SyntaxKind::FuncApplyExpr => lower_func_apply_expr(ctx, node),
        SyntaxKind::FuncSetExpr => lower_func_set_expr(ctx, node),
        SyntaxKind::ExceptExpr => lower_except_expr(ctx, node),
        SyntaxKind::RecordExpr => lower_record_expr(ctx, node),
        SyntaxKind::RecordAccessExpr => lower_record_access_expr(ctx, node),
        SyntaxKind::RecordSetExpr => lower_record_set_expr(ctx, node),
        SyntaxKind::TupleExpr => lower_tuple_expr(ctx, node),
        SyntaxKind::IfExpr => lower_if_expr(ctx, node),
        SyntaxKind::CaseExpr => lower_case_expr(ctx, node),
        SyntaxKind::LetExpr => lower_let_expr(ctx, node),
        SyntaxKind::LabelExpr => lower_label_expr(ctx, node),
        SyntaxKind::ModuleRefExpr => lower_module_ref_expr(ctx, node),
        SyntaxKind::SubscriptExpr => lower_subscript_expr(ctx, node),
        SyntaxKind::InstanceDecl => lower_instance_expr(ctx, node),
        SyntaxKind::OperatorRef => lower_operator_ref(node),

        // Try to handle token nodes (leaf nodes that are expressions)
        _ => lower_leaf_expr(ctx, node),
    }
}

/// Lower a leaf expression (identifier, number, string)
fn lower_leaf_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut pending_underscore = false;
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            let kind = token.kind();
            if kind == SyntaxKind::Underscore {
                pending_underscore = true;
                continue;
            }
            if let Some(expr) = lower_token_to_expr(kind, token.text(), pending_underscore) {
                return Some(expr);
            }
        }
    }

    // Try children nodes
    for child in node.children() {
        if let Some(expr) = lower_expr(ctx, &child) {
            return Some(expr);
        }
    }

    None
}

/// Lower an operator reference (bare operator as value: +, -, *, \cup, etc.)
fn lower_operator_ref(node: &SyntaxNode) -> Option<Expr> {
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if let Some(name) = operator_token_to_name(token.kind()) {
                return Some(Expr::OpRef(name.to_string()));
            }
        }
    }
    None
}

/// Lower parenthesized expression
fn lower_paren_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    for child in node.children() {
        if let Some(expr) = lower_expr(ctx, &child) {
            return Some(expr);
        }
    }
    lower_leaf_expr(ctx, node)
}
