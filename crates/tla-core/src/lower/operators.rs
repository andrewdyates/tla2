// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Operator mapping tables, binary/unary expression construction, apply/lambda.

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_core::{lower_expr, make_apply_binary, operator_token_to_name};
use super::module_items::make_apply_expr;
use crate::ast::Expr;
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};
use num_bigint::BigInt;

pub(super) fn make_binary_expr(
    op: SyntaxKind,
    parenthesized: bool,
    left: Spanned<Expr>,
    right: Spanned<Expr>,
) -> Expr {
    let left = Box::new(left);
    let right = Box::new(right);

    // Handle parenthesized operators first - these map to different operators
    // In TLA+, (op) is a user-definable operator distinct from op:
    // - (+) is \oplus (circled plus), not + (arithmetic)
    // - (-) is \ominus (circled minus), not - (arithmetic)
    // - (*) is \otimes (circled times), not * (arithmetic)
    if parenthesized {
        let op_name = match op {
            SyntaxKind::PlusOp => "\\oplus",
            SyntaxKind::MinusOp => "\\ominus",
            SyntaxKind::StarOp => "\\otimes",
            SyntaxKind::SlashOp => "\\oslash",
            // Other operators keep their regular name (they don't have a distinct circled form)
            _ => return make_apply_from_op_kind(op, *left, *right),
        };
        return make_apply_binary(op_name, *left, *right);
    }

    match op {
        SyntaxKind::AndOp => Expr::And(left, right),
        SyntaxKind::OrOp => Expr::Or(left, right),
        SyntaxKind::ImpliesOp => Expr::Implies(left, right),
        SyntaxKind::EquivOp => Expr::Equiv(left, right),
        SyntaxKind::EqOp => Expr::Eq(left, right),
        SyntaxKind::NeqOp => Expr::Neq(left, right),
        SyntaxKind::LtOp => Expr::Lt(left, right),
        SyntaxKind::GtOp => Expr::Gt(left, right),
        SyntaxKind::LeqOp => Expr::Leq(left, right),
        SyntaxKind::GeqOp => Expr::Geq(left, right),
        SyntaxKind::InOp => Expr::In(left, right),
        SyntaxKind::NotInOp => Expr::NotIn(left, right),
        SyntaxKind::SubseteqOp => Expr::Subseteq(left, right),
        SyntaxKind::UnionOp => Expr::Union(left, right),
        SyntaxKind::IntersectOp => Expr::Intersect(left, right),
        SyntaxKind::SetMinusOp => Expr::SetMinus(left, right),
        SyntaxKind::PlusOp => Expr::Add(left, right),
        SyntaxKind::MinusOp => Expr::Sub(left, right),
        SyntaxKind::StarOp => Expr::Mul(left, right),
        SyntaxKind::SlashOp => Expr::Div(left, right),
        SyntaxKind::DivOp => Expr::IntDiv(left, right),
        SyntaxKind::PercentOp => Expr::Mod(left, right),
        SyntaxKind::CaretOp => Expr::Pow(left, right),
        SyntaxKind::DotDotOp => Expr::Range(left, right),
        SyntaxKind::LeadsToOp => Expr::LeadsTo(left, right),
        SyntaxKind::TimesOp => {
            // Flatten nested Times expressions so A \X B \X C produces Times([A, B, C])
            // rather than Times([Times([A, B]), C]), which ensures tuples are flat.
            match left.node {
                Expr::Times(mut factors) => {
                    factors.push(*right);
                    Expr::Times(factors)
                }
                _ => Expr::Times(vec![*left, *right]),
            }
        }
        SyntaxKind::ConcatOp => {
            // Sequence concatenation - model as Apply
            make_apply_binary("\\o", *left, *right)
        }
        // TLC module function operators
        SyntaxKind::ColonGt => {
            // d :> e creates single-element function [d |-> e]
            make_apply_binary(":>", *left, *right)
        }
        SyntaxKind::AtAt => {
            // f @@ g merges two functions (f takes priority)
            make_apply_binary("@@", *left, *right)
        }
        // Fairness operators
        SyntaxKind::WeakFairKw => Expr::WeakFair(left, right),
        SyntaxKind::StrongFairKw => Expr::StrongFair(left, right),
        _ => {
            // Unknown binary operator - wrap as application using its concrete token text when possible.
            match operator_token_to_name(op) {
                Some(op_name) => make_apply_binary(op_name, *left, *right),
                None => Expr::Apply(
                    Box::new(Spanned::dummy(Expr::Ident(
                        format!("{op:?}"),
                        NameId::INVALID,
                    ))),
                    vec![*left, *right],
                ),
            }
        }
    }
}

/// Make an Apply expression from an operator kind
fn make_apply_from_op_kind(op: SyntaxKind, left: Spanned<Expr>, right: Spanned<Expr>) -> Expr {
    match operator_token_to_name(op) {
        Some(op_name) => make_apply_binary(op_name, left, right),
        None => Expr::Apply(
            Box::new(Spanned::dummy(Expr::Ident(
                format!("{op:?}"),
                NameId::INVALID,
            ))),
            vec![left, right],
        ),
    }
}

/// Check if a syntax kind is a binary operator
pub(super) fn is_binary_op(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::AndOp
            | SyntaxKind::OrOp
            | SyntaxKind::ImpliesOp
            | SyntaxKind::EquivOp
            | SyntaxKind::ColonColonEqOp
            | SyntaxKind::ColonEqOp
            | SyntaxKind::EqOp
            | SyntaxKind::NeqOp
            | SyntaxKind::LtOp
            | SyntaxKind::GtOp
            | SyntaxKind::LeqOp
            | SyntaxKind::GeqOp
            // Ordering relations (user-definable)
            | SyntaxKind::PrecOp
            | SyntaxKind::PreceqOp
            | SyntaxKind::SuccOp
            | SyntaxKind::SucceqOp
            | SyntaxKind::LlOp
            | SyntaxKind::GgOp
            | SyntaxKind::SimOp
            | SyntaxKind::SimeqOp
            | SyntaxKind::AsympOp
            | SyntaxKind::ApproxOp
            | SyntaxKind::CongOp
            | SyntaxKind::DoteqOp
            | SyntaxKind::ProptoOp
            | SyntaxKind::InOp
            | SyntaxKind::NotInOp
            | SyntaxKind::SubseteqOp
            | SyntaxKind::SubsetOp
            | SyntaxKind::SupseteqOp
            | SyntaxKind::SupsetOp
            | SyntaxKind::UnionOp
            | SyntaxKind::IntersectOp
            | SyntaxKind::SetMinusOp
            // Bag subset operators (user-definable)
            | SyntaxKind::SqsubseteqOp
            | SyntaxKind::SqsupseteqOp
            | SyntaxKind::PlusOp
            | SyntaxKind::MinusOp
            // Multi-character user-definable operators
            | SyntaxKind::PlusPlusOp
            | SyntaxKind::MinusMinusOp
            | SyntaxKind::StarOp
            | SyntaxKind::SlashOp
            | SyntaxKind::DivOp
            | SyntaxKind::PercentOp
            | SyntaxKind::StarStarOp
            | SyntaxKind::SlashSlashOp
            | SyntaxKind::PercentPercentOp
            | SyntaxKind::CaretOp
            | SyntaxKind::CaretCaretOp
            // Circled operators (user-definable)
            | SyntaxKind::OplusOp
            | SyntaxKind::OminusOp
            | SyntaxKind::OtimesOp
            | SyntaxKind::OslashOp
            | SyntaxKind::OdotOp
            | SyntaxKind::UplusOp
            | SyntaxKind::SqcapOp
            | SyntaxKind::SqcupOp
            // Action composition
            | SyntaxKind::CdotOp
            | SyntaxKind::DotDotOp
            | SyntaxKind::LeadsToOp
            | SyntaxKind::TimesOp
            | SyntaxKind::ConcatOp
            // User-defined infix operator symbols
            | SyntaxKind::Pipe
            | SyntaxKind::Amp
            | SyntaxKind::AmpAmpOp
            | SyntaxKind::WeakFairKw
            | SyntaxKind::StrongFairKw
            | SyntaxKind::ColonGt
            | SyntaxKind::AtAt
            // Apalache type annotation
            | SyntaxKind::LtColonOp
    )
}

/// Lower unary expression
pub(super) fn lower_unary_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut op: Option<SyntaxKind> = None;
    let mut operand: Option<Spanned<Expr>> = None;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if is_unary_op(kind) {
                    op = Some(kind);
                } else {
                    // Handle leaf token as operand (for postfix ops like Prime)
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
                        operand = Some(Spanned::new(e, span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.span(&child_node);
                    operand = Some(Spanned::new(expr, span));
                }
            }
        }
    }

    let op = op?;
    let operand = operand?;

    Some(make_unary_expr(op, operand))
}

/// Make a unary expression from operator and operand
fn make_unary_expr(op: SyntaxKind, operand: Spanned<Expr>) -> Expr {
    let operand = Box::new(operand);

    match op {
        SyntaxKind::NotOp => Expr::Not(operand),
        SyntaxKind::MinusOp => Expr::Neg(operand),
        SyntaxKind::AlwaysOp => Expr::Always(operand),
        SyntaxKind::EventuallyOp => Expr::Eventually(operand),
        SyntaxKind::EnabledKw => Expr::Enabled(operand),
        SyntaxKind::UnchangedKw => Expr::Unchanged(operand),
        SyntaxKind::PowersetKw => Expr::Powerset(operand),
        SyntaxKind::BigUnionKw => Expr::BigUnion(operand),
        SyntaxKind::DomainKw => Expr::Domain(operand),
        SyntaxKind::PrimeOp => Expr::Prime(operand),
        _ => {
            // Unknown unary operator
            Expr::Apply(
                Box::new(Spanned::dummy(Expr::Ident(
                    format!("{op:?}"),
                    NameId::INVALID,
                ))),
                vec![*operand],
            )
        }
    }
}

/// Check if a syntax kind is a unary operator
pub(super) fn is_unary_op(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::NotOp
            | SyntaxKind::MinusOp
            | SyntaxKind::AlwaysOp
            | SyntaxKind::EventuallyOp
            | SyntaxKind::EnabledKw
            | SyntaxKind::UnchangedKw
            | SyntaxKind::PowersetKw
            | SyntaxKind::BigUnionKw
            | SyntaxKind::DomainKw
            | SyntaxKind::PrimeOp
    )
}

/// Lower operator application
pub(super) fn lower_apply_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut op: Option<Spanned<Expr>> = None;
    let mut args = Vec::new();

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                // Handle identifier tokens as operator names
                if kind == SyntaxKind::Ident && op.is_none() {
                    let span = ctx.token_span(&token);
                    op = Some(Spanned::new(
                        Expr::Ident(token.text().to_string(), NameId::INVALID),
                        span,
                    ));
                }
                // Handle stdlib keyword tokens (Len, Head, Tail, SelectSeq, etc.)
                else if op.is_none() {
                    let op_name = match kind {
                        SyntaxKind::LenKw => Some("Len"),
                        SyntaxKind::SeqKw => Some("Seq"),
                        SyntaxKind::SubSeqKw => Some("SubSeq"),
                        SyntaxKind::SelectSeqKw => Some("SelectSeq"),
                        SyntaxKind::HeadKw => Some("Head"),
                        SyntaxKind::TailKw => Some("Tail"),
                        SyntaxKind::AppendKw => Some("Append"),
                        _ => None,
                    };
                    if let Some(name) = op_name {
                        let span = ctx.token_span(&token);
                        op = Some(Spanned::new(
                            Expr::Ident(name.to_string(), NameId::INVALID),
                            span,
                        ));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::ArgList {
                    args = lower_arg_list(ctx, &child_node);
                } else if op.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        op = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    Some(make_apply_expr(op?, args))
}

/// Lower argument list
pub(super) fn lower_arg_list(ctx: &mut LowerCtx, node: &SyntaxNode) -> Vec<Spanned<Expr>> {
    let mut args = Vec::new();

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                // Handle leaf tokens as arguments
                let kind = token.kind();
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

/// Lower lambda expression
pub(super) fn lower_lambda_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut params = Vec::new();
    let mut body: Option<Spanned<Expr>> = None;
    let mut after_colon = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                match token.kind() {
                    SyntaxKind::Colon => {
                        after_colon = true;
                    }
                    SyntaxKind::Ident if !after_colon => {
                        let span = ctx.token_span(&token);
                        params.push(Spanned::new(token.text().to_string(), span));
                    }
                    // Lambda bodies can be a single leaf token (e.g., `LAMBDA x : 0`).
                    // In that case, the CST stores the body as a token rather than a child node.
                    _ if after_colon && body.is_none() => {
                        let expr = match token.kind() {
                            SyntaxKind::Ident => {
                                Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                            }
                            SyntaxKind::At => Some(Expr::Ident("@".to_string(), NameId::INVALID)),
                            SyntaxKind::Number => {
                                token.text().parse::<BigInt>().ok().map(Expr::Int)
                            }
                            SyntaxKind::String => {
                                Some(Expr::String(unescape_tla_string(token.text())))
                            }
                            SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                            SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                            SyntaxKind::BooleanKw => {
                                Some(Expr::Ident("BOOLEAN".to_string(), NameId::INVALID))
                            }
                            _ => None,
                        };
                        if let Some(e) = expr {
                            let span = ctx.token_span(&token);
                            body = Some(Spanned::new(e, span));
                        }
                    }
                    _ => {}
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if body.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        body = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    Some(Expr::Lambda(params, Box::new(body?)))
}
