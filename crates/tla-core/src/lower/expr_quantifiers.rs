// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier and bound variable lowering: \A, \E, CHOOSE, bound variables.

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_core::lower_expr;
use crate::ast::{BoundPattern, BoundVar, Expr};
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};
use num_bigint::BigInt;

pub(super) fn lower_quant_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut is_forall = false;
    let mut bounds = Vec::new();
    let mut body: Option<Spanned<Expr>> = None;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind == SyntaxKind::ForallKw {
                    is_forall = true;
                    continue;
                }
                if kind == SyntaxKind::ExistsKw {
                    is_forall = false;
                    continue;
                }
                // Handle bare token bodies like TRUE, FALSE, identifiers
                if body.is_some() || bounds.is_empty() {
                    continue;
                }
                let expr = match kind {
                    SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                    SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                    SyntaxKind::Ident => {
                        Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                    }
                    SyntaxKind::Number => token.text().parse::<BigInt>().ok().map(Expr::Int),
                    SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                    _ => None,
                };
                if let Some(e) = expr {
                    let span = ctx.token_span(&token);
                    body = Some(Spanned::new(e, span));
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::BoundVar {
                    if let Some(bv) = lower_bound_var(ctx, &child_node) {
                        bounds.push(bv);
                    }
                } else if body.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        body = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    // In TLA+, syntax like `\A a, b \in S : P` means both a and b are in S.
    // The parser may produce bounds where only the last one has a domain.
    // Propagate the domain from the last bound with a domain to all earlier
    // bounds that don't have one.
    propagate_bound_domains(&mut bounds);

    let body = Box::new(body?);

    if is_forall {
        Some(Expr::Forall(bounds, body))
    } else {
        Some(Expr::Exists(bounds, body))
    }
}

/// Propagate domains in bound variable lists.
/// In TLA+, `\A a, b \in S` means both `a` and `b` are in S.
/// This function finds the domain from the last bound that has one
/// and propagates it to all earlier bounds without domains.
pub(super) fn propagate_bound_domains(bounds: &mut [BoundVar]) {
    // TLA+ shorthand like `a, b \in S, c \in T` means:
    // - a \in S
    // - b \in S
    // - c \in T
    //
    // The parser may only attach the domain to the last identifier in a comma-run.
    // Propagate domains backwards within each run, stopping at explicit domains.
    let mut last_domain: Option<Box<Spanned<Expr>>> = None;
    for bound in bounds.iter_mut().rev() {
        if bound.domain.is_some() {
            last_domain.clone_from(&bound.domain);
            continue;
        }
        if let Some(domain) = &last_domain {
            bound.domain = Some(domain.clone());
        }
    }
}

/// Lower bound variable
pub(super) fn lower_bound_var(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<BoundVar> {
    let mut name: Option<Spanned<String>> = None;
    let mut domain: Option<Box<Spanned<Expr>>> = None;
    let mut pattern: Option<BoundPattern> = None;
    let mut seen_in = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind == SyntaxKind::InOp {
                    seen_in = true;
                } else if kind == SyntaxKind::Ident {
                    if !seen_in && name.is_none() {
                        // This is the variable name
                        let span = ctx.token_span(&token);
                        name = Some(Spanned::new(token.text().to_string(), span));
                    } else if seen_in && domain.is_none() {
                        // This is a simple domain (identifier)
                        let span = ctx.token_span(&token);
                        domain = Some(Box::new(Spanned::new(
                            Expr::Ident(token.text().to_string(), NameId::INVALID),
                            span,
                        )));
                    }
                } else if seen_in && domain.is_none() {
                    // Handle other token types as domain
                    let expr = match kind {
                        SyntaxKind::Number => token.text().parse::<BigInt>().ok().map(Expr::Int),
                        SyntaxKind::String => Some(Expr::String(unescape_tla_string(token.text()))),
                        SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                        SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                        // BOOLEAN is a built-in set keyword
                        SyntaxKind::BooleanKw => {
                            Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                        }
                        _ => None,
                    };
                    if let Some(e) = expr {
                        let span = ctx.token_span(&token);
                        domain = Some(Box::new(Spanned::new(e, span)));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                let node_kind = child_node.kind();
                if !seen_in && node_kind == SyntaxKind::TuplePattern {
                    // Handle tuple pattern: <<x, y>>
                    let (pat, pat_name) = lower_tuple_pattern(ctx, &child_node);
                    pattern = Some(pat);
                    name = Some(pat_name);
                } else if seen_in && domain.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        domain = Some(Box::new(Spanned::new(expr, span)));
                    }
                }
            }
        }
    }

    Some(BoundVar {
        name: name?,
        domain,
        pattern,
    })
}

/// Lower tuple pattern <<x, y, ...>> and return the pattern and a synthetic name
fn lower_tuple_pattern(ctx: &mut LowerCtx, node: &SyntaxNode) -> (BoundPattern, Spanned<String>) {
    let mut vars = Vec::new();
    let span = ctx.span(node);

    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::Ident {
                let token_span = ctx.token_span(&token);
                vars.push(Spanned::new(token.text().to_string(), token_span));
            }
        }
    }

    // Create a synthetic name from the pattern variables
    let synthetic_name = format!(
        "<<{}>>",
        vars.iter()
            .map(|v| v.node.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    );

    (
        BoundPattern::Tuple(vars),
        Spanned::new(synthetic_name, span),
    )
}

/// Lower CHOOSE expression
pub(super) fn lower_choose_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut bound: Option<BoundVar> = None;
    let mut body: Option<Spanned<Expr>> = None;
    let mut after_colon = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind.is_trivia() {
                    continue;
                }
                if kind == SyntaxKind::Colon {
                    after_colon = true;
                    continue;
                }
                if !after_colon || body.is_some() {
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
                    body = Some(Spanned::new(e, span));
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::BoundVar {
                    bound = lower_bound_var(ctx, &child_node);
                } else if body.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        body = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    Some(Expr::Choose(bound?, Box::new(body?)))
}
