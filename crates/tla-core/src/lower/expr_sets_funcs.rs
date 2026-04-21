// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set and function expression lowering.

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_core::lower_expr;
use super::expr_quantifiers::lower_bound_var;
use crate::ast::{BoundVar, Expr};
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};
use num_bigint::BigInt;

/// Lower set enumeration
pub(super) fn lower_set_enum_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
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

    Some(Expr::SetEnum(elements))
}

/// Lower set builder expression {expr : x \in S}
/// Handles multi-variable patterns like {<<x, y>> : x, y \in S} where x and y share domain S
pub(super) fn lower_set_builder_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut body: Option<Spanned<Expr>> = None;
    let mut bounds = Vec::new();

    // Iterate over both nodes AND tokens to find the body expression.
    // The body may be a token (e.g., Ident "x" in "{ x : x \in S }") or a node
    // (e.g., a BinaryExpr in "{ x + y : x \in S, y \in T }").
    for child in node.children_with_tokens() {
        match child {
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
            rowan::NodeOrToken::Token(token) => {
                // Handle token-only body expressions (Ident, Number, String, TRUE, FALSE)
                if body.is_none() {
                    let kind = token.kind();
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
                        body = Some(Spanned::new(e, span));
                    }
                }
            }
        }
    }

    // Propagate domains from variables that have them to preceding variables that don't.
    // This handles patterns like "x, y \in S" where both x and y share domain S.
    if !bounds.is_empty() {
        let mut last_domain: Option<Box<Spanned<Expr>>> = None;

        // Iterate backwards to find domain and propagate to preceding variables
        for i in (0..bounds.len()).rev() {
            if bounds[i].domain.is_some() {
                last_domain.clone_from(&bounds[i].domain);
            } else if let Some(ref d) = last_domain {
                bounds[i].domain = Some(d.clone());
            }
        }
    }

    Some(Expr::SetBuilder(Box::new(body?), bounds))
}

/// Lower set filter expression {x \in S : P}
pub(super) fn lower_set_filter_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut bound: Option<BoundVar> = None;
    let mut predicate: Option<Spanned<Expr>> = None;
    let mut past_colon = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                // Track when we pass the colon to know the predicate starts
                if kind == SyntaxKind::Colon {
                    past_colon = true;
                } else if past_colon && predicate.is_none() {
                    // Handle bare token predicates (TRUE, FALSE, identifier, number, string)
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
                        predicate = Some(Spanned::new(e, span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::BoundVar {
                    bound = lower_bound_var(ctx, &child_node);
                } else if predicate.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        predicate = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    Some(Expr::SetFilter(bound?, Box::new(predicate?)))
}

/// Lower function definition [x \in S |-> e]
pub(super) fn lower_func_def_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut bounds = Vec::new();
    let mut body: Option<Spanned<Expr>> = None;
    let mut saw_maps_to = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind == SyntaxKind::MapsTo {
                    saw_maps_to = true;
                } else if saw_maps_to && body.is_none() {
                    // Handle simple token bodies (String, Number, Ident, Bool)
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
                        body = Some(Spanned::new(e, span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::BoundVar {
                    if let Some(bv) = lower_bound_var(ctx, &child_node) {
                        bounds.push(bv);
                    }
                } else if saw_maps_to && body.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        body = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    // Propagate domains from variables that have them to preceding variables that don't.
    // This handles patterns like "x, y \in S" where both x and y share domain S.
    if !bounds.is_empty() {
        let mut last_domain: Option<Box<Spanned<Expr>>> = None;
        for i in (0..bounds.len()).rev() {
            if bounds[i].domain.is_some() {
                last_domain.clone_from(&bounds[i].domain);
            } else if let Some(ref d) = last_domain {
                bounds[i].domain = Some(d.clone());
            }
        }
    }

    Some(Expr::FuncDef(bounds, Box::new(body?)))
}

/// Lower function application f[x]
pub(super) fn lower_func_apply_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut func: Option<Spanned<Expr>> = None;
    let mut args: Vec<Spanned<Expr>> = Vec::new();

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                let span = ctx.token_span(&token);

                // First, try to set func from Ident or @ (for EXCEPT expressions)
                if kind == SyntaxKind::Ident && func.is_none() {
                    func = Some(Spanned::new(
                        Expr::Ident(token.text().to_string(), NameId::INVALID),
                        span,
                    ));
                } else if kind == SyntaxKind::At && func.is_none() {
                    // @ is used inside EXCEPT specs to refer to the old value
                    func = Some(Spanned::new(
                        Expr::Ident("@".to_string(), NameId::INVALID),
                        span,
                    ));
                } else if func.is_some() {
                    // After func is set, handle literal tokens for args
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
                        args.push(Spanned::new(e, span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.span(&child_node);
                    if func.is_none() {
                        func = Some(Spanned::new(expr, span));
                    } else {
                        args.push(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    let func = func?;
    let arg = match args.len() {
        0 => return None,
        1 => args.pop().expect("len checked == 1"),
        _ => Spanned::new(Expr::Tuple(args), ctx.span(node)),
    };
    Some(Expr::FuncApply(Box::new(func), Box::new(arg)))
}

/// Lower function set [S -> T]
pub(super) fn lower_func_set_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut domain: Option<Spanned<Expr>> = None;
    let mut range: Option<Spanned<Expr>> = None;
    let mut saw_arrow = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind == SyntaxKind::Arrow {
                    saw_arrow = true;
                } else if kind == SyntaxKind::Ident || kind == SyntaxKind::BooleanKw {
                    // Handle Ident and BOOLEAN keyword tokens as domain or range
                    let span = ctx.token_span(&token);
                    let expr = if kind == SyntaxKind::BooleanKw {
                        Expr::Ident("BOOLEAN".to_string(), NameId::INVALID)
                    } else {
                        Expr::Ident(token.text().to_string(), NameId::INVALID)
                    };
                    if !saw_arrow && domain.is_none() {
                        domain = Some(Spanned::new(expr, span));
                    } else if saw_arrow && range.is_none() {
                        range = Some(Spanned::new(expr, span));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if let Some(expr) = lower_expr(ctx, &child_node) {
                    let span = ctx.span(&child_node);
                    if !saw_arrow && domain.is_none() {
                        domain = Some(Spanned::new(expr, span));
                    } else if saw_arrow && range.is_none() {
                        range = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    Some(Expr::FuncSet(Box::new(domain?), Box::new(range?)))
}
