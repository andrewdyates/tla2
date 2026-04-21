// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Operator definition and apply expression lowering.

use super::super::ctx::LowerCtx;
use super::super::expr_core::{
    lower_expr_from_children, lower_operator_param, operator_token_to_name, stdlib_keyword_to_name,
};
use super::super::expr_quantifiers::{lower_bound_var, propagate_bound_domains};
use super::is_preceded_by_local_kw;
use crate::ast::{BoundVar, Expr, OpParam, OperatorDef};
use crate::name_intern::NameId;
use crate::span::{Span, Spanned};
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

/// Create an Apply expression, handling WF_xxx/SF_xxx identifiers.
///
/// Due to lexer "maximal munch" behavior, `WF_cvars(CRcvMsg)` is tokenized as
/// `Ident("WF_cvars")` + `ArgList` rather than `WeakFair` + `Ident("cvars")` + `ArgList`.
/// This function detects WF_/SF_ prefixed identifiers and converts them to the
/// proper WeakFair/StrongFair expression.
pub(in crate::lower) fn make_apply_expr(op: Spanned<Expr>, mut args: Vec<Spanned<Expr>>) -> Expr {
    if let Expr::Ident(name, NameId::INVALID) = &op.node {
        // WF_vars(Action) => WeakFair(vars, Action)
        if let Some(vars_name) = name.strip_prefix("WF_") {
            if args.len() == 1 {
                let vars_expr =
                    Spanned::new(Expr::Ident(vars_name.to_string(), NameId::INVALID), op.span);
                return Expr::WeakFair(Box::new(vars_expr), Box::new(args.remove(0)));
            }
        }
        // SF_vars(Action) => StrongFair(vars, Action)
        else if let Some(vars_name) = name.strip_prefix("SF_") {
            if args.len() == 1 {
                let vars_expr =
                    Spanned::new(Expr::Ident(vars_name.to_string(), NameId::INVALID), op.span);
                return Expr::StrongFair(Box::new(vars_expr), Box::new(args.remove(0)));
            }
        }
    }
    Expr::Apply(Box::new(op), args)
}

/// Lower operator definition
pub(in crate::lower) fn lower_operator_def(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<OperatorDef> {
    let mut name: Option<Spanned<String>> = None;
    let mut params = Vec::new();
    let mut func_bounds: Vec<BoundVar> = Vec::new(); // Bound vars for function operators
    let local = is_preceded_by_local_kw(node);
    let mut header_tokens: Vec<(SyntaxKind, String, Span)> = Vec::new();

    // Collect header tokens (before ==) and parse any ArgList params.
    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                let kind = token.kind();
                if kind == SyntaxKind::DefEqOp || kind == SyntaxKind::TriangleEqOp {
                    break;
                }
                if kind.is_trivia() {
                    continue;
                }
                header_tokens.push((kind, token.text().to_string(), ctx.token_span(&token)));
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::ArgList {
                    // Check if ArgList contains BoundVars (function operator syntax: f[x \in S])
                    let (regular_params, bounds) = lower_op_def_arg_list(ctx, &child_node);
                    params = regular_params;
                    func_bounds = bounds;
                }
            }
        }
    }

    // Detect infix operator definitions:
    // - a \prec b == ...
    // - a (+) b == ...
    // We lower these as operator name = infix symbol, params = [a, b].
    if params.is_empty() && func_bounds.is_empty() {
        // Find left operand identifier.
        let mut idx = 0;
        while idx < header_tokens.len() && header_tokens[idx].0 != SyntaxKind::Ident {
            idx += 1;
        }

        if idx + 2 < header_tokens.len() {
            let (_lk, left_text, left_span) = &header_tokens[idx];
            idx += 1;

            let mut parenthesized = false;
            if idx < header_tokens.len() && header_tokens[idx].0 == SyntaxKind::LParen {
                parenthesized = true;
                idx += 1;
            }

            if idx < header_tokens.len() {
                let (op_kind, _op_text, op_span) = &header_tokens[idx];
                let op_name = operator_token_to_name(*op_kind);
                idx += 1;

                if parenthesized {
                    if idx < header_tokens.len() && header_tokens[idx].0 == SyntaxKind::RParen {
                        idx += 1;
                    } else {
                        // Not a valid parenthesized infix operator form.
                        idx = header_tokens.len();
                    }
                }

                if let Some(op_name) = op_name {
                    if idx < header_tokens.len() && header_tokens[idx].0 == SyntaxKind::Ident {
                        let (_rk, right_text, right_span) = &header_tokens[idx];
                        name = Some(Spanned::new(op_name.to_string(), *op_span));
                        params = vec![
                            OpParam {
                                name: Spanned::new(left_text.clone(), *left_span),
                                arity: 0,
                            },
                            OpParam {
                                name: Spanned::new(right_text.clone(), *right_span),
                                arity: 0,
                            },
                        ];
                    }
                }
            }
        }
    }

    // Fallback: standard operator definition name.
    if name.is_none() {
        // Underscore-prefixed operator name: _name
        if header_tokens.len() >= 2
            && header_tokens[0].0 == SyntaxKind::Underscore
            && header_tokens[1].0 == SyntaxKind::Ident
        {
            let span = header_tokens[0].2;
            name = Some(Spanned::new(format!("_{}", header_tokens[1].1), span));
        } else if let Some((kind, text, span)) = header_tokens.first() {
            if *kind == SyntaxKind::Ident {
                name = Some(Spanned::new(text.clone(), *span));
            } else if let Some(std_name) = stdlib_keyword_to_name(*kind) {
                name = Some(Spanned::new(std_name, *span));
            } else if let Some(op_name) = operator_token_to_name(*kind) {
                name = Some(Spanned::new(op_name.to_string(), *span));
            }
        }
    }

    // Second pass: collect the body expression parts after ==
    let mut body = lower_expr_from_children(ctx, node)?;

    // If there are bound variables from function operator syntax,
    // wrap the body in a FuncDef expression: f[x \in S] == body becomes f == [x \in S |-> body]
    if !func_bounds.is_empty() {
        let body_span = body.span;
        body = Spanned::new(Expr::FuncDef(func_bounds, Box::new(body)), body_span);
    }

    Some(OperatorDef {
        name: name?,
        params,
        body,
        local,
        contains_prime: false, // Computed later by compute_contains_prime
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false, // Computed later by compute_is_recursive
        self_call_count: 0,  // Computed later by compute_is_recursive
    })
}

/// Lower an ArgList in operator definition, returning both regular params and any bound variables (for function operators)
fn lower_op_def_arg_list(ctx: &mut LowerCtx, node: &SyntaxNode) -> (Vec<OpParam>, Vec<BoundVar>) {
    let mut params = Vec::new();
    let mut bounds = Vec::new();

    for child in node.children() {
        if child.kind() == SyntaxKind::OperatorParam {
            if let Some(param) = lower_operator_param(ctx, &child) {
                params.push(param);
            }
        } else if child.kind() == SyntaxKind::BoundVar {
            if let Some(bv) = lower_bound_var(ctx, &child) {
                bounds.push(bv);
            }
        }
    }

    // Also check for direct Ident tokens (simple params like f(a, b))
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::Ident {
                let span = ctx.token_span(&token);
                params.push(OpParam {
                    name: Spanned::new(token.text().to_string(), span),
                    arity: 0,
                });
            }
        }
    }

    // Propagate domains in bound variable lists.
    // In TLA+, `f[a, b \in S]` means both `a` and `b` are in S.
    propagate_bound_domains(&mut bounds);

    (params, bounds)
}
