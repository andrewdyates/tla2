// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ASSUME/PROVE statement lowering.

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_core::lower_expr;
use crate::ast::{BoundVar, Expr};
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode, SyntaxToken};
use num_bigint::BigInt;

pub(super) fn lower_assume_prove_stmt_expr(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<Spanned<Expr>> {
    // TLAPS-style theorem/proof statements can be written as:
    //   ASSUME NEW x \\in S, P(x) PROVE Q
    //
    // The parser keeps this permissive and does not build a dedicated syntax node. Here we lower
    // it to:
    //   \\A x \\in S : (P(x) => Q)
    //
    // Multiple assumptions are conjoined in the antecedent.

    fn is_leaf_expr_token(kind: SyntaxKind) -> bool {
        matches!(
            kind,
            SyntaxKind::Ident
                | SyntaxKind::Number
                | SyntaxKind::String
                | SyntaxKind::TrueKw
                | SyntaxKind::FalseKw
                | SyntaxKind::At
        )
    }

    fn lower_leaf_expr_token(ctx: &LowerCtx, token: &SyntaxToken) -> Option<Spanned<Expr>> {
        let span = ctx.token_span(token);
        let expr = match token.kind() {
            SyntaxKind::Ident => Expr::Ident(token.text().to_string(), NameId::INVALID),
            SyntaxKind::At => Expr::Ident("@".to_string(), NameId::INVALID),
            SyntaxKind::Number => token.text().parse::<BigInt>().ok().map(Expr::Int)?,
            SyntaxKind::String => Expr::String(unescape_tla_string(token.text())),
            SyntaxKind::TrueKw => Expr::Bool(true),
            SyntaxKind::FalseKw => Expr::Bool(false),
            _ => return None,
        };
        Some(Spanned::new(expr, span))
    }

    let items: Vec<_> = node.children_with_tokens().collect();

    // Find an ASSUME at this level.
    let mut idx = items.iter().position(|it| match it {
        rowan::NodeOrToken::Token(t) => t.kind() == SyntaxKind::AssumeKw,
        rowan::NodeOrToken::Node(_) => false,
    })?;
    idx += 1; // after ASSUME

    // Quick check: if we never see PROVE, bail (avoid changing non-ASSUME/PROVE shapes).
    if !items.iter().any(|it| match it {
        rowan::NodeOrToken::Token(t) => t.kind() == SyntaxKind::Ident && t.text() == "PROVE",
        rowan::NodeOrToken::Node(_) => false,
    }) {
        return None;
    }

    #[derive(Debug)]
    struct PendingNew {
        name: Option<Spanned<String>>,
        expecting_domain: bool,
        paren_depth: usize,
    }

    enum Phase {
        Assumptions,
        Goal,
    }

    let mut pending_new: Option<PendingNew> = None;
    let mut bounds: Vec<BoundVar> = Vec::new();
    let mut assumptions: Vec<Spanned<Expr>> = Vec::new();
    let mut goal: Option<Spanned<Expr>> = None;
    let mut phase = Phase::Assumptions;

    let flush_pending_new = |bounds: &mut Vec<BoundVar>, pending: &mut Option<PendingNew>| {
        if let Some(p) = pending.take() {
            if let Some(name) = p.name {
                bounds.push(BoundVar {
                    name,
                    domain: None,
                    pattern: None,
                });
            }
        }
    };

    while idx < items.len() {
        match &items[idx] {
            rowan::NodeOrToken::Token(t) => match t.kind() {
                SyntaxKind::NewKw => {
                    flush_pending_new(&mut bounds, &mut pending_new);
                    pending_new = Some(PendingNew {
                        name: None,
                        expecting_domain: false,
                        paren_depth: 0,
                    });
                }
                SyntaxKind::Ident if t.text() == "PROVE" => {
                    flush_pending_new(&mut bounds, &mut pending_new);
                    phase = Phase::Goal;
                }
                SyntaxKind::Ident => {
                    if let Some(p) = pending_new.as_mut() {
                        if p.name.is_none() {
                            let span = ctx.token_span(t);
                            p.name = Some(Spanned::new(t.text().to_string(), span));
                            idx += 1;
                            continue;
                        }
                        if p.expecting_domain {
                            let Some(name) = p.name.take() else {
                                idx += 1;
                                continue;
                            };
                            p.expecting_domain = false;
                            pending_new = None;
                            let domain = lower_leaf_expr_token(ctx, t)?;
                            bounds.push(BoundVar {
                                name,
                                domain: Some(Box::new(domain)),
                                pattern: None,
                            });
                            idx += 1;
                            continue;
                        }
                    }

                    if pending_new.is_none() {
                        if let Some(expr) = lower_leaf_expr_token(ctx, t) {
                            match phase {
                                Phase::Assumptions => assumptions.push(expr),
                                Phase::Goal => {
                                    if goal.is_none() {
                                        goal = Some(expr);
                                    }
                                }
                            }
                        }
                    }
                }
                kind if is_leaf_expr_token(kind) => {
                    if let Some(p) = pending_new.as_mut() {
                        if p.expecting_domain {
                            let Some(name) = p.name.take() else {
                                idx += 1;
                                continue;
                            };
                            p.expecting_domain = false;
                            pending_new = None;
                            let domain = lower_leaf_expr_token(ctx, t)?;
                            bounds.push(BoundVar {
                                name,
                                domain: Some(Box::new(domain)),
                                pattern: None,
                            });
                            idx += 1;
                            continue;
                        }
                    }

                    if pending_new.is_none() {
                        if let Some(expr) = lower_leaf_expr_token(ctx, t) {
                            match phase {
                                Phase::Assumptions => assumptions.push(expr),
                                Phase::Goal => {
                                    if goal.is_none() {
                                        goal = Some(expr);
                                    }
                                }
                            }
                        }
                    }
                }
                SyntaxKind::LParen => {
                    if let Some(p) = pending_new.as_mut() {
                        p.paren_depth += 1;
                    }
                }
                SyntaxKind::RParen => {
                    if let Some(p) = pending_new.as_mut() {
                        p.paren_depth = p.paren_depth.saturating_sub(1);
                    }
                }
                SyntaxKind::InOp => {
                    if let Some(p) = pending_new.as_mut() {
                        if p.name.is_some() && p.paren_depth == 0 {
                            p.expecting_domain = true;
                        }
                    }
                }
                SyntaxKind::Comma => {
                    if let Some(p) = pending_new.as_mut() {
                        if p.name.is_some() && !p.expecting_domain {
                            flush_pending_new(&mut bounds, &mut pending_new);
                        }
                    }
                }
                _ => {}
            },
            rowan::NodeOrToken::Node(n) => {
                if n.kind() == SyntaxKind::Proof || n.kind() == SyntaxKind::StepLabel {
                    idx += 1;
                    continue;
                }

                let Some(expr) = lower_expr(ctx, n) else {
                    idx += 1;
                    continue;
                };
                let expr = Spanned::new(expr, ctx.tight_span(n));

                if let Some(p) = pending_new.as_mut() {
                    if p.expecting_domain {
                        let Some(name) = p.name.take() else {
                            idx += 1;
                            continue;
                        };
                        p.expecting_domain = false;
                        pending_new = None;
                        bounds.push(BoundVar {
                            name,
                            domain: Some(Box::new(expr)),
                            pattern: None,
                        });
                        idx += 1;
                        continue;
                    }
                }

                match phase {
                    Phase::Assumptions => assumptions.push(expr),
                    Phase::Goal => {
                        if goal.is_none() {
                            goal = Some(expr);
                        }
                    }
                }
            }
        }
        idx += 1;
    }

    flush_pending_new(&mut bounds, &mut pending_new);

    let span = ctx.tight_span(node);
    let goal = goal.unwrap_or_else(|| Spanned::new(Expr::Bool(true), span));

    let mut antecedent: Option<Spanned<Expr>> = None;
    for a in assumptions {
        antecedent = Some(match antecedent {
            None => a,
            Some(prev) => {
                let span = prev.span.merge(a.span);
                Spanned::new(Expr::And(Box::new(prev), Box::new(a)), span)
            }
        });
    }

    let mut lowered = match antecedent {
        None => goal,
        Some(ant) => {
            let span = ant.span.merge(goal.span);
            Spanned::new(Expr::Implies(Box::new(ant), Box::new(goal)), span)
        }
    };

    if !bounds.is_empty() {
        let span = span.merge(lowered.span);
        lowered = Spanned::new(Expr::Forall(bounds, Box::new(lowered)), span);
    }

    Some(lowered)
}
