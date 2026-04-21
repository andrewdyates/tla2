// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ASSUME and THEOREM statement lowering.

use super::super::assume_prove::lower_assume_prove_stmt_expr;
use super::super::ctx::LowerCtx;
use super::super::expr_core::{lower_expr_from_children, lower_expr_from_children_after_keyword};
use super::super::proof::lower_proof;
use crate::ast::{AssumeDecl, Proof, TheoremDecl};
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

/// Lower ASSUME statement
pub(in crate::lower) fn lower_assume(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<AssumeDecl> {
    let mut name: Option<Spanned<String>> = None;

    // Check if there's a name (Ident before ==)
    // Similar to lower_theorem name extraction
    let tokens: Vec<_> = node.children_with_tokens().collect();
    let mut i = 0;
    while i < tokens.len() {
        if let rowan::NodeOrToken::Token(token) = &tokens[i] {
            if token.kind() == SyntaxKind::Ident {
                // Check if next non-trivia is ==
                let mut j = i + 1;
                while j < tokens.len() {
                    if let rowan::NodeOrToken::Token(next) = &tokens[j] {
                        if !next.kind().is_trivia() {
                            if next.kind() == SyntaxKind::DefEqOp {
                                let span = ctx.token_span(token);
                                name = Some(Spanned::new(token.text().to_string(), span));
                            }
                            break;
                        }
                    }
                    j += 1;
                }
            }
        }
        i += 1;
    }

    let expr = lower_expr_from_children(ctx, node)
        .or_else(|| lower_expr_from_children_after_keyword(ctx, node, SyntaxKind::AssumeKw))?;

    Some(AssumeDecl { name, expr })
}

/// Lower THEOREM statement
pub(in crate::lower) fn lower_theorem(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<TheoremDecl> {
    let mut name: Option<Spanned<String>> = None;
    let mut proof: Option<Spanned<Proof>> = None;

    // Check if there's a name (Ident before ==)
    let tokens: Vec<_> = node.children_with_tokens().collect();
    let mut i = 0;
    while i < tokens.len() {
        if let rowan::NodeOrToken::Token(token) = &tokens[i] {
            if token.kind() == SyntaxKind::Ident {
                // Check if next non-trivia is ==
                let mut j = i + 1;
                while j < tokens.len() {
                    if let rowan::NodeOrToken::Token(next) = &tokens[j] {
                        if !next.kind().is_trivia() {
                            if next.kind() == SyntaxKind::DefEqOp {
                                let span = ctx.token_span(token);
                                name = Some(Spanned::new(token.text().to_string(), span));
                            }
                            break;
                        }
                    }
                    j += 1;
                }
            }
        }
        i += 1;
    }

    for child in node.children() {
        if child.kind() == SyntaxKind::Proof {
            proof = lower_proof(ctx, &child).map(|p| {
                let span = ctx.span(&child);
                Spanned::new(p, span)
            });
        }
    }

    let theorem_kw = node.children_with_tokens().find_map(|child| match child {
        rowan::NodeOrToken::Token(token) => match token.kind() {
            SyntaxKind::TheoremKw
            | SyntaxKind::LemmaKw
            | SyntaxKind::PropositionKw
            | SyntaxKind::CorollaryKw => Some(token.kind()),
            _ => None,
        },
        rowan::NodeOrToken::Node(_) => None,
    });

    let body = lower_assume_prove_stmt_expr(ctx, node).or_else(|| {
        lower_expr_from_children(ctx, node).or_else(|| {
            theorem_kw.and_then(|kw| lower_expr_from_children_after_keyword(ctx, node, kw))
        })
    });

    Some(TheoremDecl {
        name,
        body: body?,
        proof,
    })
}
