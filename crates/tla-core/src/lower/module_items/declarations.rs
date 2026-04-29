// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Declaration and instance lowering: VARIABLE, CONSTANT, RECURSIVE, INSTANCE, substitution.

use super::super::collect_idents;
use super::super::ctx::LowerCtx;
use super::super::expr_core::lower_expr_from_children_after_keyword;
use super::is_preceded_by_local_kw;
use crate::ast::{ConstantDecl, InstanceDecl, RecursiveDecl, Substitution, Unit};
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

/// Lower VARIABLE declaration
pub(in crate::lower) fn lower_variable_decl(ctx: &mut LowerCtx, node: &SyntaxNode) -> Unit {
    let names = collect_idents(ctx, node);
    Unit::Variable(names)
}

/// Lower CONSTANT declaration
pub(in crate::lower) fn lower_constant_decl(ctx: &mut LowerCtx, node: &SyntaxNode) -> Unit {
    let mut decls = Vec::new();

    let tokens: Vec<_> = node
        .children_with_tokens()
        .filter_map(|child| match child {
            rowan::NodeOrToken::Token(token) => Some(token),
            rowan::NodeOrToken::Node(_) => None,
        })
        .collect();

    let mut i = 0;
    while i < tokens.len() {
        let token = &tokens[i];

        if token.kind() != SyntaxKind::Ident {
            i += 1;
            continue;
        }

        let span = ctx.token_span(token);
        let name = Spanned::new(token.text().to_string(), span);

        // CONSTANTS can have arity: C(_, _)
        let mut arity = None;
        let mut j = i + 1;

        while j < tokens.len() && tokens[j].kind().is_trivia() {
            j += 1;
        }

        if j < tokens.len() && tokens[j].kind() == SyntaxKind::LParen {
            j += 1;
            let mut count = 0usize;
            while j < tokens.len() {
                match tokens[j].kind() {
                    SyntaxKind::Underscore => {
                        count += 1;
                    }
                    SyntaxKind::RParen => {
                        j += 1;
                        break;
                    }
                    _ => {}
                }
                j += 1;
            }
            arity = Some(count);
            i = j;
        } else {
            i += 1;
        }

        decls.push(ConstantDecl { name, arity });
    }

    Unit::Constant(decls)
}

/// Lower RECURSIVE declaration: RECURSIVE Op(_, _)
pub(in crate::lower) fn lower_recursive_decl(ctx: &mut LowerCtx, node: &SyntaxNode) -> Unit {
    let mut decls = Vec::new();

    let tokens: Vec<_> = node
        .children_with_tokens()
        .filter_map(|child| match child {
            rowan::NodeOrToken::Token(token) => Some(token),
            rowan::NodeOrToken::Node(_) => None,
        })
        .collect();

    let mut i = 0;
    while i < tokens.len() {
        let token = &tokens[i];

        if token.kind() != SyntaxKind::Ident {
            i += 1;
            continue;
        }

        let span = ctx.token_span(token);
        let name = Spanned::new(token.text().to_string(), span);

        // Parse arity: Op(_, _)
        let mut arity = 0usize;
        let mut j = i + 1;

        while j < tokens.len() && tokens[j].kind().is_trivia() {
            j += 1;
        }

        if j < tokens.len() && tokens[j].kind() == SyntaxKind::LParen {
            j += 1;
            while j < tokens.len() {
                match tokens[j].kind() {
                    SyntaxKind::Underscore => {
                        arity += 1;
                    }
                    SyntaxKind::RParen => {
                        j += 1;
                        break;
                    }
                    _ => {}
                }
                j += 1;
            }
            i = j;
        } else {
            i += 1;
        }

        decls.push(RecursiveDecl { name, arity });
    }

    Unit::Recursive(decls)
}

/// Lower INSTANCE declaration
pub(in crate::lower) fn lower_instance_decl(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<InstanceDecl> {
    let mut module: Option<Spanned<String>> = None;
    let mut substitutions = Vec::new();
    let local = is_preceded_by_local_kw(node);

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::Ident && module.is_none() {
                    let span = ctx.token_span(&token);
                    module = Some(Spanned::new(token.text().to_string(), span));
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if child_node.kind() == SyntaxKind::Substitution {
                    if let Some(sub) = lower_substitution(ctx, &child_node) {
                        substitutions.push(sub);
                    }
                }
            }
        }
    }

    Some(InstanceDecl {
        module: module?,
        substitutions,
        local,
    })
}

/// Lower a substitution (x <- e)
pub(in crate::lower) fn lower_substitution(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> Option<Substitution> {
    let mut from: Option<Spanned<String>> = None;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::Ident && from.is_none() {
                    let span = ctx.token_span(&token);
                    from = Some(Spanned::new(token.text().to_string(), span));
                }
            }
            rowan::NodeOrToken::Node(_) => {}
        }
    }

    let to = lower_expr_from_children_after_keyword(ctx, node, SyntaxKind::LArrow)?;

    Some(Substitution { from: from?, to })
}
