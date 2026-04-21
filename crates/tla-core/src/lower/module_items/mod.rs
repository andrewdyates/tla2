// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Module structure lowering: modules, extends, declarations, operators, instances.

mod declarations;
mod operators;
mod statements;

pub(super) use declarations::lower_substitution;
pub(super) use operators::{lower_operator_def, make_apply_expr};

use super::ctx::LowerCtx;
use crate::ast::{Module, Unit};
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

/// Lower a CST root to AST Module (first MODULE node)
pub(super) fn lower_module(ctx: &mut LowerCtx, root: &SyntaxNode) -> Option<Module> {
    // Find the Module node in the Root
    let module_node = root.children().find(|n| n.kind() == SyntaxKind::Module)?;

    lower_module_node(ctx, &module_node)
}

/// Lower the "main" module from a multi-module file.
///
/// For multi-module files (`---- MODULE A ---- ... ==== ---- MODULE B ---- ... ====`),
/// the last top-level module is the "main" entry point. Earlier modules are dependencies
/// available for EXTENDS/INSTANCE resolution.
///
/// If `hint_name` is provided (e.g. from the filename), prefers the module whose name
/// matches; otherwise falls back to the last module.
pub(super) fn lower_main_module(
    ctx: &mut LowerCtx,
    root: &SyntaxNode,
    hint_name: Option<&str>,
) -> Option<Module> {
    let module_nodes: Vec<_> = root
        .children()
        .filter(|n| n.kind() == SyntaxKind::Module)
        .collect();

    if module_nodes.is_empty() {
        return None;
    }

    // Single module: no ambiguity.
    if module_nodes.len() == 1 {
        return lower_module_node(ctx, &module_nodes[0]);
    }

    // If a filename hint is given, try to match a module by name.
    if let Some(hint) = hint_name {
        for node in &module_nodes {
            if let Some(name) = extract_module_name_from_node(node) {
                if name == hint {
                    return lower_module_node(ctx, node);
                }
            }
        }
    }

    // Default: last module is the main entry point.
    lower_module_node(ctx, module_nodes.last()?)
}

/// Extract the module name string from a Module syntax node (without lowering).
fn extract_module_name_from_node(node: &SyntaxNode) -> Option<String> {
    let mut saw_module_kw = false;
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::ModuleKw {
                saw_module_kw = true;
            } else if saw_module_kw && token.kind() == SyntaxKind::Ident {
                return Some(token.text().to_string());
            }
        }
    }
    None
}

/// Lower a Module node
pub(super) fn lower_module_node(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Module> {
    let span = ctx.span(node);

    // Find the module name (Ident token after MODULE keyword)
    let name = find_module_name(ctx, node)?;

    // Find EXTENDS clause
    let extends = node
        .children()
        .find(|n| n.kind() == SyntaxKind::ExtendsClause)
        .map(|n| lower_extends(ctx, &n))
        .unwrap_or_default();

    // Collect all units
    let mut units = Vec::new();
    for child in node.children() {
        if let Some(unit) = lower_unit(ctx, &child) {
            let unit_span = ctx.span(&child);
            units.push(Spanned::new(unit, unit_span));
        }
    }

    Some(Module {
        name,
        extends,
        units,
        action_subscript_spans: ctx.take_action_subscript_spans(),
        span,
    })
}

/// Find the module name from the Module node
fn find_module_name(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Spanned<String>> {
    let mut saw_module_kw = false;
    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::ModuleKw {
                    saw_module_kw = true;
                } else if saw_module_kw && token.kind() == SyntaxKind::Ident {
                    let span = ctx.token_span(&token);
                    return Some(Spanned::new(token.text().to_string(), span));
                }
            }
            rowan::NodeOrToken::Node(_) => {}
        }
    }
    None
}

/// Lower EXTENDS clause
fn lower_extends(ctx: &mut LowerCtx, node: &SyntaxNode) -> Vec<Spanned<String>> {
    let mut names = Vec::new();
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::Ident {
                let span = ctx.token_span(&token);
                names.push(Spanned::new(token.text().to_string(), span));
            }
        }
    }
    names
}

/// Detect whether a node is preceded by the LOCAL keyword
pub(in crate::lower) fn is_preceded_by_local_kw(node: &SyntaxNode) -> bool {
    let mut prev = node.prev_sibling_or_token();

    while let Some(el) = prev {
        match el {
            rowan::NodeOrToken::Token(token) => {
                if token.kind().is_trivia() {
                    prev = token.prev_sibling_or_token();
                    continue;
                }
                return token.kind() == SyntaxKind::LocalKw;
            }
            rowan::NodeOrToken::Node(_) => return false,
        }
    }

    false
}

/// Lower a unit (top-level declaration or definition)
fn lower_unit(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Unit> {
    match node.kind() {
        SyntaxKind::VariableDecl => Some(declarations::lower_variable_decl(ctx, node)),
        SyntaxKind::ConstantDecl => Some(declarations::lower_constant_decl(ctx, node)),
        SyntaxKind::RecursiveDecl => Some(declarations::lower_recursive_decl(ctx, node)),
        SyntaxKind::OperatorDef => operators::lower_operator_def(ctx, node).map(Unit::Operator),
        SyntaxKind::InstanceDecl => {
            declarations::lower_instance_decl(ctx, node).map(Unit::Instance)
        }
        SyntaxKind::AssumeStmt => statements::lower_assume(ctx, node).map(Unit::Assume),
        SyntaxKind::TheoremStmt => statements::lower_theorem(ctx, node).map(Unit::Theorem),
        SyntaxKind::Separator => Some(Unit::Separator),
        _ => None,
    }
}
