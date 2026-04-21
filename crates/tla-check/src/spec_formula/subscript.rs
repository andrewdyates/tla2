// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Action and subscript CST parsing for spec formula extraction.
//!
//! Handles `[Action]_vars` and `<<Action>>_vars` patterns from TLA+ subscript expressions.

use super::cst_helpers::{extract_ident, node_text_trimmed};
use super::types::ActionExtraction;
use tla_core::{SyntaxElement, SyntaxKind, SyntaxNode};

/// Extract [][Next]_vars pattern from an Always expression
pub(super) fn extract_always_subscript(node: &SyntaxNode) -> Option<ActionExtraction> {
    // Check for UnaryExpr with AlwaysOp
    if node.kind() != SyntaxKind::UnaryExpr {
        return None;
    }

    let has_always = node
        .children_with_tokens()
        .any(|c| matches!(c, SyntaxElement::Token(t) if t.kind() == SyntaxKind::AlwaysOp));

    if !has_always {
        return None;
    }

    // Find SubscriptExpr inside
    for child in node.children() {
        if child.kind() == SyntaxKind::SubscriptExpr {
            return extract_subscript(&child);
        }
    }

    None
}

/// Extract [Action]_vars or <<Action>>_vars from a SubscriptExpr
pub(super) fn extract_subscript(node: &SyntaxNode) -> Option<ActionExtraction> {
    if node.kind() != SyntaxKind::SubscriptExpr {
        return None;
    }

    let mut action_name: Option<String> = None;
    let mut action_node: Option<SyntaxNode> = None;
    let mut vars: Option<String> = None;
    let mut saw_underscore_token = false;
    // Default to stuttering allowed (most common). Will be set to false if TupleExpr detected.
    let mut stuttering_allowed = true;

    fn strip_leading_underscore(text: &str) -> &str {
        text.strip_prefix('_').unwrap_or(text)
    }

    for child in node.children_with_tokens() {
        match child {
            SyntaxElement::Token(t) => {
                if t.kind() == SyntaxKind::Underscore {
                    saw_underscore_token = true;
                } else if t.kind() == SyntaxKind::Ident && action_name.is_some() && vars.is_none() {
                    // Vars can appear as a bare Ident token (older parse tree) or as an Ident
                    // tokenized with a leading `_` (new lexer behavior).
                    let text = t.text();
                    if saw_underscore_token || text.starts_with('_') {
                        vars = Some(strip_leading_underscore(text).to_string());
                    }
                }
            }
            SyntaxElement::Node(n) => {
                if action_name.is_none() {
                    // Action part: [Action] or <<Action>>.
                    // Detect whether it's FuncSetExpr (brackets, stuttering OK) or TupleExpr (angles, stuttering forbidden)
                    // [A]_v uses FuncSetExpr (square brackets) - stuttering allowed
                    // <<A>>_v uses TupleExpr (angle brackets) - stuttering forbidden
                    if n.kind() == SyntaxKind::TupleExpr {
                        stuttering_allowed = false;
                    }
                    let (name, node) = extract_action(&n);
                    action_name = name;
                    action_node = node;
                } else if vars.is_none() {
                    // Vars part can be a node (tuple, paren expr, module ref, etc). In the `_vars`
                    // case, the lexer may produce a node whose text starts with `_`, so strip it.
                    let text = n.text().to_string();
                    let trimmed = text.trim();
                    vars = Some(strip_leading_underscore(trimmed).to_string());
                }
            }
        }
    }

    Some(ActionExtraction {
        name: action_name?,
        node: action_node,
        vars: vars?,
        stuttering_allowed,
    })
}

/// Extract action identity from a CST node.
///
/// Unified replacement for the previous `extract_action_with_node` + `extract_action_name`
/// pair (design doc R1). Returns (name, optional_node) where node is present for inline
/// expressions that require lowering.
///
/// For simple actions like `[Next]_vars`, returns (Some("Next"), None).
/// For complex actions like `[\E n \in Node: Next(n)]_vars`, returns the full expression
/// text and the syntax node for lowering.
pub(super) fn extract_action(node: &SyntaxNode) -> (Option<String>, Option<SyntaxNode>) {
    // Check if this node contains a complex expression (QuantExpr, BinaryExpr, etc.)
    // that should be treated as an inline action expression requiring lowering.
    if let Some((text, expr_node)) = find_complex_action_node(node) {
        return (Some(text), Some(expr_node));
    }

    // Fallback: extract simple identifier (design doc R3: delegates to cst_helpers::extract_ident)
    (extract_ident(node), None)
}

/// Check if a syntax kind represents a complex expression that requires inline lowering.
///
/// Returns true for expression types that cannot be resolved by simple name lookup
/// and instead need the full CST node for lowering into an AST expression.
fn is_complex_action_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::QuantExpr     // \E n \in Node: Next(n)
            | SyntaxKind::BinaryExpr  // Next \/ UNCHANGED vars (#1278)
            | SyntaxKind::LetExpr     // LET ... IN expr
            | SyntaxKind::ApplyExpr   // Step(1) — function application with args
            | SyntaxKind::UnaryExpr // UNCHANGED vars
    )
}

/// Check if the node contains a complex action expression and return its text and node.
///
/// Handles QuantExpr, BinaryExpr (disjunction), and other non-trivial actions
/// inside bracket expressions like `[...]` or `<<...>>`.
fn find_complex_action_node(node: &SyntaxNode) -> Option<(String, SyntaxNode)> {
    // Check if this node itself is a complex expression
    if is_complex_action_kind(node.kind()) {
        return Some((node_text_trimmed(node), node.clone()));
    }

    // For FuncSetExpr (the `[...]` wrapper) or TupleExpr (the `<<...>>` wrapper),
    // check if its direct child is a complex expression.
    // Also unwrap ParenExpr: `[(expr)]_v` has FuncSetExpr → ParenExpr → BinaryExpr.
    if node.kind() == SyntaxKind::FuncSetExpr || node.kind() == SyntaxKind::TupleExpr {
        for child in node.children() {
            if is_complex_action_kind(child.kind()) {
                return Some((node_text_trimmed(&child), child));
            }
            if child.kind() == SyntaxKind::ParenExpr {
                for inner in child.children() {
                    if is_complex_action_kind(inner.kind()) {
                        return Some((node_text_trimmed(&inner), inner));
                    }
                }
            }
        }
    }

    // For other wrapping nodes (like ParenExpr), check direct children
    for child in node.children() {
        if is_complex_action_kind(child.kind()) {
            return Some((node_text_trimmed(&child), child));
        }
    }

    None
}
