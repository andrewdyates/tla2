// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CST helper functions for spec formula extraction.

use tla_core::{SyntaxElement, SyntaxKind, SyntaxNode};

/// Get trimmed text content of a CST node.
///
/// Replaces the repeated `node.text().to_string().trim().to_string()` pattern.
pub(super) fn node_text_trimmed(node: &SyntaxNode) -> String {
    node.text().to_string().trim().to_string()
}

/// Extract identifier from a node by recursively searching for an Ident token.
pub(super) fn extract_ident(node: &SyntaxNode) -> Option<String> {
    for child in node.children_with_tokens() {
        if let SyntaxElement::Token(t) = child {
            if t.kind() == SyntaxKind::Ident {
                return Some(t.text().to_string());
            }
        }
    }
    // Recurse into children
    for child in node.children() {
        if let Some(ident) = extract_ident(&child) {
            return Some(ident);
        }
    }
    None
}

/// Extract the inner expression from a parenthesized node.
pub(super) fn extract_inner_expr(node: &SyntaxNode) -> SyntaxNode {
    // If this is a ParenExpr, extract the inner expression
    if node.kind() == SyntaxKind::ParenExpr {
        if let Some(child) = node.children().next() {
            return child;
        }
    }
    node.clone()
}
