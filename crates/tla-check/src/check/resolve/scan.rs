// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CST scanning helpers for spec resolution.
//!
//! Pure syntax-tree traversal utilities with no dependency on config dispatch.

use rustc_hash::FxHashSet;
use tla_core::{SyntaxElement, SyntaxKind, SyntaxNode};

/// Find an operator body in the syntax tree by name.
pub(super) fn find_op_body_in_tree(tree: &SyntaxNode, name: &str) -> Option<SyntaxNode> {
    fn search(node: &SyntaxNode, name: &str) -> Option<SyntaxNode> {
        if node.kind() == SyntaxKind::OperatorDef {
            // Check if this operator has the target name
            let mut found_name = false;
            let mut name_token_index = 0;
            for (i, child) in node.children_with_tokens().enumerate() {
                if let SyntaxElement::Token(t) = child {
                    if t.kind() == SyntaxKind::Ident && t.text() == name {
                        found_name = true;
                        name_token_index = i;
                        break;
                    }
                }
            }
            if found_name {
                // Return the body expression(s).
                //
                // Most operator bodies are represented as a single CST node after `==`.
                // However, conjunction-list style bodies can appear as multiple top-level
                // expression nodes (one per `/\` line). In that case, return the OperatorDef
                // node itself so downstream traversals see the full body.
                let mut body_nodes = Vec::new();
                let mut past_def_eq = false;
                for child in node.children_with_tokens() {
                    match child {
                        SyntaxElement::Token(t) if t.kind() == SyntaxKind::DefEqOp => {
                            past_def_eq = true;
                        }
                        SyntaxElement::Node(n) if past_def_eq => {
                            body_nodes.push(n);
                        }
                        _ => {}
                    }
                }
                match body_nodes.as_slice() {
                    [single] => return Some(single.clone()),
                    [] => {}
                    _ => return Some(node.clone()),
                }
                // If no explicit expression node found, the body might be a bare identifier
                // (e.g., `spec_123 == LSpec`). In this case, return the OperatorDef node itself
                // so the caller can handle the identifier body specially.
                // Look for any Ident token after the == operator that isn't the operator name.
                let mut past_def_eq = false;
                for (i, child) in node.children_with_tokens().enumerate() {
                    if let SyntaxElement::Token(t) = child {
                        if t.kind() == SyntaxKind::DefEqOp {
                            past_def_eq = true;
                            continue;
                        }
                        if past_def_eq && t.kind() == SyntaxKind::Ident && i > name_token_index {
                            // Found a bare identifier body - return the OperatorDef
                            // so the caller can extract and follow the reference
                            return Some(node.clone());
                        }
                    }
                }
            }
        }
        for child in node.children() {
            if let Some(found) = search(&child, name) {
                return Some(found);
            }
        }
        None
    }
    search(tree, name)
}

/// Check if a syntax node contains temporal operators (WF, SF, [], <>, ~>).
/// This is used to detect complex fairness formulas like `\A p: WF_vars(Action(p))`
/// that can't be extracted as simple FairnessConstraints.
pub(super) fn contains_temporal_operators(node: &SyntaxNode) -> bool {
    fn search(node: &SyntaxNode) -> bool {
        // Check for temporal operator tokens
        for child in node.children_with_tokens() {
            match child {
                SyntaxElement::Token(t) => {
                    match t.kind() {
                        // Temporal operator keywords
                        SyntaxKind::WeakFairKw
                        | SyntaxKind::StrongFairKw
                        | SyntaxKind::AlwaysOp
                        | SyntaxKind::EventuallyOp
                        | SyntaxKind::LeadsToOp => return true,
                        // WF_xxx or SF_xxx identifiers (parsed as single tokens)
                        SyntaxKind::Ident => {
                            let text = t.text();
                            if text.starts_with("WF_") || text.starts_with("SF_") {
                                return true;
                            }
                        }
                        _ => {}
                    }
                }
                SyntaxElement::Node(n) => {
                    if search(&n) {
                        return true;
                    }
                }
            }
        }
        false
    }
    search(node)
}

/// Find an operator body in any of the provided trees (main + extended).
pub(super) fn find_op_body_in_any_tree(
    syntax_tree: &SyntaxNode,
    extended_trees: &[&SyntaxNode],
    name: &str,
) -> Option<SyntaxNode> {
    find_op_body_in_tree(syntax_tree, name).or_else(|| {
        extended_trees
            .iter()
            .find_map(|ext_tree| find_op_body_in_tree(ext_tree, name))
    })
}

/// Collect unique identifier candidates from a syntax node, preserving first-seen order.
pub(super) fn collect_ident_candidates(node: &SyntaxNode) -> Vec<String> {
    let mut candidates = Vec::new();
    let mut seen = FxHashSet::default();
    for element in node.descendants_with_tokens() {
        if let SyntaxElement::Token(t) = element {
            if t.kind() == SyntaxKind::Ident {
                let name = t.text().to_string();
                if seen.insert(name.clone()) {
                    candidates.push(name);
                }
            }
        }
    }
    candidates
}
