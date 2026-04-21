// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Conjunction extraction for spec formula parsing.
//!
//! Extracts and classifies conjuncts from TLA+ temporal formulas, identifying
//! Init predicates, Next relations, and fairness constraints.

use super::cst_helpers::extract_ident;
use super::fairness::{contains_temporal_operators, extract_fairness};
use super::subscript::extract_always_subscript;
use super::types::{Conjunct, FairnessConstraint, SpecFormula};
use tla_core::{SyntaxElement, SyntaxKind, SyntaxNode};

/// Extract from pattern: Init /\ [][Next]_vars
pub(super) fn extract_and_pattern(node: &SyntaxNode) -> Option<SpecFormula> {
    if node.kind() != SyntaxKind::BinaryExpr {
        // Check if this is a UnaryExpr (conjunction list starting with /\)
        if node.kind() == SyntaxKind::UnaryExpr {
            return extract_conjunction_list(node);
        }
        return None;
    }

    let mut init: Option<String> = None;
    let mut next: Option<String> = None;
    let mut next_node: Option<SyntaxNode> = None;
    let mut vars: Option<String> = None;
    let mut fairness = Vec::new();
    // Default to stuttering allowed (most common TLA+ pattern)
    let mut stuttering_allowed = true;

    // Collect all conjuncts (including tokens and nodes)
    let conjuncts = collect_conjuncts(node);

    for conjunct in conjuncts {
        match conjunct {
            Conjunct::Ident(name) => {
                // First identifier is Init
                if init.is_none() {
                    init = Some(name);
                }
            }
            Conjunct::Node(ref n) => {
                // Check if this is an Always operator ([][Next]_vars)
                if let Some(extraction) = extract_always_subscript(n) {
                    next = Some(extraction.name);
                    next_node = extraction.node;
                    vars = Some(extraction.vars);
                    stuttering_allowed = extraction.stuttering_allowed;
                } else if let Some(fc) = extract_fairness(n) {
                    fairness.push(fc);
                } else if n.kind() == SyntaxKind::QuantExpr && contains_temporal_operators(n) {
                    // Quantified fairness like `\A c \in Clients: WF_vars(Action(c))`
                    fairness.push(FairnessConstraint::QuantifiedTemporal { node: n.clone() });
                } else if let Some(ident) = extract_ident(n) {
                    // Fallback: extract identifier from node
                    if init.is_none() {
                        init = Some(ident);
                    }
                }
            }
        }
    }

    Some(SpecFormula {
        init: init?,
        next: next?,
        next_node,
        vars,
        fairness,
        stuttering_allowed,
    })
}

/// Extract from conjunction list pattern: /\ Init /\ [][Next]_vars
pub(super) fn extract_conjunction_list(node: &SyntaxNode) -> Option<SpecFormula> {
    // Find the first BinaryExpr inside
    for child in node.children() {
        if child.kind() == SyntaxKind::BinaryExpr {
            return extract_and_pattern(&child);
        }
    }
    None
}

/// Collect all conjuncts from a conjunction expression
fn collect_conjuncts(node: &SyntaxNode) -> Vec<Conjunct> {
    let mut result = Vec::new();
    collect_conjuncts_rec(node, &mut result);
    result
}

fn collect_conjuncts_rec(node: &SyntaxNode, result: &mut Vec<Conjunct>) {
    if node.kind() == SyntaxKind::BinaryExpr {
        // Check if this is an AND expression
        let has_and = node
            .children_with_tokens()
            .any(|c| matches!(c, SyntaxElement::Token(t) if t.kind() == SyntaxKind::AndOp));

        if has_and {
            // Process all children (both tokens and nodes)
            for child in node.children_with_tokens() {
                match child {
                    SyntaxElement::Token(t) => {
                        if t.kind() == SyntaxKind::Ident {
                            result.push(Conjunct::Ident(t.text().to_string()));
                        }
                        // Skip AndOp and other tokens
                    }
                    SyntaxElement::Node(n) => {
                        // Recursively collect from child nodes
                        collect_conjuncts_rec(&n, result);
                    }
                }
            }
            return;
        }
    }

    // This is a leaf conjunct - add as node
    result.push(Conjunct::Node(node.clone()));
}
