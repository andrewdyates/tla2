// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fairness constraint extraction from TLA+ spec formulas.
//!
//! Handles WF_vars(Action), SF_vars(Action), and quantified temporal fairness.

use super::cst_helpers::{extract_inner_expr, node_text_trimmed};
use super::types::FairnessConstraint;
use tla_core::{SyntaxElement, SyntaxKind, SyntaxNode};

/// Extract the action argument from an ArgList node.
/// Returns (action_text, action_node) if found.
pub(super) fn extract_action_from_arglist(
    arglist: &SyntaxNode,
) -> (Option<String>, Option<SyntaxNode>) {
    for arg_child in arglist.children_with_tokens() {
        match arg_child {
            SyntaxElement::Token(t) if t.kind() == SyntaxKind::Ident => {
                return (Some(t.text().to_string()), None);
            }
            SyntaxElement::Node(arg_node) => {
                let action = Some(node_text_trimmed(&arg_node));
                return (action, Some(arg_node.clone()));
            }
            _ => {}
        }
    }
    (None, None)
}

/// Extract fairness constraint (WF_vars(Action) or SF_vars(Action))
///
/// Due to lexer behavior, `WF_vars(Next)` is often parsed as an ApplyExpr
/// with identifier `WF_vars` rather than as a BinaryExpr with WeakFairKw.
/// This function handles both cases.
pub(super) fn extract_fairness(node: &SyntaxNode) -> Option<FairnessConstraint> {
    // Case 1: BinaryExpr with WeakFairKw or StrongFairKw (ideal parsing)
    if node.kind() == SyntaxKind::BinaryExpr {
        let mut is_weak = false;
        let mut is_strong = false;
        let mut vars: Option<String> = None;
        let mut action: Option<String> = None;
        let mut action_node: Option<SyntaxNode> = None;
        let mut saw_lparen = false;

        for child in node.children_with_tokens() {
            match child {
                SyntaxElement::Token(t) => {
                    if t.kind() == SyntaxKind::WeakFairKw {
                        is_weak = true;
                    } else if t.kind() == SyntaxKind::StrongFairKw {
                        is_strong = true;
                    } else if t.kind() == SyntaxKind::LParen {
                        saw_lparen = true;
                    } else if t.kind() == SyntaxKind::Ident
                        && saw_lparen
                        && vars.is_some()
                        && action.is_none()
                    {
                        // Some fairness expressions use tokens for the parenthesized action,
                        // e.g. `WF_<<v1,v2>>(Next)` parses with `Ident` rather than a child node.
                        action = Some(t.text().to_string());
                    }
                }
                SyntaxElement::Node(n) => {
                    // First child node is vars (subscript), second is action
                    if vars.is_none() {
                        vars = Some(node_text_trimmed(&n));
                    } else if action.is_none() {
                        // Store the action node for inline expression support
                        action_node = Some(extract_inner_expr(&n));
                        // The action is typically in parentheses, extract the inner part
                        let action_text = n.text().to_string();
                        // Remove surrounding parentheses if present
                        let trimmed = action_text.trim();
                        let inner = if trimmed.starts_with('(') && trimmed.ends_with(')') {
                            trimmed[1..trimmed.len() - 1].trim().to_string()
                        } else {
                            trimmed.to_string()
                        };
                        action = Some(inner);
                    }
                }
            }
        }

        if is_weak {
            return Some(FairnessConstraint::Weak {
                vars: vars?,
                action: action?,
                action_node,
            });
        } else if is_strong {
            return Some(FairnessConstraint::Strong {
                vars: vars?,
                action: action?,
                action_node,
            });
        }
    }

    // Case 2: ApplyExpr where identifier is WF_xxx or SF_xxx
    // This happens because the lexer matches WF_vars as a single identifier
    if node.kind() == SyntaxKind::ApplyExpr {
        let mut func_name: Option<String> = None;
        let mut action: Option<String> = None;
        let mut action_node: Option<SyntaxNode> = None;

        for child in node.children_with_tokens() {
            match child {
                SyntaxElement::Token(t) => {
                    if t.kind() == SyntaxKind::Ident && func_name.is_none() {
                        func_name = Some(t.text().to_string());
                    }
                }
                SyntaxElement::Node(n) => {
                    if n.kind() == SyntaxKind::ArgList {
                        let (a, an) = extract_action_from_arglist(&n);
                        action = a;
                        action_node = an;
                    }
                }
            }
        }

        if let Some(name) = func_name {
            if let Some(vars) = name.strip_prefix("WF_") {
                return Some(FairnessConstraint::Weak {
                    vars: vars.to_string(),
                    action: action?,
                    action_node,
                });
            } else if let Some(vars) = name.strip_prefix("SF_") {
                return Some(FairnessConstraint::Strong {
                    vars: vars.to_string(),
                    action: action?,
                    action_node,
                });
            }
        }
    }

    None
}

/// Extract all fairness constraints from a spec body.
///
/// This is useful when a spec body like `SpecWeakFair == Spec /\ WF_vars(Next)`
/// doesn't match the full `Init /\ [][Next]_vars` pattern but still contains
/// fairness constraints that should be merged with the resolved Init/Next.
pub(crate) fn extract_all_fairness(spec_body: &SyntaxNode) -> Vec<FairnessConstraint> {
    let mut result = Vec::new();
    extract_all_fairness_rec(spec_body, &mut result);
    result
}

fn extract_all_fairness_rec(node: &SyntaxNode, result: &mut Vec<FairnessConstraint>) {
    // Handle quantified expressions (\A, \E) specially.
    // Quantified fairness like `\A p: WF_vars(Action(p))` should be handled
    // as a whole via QuantifiedTemporal, not by extracting the WF individually
    // (which would leave `p` as an unbound variable).
    if node.kind() == SyntaxKind::QuantExpr {
        // Check if this quantified expression contains temporal operators (WF, SF, [], <>)
        if contains_temporal_operators(node) {
            result.push(FairnessConstraint::QuantifiedTemporal { node: node.clone() });
        }
        return;
    }
    // Check if this node is a fairness constraint
    if let Some(fc) = extract_fairness(node) {
        result.push(fc);
        return; // Don't recurse into fairness nodes
    }
    // Recurse into children
    for child in node.children() {
        extract_all_fairness_rec(&child, result);
    }
}

/// Check if a syntax node contains temporal operators (WF, SF, [], <>, ~>).
pub(super) fn contains_temporal_operators(node: &SyntaxNode) -> bool {
    fn search(node: &SyntaxNode) -> bool {
        // Check for temporal operator tokens
        for child in node.children_with_tokens() {
            match child {
                SyntaxElement::Token(t) => {
                    let kind = t.kind();
                    if kind == SyntaxKind::AlwaysOp
                        || kind == SyntaxKind::EventuallyOp
                        || kind == SyntaxKind::LeadsToOp
                        || kind == SyntaxKind::WeakFairKw
                        || kind == SyntaxKind::StrongFairKw
                    {
                        return true;
                    }
                    // Also check for WF_xxx or SF_xxx identifiers
                    if kind == SyntaxKind::Ident {
                        let text = t.text();
                        if text.starts_with("WF_") || text.starts_with("SF_") {
                            return true;
                        }
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
