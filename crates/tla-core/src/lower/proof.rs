// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof lowering: proofs, proof steps, proof hints.

use super::assume_prove::lower_assume_prove_stmt_expr;
use super::ctx::LowerCtx;
use super::expr_core::lower_expr;
use super::expr_quantifiers::lower_bound_var;
use super::module_items::lower_operator_def;
use crate::ast::{BoundVar, Expr, OperatorDef, Proof, ProofHint, ProofStep, ProofStepKind};
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};

pub(super) fn lower_proof(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Proof> {
    // Check for simple proofs first
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            match token.kind() {
                SyntaxKind::ObviousKw => return Some(Proof::Obvious),
                SyntaxKind::OmittedKw => return Some(Proof::Omitted),
                _ => {}
            }
        }
    }

    // Check for BY clause
    for child in node.children() {
        if child.kind() == SyntaxKind::ByClause {
            let hints = lower_proof_hints(ctx, &child);
            return Some(Proof::By(hints));
        }
    }

    // Check for structured proof (steps)
    let mut steps = Vec::new();
    for child in node.children() {
        if child.kind() == SyntaxKind::ProofStep {
            if let Some(step) = lower_proof_step(ctx, &child) {
                steps.push(step);
            }
        }
    }
    if !steps.is_empty() {
        return Some(Proof::Steps(steps));
    }

    None
}

/// Lower proof hints
fn lower_proof_hints(ctx: &mut LowerCtx, node: &SyntaxNode) -> Vec<ProofHint> {
    let mut hints = Vec::new();

    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::Ident {
                let span = ctx.token_span(&token);
                hints.push(ProofHint::Ref(Spanned::new(token.text().to_string(), span)));
            }
        }
    }

    hints
}

/// Lower a proof step
fn lower_proof_step(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<ProofStep> {
    let mut level = 1;
    let mut label: Option<Spanned<String>> = None;

    // Find step label
    for child in node.children() {
        if child.kind() == SyntaxKind::StepLabel {
            // Parse level from <n>
            for tok in child.children_with_tokens() {
                if let rowan::NodeOrToken::Token(token) = tok {
                    match token.kind() {
                        SyntaxKind::Number => {
                            if let Ok(n) = token.text().parse::<usize>() {
                                level = n;
                            }
                        }
                        SyntaxKind::Ident => {
                            let span = ctx.token_span(&token);
                            label = Some(Spanned::new(token.text().to_string(), span));
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    // Determine step kind
    let kind = lower_proof_step_kind(ctx, node)?;

    Some(ProofStep { level, label, kind })
}

/// Lower proof step kind
fn lower_proof_step_kind(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<ProofStepKind> {
    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                match token.kind() {
                    SyntaxKind::SufficesKw => {
                        // Find the expression and optional proof
                        let (expr, proof) = find_step_expr_and_proof(ctx, node);
                        return Some(ProofStepKind::Suffices(expr?, proof));
                    }
                    SyntaxKind::HaveKw => {
                        let (expr, _) = find_step_expr_and_proof(ctx, node);
                        return Some(ProofStepKind::Have(expr?));
                    }
                    SyntaxKind::TakeKw => {
                        let bounds = find_bound_vars(ctx, node);
                        return Some(ProofStepKind::Take(bounds));
                    }
                    SyntaxKind::WitnessKw => {
                        let exprs = find_all_exprs(ctx, node);
                        return Some(ProofStepKind::Witness(exprs));
                    }
                    SyntaxKind::PickKw => {
                        let bounds = find_bound_vars(ctx, node);
                        let (expr, proof) = find_step_expr_and_proof(ctx, node);
                        return Some(ProofStepKind::Pick(bounds, expr?, proof));
                    }
                    SyntaxKind::UseKw => {
                        let hints = collect_proof_hints_from_node(ctx, node);
                        return Some(ProofStepKind::UseOrHide {
                            use_: true,
                            facts: hints,
                        });
                    }
                    SyntaxKind::HideKw => {
                        let hints = collect_proof_hints_from_node(ctx, node);
                        return Some(ProofStepKind::UseOrHide {
                            use_: false,
                            facts: hints,
                        });
                    }
                    SyntaxKind::DefineKw => {
                        let defs = collect_operator_defs(ctx, node);
                        return Some(ProofStepKind::Define(defs));
                    }
                    SyntaxKind::QedKw => {
                        // Look for nested proof
                        let proof = node
                            .children()
                            .find(|n| n.kind() == SyntaxKind::Proof)
                            .and_then(|n| lower_proof(ctx, &n))
                            .map(|p| Spanned::new(p, ctx.span(node)));
                        return Some(ProofStepKind::Qed(proof));
                    }
                    _ => {}
                }
            }
            rowan::NodeOrToken::Node(_) => {}
        }
    }

    // Default: assertion
    let (expr, proof) = find_step_expr_and_proof(ctx, node);
    Some(ProofStepKind::Assert(expr?, proof))
}

/// Find expression and optional proof in a proof step
fn find_step_expr_and_proof(
    ctx: &mut LowerCtx,
    node: &SyntaxNode,
) -> (Option<Spanned<Expr>>, Option<Spanned<Proof>>) {
    let mut expr: Option<Spanned<Expr>> = lower_assume_prove_stmt_expr(ctx, node);
    let mut proof: Option<Spanned<Proof>> = None;

    for child in node.children() {
        match child.kind() {
            SyntaxKind::Proof => {
                proof = lower_proof(ctx, &child).map(|p| Spanned::new(p, ctx.span(&child)));
            }
            SyntaxKind::StepLabel => {}
            _ => {
                if expr.is_none() {
                    if let Some(e) = lower_expr(ctx, &child) {
                        expr = Some(Spanned::new(e, ctx.span(&child)));
                    }
                }
            }
        }
    }

    (expr, proof)
}

/// Find bound variables in a node
fn find_bound_vars(ctx: &mut LowerCtx, node: &SyntaxNode) -> Vec<BoundVar> {
    let mut vars = Vec::new();
    for child in node.children() {
        if child.kind() == SyntaxKind::BoundVar {
            if let Some(bv) = lower_bound_var(ctx, &child) {
                vars.push(bv);
            }
        }
    }
    vars
}

/// Find all expressions in a node (for WITNESS)
fn find_all_exprs(ctx: &mut LowerCtx, node: &SyntaxNode) -> Vec<Spanned<Expr>> {
    let mut exprs = Vec::new();
    for child in node.children() {
        if let Some(e) = lower_expr(ctx, &child) {
            exprs.push(Spanned::new(e, ctx.span(&child)));
        }
    }
    exprs
}

/// Collect proof hints from a node
fn collect_proof_hints_from_node(ctx: &mut LowerCtx, node: &SyntaxNode) -> Vec<ProofHint> {
    let mut hints = Vec::new();
    for child in node.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == SyntaxKind::Ident {
                let span = ctx.token_span(&token);
                hints.push(ProofHint::Ref(Spanned::new(token.text().to_string(), span)));
            }
        }
    }
    hints
}

/// Collect operator definitions from a node (for DEFINE)
fn collect_operator_defs(ctx: &mut LowerCtx, node: &SyntaxNode) -> Vec<OperatorDef> {
    let mut defs = Vec::new();
    for child in node.children() {
        if child.kind() == SyntaxKind::OperatorDef {
            if let Some(def) = lower_operator_def(ctx, &child) {
                defs.push(def);
            }
        }
    }
    defs
}
