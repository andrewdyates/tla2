// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Module reference, action subscript, and INSTANCE expression lowering.

use super::ctx::{unescape_tla_string, LowerCtx};
use super::expr_core::{lower_apply_args, lower_expr};
use super::expr_records_tuples::lower_tuple_expr;
use super::module_items::lower_substitution;
use super::operators::lower_arg_list;
use crate::ast::{Expr, ModuleTarget};
use crate::name_intern::NameId;
use crate::span::Spanned;
use crate::syntax::kinds::{SyntaxKind, SyntaxNode};
use num_bigint::BigInt;

/// Lower module reference expression: M!Op or M!Op(args) or IS(x,y)!Op
pub(super) fn lower_module_ref_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    // ModuleRefExpr is created by wrapping an already-parsed expression node at
    // the checkpoint where `!` appears. That means the module name is usually
    // contained inside a child expression node (e.g., NameExpr) rather than as a
    // direct Ident token child of ModuleRefExpr.
    //
    // Structure (conceptually): <module_expr> ! <op_token> [ArgList]
    //
    // Examples:
    // - InChan!Init
    // - InChan!Send(msg)
    // - R!+(a, b)
    // - IS(chosen, allInput)!ISpec  (parameterized instance)
    let mut module_expr: Option<SyntaxNode> = None;
    let mut module_target: Option<ModuleTarget> = None;
    let mut op_name: Option<String> = None;
    let mut args: Vec<Spanned<Expr>> = Vec::new();

    let mut seen_bang = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::Bang {
                    seen_bang = true;
                    continue;
                }
                if !seen_bang {
                    if module_target.is_none() && token.kind() == SyntaxKind::Ident {
                        // Best-effort: some forms may expose the module name as a direct token.
                        module_target = Some(ModuleTarget::Named(token.text().to_string()));
                    }
                    continue;
                }

                if op_name.is_none() {
                    // Operator name after `!` can be:
                    // - Ident: M!Op
                    // - Number: TLAPS sometimes emits `TLANext!1`
                    // - Operator symbol: R!+(a, b), R!\leq(a, b)
                    match token.kind() {
                        SyntaxKind::Ident | SyntaxKind::Number => {
                            op_name = Some(token.text().to_string());
                        }
                        // For operator symbols, accept the token text. Ignore punctuation that
                        // belongs to argument lists.
                        SyntaxKind::LParen | SyntaxKind::RParen | SyntaxKind::Comma => {}
                        _ => {
                            op_name = Some(token.text().to_string());
                        }
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                if !seen_bang {
                    if module_expr.is_none() {
                        module_expr = Some(child_node);
                    }
                    continue;
                }

                // Handle argument list (ApplyExpr or ArgList children)
                if child_node.kind() == SyntaxKind::ApplyExpr {
                    args = lower_apply_args(ctx, &child_node);
                } else if child_node.kind() == SyntaxKind::ArgList {
                    // ArgList is directly a child of ModuleRefExpr
                    args = lower_arg_list(ctx, &child_node);
                }
            }
        }
    }

    if module_target.is_none() {
        if let Some(module_node) = module_expr {
            let lowered = lower_expr(ctx, &module_node)?;
            let module_span = ctx.span(&module_node);
            match lowered {
                Expr::Ident(name, NameId::INVALID) => {
                    module_target = Some(ModuleTarget::Named(name));
                }
                // Handle parameterized instance calls: IS(x, y)!Op
                // The module part is an Apply expression like Apply(Ident("IS"), [x, y])
                Expr::Apply(func_expr, param_args) => {
                    if let Expr::Ident(name, NameId::INVALID) = &func_expr.node {
                        module_target = Some(ModuleTarget::Parameterized(name.clone(), param_args));
                    } else {
                        ctx.error(
                            format!(
                                "parameterized module reference requires identifier, got: {:?}",
                                func_expr.node
                            ),
                            module_span,
                        );
                        return None;
                    }
                }
                // Handle chained module references: A!B!C!D
                // The module part is itself a ModuleRef (e.g., A!B!C)
                Expr::ModuleRef(_, _, _) => {
                    module_target = Some(ModuleTarget::Chained(Box::new(Spanned::new(
                        lowered,
                        module_span,
                    ))));
                }
                other => {
                    ctx.error(
                        format!("module reference requires module name identifier, got: {other:?}"),
                        module_span,
                    );
                    return None;
                }
            }
        }
    }

    let Some(module_target) = module_target else {
        ctx.error(
            "module reference requires module and operator name".to_string(),
            ctx.span(node),
        );
        return None;
    };
    let Some(op_name) = op_name else {
        ctx.error(
            "module reference requires module and operator name".to_string(),
            ctx.span(node),
        );
        return None;
    };

    Some(Expr::ModuleRef(module_target, op_name, args))
}

/// Lower action subscripts. TLC treats `[A]_v` as `A \/ UNCHANGED v`
/// and `<<A>>_v` as `A /\ ~UNCHANGED v`.
pub(super) fn lower_subscript_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    // SubscriptExpr wraps a previously-parsed base expression at a checkpoint where `_` appears.
    // The base expression is either:
    // - a bracketed action `[A]` (parsed as FuncSetExpr with no `->`), or
    // - an angle action `<<A>>` (parsed as TupleExpr with a single element).

    let mut base: Option<SyntaxNode> = None;
    let mut subscript: Option<Spanned<Expr>> = None;
    let mut saw_underscore = false;

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::Underscore {
                    saw_underscore = true;
                    continue;
                }
                // Handle simple identifier subscripts, e.g. `[A]_vars`.
                // With the lexer change, `_vars` is now a single Ident token starting with `_`,
                // so we check for underscore-prefixed identifiers as well as the legacy
                // Underscore + Ident sequence.
                if subscript.is_none() {
                    if token.kind() == SyntaxKind::Ident {
                        let text = token.text();
                        if saw_underscore {
                            // Legacy: Underscore + Ident("vars")
                            let span = ctx.token_span(&token);
                            subscript = Some(Spanned::new(
                                Expr::Ident(text.to_string(), NameId::INVALID),
                                span,
                            ));
                        } else if text.starts_with('_') {
                            // New: Ident("_vars") - strip exactly one leading underscore
                            // (the subscript marker). Don't strip multiple underscores
                            // to preserve Apalache identifiers like __vars.
                            let span = ctx.token_span(&token);
                            let var_name = text.strip_prefix('_').unwrap_or(text);
                            subscript = Some(Spanned::new(
                                Expr::Ident(var_name.to_string(), NameId::INVALID),
                                span,
                            ));
                            saw_underscore = true; // Mark as having seen subscript marker
                        }
                    } else if saw_underscore && token.kind() == SyntaxKind::At {
                        let span = ctx.token_span(&token);
                        subscript = Some(Spanned::new(
                            Expr::Ident("@".to_string(), NameId::INVALID),
                            span,
                        ));
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                // Special case: ModuleRefExpr with underscore-prefixed identifier (_M!vars)
                // The leading underscore is the subscript marker, so we need to check if
                // this is a subscript module ref even before saw_underscore is set.
                if child_node.kind() == SyntaxKind::ModuleRefExpr && subscript.is_none() {
                    // Check if first identifier starts with underscore
                    let first_ident = child_node
                        .children_with_tokens()
                        .filter_map(rowan::NodeOrToken::into_token)
                        .find(|t| t.kind() == SyntaxKind::Ident);
                    if let Some(token) = first_ident {
                        if token.text().starts_with('_') {
                            // This is a subscript module ref like _M!vars
                            if let Some(expr) = lower_subscript_module_ref(ctx, &child_node) {
                                let span = ctx.span(&child_node);
                                subscript = Some(Spanned::new(expr, span));
                                saw_underscore = true;
                                continue;
                            }
                        }
                    }
                }

                if !saw_underscore {
                    if base.is_none() {
                        base = Some(child_node);
                    }
                    continue;
                }
                if subscript.is_none() {
                    if let Some(expr) = lower_expr(ctx, &child_node) {
                        let span = ctx.span(&child_node);
                        subscript = Some(Spanned::new(expr, span));
                    }
                }
            }
        }
    }

    let base = base?;
    let subscript = subscript?;

    let node_span = ctx.span(node); // #3184: span() not tight_span() — match lower_unary_expr

    let unchanged = Spanned::new(Expr::Unchanged(Box::new(subscript)), node_span);

    match base.kind() {
        // `[A]_v` - base `[A]` is parsed as a FuncSetExpr with no arrow.
        SyntaxKind::FuncSetExpr => {
            // Extract the action expression `A` from inside `[A]`.
            let mut saw_arrow = false;
            for child in base.children_with_tokens() {
                if let rowan::NodeOrToken::Token(t) = &child {
                    if t.kind() == SyntaxKind::Arrow {
                        saw_arrow = true;
                        break;
                    }
                }
            }
            if saw_arrow {
                ctx.error(
                    "action subscript base '[A]' cannot be a function set '[S -> T]'".to_string(),
                    ctx.span(&base),
                );
                return None;
            }

            let mut action: Option<Spanned<Expr>> = None;
            for child in base.children_with_tokens() {
                match child {
                    rowan::NodeOrToken::Node(child_node) => {
                        if let Some(expr) = lower_expr(ctx, &child_node) {
                            let span = ctx.span(&child_node);
                            action = Some(Spanned::new(expr, span));
                            break;
                        }
                    }
                    rowan::NodeOrToken::Token(token) => {
                        // Fallback for action atoms like `[Next]` where Next is a bare token.
                        let expr = match token.kind() {
                            SyntaxKind::Ident => {
                                Some(Expr::Ident(token.text().to_string(), NameId::INVALID))
                            }
                            SyntaxKind::At => Some(Expr::Ident("@".to_string(), NameId::INVALID)),
                            SyntaxKind::Number => {
                                token.text().parse::<BigInt>().ok().map(Expr::Int)
                            }
                            SyntaxKind::String => {
                                Some(Expr::String(unescape_tla_string(token.text())))
                            }
                            SyntaxKind::TrueKw => Some(Expr::Bool(true)),
                            SyntaxKind::FalseKw => Some(Expr::Bool(false)),
                            _ => None,
                        };
                        if let Some(e) = expr {
                            let span = ctx.token_span(&token);
                            action = Some(Spanned::new(e, span));
                            break;
                        }
                    }
                }
            }

            ctx.record_action_subscript_span(node_span);
            Some(Expr::Or(Box::new(action?), Box::new(unchanged)))
        }

        // `<<A>>_v` - base is parsed as a TupleExpr with a single element.
        SyntaxKind::TupleExpr => {
            let tuple = lower_tuple_expr(ctx, &base)?;
            let Expr::Tuple(mut elems) = tuple else {
                ctx.error(
                    "angle action '<<A>>_v' did not lower to a tuple".to_string(),
                    ctx.span(&base),
                );
                return None;
            };
            if elems.len() != 1 {
                ctx.error(
                    "angle action '<<A>>_v' must contain exactly one expression".to_string(),
                    ctx.span(&base),
                );
                return None;
            }
            let action = elems.pop()?;

            let not_unchanged = Spanned::new(Expr::Not(Box::new(unchanged)), node_span);
            ctx.record_action_subscript_span(node_span);
            Some(Expr::And(Box::new(action), Box::new(not_unchanged)))
        }

        other => {
            ctx.error(
                format!("unexpected base for action subscript expression: {other:?}"),
                ctx.span(&base),
            );
            None
        }
    }
}

/// Lower an INSTANCE declaration as an expression (for named instances)
/// InChan == INSTANCE Channel WITH Data <- Message, chan <- in
/// becomes Expr::InstanceExpr("Channel", [Data <- Message, chan <- in])
pub(super) fn lower_instance_expr(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    let mut module_name: Option<String> = None;
    let mut substitutions = Vec::new();

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::Ident && module_name.is_none() {
                    module_name = Some(token.text().to_string());
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

    Some(Expr::InstanceExpr(module_name?, substitutions))
}

/// Lower a module reference expression in subscript context.
/// When we have `_M!vars` as a subscript, the `_M` is tokenized as a single identifier
/// but the leading `_` is actually the subscript marker. This function strips the leading
/// underscore from the module name to produce the correct module reference.
fn lower_subscript_module_ref(ctx: &mut LowerCtx, node: &SyntaxNode) -> Option<Expr> {
    // Extract the components of the module reference
    let mut module_name: Option<String> = None;
    let mut operator_name: Option<String> = None;
    let mut args = Vec::new();

    for child in node.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == SyntaxKind::Ident {
                    if module_name.is_none() {
                        // First identifier is the module name (possibly with leading _)
                        let text = token.text();
                        // Strip exactly one leading underscore (the subscript marker).
                        // Don't strip multiple underscores to preserve Apalache identifiers.
                        let stripped = text.strip_prefix('_').unwrap_or(text);
                        module_name = Some(stripped.to_string());
                    } else if operator_name.is_none() {
                        operator_name = Some(token.text().to_string());
                    }
                }
            }
            rowan::NodeOrToken::Node(child_node) => {
                // Arguments
                if child_node.kind() == SyntaxKind::ArgList {
                    for arg in child_node.children() {
                        if let Some(expr) = lower_expr(ctx, &arg) {
                            let span = ctx.span(&arg);
                            args.push(Spanned::new(expr, span));
                        }
                    }
                }
            }
        }
    }

    let module_name = module_name?;
    let operator_name = operator_name?;

    // Create a module reference using ModuleTarget::Named
    Some(Expr::ModuleRef(
        ModuleTarget::Named(module_name),
        operator_name,
        args,
    ))
}
