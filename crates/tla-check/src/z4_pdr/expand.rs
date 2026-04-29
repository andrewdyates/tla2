// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CHC-specific operator expansion for PDR translation.
//!
//! Unlike the standard `expand_operators`, this version DOES inline operators
//! containing primed variables when `allow_primed` is true. This is required
//! for Next relation translation where `x' = x + 1` patterns are common.

use std::collections::HashSet;

use tla_core::ast::{Expr, Substitution};
use tla_core::inlining_is_capture_safe;
use tla_core::name_intern::NameId;
use tla_core::ExprFold;
use tla_core::{Span, Spanned};

use crate::enumerate::try_value_to_expr;
use crate::error_policy::{eval_speculative, FallbackClass};
use crate::eval::{apply_substitutions, EvalCtx};
use crate::expr_visitor::expr_contains_prime_v as expr_contains_prime;

/// Expand operators in an expression for CHC translation
///
/// # Arguments
/// * `ctx` - Evaluation context with operator definitions
/// * `expr` - Expression to expand
/// * `allow_primed` - If true, inline operators even if they contain primes
pub fn expand_operators_for_chc(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    allow_primed: bool,
) -> Spanned<Expr> {
    let mut expand = ExpandOperatorsChc::new(ctx, allow_primed);
    expand.fold_expr(expr.clone())
}

struct ExpandOperatorsChc<'a> {
    ctx: &'a EvalCtx,
    allow_primed: bool,
    expanding: HashSet<String>,
}

impl<'a> ExpandOperatorsChc<'a> {
    fn new(ctx: &'a EvalCtx, allow_primed: bool) -> Self {
        Self {
            ctx,
            allow_primed,
            expanding: HashSet::new(),
        }
    }

    fn can_inline(&self, body: &Spanned<Expr>, contains_prime: bool) -> bool {
        let has_primes = contains_prime || expr_contains_prime(&body.node);
        self.allow_primed || !has_primes
    }

    fn fold_config_constant_ident(&self, name: String, span: Span) -> Spanned<Expr> {
        let ident = Spanned::new(Expr::Ident(name.clone(), NameId::INVALID), span);
        match eval_speculative(self.ctx, &ident, &[FallbackClass::ConstantResolution]) {
            Ok(Some(value)) => {
                if let Some(expr) = try_value_to_expr(&value) {
                    return Spanned::new(expr, span);
                }
            }
            Ok(None) => {}
            Err(e) => {
                eprintln!(
                    "Warning: unexpected eval error during config constant '{name}' resolution (kept as Ident): {e}"
                );
            }
        }
        ident
    }

    fn fold_ident_expr(&mut self, name: String, span: Span) -> Spanned<Expr> {
        if self.ctx.is_config_constant(name.as_str()) {
            return self.fold_config_constant_ident(name, span);
        }

        let resolved_name = self.ctx.resolve_op_name(&name);
        if let Some(def) = self.ctx.get_op(resolved_name) {
            if def.params.is_empty()
                && !self.expanding.contains(resolved_name)
                && self.can_inline(&def.body, def.contains_prime)
            {
                self.expanding.insert(resolved_name.to_string());
                let expanded = self.fold_expr(def.body.clone());
                self.expanding.remove(resolved_name);
                return expanded;
            }
        }

        Spanned::new(Expr::Ident(name, NameId::INVALID), span)
    }

    fn fold_apply_expr(
        &mut self,
        op_expr: Box<Spanned<Expr>>,
        args: Vec<Spanned<Expr>>,
        span: Span,
    ) -> Spanned<Expr> {
        if let Expr::Ident(op_name, _) = &op_expr.node {
            let resolved_op_name = self.ctx.resolve_op_name(op_name);

            // Keep operator token untouched while still expanding args under recursion.
            if self.expanding.contains(resolved_op_name) {
                let new_args = args.into_iter().map(|arg| self.fold_expr(arg)).collect();
                return Spanned::new(Expr::Apply(op_expr, new_args), span);
            }

            if let Some(def) = self.ctx.get_op(resolved_op_name) {
                if self.can_inline(&def.body, def.contains_prime) {
                    let expanded_args: Vec<_> =
                        args.into_iter().map(|arg| self.fold_expr(arg)).collect();
                    if def.params.len() != expanded_args.len()
                        || !inlining_is_capture_safe(def, &expanded_args)
                    {
                        return Spanned::new(Expr::Apply(op_expr, expanded_args), span);
                    }
                    let subs: Vec<Substitution> = def
                        .params
                        .iter()
                        .zip(expanded_args.iter())
                        .map(|(param, arg)| Substitution {
                            from: param.name.clone(),
                            to: arg.clone(),
                        })
                        .collect();
                    let substituted = apply_substitutions(&def.body, &subs);
                    self.expanding.insert(resolved_op_name.to_string());
                    let expanded = self.fold_expr(substituted);
                    self.expanding.remove(resolved_op_name);
                    return expanded;
                }
            }
        }

        Spanned::new(
            Expr::Apply(
                Box::new(self.fold_expr(*op_expr)),
                args.into_iter().map(|arg| self.fold_expr(arg)).collect(),
            ),
            span,
        )
    }
}

impl ExprFold for ExpandOperatorsChc<'_> {
    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let span = expr.span;
        match expr.node {
            Expr::Ident(name, _) => self.fold_ident_expr(name, span),
            Expr::Apply(op_expr, args) => self.fold_apply_expr(op_expr, args, span),
            node => Spanned::new(self.fold_expr_inner(node), span),
        }
    }
}
