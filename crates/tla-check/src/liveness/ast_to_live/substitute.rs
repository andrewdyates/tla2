// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::core::AstToLive;
use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_core::{ExprFold, SpanPolicy, SubstituteExpr};

impl AstToLive {
    /// Apply LET binding substitutions to an expression.
    ///
    /// This is used to expand zero-arg LET bindings during liveness expression conversion.
    /// For `LET r == expr IN body`, this substitutes all occurrences of `r` in `body`
    /// with `expr`. This fixes issue #233 where LET bindings were not preserved
    /// during liveness SCC checking.
    pub(super) fn apply_let_substitutions(
        &self,
        expr: &Spanned<Expr>,
        subs: &[(String, Spanned<Expr>)],
    ) -> Spanned<Expr> {
        let sub_map: std::collections::HashMap<&str, &Spanned<Expr>> =
            subs.iter().map(|(name, e)| (name.as_str(), e)).collect();
        let mut substitute = SubstituteExpr {
            subs: sub_map,
            span_policy: SpanPolicy::DummyAll,
        };
        let result = substitute.fold_expr(expr.clone());
        // Preserve the outer expression's span (caller expects it unchanged)
        Spanned {
            node: result.node,
            span: expr.span,
        }
    }

    /// Substitute parameter names with argument expressions in an expression.
    ///
    /// This is used for inlining parameterized operator definitions.
    /// It replaces each occurrence of a parameter name (as an identifier) with
    /// the corresponding argument expression.
    ///
    /// Uses `SpanPolicy::DummyAll` to prevent LITERAL_CACHE collisions (#575).
    pub fn substitute_params_in_expr(
        &self,
        body: &Expr,
        params: &[tla_core::ast::OpParam],
        args: &[Spanned<Expr>],
    ) -> Expr {
        let subs: std::collections::HashMap<&str, &Spanned<Expr>> = params
            .iter()
            .zip(args.iter())
            .map(|(p, a)| (p.name.node.as_str(), a))
            .collect();
        let mut substitute = SubstituteExpr {
            subs,
            span_policy: SpanPolicy::DummyAll,
        };
        let spanned_body = Spanned::new(body.clone(), tla_core::Span::dummy());
        substitute.fold_expr(spanned_body).node
    }
}
