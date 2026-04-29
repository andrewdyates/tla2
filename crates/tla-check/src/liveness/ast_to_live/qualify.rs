// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::core::AstToLive;
use crate::eval::{apply_substitutions, EvalCtx, OpEnv};
use rustc_hash::FxHashSet;
use tla_core::ast::{BoundPattern, BoundVar, Expr, ModuleTarget};
use tla_core::ExprFold;
use tla_core::Spanned;

impl AstToLive {
    pub(super) fn qualify_predicate_expr(
        &self,
        ctx: &EvalCtx,
        expr: &Spanned<Expr>,
    ) -> Spanned<Expr> {
        let Some(target) = self.current_target() else {
            return expr.clone();
        };
        let substitutions = ctx.instance_substitutions().unwrap_or(&[]);
        let substituted = if substitutions.is_empty() {
            expr.clone()
        } else {
            apply_substitutions(expr, substitutions)
        };
        let empty_ops = OpEnv::new();
        let local_ops = ctx
            .local_ops()
            .as_ref()
            .map(AsRef::as_ref)
            .unwrap_or(&empty_ops);
        if local_ops.is_empty() && substitutions.is_empty() {
            return expr.clone();
        }

        let mut qualifier = QualifyExpr {
            target: target.as_ref(),
            local_ops,
            bound: FxHashSet::default(),
        };
        qualifier.fold_expr(substituted)
    }
}

/// Transforms unqualified operator references (`Ident(name)`) into
/// module-qualified references (`ModuleRef(target, name, args)`) for operators
/// found in `local_ops` that are not shadowed by bound variables.
/// Instance substitutions are applied before qualification using the shared
/// capture-avoiding substitution helper.
struct QualifyExpr<'a> {
    target: &'a ModuleTarget,
    local_ops: &'a OpEnv,
    bound: FxHashSet<String>,
}

impl QualifyExpr<'_> {
    fn with_extended_bound(&self, names: impl IntoIterator<Item = String>) -> Self {
        let mut new_bound = self.bound.clone();
        new_bound.extend(names);
        QualifyExpr {
            target: self.target,
            local_ops: self.local_ops,
            bound: new_bound,
        }
    }

    fn bound_names_from_bv(bv: &BoundVar) -> Vec<String> {
        let mut names = vec![bv.name.node.clone()];
        if let Some(pattern) = &bv.pattern {
            match pattern {
                BoundPattern::Var(v) => names.push(v.node.clone()),
                BoundPattern::Tuple(vs) => names.extend(vs.iter().map(|v| v.node.clone())),
            }
        }
        names
    }
}

impl ExprFold for QualifyExpr<'_> {
    fn fold_ident(&mut self, name: String, name_id: tla_core::NameId) -> Expr {
        if self.bound.contains(&name) {
            Expr::Ident(name, name_id)
        } else if let Some(def) = self.local_ops.get(&name) {
            if def.params.is_empty() {
                Expr::ModuleRef(self.target.clone(), name, Vec::new())
            } else {
                Expr::Ident(name, name_id)
            }
        } else {
            Expr::Ident(name, name_id)
        }
    }

    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let span = expr.span;
        let new_node = match expr.node {
            // Special case: Apply(Ident(name), args) → ModuleRef when name is in local_ops
            Expr::Apply(op, args) => {
                if let Expr::Ident(ref name, _) = op.node {
                    if !self.bound.contains(name) && self.local_ops.contains_key(name) {
                        let new_args: Vec<_> =
                            args.into_iter().map(|a| self.fold_expr(a)).collect();
                        return Spanned::new(
                            Expr::ModuleRef(self.target.clone(), name.clone(), new_args),
                            span,
                        );
                    }
                }
                let new_op = self.fold_expr(*op);
                let new_args: Vec<_> = args.into_iter().map(|a| self.fold_expr(a)).collect();
                Expr::Apply(Box::new(new_op), new_args)
            }

            // Binding forms: extend bound set for body, recurse domains with current bound
            Expr::Forall(bounds, body) => {
                let names: Vec<_> = bounds.iter().flat_map(Self::bound_names_from_bv).collect();
                let new_bounds = self.fold_bound_vars(bounds);
                let mut inner = self.with_extended_bound(names);
                Expr::Forall(new_bounds, Box::new(inner.fold_expr(*body)))
            }
            Expr::Exists(bounds, body) => {
                let names: Vec<_> = bounds.iter().flat_map(Self::bound_names_from_bv).collect();
                let new_bounds = self.fold_bound_vars(bounds);
                let mut inner = self.with_extended_bound(names);
                Expr::Exists(new_bounds, Box::new(inner.fold_expr(*body)))
            }
            Expr::Choose(bv, body) => {
                let names = Self::bound_names_from_bv(&bv);
                let new_bv = self.fold_bound_var(bv);
                let mut inner = self.with_extended_bound(names);
                Expr::Choose(new_bv, Box::new(inner.fold_expr(*body)))
            }
            Expr::SetBuilder(body, bounds) => {
                let names: Vec<_> = bounds.iter().flat_map(Self::bound_names_from_bv).collect();
                let new_bounds = self.fold_bound_vars(bounds);
                let mut inner = self.with_extended_bound(names);
                Expr::SetBuilder(Box::new(inner.fold_expr(*body)), new_bounds)
            }
            Expr::SetFilter(bv, pred) => {
                let names = Self::bound_names_from_bv(&bv);
                let new_bv = self.fold_bound_var(bv);
                let mut inner = self.with_extended_bound(names);
                Expr::SetFilter(new_bv, Box::new(inner.fold_expr(*pred)))
            }
            Expr::FuncDef(bounds, body) => {
                let names: Vec<_> = bounds.iter().flat_map(Self::bound_names_from_bv).collect();
                let new_bounds = self.fold_bound_vars(bounds);
                let mut inner = self.with_extended_bound(names);
                Expr::FuncDef(new_bounds, Box::new(inner.fold_expr(*body)))
            }
            Expr::Lambda(params, body) => {
                let names: Vec<_> = params.iter().map(|p| p.node.clone()).collect();
                let mut inner = self.with_extended_bound(names);
                Expr::Lambda(params, Box::new(inner.fold_expr(*body)))
            }
            Expr::Let(defs, body) => {
                let new_defs = self.fold_operator_defs(defs.clone());
                let def_names = defs.into_iter().map(|d| d.name.node);
                let mut inner = self.with_extended_bound(def_names);
                Expr::Let(new_defs, Box::new(inner.fold_expr(*body)))
            }

            // All other variants: default identity recursion
            other => self.fold_expr_inner(other),
        };
        Spanned::new(new_node, span)
    }
}
