// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Instance operator qualification — Part of #2949.
//!
//! After INSTANCE substitution replaces WITH parameters, module-local operator
//! references (e.g., `Next`, `vars`, `System`) remain as bare `Ident` nodes.
//! The evaluator cannot resolve these in the outer module's context. This module
//! provides an `ExprFold`-based transformation that replaces them with
//! `ModuleRef(target, name, [])` so the evaluator resolves them through the
//! correct instance scope.

use crate::eval::EvalCtx;
use rustc_hash::FxHashMap;
use tla_core::ast::{BoundPattern, BoundVar, Expr, ModuleTarget};
use tla_core::{ExprFold, NameId, Spanned};

/// Qualify remaining bare `Ident` references in an INSTANCE-resolved expression.
pub(crate) fn qualify_instance_ops(
    ctx: &EvalCtx,
    target: &ModuleTarget,
    module_name: &str,
    expr: Spanned<Expr>,
) -> Spanned<Expr> {
    let mut folder = QualifyInstanceOpsFolder {
        ctx,
        target: target.clone(),
        module_name: module_name.to_string(),
        bound_vars: FxHashMap::default(),
    };
    folder.fold_expr(expr)
}

struct QualifyInstanceOpsFolder<'a> {
    ctx: &'a EvalCtx,
    target: ModuleTarget,
    module_name: String,
    /// Reference-counted bound variable tracker. Each nested binding of the same
    /// name increments the count; exiting that scope decrements it. A name is
    /// considered bound as long as its count > 0. This prevents inner scope exits
    /// from leaking outer same-name bindings (the FxHashSet bug from #2953).
    bound_vars: FxHashMap<String, usize>,
}

/// Extract all bound names from a BoundVar, including pattern variables.
/// For `<<x, y>> \in S`, returns the synthetic name AND the pattern names.
fn bound_var_names(b: &BoundVar) -> Vec<String> {
    let mut names = vec![b.name.node.clone()];
    if let Some(pattern) = &b.pattern {
        match pattern {
            BoundPattern::Var(v) => names.push(v.node.clone()),
            BoundPattern::Tuple(vars) => names.extend(vars.iter().map(|v| v.node.clone())),
        }
    }
    names
}

/// Collect bound variable names introduced by an expression node.
fn collect_bound_names(expr: &Expr) -> Vec<String> {
    match expr {
        Expr::Exists(bounds, _)
        | Expr::Forall(bounds, _)
        | Expr::SetBuilder(_, bounds)
        | Expr::FuncDef(bounds, _) => bounds.iter().flat_map(bound_var_names).collect(),
        Expr::Choose(bound, _) | Expr::SetFilter(bound, _) => bound_var_names(bound),
        Expr::Let(defs, _) => defs.iter().map(|d| d.name.node.clone()).collect(),
        Expr::Lambda(params, _) => params.iter().map(|p| p.node.clone()).collect(),
        _ => Vec::new(),
    }
}

impl ExprFold for QualifyInstanceOpsFolder<'_> {
    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        // Track bound variable names for binding forms so we don't qualify them.
        // Use reference counting so nested same-name bindings don't leak on exit.
        let new_bounds = collect_bound_names(&expr.node);
        for n in &new_bounds {
            *self.bound_vars.entry(n.clone()).or_insert(0) += 1;
        }
        let span = expr.span;
        let result = Spanned {
            node: self.fold_expr_inner(expr.node),
            span,
        };
        for n in &new_bounds {
            if let Some(count) = self.bound_vars.get_mut(n) {
                *count -= 1;
                if *count == 0 {
                    self.bound_vars.remove(n);
                }
            }
        }
        result
    }

    fn fold_ident(&mut self, name: String, name_id: NameId) -> Expr {
        if self.bound_vars.contains_key(&name) {
            return Expr::Ident(name, name_id);
        }
        // Qualify identifiers that are operators in the instanced module.
        if self.ctx.get_instance_op(&self.module_name, &name).is_some() {
            return Expr::ModuleRef(self.target.clone(), name, Vec::new());
        }
        Expr::Ident(name, name_id)
    }

    // Part of #2996: After resolve_state_vars_in_loaded_ops() lowers Ident→StateVar,
    // state variable names that collide with instance module operator names would be
    // missed by fold_ident (which only matches Ident nodes). This defense-in-depth
    // override handles the rare case where a state variable name matches an operator.
    fn fold_state_var(&mut self, name: String, idx: u16, name_id: NameId) -> Expr {
        if self.bound_vars.contains_key(&name) {
            return Expr::StateVar(name, idx, name_id);
        }
        if self.ctx.get_instance_op(&self.module_name, &name).is_some() {
            return Expr::ModuleRef(self.target.clone(), name, Vec::new());
        }
        Expr::StateVar(name, idx, name_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::Spanned;

    fn spanned_str(s: &str) -> Spanned<String> {
        Spanned::dummy(s.to_string())
    }

    fn bound_var(name: &str) -> BoundVar {
        BoundVar {
            name: spanned_str(name),
            domain: None,
            pattern: None,
        }
    }

    #[allow(clippy::unnecessary_box_returns)]
    fn dummy_body() -> Box<Spanned<Expr>> {
        Box::new(Spanned::dummy(Expr::Bool(true)))
    }

    #[test]
    fn collect_bound_names_lambda_returns_param_names() {
        let expr = Expr::Lambda(vec![spanned_str("x"), spanned_str("y")], dummy_body());
        assert_eq!(collect_bound_names(&expr), vec!["x", "y"]);
    }

    #[test]
    fn collect_bound_names_exists_returns_bound_names() {
        let expr = Expr::Exists(vec![bound_var("a"), bound_var("b")], dummy_body());
        assert_eq!(collect_bound_names(&expr), vec!["a", "b"]);
    }

    #[test]
    fn collect_bound_names_ident_returns_empty() {
        let expr = Expr::Ident("foo".to_string(), NameId::INVALID);
        assert!(collect_bound_names(&expr).is_empty());
    }

    #[test]
    fn refcounted_bound_vars_nested_same_name_preserves_outer() {
        // Simulates: \E x \in S : ((\E x \in T : P(x)) /\ Q(x))
        // After inner scope exits, outer x should still be tracked.
        let mut bound_vars: FxHashMap<String, usize> = FxHashMap::default();

        // Outer \E x enters scope
        *bound_vars.entry("x".to_string()).or_insert(0) += 1;
        assert_eq!(bound_vars["x"], 1);

        // Inner \E x enters scope
        *bound_vars.entry("x".to_string()).or_insert(0) += 1;
        assert_eq!(bound_vars["x"], 2);

        // Inner \E x exits scope
        if let Some(count) = bound_vars.get_mut("x") {
            *count -= 1;
            if *count == 0 {
                bound_vars.remove("x");
            }
        }
        // x should still be tracked (count=1 from outer scope)
        assert!(bound_vars.contains_key("x"), "outer x binding leaked");
        assert_eq!(bound_vars["x"], 1);

        // Outer \E x exits scope
        if let Some(count) = bound_vars.get_mut("x") {
            *count -= 1;
            if *count == 0 {
                bound_vars.remove("x");
            }
        }
        // x should now be fully removed
        assert!(
            !bound_vars.contains_key("x"),
            "x should be removed after both scopes exit"
        );
    }

    #[test]
    fn collect_bound_names_tuple_destructuring_includes_pattern_vars() {
        // \E <<x, y>> \in S : body — should bind the synthetic name AND x, y
        let bv = BoundVar {
            name: spanned_str("<<x, y>>"),
            domain: None,
            pattern: Some(BoundPattern::Tuple(vec![
                spanned_str("x"),
                spanned_str("y"),
            ])),
        };
        let expr = Expr::Exists(vec![bv], dummy_body());
        let names = collect_bound_names(&expr);
        assert!(names.contains(&"<<x, y>>".to_string()));
        assert!(names.contains(&"x".to_string()));
        assert!(names.contains(&"y".to_string()));
        assert_eq!(names.len(), 3);
    }
}
