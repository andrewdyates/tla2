// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Operator expansion for pre-enumeration inlining.
//!
//! This pass recursively inlines zero-arg and parameterized operator definitions
//! into the expression tree, eliminating per-state operator lookups during
//! enumeration. It preserves recursion guards and capture-avoidance checks from
//! the legacy implementation.

use rustc_hash::FxHashSet;

use tla_core::ast::{BoundVar, Expr, OpParam, OperatorDef, Substitution};
use tla_core::{expr_mentions_name_v, inlining_is_capture_safe, single_bound_var_names, ExprFold};
use tla_core::{Span, Spanned};

use crate::eval::{apply_substitutions, EvalCtx};

use super::expr_analysis::expr_contains_prime;

/// Pre-expand all operator references in an expression tree.
///
/// This eliminates expensive operator lookups and expression tree cloning during
/// state enumeration by inlining all operator definitions once.
///
/// Part of #207: Performance optimization to reduce operator lookup overhead.
///
/// # Variable Capture Avoidance
///
/// When inlining an operator, if any argument identifier would be captured by a
/// binding in the operator body, we skip inlining that call to avoid incorrect
/// semantics. For example:
///
/// ```tla
/// RemovePending(cmd) == LET filter(c) == c # cmd IN SelectSeq(pending, filter)
/// Next == LET c == 1 IN pending' = RemovePending(c)
/// ```
///
/// Substituting `cmd -> c` naively would create `LET filter(c) == c # c` which
/// incorrectly binds the outer `c` to the inner parameter. By detecting this
/// potential capture and skipping expansion, we preserve correct semantics.
///
/// # Arguments
/// * `ctx` - Evaluation context containing operator definitions
/// * `expr` - The expression to expand
///
/// # Returns
/// A new expression with all operator references replaced by their bodies.
/// Recursive operators and operators with potential capture are NOT expanded.
pub fn expand_operators(ctx: &EvalCtx, expr: &Spanned<Expr>) -> Spanned<Expr> {
    let mut expand = ExpandOperators::new(ctx, false);
    expand.fold_expr(expr.clone())
}

/// Expand operators including those that contain primed variables.
///
/// `expand_operators` skips inlining operators whose bodies contain `Prime`
/// (x') or `UNCHANGED` because the default call sites (guard compilation,
/// constraint evaluation) should not see primed sub-expressions. However,
/// POR dependency extraction NEEDS to see the full action body — including
/// primed assignments and UNCHANGED — to compute read/write sets.
///
/// Part of #3354 Slice 4: replaces the old CompiledAction-tree dependency walk.
pub fn expand_operators_with_primes(ctx: &EvalCtx, expr: &Spanned<Expr>) -> Spanned<Expr> {
    let mut expand = ExpandOperators::new(ctx, true);
    expand.fold_expr(expr.clone())
}

struct ExpandOperators<'a> {
    ctx: &'a EvalCtx,
    expanding: FxHashSet<String>,
    allow_primed: bool,
    local_defs: Vec<Vec<OperatorDef>>,
    /// Tracks bound variable names from enclosing binding constructs (FuncDef,
    /// Choose, SetFilter, SetBuilder, Forall, Exists, Lambda). Prevents
    /// fold_ident_expr from incorrectly inlining a LET definition when the
    /// identifier is actually a bound variable shadowing that LET. Fix for #1558.
    bound_vars: FxHashSet<String>,
}

struct ResolvedOperator<'a> {
    def: &'a OperatorDef,
    key: String,
}

impl<'a> ExpandOperators<'a> {
    fn new(ctx: &'a EvalCtx, allow_primed: bool) -> Self {
        Self {
            ctx,
            expanding: FxHashSet::default(),
            allow_primed,
            local_defs: Vec::new(),
            bound_vars: FxHashSet::default(),
        }
    }

    fn can_inline(&self, def: &OperatorDef) -> bool {
        let has_primes = def.contains_prime || expr_contains_prime(&def.body.node);
        self.allow_primed || !has_primes
    }

    /// Check if a zero-arg operator definition is a self-referential FuncDef.
    /// Such definitions get special LazyFunc treatment at runtime (with
    /// memoization). Inlining them as raw FuncDef expressions would create
    /// `FuncApply(FuncDef(...), args)` which eagerly evaluates the entire
    /// function domain at each call site, bypassing LazyFunc memoization and
    /// causing infinite recursion. Fix for #2741.
    fn is_self_referential_func_def(def: &OperatorDef) -> bool {
        if !def.params.is_empty() {
            return false;
        }
        if let Expr::FuncDef(_, func_body) = &def.body.node {
            expr_mentions_name_v(&func_body.node, def.name.node.as_str())
        } else {
            false
        }
    }

    /// Check if a zero-arg operator body is a FuncDef expression.
    /// FuncDef evaluation is expensive (enumerates entire domain), so inlining
    /// replaces a cached-once-per-state lookup with repeated full re-evaluation.
    /// Non-self-referential, state-dependent FuncDefs (e.g., GameOfLife's `sc`)
    /// should go through eval_ident → eval_zero_arg_cached for per-state caching.
    /// Constant FuncDefs are already blocked by `is_precomputed_constant`.
    /// Fix for #2955.
    fn is_func_def_body(def: &OperatorDef) -> bool {
        def.params.is_empty() && matches!(def.body.node, Expr::FuncDef(_, _))
    }

    /// Check if a zero-arg operator has been precomputed by precompute_constant_operators().
    /// If so, the eval fast path returns the cached value via NameId lookup — inlining
    /// the body would bypass this cache. Part of #2834.
    fn is_precomputed_constant(&self, name: &str) -> bool {
        use tla_core::name_intern::lookup_name_id;
        if let Some(name_id) = lookup_name_id(name) {
            self.ctx.precomputed_constants().contains_key(&name_id)
        } else {
            false
        }
    }

    fn resolve_local_operator(&self, name: &str) -> Option<ResolvedOperator<'_>> {
        self.local_defs
            .iter()
            .enumerate()
            .rev()
            .find_map(|(scope_idx, defs)| {
                defs.iter()
                    .find(|def| def.name.node == name)
                    .map(|def| ResolvedOperator {
                        def,
                        key: format!("let:{scope_idx}:{name}"),
                    })
            })
    }

    fn resolve_global_operator(&self, name: &str) -> Option<ResolvedOperator<'_>> {
        let resolved_name = self.ctx.resolve_op_name(name);
        self.ctx.get_op(resolved_name).map(|def| ResolvedOperator {
            def,
            key: resolved_name.to_string(),
        })
    }

    fn resolve_ident_operator(&self, name: &str) -> Option<ResolvedOperator<'_>> {
        if let Some(local) = self.resolve_local_operator(name) {
            return Some(local);
        }
        if self.ctx.is_config_constant(name) {
            return None;
        }
        self.resolve_global_operator(name)
    }

    fn resolve_apply_operator(&self, name: &str) -> Option<ResolvedOperator<'_>> {
        if let Some(local) = self.resolve_local_operator(name) {
            return Some(local);
        }
        self.resolve_global_operator(name)
    }

    /// Collect all individual variable names from bound variable declarations,
    /// including destructured tuple pattern components (e.g., `<<x, y>>` yields
    /// both `"x"` and `"y"`).
    fn collect_names_from_bounds(bounds: &[BoundVar]) -> Vec<String> {
        bounds.iter().flat_map(single_bound_var_names).collect()
    }

    /// Fold an expression body under a set of bound variable names.
    /// The bound names are added to `self.bound_vars` during the fold and
    /// removed afterwards, preventing `fold_ident_expr` from incorrectly
    /// inlining LET definitions that are shadowed by these bindings.
    fn fold_with_bound_scope(&mut self, names: Vec<String>, body: Spanned<Expr>) -> Spanned<Expr> {
        let added: Vec<String> = names
            .into_iter()
            .filter(|n| self.bound_vars.insert(n.clone()))
            .collect();
        let result = self.fold_expr(body);
        for n in added {
            self.bound_vars.remove(&n);
        }
        result
    }

    fn fold_ident_expr(&mut self, name: String, span: Span) -> Spanned<Expr> {
        // If the identifier is a bound variable from an enclosing binding
        // construct (FuncDef, Choose, Forall, etc.), do not inline — the
        // binding shadows any LET definition with the same name. (#1558)
        let inline_target = if self.bound_vars.contains(&name) {
            None
        } else if let Some(resolved) = self.resolve_ident_operator(name.as_str()) {
            if resolved.def.params.is_empty()
                && !self.expanding.contains(resolved.key.as_str())
                && self.can_inline(resolved.def)
                && !Self::is_self_referential_func_def(resolved.def)
                // Part of #2955: Do not inline zero-arg FuncDef operators.
                // FuncDef evaluation is expensive (enumerates entire domain).
                // Inlining bypasses eval_zero_arg_cached, causing re-evaluation
                // on every reference instead of caching once per state.
                && !Self::is_func_def_body(resolved.def)
                // Part of #2834: Do not inline operators whose values have been
                // precomputed by precompute_constant_operators(). Inlining replaces
                // the Ident("SortedSeqs") with the raw expression body, so at runtime
                // the eval fast path's precomputed_constants lookup (by NameId) is
                // never reached — the expression is re-evaluated from scratch on every
                // state. For expensive constants like SortedSeqs (488K-element set
                // filter), this turns O(1) lookups into O(n) re-evaluations per state.
                && !self.is_precomputed_constant(&name)
            {
                Some((resolved.key, resolved.def.body.clone()))
            } else {
                None
            }
        } else {
            None
        };

        if let Some((key, body)) = inline_target {
            self.expanding.insert(key.clone());
            let expanded = self.fold_expr(body);
            self.expanding.remove(key.as_str());
            return expanded;
        }

        Spanned::new(Expr::Ident(name, tla_core::NameId::INVALID), span)
    }

    #[allow(clippy::if_same_then_else)]
    fn fold_apply_expr(
        &mut self,
        op_expr: Box<Spanned<Expr>>,
        args: Vec<Spanned<Expr>>,
        span: Span,
    ) -> Spanned<Expr> {
        let mut inline_target: Option<(String, Vec<OpParam>, Spanned<Expr>)> = None;
        let mut keep_operator_token = false;

        if let Expr::Ident(op_name, _) = &op_expr.node {
            if let Some(resolved) = self.resolve_apply_operator(op_name) {
                // Part of #2834: Do not inline operators that have complete Rust builtin
                // implementations. Their TLA+ bodies may reference operators from LOCAL
                // INSTANCE'd modules (e.g., FoldFunctionOnSet → MapThenFoldSet from Folds)
                // that are not available in the eval context. At runtime, eval_apply will
                // dispatch to the builtin implementation instead.
                let resolved_name = self.ctx.resolve_op_name(op_name);
                if crate::eval::has_complete_builtin_override(resolved_name, args.len(), self.ctx)
                    || self.expanding.contains(resolved.key.as_str())
                    || !self.can_inline(resolved.def)
                {
                    keep_operator_token = true;
                } else if !inlining_is_capture_safe(resolved.def, &args) {
                    keep_operator_token = true;
                } else {
                    inline_target = Some((
                        resolved.key,
                        resolved.def.params.clone(),
                        resolved.def.body.clone(),
                    ));
                }
            }
        }

        if keep_operator_token {
            let new_args = args.into_iter().map(|arg| self.fold_expr(arg)).collect();
            return Spanned::new(Expr::Apply(op_expr, new_args), span);
        }

        if let Some((key, params, body)) = inline_target {
            // Build substitutions from the original call-site arguments. If we eagerly fold
            // arguments first, LET-bound identifiers can expand to binder-heavy expressions
            // (for example function comprehensions) that get conservatively dropped by
            // capture-avoiding substitution, leaving operator parameters unbound.
            let subs: Vec<Substitution> = params
                .iter()
                .zip(args.iter())
                .map(|(param, arg)| Substitution {
                    from: param.name.clone(),
                    to: arg.clone(),
                })
                .collect();

            let substituted = apply_substitutions(&body, &subs);
            self.expanding.insert(key.clone());
            let expanded = self.fold_expr(substituted);
            self.expanding.remove(key.as_str());
            return expanded;
        }

        Spanned::new(
            Expr::Apply(
                Box::new(self.fold_expr(*op_expr)),
                args.into_iter().map(|arg| self.fold_expr(arg)).collect(),
            ),
            span,
        )
    }

    fn fold_let_expr(
        &mut self,
        defs: Vec<OperatorDef>,
        body: Spanned<Expr>,
        span: Span,
    ) -> Spanned<Expr> {
        // LET definitions are in scope for all definition bodies and the LET body.
        self.local_defs.push(defs.clone());

        let new_defs = defs
            .into_iter()
            .map(|def| OperatorDef {
                name: def.name,
                params: def.params,
                body: self.fold_expr(def.body),
                local: def.local,
                contains_prime: def.contains_prime,
                guards_depend_on_prime: def.guards_depend_on_prime,
                has_primed_param: def.has_primed_param,
                is_recursive: def.is_recursive,
                self_call_count: def.self_call_count,
            })
            .collect();

        let new_body = Box::new(self.fold_expr(body));
        self.local_defs.pop();

        Spanned::new(Expr::Let(new_defs, new_body), span)
    }
}

impl ExprFold for ExpandOperators<'_> {
    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let span = expr.span;
        match expr.node {
            Expr::Ident(name, _) => self.fold_ident_expr(name, span),
            Expr::Apply(op_expr, args) => self.fold_apply_expr(op_expr, args, span),
            Expr::Let(defs, body) => self.fold_let_expr(defs, *body, span),

            // Binding constructs: fold the body under a scope that includes
            // the bound variable names, preventing incorrect LET inlining
            // when a bound variable shadows a LET definition. (#1558)
            Expr::FuncDef(bounds, body) => {
                let names = Self::collect_names_from_bounds(&bounds);
                let new_bounds = self.fold_bound_vars(bounds);
                let new_body = self.fold_with_bound_scope(names, *body);
                Spanned::new(Expr::FuncDef(new_bounds, Box::new(new_body)), span)
            }
            Expr::Forall(bounds, body) => {
                let names = Self::collect_names_from_bounds(&bounds);
                let new_bounds = self.fold_bound_vars(bounds);
                let new_body = self.fold_with_bound_scope(names, *body);
                Spanned::new(Expr::Forall(new_bounds, Box::new(new_body)), span)
            }
            Expr::Exists(bounds, body) => {
                let names = Self::collect_names_from_bounds(&bounds);
                let new_bounds = self.fold_bound_vars(bounds);
                let new_body = self.fold_with_bound_scope(names, *body);
                Spanned::new(Expr::Exists(new_bounds, Box::new(new_body)), span)
            }
            Expr::Choose(bound, body) => {
                let names = single_bound_var_names(&bound);
                let new_bound = self.fold_bound_var(bound);
                let new_body = self.fold_with_bound_scope(names, *body);
                Spanned::new(Expr::Choose(new_bound, Box::new(new_body)), span)
            }
            Expr::SetFilter(bound, body) => {
                let names = single_bound_var_names(&bound);
                let new_bound = self.fold_bound_var(bound);
                let new_body = self.fold_with_bound_scope(names, *body);
                Spanned::new(Expr::SetFilter(new_bound, Box::new(new_body)), span)
            }
            Expr::SetBuilder(body, bounds) => {
                let names = Self::collect_names_from_bounds(&bounds);
                let new_bounds = self.fold_bound_vars(bounds);
                let new_body = self.fold_with_bound_scope(names, *body);
                Spanned::new(Expr::SetBuilder(Box::new(new_body), new_bounds), span)
            }
            Expr::Lambda(params, body) => {
                let names: Vec<String> = params.iter().map(|p| p.node.clone()).collect();
                let new_body = self.fold_with_bound_scope(names, *body);
                Spanned::new(Expr::Lambda(params, Box::new(new_body)), span)
            }

            node => Spanned::new(self.fold_expr_inner(node), span),
        }
    }
}

#[cfg(test)]
#[path = "expand_ops_tests.rs"]
mod tests;
