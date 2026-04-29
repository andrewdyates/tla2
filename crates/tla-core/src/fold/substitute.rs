// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::span::{Span, Spanned};

use super::free_vars::{bound_names_for_substitution, filter_substitutions_capture_avoiding};
use super::ExprFold;

/// Controls span behavior for substitution replacements.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanPolicy {
    /// Keep the replacement expression's original span.
    Preserve,
    /// Force substituted nodes to use `Span::dummy()`.
    Dummy,
    /// Force ALL output nodes (not just substituted ones) to use `Span::dummy()`.
    /// Required by liveness to prevent LITERAL_CACHE collisions (#575).
    DummyAll,
}

impl SpanPolicy {
    fn apply_to(self, replacement: &Spanned<Expr>) -> Spanned<Expr> {
        match self {
            Self::Preserve => replacement.clone(),
            Self::Dummy | Self::DummyAll => Spanned::new(replacement.node.clone(), Span::dummy()),
        }
    }

    fn output_span(self, original: Span) -> Span {
        match self {
            Self::Preserve | Self::Dummy => original,
            Self::DummyAll => Span::dummy(),
        }
    }
}

/// Capture-avoiding expression substitution over all `Expr` variants.
pub struct SubstituteExpr<'a> {
    pub subs: HashMap<&'a str, &'a Spanned<Expr>>,
    pub span_policy: SpanPolicy,
}

impl<'a> SubstituteExpr<'a> {
    fn with_subs(&self, subs: HashMap<&'a str, &'a Spanned<Expr>>) -> Self {
        Self {
            subs,
            span_policy: self.span_policy,
        }
    }

    fn replacement_for(&self, name: &str) -> Option<Spanned<Expr>> {
        self.subs
            .get(name)
            .map(|replacement| self.span_policy.apply_to(replacement))
    }
}

impl ExprFold for SubstituteExpr<'_> {
    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let span = expr.span;
        let new_node = match expr.node {
            Expr::Ident(name, name_id) => {
                if let Some(replacement) = self.replacement_for(name.as_str()) {
                    return replacement;
                }
                Expr::Ident(name, name_id)
            }
            // Part of #2996: handle StateVar nodes for INSTANCE WITH substitutions.
            // After resolve_state_vars_in_loaded_ops() rewrites Ident→StateVar during
            // checker setup, apply_substitutions must also match StateVar names against
            // substitution targets. Without this, INSTANCE WITH state_var <- expr
            // silently skips state variable substitution in compiled guard, liveness,
            // and enumerator paths.
            Expr::StateVar(name, idx, name_id) => {
                if let Some(replacement) = self.replacement_for(name.as_str()) {
                    return replacement;
                }
                Expr::StateVar(name, idx, name_id)
            }
            Expr::Forall(bounds, body) => {
                let bound_names: HashSet<_> = bounds
                    .iter()
                    .flat_map(bound_names_for_substitution)
                    .collect();
                let filtered_subs = filter_substitutions_capture_avoiding(&self.subs, &bound_names);
                let new_bounds = bounds
                    .into_iter()
                    .map(|bound| BoundVar {
                        name: bound.name,
                        pattern: bound.pattern,
                        domain: bound.domain.map(|domain| {
                            let mut sub = self.with_subs(self.subs.clone());
                            Box::new(sub.fold_expr(*domain))
                        }),
                    })
                    .collect();
                let mut body_sub = self.with_subs(filtered_subs);
                Expr::Forall(new_bounds, Box::new(body_sub.fold_expr(*body)))
            }
            Expr::Exists(bounds, body) => {
                let bound_names: HashSet<_> = bounds
                    .iter()
                    .flat_map(bound_names_for_substitution)
                    .collect();
                let filtered_subs = filter_substitutions_capture_avoiding(&self.subs, &bound_names);
                let new_bounds = bounds
                    .into_iter()
                    .map(|bound| BoundVar {
                        name: bound.name,
                        pattern: bound.pattern,
                        domain: bound.domain.map(|domain| {
                            let mut sub = self.with_subs(self.subs.clone());
                            Box::new(sub.fold_expr(*domain))
                        }),
                    })
                    .collect();
                let mut body_sub = self.with_subs(filtered_subs);
                Expr::Exists(new_bounds, Box::new(body_sub.fold_expr(*body)))
            }
            Expr::Choose(bound, body) => {
                let bound_names: HashSet<_> =
                    bound_names_for_substitution(&bound).into_iter().collect();
                let filtered_subs = filter_substitutions_capture_avoiding(&self.subs, &bound_names);
                let new_bound = BoundVar {
                    name: bound.name,
                    pattern: bound.pattern,
                    domain: bound.domain.map(|domain| {
                        let mut sub = self.with_subs(self.subs.clone());
                        Box::new(sub.fold_expr(*domain))
                    }),
                };
                let mut body_sub = self.with_subs(filtered_subs);
                Expr::Choose(new_bound, Box::new(body_sub.fold_expr(*body)))
            }
            Expr::Let(defs, body) => {
                let def_names: HashSet<_> = defs.iter().map(|def| def.name.node.as_str()).collect();
                let filtered_subs = filter_substitutions_capture_avoiding(&self.subs, &def_names);
                let new_defs = defs
                    .into_iter()
                    .map(|def| {
                        let param_names: HashSet<_> = def
                            .params
                            .iter()
                            .map(|param| param.name.node.as_str())
                            .collect();
                        let body_subs = if param_names.is_empty() {
                            self.subs.clone()
                        } else {
                            filter_substitutions_capture_avoiding(&self.subs, &param_names)
                        };
                        let mut def_sub = self.with_subs(body_subs);
                        OperatorDef {
                            name: def.name,
                            params: def.params,
                            body: def_sub.fold_expr(def.body),
                            local: def.local,
                            contains_prime: def.contains_prime,
                            guards_depend_on_prime: def.guards_depend_on_prime,
                            has_primed_param: def.has_primed_param,
                            is_recursive: def.is_recursive,
                            self_call_count: def.self_call_count,
                        }
                    })
                    .collect();
                let mut body_sub = self.with_subs(filtered_subs);
                Expr::Let(new_defs, Box::new(body_sub.fold_expr(*body)))
            }
            Expr::FuncDef(bounds, body) => {
                let bound_names: HashSet<_> = bounds
                    .iter()
                    .flat_map(bound_names_for_substitution)
                    .collect();
                let filtered_subs = filter_substitutions_capture_avoiding(&self.subs, &bound_names);
                let new_bounds = bounds
                    .into_iter()
                    .map(|bound| BoundVar {
                        name: bound.name,
                        pattern: bound.pattern,
                        domain: bound.domain.map(|domain| {
                            let mut sub = self.with_subs(self.subs.clone());
                            Box::new(sub.fold_expr(*domain))
                        }),
                    })
                    .collect();
                let mut body_sub = self.with_subs(filtered_subs);
                Expr::FuncDef(new_bounds, Box::new(body_sub.fold_expr(*body)))
            }
            Expr::SetBuilder(body, bounds) => {
                let bound_names: HashSet<_> = bounds
                    .iter()
                    .flat_map(bound_names_for_substitution)
                    .collect();
                let filtered_subs = filter_substitutions_capture_avoiding(&self.subs, &bound_names);
                let new_bounds = bounds
                    .into_iter()
                    .map(|bound| BoundVar {
                        name: bound.name,
                        pattern: bound.pattern,
                        domain: bound.domain.map(|domain| {
                            let mut sub = self.with_subs(self.subs.clone());
                            Box::new(sub.fold_expr(*domain))
                        }),
                    })
                    .collect();
                let mut body_sub = self.with_subs(filtered_subs);
                Expr::SetBuilder(Box::new(body_sub.fold_expr(*body)), new_bounds)
            }
            Expr::SetFilter(bound, pred) => {
                let bound_names: HashSet<_> =
                    bound_names_for_substitution(&bound).into_iter().collect();
                let filtered_subs = filter_substitutions_capture_avoiding(&self.subs, &bound_names);
                let new_bound = BoundVar {
                    name: bound.name,
                    pattern: bound.pattern,
                    domain: bound.domain.map(|domain| {
                        let mut sub = self.with_subs(self.subs.clone());
                        Box::new(sub.fold_expr(*domain))
                    }),
                };
                let mut body_sub = self.with_subs(filtered_subs);
                Expr::SetFilter(new_bound, Box::new(body_sub.fold_expr(*pred)))
            }
            Expr::Lambda(params, body) => {
                let param_names: HashSet<_> =
                    params.iter().map(|param| param.node.as_str()).collect();
                let filtered_subs = filter_substitutions_capture_avoiding(&self.subs, &param_names);
                let mut body_sub = self.with_subs(filtered_subs);
                Expr::Lambda(params, Box::new(body_sub.fold_expr(*body)))
            }
            other => self.fold_expr_inner(other),
        };
        Spanned::new(new_node, self.span_policy.output_span(span))
    }
}

/// Replace all `@` identifiers with a provided expression.
///
/// Respects EXCEPT scoping: `@` inside a nested EXCEPT spec's value expression
/// is scoped to the inner EXCEPT (not the outer one), so it is NOT replaced.
/// Only `@` at the current scope level (including the base expression of nested
/// EXCEPTs) is substituted. This matches TLA+ semantics where each EXCEPT level
/// binds its own `@` to the old value at that path.
pub struct SubstituteAt<'a> {
    pub replacement: &'a Spanned<Expr>,
}

impl ExprFold for SubstituteAt<'_> {
    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let span = expr.span;
        let new_node = match expr.node {
            Expr::Ident(name, _) if name == "@" => return self.replacement.clone(),
            other => self.fold_expr_inner(other),
        };
        Spanned::new(new_node, span)
    }

    /// Override to stop `@` substitution at EXCEPT scope boundaries.
    ///
    /// In `[f EXCEPT ![i] = [@ EXCEPT !.field = [@ EXCEPT ![j] = v]]]`:
    /// - The outer `@` (base of middle EXCEPT) refers to `f[i]` -> replaced
    /// - The middle `@` (base of inner EXCEPT) refers to `f[i].field` -> not replaced
    /// - `@` in path index expressions is still replaced (same scope)
    fn fold_except_specs(&mut self, specs: Vec<ExceptSpec>) -> Vec<ExceptSpec> {
        specs
            .into_iter()
            .map(|spec| ExceptSpec {
                path: spec
                    .path
                    .into_iter()
                    .map(|elem| match elem {
                        ExceptPathElement::Index(idx) => {
                            ExceptPathElement::Index(self.fold_expr(idx))
                        }
                        ExceptPathElement::Field(f) => ExceptPathElement::Field(f),
                    })
                    .collect(),
                // Do NOT fold the value: `@` in the value expression is bound by
                // THIS EXCEPT level, not the outer one being substituted.
                value: spec.value,
            })
            .collect()
    }
}
