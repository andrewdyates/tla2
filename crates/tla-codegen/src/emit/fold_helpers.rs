// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    build_param_substitutions, compose_substitutions, instance_from_resolved_operator,
    instantiate_substitutions, CodegenModuleEnv, ResolvedInstance, ResolvedOperator,
    ResolvedOperatorOrigin,
};
use std::collections::{HashMap, HashSet};
use tla_core::ast::{BoundVar, Expr, ModuleTarget, OperatorDef, Substitution};
use tla_core::name_intern::NameId;
use tla_core::span::{Span, Spanned};
use tla_core::{apply_substitutions_v, ExprFold};

/// Operator expansion for codegen using local scopes plus dependency-aware module lookup.
pub(super) struct ExpandOperatorsCodegen<'a> {
    /// Layered operator environment for LET-bound defs and the current module's own defs.
    pub(super) env: Vec<HashMap<String, OperatorDef>>,
    pub(super) expanding: HashSet<String>,
    pub(super) bound: HashSet<String>,
    pub(super) module_env: &'a CodegenModuleEnv,
    pub(super) state_vars: &'a HashSet<String>,
    pub(super) module_name: String,
}

impl<'a> ExpandOperatorsCodegen<'a> {
    pub(super) fn new(
        module_env: &'a CodegenModuleEnv,
        state_vars: &'a HashSet<String>,
        module_name: &str,
    ) -> Self {
        Self {
            env: Vec::new(),
            expanding: HashSet::new(),
            bound: HashSet::new(),
            module_env,
            state_vars,
            module_name: module_name.to_string(),
        }
    }

    fn lookup_operator(&self, name: &str) -> Option<ResolvedOperator> {
        for scope in self.env.iter().rev() {
            if let Some(op) = scope.get(name) {
                return Some(ResolvedOperator {
                    def: op.clone(),
                    module_name: self.module_name.clone(),
                    substitutions: Vec::new(),
                    origin: ResolvedOperatorOrigin::LocalEnv,
                });
            }
        }
        self.module_env
            .resolve_operator_in_module_scope(&self.module_name, name)
    }

    fn fold_expr_with_bound_scope<F>(&mut self, f: F) -> Expr
    where
        F: FnOnce(&mut Self) -> Expr,
    {
        let saved_bound = self.bound.clone();
        let result = f(self);
        self.bound = saved_bound;
        result
    }

    fn with_isolated_module_scope<F>(&mut self, module_name: String, f: F) -> Expr
    where
        F: FnOnce(&mut Self) -> Expr,
    {
        let saved = std::mem::replace(&mut self.module_name, module_name);
        let saved_env = std::mem::take(&mut self.env);
        let saved_bound = std::mem::take(&mut self.bound);
        let result = f(self);
        self.bound = saved_bound;
        self.env = saved_env;
        self.module_name = saved;
        result
    }

    fn materialize_substitutions_in_caller_scope(
        &mut self,
        substitutions: &[Substitution],
        bound_names: &[String],
    ) -> Vec<Substitution> {
        let saved_bound = self.bound.clone();
        self.bound.extend(bound_names.iter().cloned());
        let materialized = substitutions
            .iter()
            .map(|sub| Substitution {
                from: sub.from.clone(),
                to: self.fold_expr(sub.to.clone()),
            })
            .collect();
        self.bound = saved_bound;
        materialized
    }

    fn fold_expr_with_extra_bound_names(
        &mut self,
        expr: Spanned<Expr>,
        bound_names: &[String],
    ) -> Spanned<Expr> {
        let saved_bound = self.bound.clone();
        self.bound.extend(bound_names.iter().cloned());
        let folded = self.fold_expr(expr);
        self.bound = saved_bound;
        folded
    }

    fn expand_resolved_operator(
        &mut self,
        resolved: ResolvedOperator,
        call_subs: &[Substitution],
        outer_subs: Option<&[Substitution]>,
    ) -> Expr {
        let param_names: Vec<String> = resolved
            .def
            .params
            .iter()
            .map(|param| param.name.node.clone())
            .collect();
        let mut body = match resolved.origin {
            ResolvedOperatorOrigin::ModuleScope => {
                let body = resolved.def.body.clone();
                let param_names = param_names.clone();
                Spanned::new(
                    self.with_isolated_module_scope(resolved.module_name.clone(), |this| {
                        this.fold_expr_with_extra_bound_names(body, &param_names)
                            .node
                    }),
                    Span::dummy(),
                )
            }
            ResolvedOperatorOrigin::LocalEnv => {
                self.fold_expr_with_extra_bound_names(resolved.def.body.clone(), &param_names)
            }
        };

        let call_subs = self.materialize_substitutions_in_caller_scope(call_subs, &[]);
        if !call_subs.is_empty() {
            body = apply_substitutions_v(&body, &call_subs);
        };
        let effective_subs = compose_substitutions(&resolved.substitutions, outer_subs);
        if !effective_subs.is_empty() {
            body = apply_substitutions_v(&body, &effective_subs);
        }
        body.node
    }

    fn resolve_instance_from_operator(
        &mut self,
        resolved: ResolvedOperator,
        actuals: Option<&[Spanned<Expr>]>,
    ) -> Option<ResolvedInstance> {
        if matches!(resolved.origin, ResolvedOperatorOrigin::ModuleScope) {
            return instance_from_resolved_operator(resolved, actuals, self.module_env);
        }

        let Expr::InstanceExpr(module_name, instance_subs) = &resolved.def.body.node else {
            return None;
        };

        let param_names: Vec<String> = resolved
            .def
            .params
            .iter()
            .map(|param| param.name.node.clone())
            .collect();
        let instance_subs =
            self.materialize_substitutions_in_caller_scope(instance_subs, &param_names);
        let substitutions = match actuals {
            Some(actuals) => {
                if resolved.def.params.len() != actuals.len() {
                    return None;
                }
                let param_subs = build_param_substitutions(&resolved.def.params, actuals);
                instantiate_substitutions(&instance_subs, &param_subs)
            }
            None => {
                if !resolved.def.params.is_empty() {
                    return None;
                }
                instance_subs
            }
        };

        Some(ResolvedInstance {
            module_name: module_name.clone(),
            substitutions: compose_substitutions(
                &substitutions,
                Some(resolved.substitutions.as_slice()),
            ),
        })
    }

    fn resolve_named_target(&mut self, name: &str) -> Option<ResolvedInstance> {
        if let Some(resolved) = self.lookup_operator(name) {
            if let Some(instance) = self.resolve_instance_from_operator(resolved, None) {
                return Some(instance);
            }
        }

        if self.module_env.module(name).is_some() {
            return Some(ResolvedInstance {
                module_name: name.to_string(),
                substitutions: Vec::new(),
            });
        }

        None
    }

    fn resolve_target(&mut self, target: &ModuleTarget) -> Option<ResolvedInstance> {
        match target {
            ModuleTarget::Named(name) => self.resolve_named_target(name),
            ModuleTarget::Parameterized(name, actuals) => {
                let actuals = self.fold_vec(actuals.clone());
                let resolved = self.lookup_operator(name)?;
                self.resolve_instance_from_operator(resolved, Some(actuals.as_slice()))
            }
            ModuleTarget::Chained(base_expr) => self.resolve_chained_target(base_expr),
        }
    }

    fn resolve_chained_target(&mut self, base_expr: &Spanned<Expr>) -> Option<ResolvedInstance> {
        let Expr::ModuleRef(base_target, inst_name, inst_args) = &base_expr.node else {
            return None;
        };

        let base_instance = self.resolve_target(base_target)?;
        let resolved = self
            .module_env
            .resolve_exported_operator(&base_instance.module_name, inst_name)?;
        let inst_args = self.fold_vec(inst_args.clone());
        let chained = self.resolve_instance_from_operator(resolved, Some(inst_args.as_slice()))?;

        Some(ResolvedInstance {
            module_name: chained.module_name,
            substitutions: compose_substitutions(
                &chained.substitutions,
                Some(base_instance.substitutions.as_slice()),
            ),
        })
    }
}

impl ExprFold for ExpandOperatorsCodegen<'_> {
    fn fold_expr(&mut self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let result_node = match expr.node {
            Expr::Ident(name, name_id) => {
                if self.bound.contains(&name) || self.state_vars.contains(&name) {
                    Expr::Ident(name, name_id)
                } else if let Some(resolved) = self.lookup_operator(&name) {
                    if !resolved.def.params.is_empty()
                        || matches!(&resolved.def.body.node, Expr::InstanceExpr(..))
                    {
                        Expr::Ident(name, name_id)
                    } else if resolved.def.is_recursive {
                        Expr::Apply(
                            Box::new(Spanned::new(Expr::Ident(name, name_id), Span::dummy())),
                            Vec::new(),
                        )
                    } else {
                        let key = format!("{}::{}", resolved.module_name, resolved.def.name.node);
                        if !self.expanding.insert(key.clone()) {
                            Expr::Ident(name, name_id)
                        } else {
                            let expanded = self.expand_resolved_operator(resolved, &[], None);
                            self.expanding.remove(&key);
                            expanded
                        }
                    }
                } else {
                    Expr::Ident(name, name_id)
                }
            }
            Expr::Apply(op_expr, args) => {
                if let Expr::Ident(name, _) = &op_expr.node {
                    if !self.bound.contains(name) && !self.state_vars.contains(name) {
                        if let Some(resolved) = self.lookup_operator(name) {
                            if !matches!(&resolved.def.body.node, Expr::InstanceExpr(..))
                                && resolved.def.params.len() == args.len()
                                && resolved.def.params.iter().all(|p| p.arity == 0)
                            {
                                if resolved.def.is_recursive {
                                    let args_expanded = self.fold_vec(args);
                                    return Spanned::new(
                                        Expr::Apply(
                                            Box::new(Spanned::new(
                                                Expr::Ident(name.clone(), NameId::INVALID),
                                                Span::dummy(),
                                            )),
                                            args_expanded,
                                        ),
                                        Span::dummy(),
                                    );
                                }
                                let key =
                                    format!("{}::{}", resolved.module_name, resolved.def.name.node);
                                if self.expanding.insert(key.clone()) {
                                    let call_subs =
                                        build_param_substitutions(&resolved.def.params, &args);
                                    let expanded =
                                        self.expand_resolved_operator(resolved, &call_subs, None);
                                    self.expanding.remove(&key);
                                    return Spanned::new(expanded, Span::dummy());
                                }
                            }
                        }
                    }
                }

                let op_expanded = self.fold_expr(*op_expr);
                let args_expanded = self.fold_vec(args);
                Expr::Apply(Box::new(op_expanded), args_expanded)
            }
            Expr::ModuleRef(target, op_name, args) => {
                let Some(instance) = self.resolve_target(&target) else {
                    return Spanned::new(
                        Expr::ModuleRef(target, op_name, self.fold_vec(args)),
                        Span::dummy(),
                    );
                };
                let Some(resolved) = self
                    .module_env
                    .resolve_exported_operator(&instance.module_name, &op_name)
                else {
                    return Spanned::new(
                        Expr::ModuleRef(target, op_name, self.fold_vec(args)),
                        Span::dummy(),
                    );
                };
                if resolved.def.params.len() != args.len()
                    || !resolved.def.params.iter().all(|p| p.arity == 0)
                {
                    return Spanned::new(
                        Expr::ModuleRef(target, op_name, self.fold_vec(args)),
                        Span::dummy(),
                    );
                }

                if resolved.def.is_recursive {
                    let args_expanded = self.fold_vec(args);
                    return Spanned::new(
                        Expr::Apply(
                            Box::new(Spanned::new(
                                Expr::Ident(resolved.def.name.node.clone(), NameId::INVALID),
                                Span::dummy(),
                            )),
                            args_expanded,
                        ),
                        Span::dummy(),
                    );
                }

                let key = format!("{}::{}", resolved.module_name, resolved.def.name.node);
                if !self.expanding.insert(key.clone()) {
                    return Spanned::new(
                        Expr::ModuleRef(target, op_name, self.fold_vec(args)),
                        Span::dummy(),
                    );
                }

                let call_subs = build_param_substitutions(&resolved.def.params, &args);
                let expanded = self.expand_resolved_operator(
                    resolved,
                    &call_subs,
                    Some(instance.substitutions.as_slice()),
                );
                self.expanding.remove(&key);
                expanded
            }
            Expr::SubstIn(substitutions, body) => {
                let substituted = apply_substitutions_v(&body, &substitutions);
                self.fold_expr(substituted).node
            }
            Expr::Lambda(params, body) => self.fold_expr_with_bound_scope(|this| {
                for param in &params {
                    this.bound.insert(param.node.clone());
                }
                let body_expanded = this.fold_expr(*body);
                Expr::Lambda(params, Box::new(body_expanded))
            }),
            Expr::Forall(bounds, body) => self.fold_expr_with_bound_scope(|this| {
                let bounds = this.fold_bound_vars(bounds);
                let body = this.fold_expr(*body);
                Expr::Forall(bounds, Box::new(body))
            }),
            Expr::Exists(bounds, body) => self.fold_expr_with_bound_scope(|this| {
                let bounds = this.fold_bound_vars(bounds);
                let body = this.fold_expr(*body);
                Expr::Exists(bounds, Box::new(body))
            }),
            Expr::Choose(bound, body) => self.fold_expr_with_bound_scope(|this| {
                let bound = this.fold_bound_var(bound);
                let body = this.fold_expr(*body);
                Expr::Choose(bound, Box::new(body))
            }),
            Expr::SetBuilder(body, bounds) => self.fold_expr_with_bound_scope(|this| {
                let bounds = this.fold_bound_vars(bounds);
                let body = this.fold_expr(*body);
                Expr::SetBuilder(Box::new(body), bounds)
            }),
            Expr::SetFilter(bound, body) => self.fold_expr_with_bound_scope(|this| {
                let bound = this.fold_bound_var(bound);
                let body = this.fold_expr(*body);
                Expr::SetFilter(bound, Box::new(body))
            }),
            Expr::FuncDef(bounds, body) => self.fold_expr_with_bound_scope(|this| {
                let bounds = this.fold_bound_vars(bounds);
                let body = this.fold_expr(*body);
                Expr::FuncDef(bounds, Box::new(body))
            }),
            Expr::Let(defs, body) => {
                let local_ops: HashMap<String, OperatorDef> = defs
                    .iter()
                    .map(|d| (d.name.node.clone(), d.clone()))
                    .collect();
                self.env.push(local_ops);
                let result = self.fold_expr(*body).node;
                self.env.pop();
                result
            }
            _ => self.fold_expr_inner(expr.node),
        };
        Spanned::new(result_node, Span::dummy())
    }

    fn fold_ident(&mut self, name: String, name_id: NameId) -> Expr {
        Expr::Ident(name, name_id)
    }

    fn fold_bound_var(&mut self, bv: BoundVar) -> BoundVar {
        let domain = bv.domain.map(|d| Box::new(self.fold_expr(*d)));
        self.bound.insert(bv.name.node.clone());
        BoundVar {
            name: bv.name,
            domain,
            pattern: bv.pattern,
        }
    }
}
