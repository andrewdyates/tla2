// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::lowerer::{Lowerer, ResolutionGuard};
use super::scope::{LoweringScope, ResolvedExpr};
use super::{find_operator, is_instance_expr};
use crate::error::TirLowerError;
use std::collections::{HashSet, VecDeque};
use tla_core::ast::{Expr, Module, ModuleTarget, OperatorDef, Unit};
use tla_core::{Span, Spanned};

struct ResolvedOperator<'a> {
    scope: LoweringScope<'a>,
    def: &'a OperatorDef,
}

impl<'a> Lowerer<'a> {
    pub(super) fn resolve_target(
        &self,
        scope: &LoweringScope<'a>,
        target: &ModuleTarget,
        span: Span,
    ) -> Result<LoweringScope<'a>, TirLowerError> {
        match target {
            ModuleTarget::Named(name) => {
                if let Some(bound) = scope.lookup_binding(name) {
                    return self.resolve_instance_expr(&bound.scope, &bound.expr, name, span);
                }

                if let Some(resolved) = self.lookup_instance_operator(scope, name) {
                    if resolved.def.params.is_empty() {
                        return self.resolve_instance_expr(
                            &resolved.scope,
                            &resolved.def.body,
                            name,
                            span,
                        );
                    }
                }

                let module =
                    self.env
                        .module(name)
                        .ok_or_else(|| TirLowerError::UndefinedModule {
                            name: name.clone(),
                            span,
                        })?;
                Ok(scope.with_module(module))
            }
            ModuleTarget::Parameterized(name, params) => {
                let resolved = self.lookup_instance_operator(scope, name).ok_or_else(|| {
                    TirLowerError::UndefinedModule {
                        name: name.clone(),
                        span,
                    }
                })?;
                if resolved.def.params.len() != params.len() {
                    return Err(TirLowerError::ArityMismatch {
                        module: resolved.scope.module().name.node.clone(),
                        operator: name.clone(),
                        expected: resolved.def.params.len(),
                        got: params.len(),
                        span,
                    });
                }

                let param_scope = resolved.scope.with_bindings_from(
                    resolved.scope.module(),
                    scope,
                    resolved
                        .def
                        .params
                        .iter()
                        .zip(params.iter())
                        .map(|(param, arg)| (param.name.node.clone(), arg.clone())),
                );
                self.resolve_instance_expr(&param_scope, &resolved.def.body, name, span)
            }
            ModuleTarget::Chained(base) => {
                let Expr::ModuleRef(base_target, operator, args) = &base.node else {
                    return Err(TirLowerError::InvalidChainedTarget { span });
                };
                let base_scope = self.resolve_target(scope, base_target, base.span)?;
                self.resolve_operator_as_instance(scope, &base_scope, operator, args, base.span)
            }
        }
    }

    fn resolve_operator_as_instance(
        &self,
        callsite_scope: &LoweringScope<'a>,
        target_scope: &LoweringScope<'a>,
        operator: &str,
        args: &[Spanned<Expr>],
        span: Span,
    ) -> Result<LoweringScope<'a>, TirLowerError> {
        let resolved =
            self.resolve_operator_expr(callsite_scope, target_scope, operator, args, span)?;
        self.resolve_instance_expr(&resolved.scope, &resolved.expr, operator, span)
    }

    pub(super) fn resolve_operator_expr(
        &self,
        callsite_scope: &LoweringScope<'a>,
        target_scope: &LoweringScope<'a>,
        operator: &str,
        args: &[Spanned<Expr>],
        span: Span,
    ) -> Result<ResolvedExpr<'a>, TirLowerError> {
        if let Some(resolved) = self.lookup_operator_definition(target_scope, operator) {
            let _guard = self.enter_resolution(resolved.scope.module(), operator, span)?;
            if resolved.def.params.len() != args.len() {
                return Err(TirLowerError::ArityMismatch {
                    module: resolved.scope.module().name.node.clone(),
                    operator: operator.to_string(),
                    expected: resolved.def.params.len(),
                    got: args.len(),
                    span,
                });
            }

            let scope = resolved.scope.with_bindings_from(
                resolved.scope.module(),
                callsite_scope,
                resolved
                    .def
                    .params
                    .iter()
                    .zip(args.iter())
                    .map(|(param, arg)| (param.name.node.clone(), arg.clone())),
            );
            return Ok(ResolvedExpr {
                scope,
                expr: resolved.def.body.clone(),
            });
        }

        if args.is_empty() {
            if let Some(bound) = target_scope.lookup_binding(operator) {
                return Ok(ResolvedExpr {
                    scope: bound.scope,
                    expr: bound.expr,
                });
            }
        }

        Err(TirLowerError::UndefinedOperator {
            module: target_scope.module().name.node.clone(),
            operator: operator.to_string(),
            span,
        })
    }

    fn resolve_instance_expr(
        &self,
        scope: &LoweringScope<'a>,
        expr: &Spanned<Expr>,
        operator: &str,
        span: Span,
    ) -> Result<LoweringScope<'a>, TirLowerError> {
        match &expr.node {
            Expr::InstanceExpr(module_name, substitutions) => {
                let module =
                    self.env
                        .module(module_name)
                        .ok_or_else(|| TirLowerError::UndefinedModule {
                            name: module_name.clone(),
                            span,
                        })?;
                Ok(scope.with_bindings_from(
                    module,
                    scope,
                    substitutions
                        .iter()
                        .map(|sub| (sub.from.node.clone(), sub.to.clone())),
                ))
            }
            Expr::SubstIn(substitutions, body) => {
                let inner_scope = scope.with_same_module_substitutions(substitutions);
                self.resolve_instance_expr(&inner_scope, body, operator, span)
            }
            _ => Err(TirLowerError::ExpectedInstance {
                module: scope.module().name.node.clone(),
                operator: operator.to_string(),
                span,
            }),
        }
    }

    fn enter_resolution(
        &self,
        module: &Module,
        operator: &str,
        span: Span,
    ) -> Result<ResolutionGuard<'a, '_>, TirLowerError> {
        let key = (module.name.node.clone(), operator.to_string());
        let mut stack = self.resolution_stack.borrow_mut();
        if stack.contains(&key) {
            return Err(TirLowerError::RecursiveModuleRef {
                module: key.0,
                operator: key.1,
                span,
            });
        }
        stack.push(key);
        drop(stack);
        Ok(ResolutionGuard { lowerer: self })
    }

    fn lookup_instance_operator(
        &self,
        scope: &LoweringScope<'a>,
        name: &str,
    ) -> Option<ResolvedOperator<'a>> {
        self.lookup_operator_definition(scope, name)
            .filter(|resolved| is_instance_expr(&resolved.def.body))
    }

    /// Check if the operator is defined locally (root module or LET/LOCAL scope),
    /// excluding imported modules (EXTENDS/INSTANCE). This is used by the
    /// unsupported-builtin gate to distinguish user-defined operators that shadow
    /// a builtin name from stdlib definitions that the TIR evaluator cannot handle.
    ///
    /// Part of #3460: `has_operator_definition` returns true for `Append` when
    /// the spec `EXTENDS Sequences`, because `lookup_imported_operator` finds the
    /// stdlib definition. This caused the builtin gate to be bypassed.
    pub(super) fn has_local_operator_definition(
        &self,
        scope: &LoweringScope<'a>,
        name: &str,
    ) -> bool {
        // Check root module definitions (user-defined operators)
        if find_operator(scope.module(), name).is_some() {
            return true;
        }
        // Check LET/LOCAL bound operators
        scope.lookup_operator(name).is_some()
    }

    fn lookup_operator_definition(
        &self,
        scope: &LoweringScope<'a>,
        name: &str,
    ) -> Option<ResolvedOperator<'a>> {
        if let Some(def) = find_operator(scope.module(), name) {
            return Some(ResolvedOperator {
                scope: scope.clone(),
                def,
            });
        }

        if let Some(bound) = scope.lookup_operator(name) {
            return Some(ResolvedOperator {
                scope: bound.scope,
                def: bound.def,
            });
        }

        self.lookup_imported_operator(scope, name)
    }

    fn lookup_imported_operator(
        &self,
        scope: &LoweringScope<'a>,
        name: &str,
    ) -> Option<ResolvedOperator<'a>> {
        self.imported_modules_in_resolution_order(scope.module())
            .into_iter()
            .find_map(|module| {
                find_operator(module, name).map(|def| ResolvedOperator {
                    scope: scope.with_module(module),
                    def,
                })
            })
    }

    fn imported_modules_in_resolution_order(&self, module: &'a Module) -> Vec<&'a Module> {
        let mut extends_seen: HashSet<String> = HashSet::new();
        let mut extends_order = Vec::new();

        fn visit_extends<'a>(
            env: &'a crate::lower::TirLoweringEnv<'a>,
            module: &'a Module,
            seen: &mut HashSet<String>,
            out: &mut Vec<&'a Module>,
        ) {
            for ext in &module.extends {
                if !seen.insert(ext.node.clone()) {
                    continue;
                }
                let Some(loaded) = env.module(&ext.node) else {
                    continue;
                };
                visit_extends(env, loaded, seen, out);
                out.push(loaded);
            }
        }

        visit_extends(self.env, module, &mut extends_seen, &mut extends_order);

        fn collect_standalone_instances<'a>(
            env: &'a crate::lower::TirLoweringEnv<'a>,
            module: &'a Module,
            queue: &mut VecDeque<&'a Module>,
        ) {
            for unit in &module.units {
                if let Unit::Instance(inst) = &unit.node {
                    if let Some(loaded) = env.module(&inst.module.node) {
                        queue.push_back(loaded);
                    }
                }
            }
        }

        let mut instance_seen: HashSet<String> = HashSet::new();
        let mut instance_order = Vec::new();
        let mut queue = VecDeque::new();
        collect_standalone_instances(self.env, module, &mut queue);
        for extended in &extends_order {
            collect_standalone_instances(self.env, extended, &mut queue);
        }

        while let Some(next) = queue.pop_front() {
            if !instance_seen.insert(next.name.node.clone()) {
                continue;
            }
            instance_order.push(next);
            collect_standalone_instances(self.env, next, &mut queue);
        }

        let extends_set: HashSet<&str> =
            extends_order.iter().map(|m| m.name.node.as_str()).collect();
        instance_order.retain(|module| !extends_set.contains(module.name.node.as_str()));
        extends_order.extend(instance_order);
        extends_order
    }
}
