// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared module-reference operator resolution for direct and chained selectors.

use super::super::{eval, EvalCtx, EvalError, EvalResult, InstanceInfo, OpEnv};
use super::module_ref::build_lazy_subst_bindings;
use super::module_ref_cache::{ModuleRefScopeEntry, ModuleRefScopeKey, MODULE_REF_CACHES};
use crate::binding_chain::BindingValue;
use crate::eval_dispatch::EMPTY_EAGER_SUBST;
use crate::value::Value;
use std::sync::Arc;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::name_intern::{intern_name, NameId};
use tla_core::{Span, Spanned};

pub(crate) struct ResolvedModuleRefOperator {
    pub(crate) op_def: Arc<OperatorDef>,
    pub(crate) eval_ctx: EvalCtx,
}

/// Resolve `Instance!Op(args)` to its operator definition plus the evaluation scope needed
/// to interpret the body. This mirrors the operator-def path in `eval_module_ref` so chained
/// selectors like `Instance!Inv!P0` can reuse the same INSTANCE semantics.
pub(crate) fn try_resolve_module_ref_operator(
    ctx: &EvalCtx,
    instance_name: &str,
    op_name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<ResolvedModuleRefOperator>> {
    let instance_info: InstanceInfo = if let Some(info) = ctx.get_instance(instance_name) {
        info.clone()
    } else if let Some(def) = ctx.get_op(instance_name) {
        match &def.body.node {
            Expr::InstanceExpr(module_name, substitutions) => InstanceInfo {
                module_name: module_name.clone(),
                substitutions: substitutions.clone(),
            },
            _ => return Ok(None),
        }
    } else {
        return Ok(None);
    };

    let Some(op_def) = ctx
        .get_instance_op(&instance_info.module_name, op_name)
        .cloned()
    else {
        return Ok(None);
    };

    if op_def.params.len() != args.len() {
        return Err(EvalError::ArityMismatch {
            op: format!("{instance_name}!{op_name}"),
            expected: op_def.params.len(),
            got: args.len(),
            span,
        });
    }

    let scope_key = ModuleRefScopeKey {
        shared_id: ctx.shared.id,
        instance_name_id: intern_name(instance_name),
        outer_subs_id: ctx
            .instance_substitutions
            .as_ref()
            .map_or(0, |subs| Arc::as_ptr(subs) as usize),
        outer_local_ops_id: ctx
            .local_ops
            .as_ref()
            .map_or(0, |ops| Arc::as_ptr(ops) as usize),
    };

    let effective_substitutions = crate::compose_substitutions(
        &ctx.compute_effective_instance_substitutions(
            &instance_info.module_name,
            &instance_info.substitutions,
        ),
        ctx.instance_substitutions(),
    );

    let scope_entry = MODULE_REF_CACHES
        .with(|c| c.borrow().module_ref_scope.get(&scope_key).cloned())
        .unwrap_or_else(|| {
            let mut instance_local_ops: OpEnv = ctx
                .shared
                .instance_ops
                .get(&instance_info.module_name)
                .cloned()
                .unwrap_or_default();

            if let Some(parent_local_ops) = ctx.local_ops.as_ref() {
                for (name, def) in parent_local_ops.iter() {
                    if !instance_local_ops.contains_key(name.as_str()) {
                        instance_local_ops.insert(name.clone(), def.clone());
                    }
                }
            }

            let entry = ModuleRefScopeEntry {
                effective_subs_arc: Arc::new(effective_substitutions.clone()),
                local_ops_arc: Arc::new(instance_local_ops),
            };
            MODULE_REF_CACHES.with(|c| {
                c.borrow_mut().module_ref_scope.insert(scope_key, entry.clone());
            });
            entry
        });

    let has_effective_substitutions = !scope_entry.effective_subs_arc.is_empty();

    let mut bindings = Vec::new();
    for (param, arg) in op_def.params.iter().zip(args.iter()) {
        let value = eval(ctx, arg)?;
        bindings.push((Arc::from(param.name.node.as_str()), value));
    }

    let saved_param_bindings: Vec<(NameId, Value)> = bindings
        .iter()
        .map(|(name, value)| (intern_name(name), value.clone()))
        .collect();

    let is_chained =
        ctx.chained_ref_eval || (ctx.local_ops.is_some() && has_effective_substitutions);

    let mut new_ctx = ctx.with_module_scope_arced_subs(
        Arc::clone(&scope_entry.local_ops_arc),
        bindings,
        Arc::clone(&scope_entry.effective_subs_arc),
    );
    if is_chained {
        new_ctx.stable_mut().chained_ref_eval = true;
    }

    if has_effective_substitutions {
        new_ctx.stable_mut().eager_subst_bindings = Some(Arc::clone(&EMPTY_EAGER_SUBST));
        new_ctx.bindings =
            build_lazy_subst_bindings(&ctx.bindings, &scope_entry.effective_subs_arc);
        for (name_id, value) in saved_param_bindings.iter().rev() {
            new_ctx.bindings = new_ctx.bindings.cons_local(
                *name_id,
                BindingValue::eager(value.clone()),
                new_ctx.binding_depth,
            );
        }
    }

    Ok(Some(ResolvedModuleRefOperator {
        op_def: op_def.into(),
        eval_ctx: new_ctx,
    }))
}
