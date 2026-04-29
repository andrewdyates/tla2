// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::eval::{apply_substitutions, compose_substitutions, eval, EvalCtx};
use std::sync::Arc;
use tla_core::ast::{Expr, ModuleTarget, OpParam, Substitution};
use tla_core::Spanned;
use tla_value::error::EvalResult;

pub(super) fn resolve_module_ref_body(
    ctx: &EvalCtx,
    target: &ModuleTarget,
    op_name: &str,
    args: &[Spanned<Expr>],
) -> EvalResult<Option<(EvalCtx, Spanned<Expr>)>> {
    match target {
        ModuleTarget::Named(name) => {
            let Some((module_name, instance_subs)) = resolve_instance_info(ctx, name) else {
                return Ok(None);
            };
            resolve_named_or_parameterized_module_ref_body(
                ctx,
                &module_name,
                &instance_subs,
                op_name,
                args,
            )
        }
        ModuleTarget::Parameterized(name, params) => {
            let Some(def) = ctx.get_op(name) else {
                return Ok(None);
            };
            let Expr::InstanceExpr(module_name, instance_subs) = &def.body.node else {
                return Ok(None);
            };
            if def.params.len() != params.len() {
                return Ok(None);
            }

            let param_subs = build_param_substitutions(&def.params, params);
            let instantiated_subs = instantiate_substitutions(instance_subs, &param_subs);

            resolve_named_or_parameterized_module_ref_body(
                ctx,
                module_name,
                &instantiated_subs,
                op_name,
                args,
            )
        }
        ModuleTarget::Chained(base_expr) => {
            let mut instance_ctx = match resolve_chained_target_ctx(ctx, base_expr) {
                Some(instance_ctx) => instance_ctx,
                None => return Ok(None),
            };

            let resolved_name = instance_ctx.resolve_op_name(op_name);
            let Some(op_def) = instance_ctx.get_op(resolved_name).cloned() else {
                return Ok(None);
            };
            if op_def.params.len() != args.len() {
                return Ok(None);
            }

            for (param, arg) in op_def.params.iter().zip(args.iter()) {
                let arg_val = eval(ctx, arg)?;
                instance_ctx.bind_mut(Arc::from(param.name.node.as_str()), arg_val);
            }

            let body = match instance_ctx.instance_substitutions() {
                Some(subs) => apply_substitutions(&op_def.body, subs),
                None => op_def.body.clone(),
            };
            Ok(Some((instance_ctx, body)))
        }
    }
}

fn merged_instance_local_ops(ctx: &EvalCtx, module_name: &str) -> Arc<tla_core::OpEnv> {
    let mut instance_local_ops = ctx
        .instance_ops()
        .get(module_name)
        .cloned()
        .unwrap_or_default();
    if let Some(parent_local_ops) = ctx.local_ops().as_ref() {
        for (name, def) in parent_local_ops.iter() {
            if !instance_local_ops.contains_key(name.as_str()) {
                instance_local_ops.insert(name.clone(), def.clone());
            }
        }
    }
    Arc::new(instance_local_ops)
}

fn resolve_named_or_parameterized_module_ref_body(
    ctx: &EvalCtx,
    module_name: &str,
    instance_subs: &[Substitution],
    op_name: &str,
    args: &[Spanned<Expr>],
) -> EvalResult<Option<(EvalCtx, Spanned<Expr>)>> {
    let effective_subs = compose_substitutions(instance_subs, ctx.instance_substitutions());
    let resolved_name = ctx.resolve_op_name(op_name);
    let Some(op_def) = ctx.get_instance_op(module_name, resolved_name).cloned() else {
        return Ok(None);
    };
    if op_def.params.len() != args.len() {
        return Ok(None);
    }

    let mut bindings = Vec::with_capacity(args.len());
    for (param, arg) in op_def.params.iter().zip(args.iter()) {
        let arg_val = eval(ctx, arg)?;
        bindings.push((Arc::from(param.name.node.as_str()), arg_val));
    }

    let effective_subs = Arc::new(effective_subs);
    let instance_ctx = ctx.with_module_scope_arced_subs(
        merged_instance_local_ops(ctx, module_name),
        bindings,
        Arc::clone(&effective_subs),
    );
    let body = if effective_subs.is_empty() {
        op_def.body.clone()
    } else {
        apply_substitutions(&op_def.body, effective_subs.as_ref())
    };
    Ok(Some((instance_ctx, body)))
}

fn resolve_module_target_ctx(ctx: &EvalCtx, target: &ModuleTarget) -> Option<EvalCtx> {
    match target {
        ModuleTarget::Named(name) => {
            let (module_name, instance_subs) = resolve_instance_info(ctx, name)?;
            let effective_subs = Arc::new(compose_substitutions(
                &instance_subs,
                ctx.instance_substitutions(),
            ));
            Some(ctx.with_module_scope_arced_subs(
                merged_instance_local_ops(ctx, &module_name),
                Vec::<(Arc<str>, tla_value::Value)>::new(),
                effective_subs,
            ))
        }
        ModuleTarget::Parameterized(name, params) => {
            let def = ctx.get_op(name)?;
            let Expr::InstanceExpr(module_name, instance_subs) = &def.body.node else {
                return None;
            };
            if def.params.len() != params.len() {
                return None;
            }

            let param_subs = build_param_substitutions(&def.params, params);
            let instantiated_subs = instantiate_substitutions(instance_subs, &param_subs);
            let effective_subs = Arc::new(compose_substitutions(
                &instantiated_subs,
                ctx.instance_substitutions(),
            ));
            Some(ctx.with_module_scope_arced_subs(
                merged_instance_local_ops(ctx, module_name),
                Vec::<(Arc<str>, tla_value::Value)>::new(),
                effective_subs,
            ))
        }
        ModuleTarget::Chained(base_expr) => resolve_chained_target_ctx(ctx, base_expr),
    }
}

fn resolve_chained_target_ctx(ctx: &EvalCtx, base_expr: &Spanned<Expr>) -> Option<EvalCtx> {
    let Expr::ModuleRef(base_target, inst_name, inst_args) = &base_expr.node else {
        return None;
    };
    if !inst_args.is_empty() {
        return None;
    }

    let base_ctx = resolve_module_target_ctx(ctx, base_target)?;
    let inst_def = base_ctx.get_op(inst_name)?;
    let Expr::InstanceExpr(module_name, inst_subs) = &inst_def.body.node else {
        return None;
    };

    let effective_subs = Arc::new(compose_substitutions(
        inst_subs,
        base_ctx.instance_substitutions(),
    ));
    Some(base_ctx.with_module_scope_arced_subs(
        merged_instance_local_ops(&base_ctx, module_name),
        Vec::<(Arc<str>, tla_value::Value)>::new(),
        effective_subs,
    ))
}

fn resolve_instance_info(
    ctx: &EvalCtx,
    instance_name: &str,
) -> Option<(String, Vec<Substitution>)> {
    if let Some(info) = ctx.get_instance(instance_name) {
        return Some((info.module_name.clone(), info.substitutions.clone()));
    }
    if let Some(def) = ctx.get_op(instance_name) {
        if def.params.is_empty() {
            if let Expr::InstanceExpr(module_name, substitutions) = &def.body.node {
                return Some((module_name.clone(), substitutions.clone()));
            }
        }
    }
    None
}

fn build_param_substitutions(params: &[OpParam], args: &[Spanned<Expr>]) -> Vec<Substitution> {
    params
        .iter()
        .zip(args.iter())
        .map(|(param, arg)| Substitution {
            from: param.name.clone(),
            to: arg.clone(),
        })
        .collect()
}

fn instantiate_substitutions(
    substitutions: &[Substitution],
    param_subs: &[Substitution],
) -> Vec<Substitution> {
    substitutions
        .iter()
        .map(|sub| Substitution {
            from: sub.from.clone(),
            to: apply_substitutions(&sub.to, param_subs),
        })
        .collect()
}
