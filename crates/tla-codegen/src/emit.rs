// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Rust code emitter for TLA+ specifications
//!
//! This module generates Rust code from TLA+ modules. The generated code:
//! - Defines a state struct from TLA+ variables
//! - Implements the StateMachine trait
//! - Generates Init and Next actions
//! - Optionally generates Kani verification harnesses
//!
//! Implementation split across submodules:
//! - `checker`: production-type adapter layer emission
//! - `actions`: Init/Next action analysis and code generation
//! - `expr`: TLA+ expression to Rust translation
//! - `state_machine`: StateMachine trait emission
//! - `harness`: proptest and Kani harness generation

mod actions;
mod checker;
mod expr;
mod fold_helpers;
mod harness;
mod state_machine;
mod util;

use crate::error::CodegenError;
use crate::types::struct_registry::StructRegistry;
use crate::types::{TlaType, TypeContext, TypeInferError};
use crate::{CheckerMapConfig, CodeGenContext};
use fold_helpers::ExpandOperatorsCodegen;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use tla_core::ast::{ExceptPathElement, Expr, Module, OpParam, OperatorDef, Substitution, Unit};
use tla_core::span::Spanned;
use tla_core::{apply_substitutions_v, ExprFold};

const WRITE_TO_STRING_ERR: &str = "writing generated Rust into an in-memory String should not fail";
#[cfg(test)]
use util::validate_single_line_rust_expr;
use util::{
    to_pascal_case, to_snake_case, validate_single_line_rust_expr_trimmed,
    validate_single_line_rust_fragment_trimmed,
};
type CgResult = Result<(), CodegenError>;

/// Represents a value in Init predicate analysis
#[derive(Debug, Clone)]
enum InitValue {
    /// Direct expression assignment: x = value
    Expr(Expr),
    /// Non-deterministic choice: x \in Set
    InSet(Expr),
}

/// Code generation options
#[derive(Debug, Clone, Default)]
pub struct CodeGenOptions {
    /// Module name for generated code (defaults to TLA+ module name)
    pub module_name: Option<String>,
    /// Generate proptest harnesses
    pub generate_proptest: bool,
    /// Generate Kani harnesses
    pub generate_kani: bool,
    /// Generate a production-type adapter layer (runtime checkers).
    pub generate_checker: bool,
    /// Optional mapping config for generating `impl checker::To<Spec>State` blocks.
    pub checker_map: Option<CheckerMapConfig>,
}

#[derive(Debug, Clone)]
pub(super) enum ResolvedOperatorOrigin {
    ModuleScope,
    LocalEnv,
}

#[derive(Debug, Clone)]
pub(super) struct ResolvedOperator {
    pub(super) def: OperatorDef,
    pub(super) module_name: String,
    pub(super) substitutions: Vec<Substitution>,
    pub(super) origin: ResolvedOperatorOrigin,
}

#[derive(Debug, Clone)]
pub(super) struct ResolvedInstance {
    pub(super) module_name: String,
    pub(super) substitutions: Vec<Substitution>,
}

/// Minimal module environment needed by codegen to resolve `INSTANCE` references.
#[derive(Debug, Clone, Default)]
pub(super) struct CodegenModuleEnv {
    modules: HashMap<String, Module>,
    state_vars: HashSet<String>,
}

impl CodegenModuleEnv {
    fn new(main: &Module, context: &CodeGenContext<'_>) -> Self {
        let mut modules = HashMap::new();
        modules.insert(main.name.node.clone(), main.clone());
        for module in &context.modules {
            modules
                .entry(module.name.node.clone())
                .or_insert_with(|| (*module).clone());
        }
        let state_vars = main
            .units
            .iter()
            .filter_map(|unit| match &unit.node {
                Unit::Variable(vars) => Some(vars.iter().map(|var| var.node.clone())),
                _ => None,
            })
            .flatten()
            .collect();
        Self {
            modules,
            state_vars,
        }
    }

    pub(super) fn module(&self, name: &str) -> Option<&Module> {
        self.modules.get(name)
    }

    pub(super) fn resolve_operator_in_module_scope(
        &self,
        module_name: &str,
        op_name: &str,
    ) -> Option<ResolvedOperator> {
        let mut visited = HashSet::new();
        self.resolve_operator_in_module_scope_rec(module_name, op_name, &mut visited)
    }

    pub(super) fn resolve_exported_operator(
        &self,
        module_name: &str,
        op_name: &str,
    ) -> Option<ResolvedOperator> {
        let mut visited = HashSet::new();
        self.resolve_exported_operator_rec(module_name, op_name, &mut visited)
    }

    fn resolve_operator_in_module_scope_rec(
        &self,
        module_name: &str,
        op_name: &str,
        visited: &mut HashSet<String>,
    ) -> Option<ResolvedOperator> {
        let module = self.module(module_name)?;
        if !visited.insert(module_name.to_string()) {
            return None;
        }

        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                if op.name.node == op_name {
                    visited.remove(module_name);
                    return Some(ResolvedOperator {
                        def: op.clone(),
                        module_name: module_name.to_string(),
                        substitutions: Vec::new(),
                        origin: ResolvedOperatorOrigin::ModuleScope,
                    });
                }
            }
        }

        for ext in &module.extends {
            if let Some(resolved) = self.resolve_exported_operator_rec(&ext.node, op_name, visited)
            {
                visited.remove(module_name);
                return Some(resolved);
            }
        }

        for unit in &module.units {
            let Unit::Instance(inst) = &unit.node else {
                continue;
            };
            let instance_subs =
                self.materialize_module_substitutions(module_name, inst.substitutions.as_slice());
            if let Some(resolved) =
                self.resolve_exported_operator_rec(&inst.module.node, op_name, visited)
            {
                let substitutions =
                    compose_substitutions(&resolved.substitutions, Some(instance_subs.as_slice()));
                visited.remove(module_name);
                return Some(ResolvedOperator {
                    substitutions,
                    ..resolved
                });
            }
        }

        visited.remove(module_name);
        None
    }

    fn resolve_exported_operator_rec(
        &self,
        module_name: &str,
        op_name: &str,
        visited: &mut HashSet<String>,
    ) -> Option<ResolvedOperator> {
        let module = self.module(module_name)?;
        if !visited.insert(module_name.to_string()) {
            return None;
        }

        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                if !op.local && op.name.node == op_name {
                    visited.remove(module_name);
                    return Some(ResolvedOperator {
                        def: op.clone(),
                        module_name: module_name.to_string(),
                        substitutions: Vec::new(),
                        origin: ResolvedOperatorOrigin::ModuleScope,
                    });
                }
            }
        }

        for ext in &module.extends {
            if let Some(resolved) = self.resolve_exported_operator_rec(&ext.node, op_name, visited)
            {
                visited.remove(module_name);
                return Some(resolved);
            }
        }

        for unit in &module.units {
            let Unit::Instance(inst) = &unit.node else {
                continue;
            };
            if inst.local {
                continue;
            }
            let instance_subs =
                self.materialize_module_substitutions(module_name, inst.substitutions.as_slice());
            if let Some(resolved) =
                self.resolve_exported_operator_rec(&inst.module.node, op_name, visited)
            {
                let substitutions =
                    compose_substitutions(&resolved.substitutions, Some(instance_subs.as_slice()));
                visited.remove(module_name);
                return Some(ResolvedOperator {
                    substitutions,
                    ..resolved
                });
            }
        }

        visited.remove(module_name);
        None
    }

    fn importable_operator_names(&self, module_name: &str) -> Vec<String> {
        let mut out = Vec::new();
        let mut seen_modules = HashSet::new();
        let mut seen_names = HashSet::new();
        self.collect_importable_operator_names_rec(
            module_name,
            &mut seen_modules,
            &mut seen_names,
            &mut out,
        );
        out
    }

    fn collect_importable_operator_names_rec(
        &self,
        module_name: &str,
        seen_modules: &mut HashSet<String>,
        seen_names: &mut HashSet<String>,
        out: &mut Vec<String>,
    ) {
        let Some(module) = self.module(module_name) else {
            return;
        };
        if !seen_modules.insert(module_name.to_string()) {
            return;
        }

        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                if !op.local
                    && self.is_importable_top_level_operator(module_name, op)
                    && seen_names.insert(op.name.node.clone())
                {
                    out.push(op.name.node.clone());
                }
            }
        }

        for ext in &module.extends {
            self.collect_importable_operator_names_rec(&ext.node, seen_modules, seen_names, out);
        }

        for unit in &module.units {
            let Unit::Instance(inst) = &unit.node else {
                continue;
            };
            if inst.local {
                continue;
            }
            self.collect_importable_operator_names_rec(
                &inst.module.node,
                seen_modules,
                seen_names,
                out,
            );
        }
    }

    fn is_importable_top_level_operator(&self, module_name: &str, op: &OperatorDef) -> bool {
        let name = op.name.node.as_str();
        if name == "Init" || name == "Next" {
            return true;
        }
        if !(name.starts_with("Inv") || name.ends_with("Invariant")) || op.contains_prime {
            return false;
        }

        let expanded =
            expand_expr_for_codegen(op.body.clone(), self, &self.state_vars, module_name);
        if contains_temporal_or_enabled(&expanded.node) {
            return false;
        }

        let mut unresolved = Vec::new();
        collect_unresolved_expr_errors(&expanded.node, &mut unresolved);
        unresolved.is_empty()
    }

    fn materialize_module_substitutions(
        &self,
        module_name: &str,
        substitutions: &[Substitution],
    ) -> Vec<Substitution> {
        self.materialize_module_substitutions_with_bound_names(module_name, substitutions, &[])
    }

    fn materialize_module_substitutions_with_bound_names(
        &self,
        module_name: &str,
        substitutions: &[Substitution],
        bound_names: &[String],
    ) -> Vec<Substitution> {
        substitutions
            .iter()
            .map(|sub| Substitution {
                from: sub.from.clone(),
                to: expand_expr_for_codegen_with_bound(
                    sub.to.clone(),
                    self,
                    &self.state_vars,
                    module_name,
                    bound_names,
                ),
            })
            .collect()
    }
}

pub(super) fn compose_substitutions(
    inner_subs: &[Substitution],
    outer_subs: Option<&[Substitution]>,
) -> Vec<Substitution> {
    let Some(outer_subs) = outer_subs else {
        return inner_subs.to_vec();
    };
    if outer_subs.is_empty() {
        return inner_subs.to_vec();
    }

    let mut combined = Vec::with_capacity(inner_subs.len() + outer_subs.len());
    let mut overridden: HashSet<&str> = HashSet::new();

    for sub in inner_subs {
        overridden.insert(sub.from.node.as_str());
        combined.push(Substitution {
            from: sub.from.clone(),
            to: apply_substitutions_v(&sub.to, outer_subs),
        });
    }

    for sub in outer_subs {
        if overridden.contains(sub.from.node.as_str()) {
            continue;
        }
        combined.push(sub.clone());
    }

    combined
}

pub(super) fn build_param_substitutions(
    params: &[OpParam],
    args: &[Spanned<Expr>],
) -> Vec<Substitution> {
    params
        .iter()
        .zip(args.iter())
        .map(|(param, arg)| Substitution {
            from: param.name.clone(),
            to: arg.clone(),
        })
        .collect()
}

pub(super) fn instantiate_substitutions(
    substitutions: &[Substitution],
    param_subs: &[Substitution],
) -> Vec<Substitution> {
    substitutions
        .iter()
        .map(|sub| Substitution {
            from: sub.from.clone(),
            to: apply_substitutions_v(&sub.to, param_subs),
        })
        .collect()
}

pub(super) fn instance_from_resolved_operator(
    resolved: ResolvedOperator,
    actuals: Option<&[Spanned<Expr>]>,
    module_env: &CodegenModuleEnv,
) -> Option<ResolvedInstance> {
    let Expr::InstanceExpr(module_name, instance_subs) = &resolved.def.body.node else {
        return None;
    };

    let param_names: Vec<String> = resolved
        .def
        .params
        .iter()
        .map(|param| param.name.node.clone())
        .collect();
    let instance_subs = match resolved.origin {
        ResolvedOperatorOrigin::ModuleScope => module_env
            .materialize_module_substitutions_with_bound_names(
                &resolved.module_name,
                instance_subs,
                &param_names,
            ),
        ResolvedOperatorOrigin::LocalEnv => instance_subs.clone(),
    };

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

fn contains_temporal_or_enabled(expr: &Expr) -> bool {
    match expr {
        Expr::Always(_)
        | Expr::Eventually(_)
        | Expr::LeadsTo(_, _)
        | Expr::WeakFair(_, _)
        | Expr::StrongFair(_, _)
        | Expr::Enabled(_) => true,
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_) => false,
        Expr::Apply(op, args) => {
            contains_temporal_or_enabled(&op.node)
                || args
                    .iter()
                    .any(|arg| contains_temporal_or_enabled(&arg.node))
        }
        Expr::Lambda(_, body)
        | Expr::Not(body)
        | Expr::Prime(body)
        | Expr::Unchanged(body)
        | Expr::Powerset(body)
        | Expr::BigUnion(body)
        | Expr::Domain(body)
        | Expr::Neg(body) => contains_temporal_or_enabled(&body.node),
        Expr::Label(label) => contains_temporal_or_enabled(&label.body.node),
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::FuncSet(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b)
        | Expr::FuncApply(a, b) => {
            contains_temporal_or_enabled(&a.node) || contains_temporal_or_enabled(&b.node)
        }
        Expr::RecordAccess(a, _) => contains_temporal_or_enabled(&a.node),
        Expr::Forall(bounds, body)
        | Expr::Exists(bounds, body)
        | Expr::FuncDef(bounds, body)
        | Expr::SetBuilder(body, bounds) => {
            bounds
                .iter()
                .filter_map(|bound| bound.domain.as_ref())
                .any(|domain| contains_temporal_or_enabled(&domain.node))
                || contains_temporal_or_enabled(&body.node)
        }
        Expr::Choose(bound, body) | Expr::SetFilter(bound, body) => {
            bound
                .domain
                .as_ref()
                .map(|domain| contains_temporal_or_enabled(&domain.node))
                .unwrap_or(false)
                || contains_temporal_or_enabled(&body.node)
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => elems
            .iter()
            .any(|elem| contains_temporal_or_enabled(&elem.node)),
        Expr::Except(base, specs) => {
            contains_temporal_or_enabled(&base.node)
                || specs.iter().any(|spec| {
                    spec.path.iter().any(|elem| match elem {
                        ExceptPathElement::Field(_) => false,
                        ExceptPathElement::Index(idx) => contains_temporal_or_enabled(&idx.node),
                    }) || contains_temporal_or_enabled(&spec.value.node)
                })
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, value)| contains_temporal_or_enabled(&value.node)),
        Expr::If(c, t, e) => {
            contains_temporal_or_enabled(&c.node)
                || contains_temporal_or_enabled(&t.node)
                || contains_temporal_or_enabled(&e.node)
        }
        Expr::Case(arms, other) => {
            arms.iter().any(|arm| {
                contains_temporal_or_enabled(&arm.guard.node)
                    || contains_temporal_or_enabled(&arm.body.node)
            }) || other
                .as_ref()
                .map(|expr| contains_temporal_or_enabled(&expr.node))
                .unwrap_or(false)
        }
        Expr::Let(defs, body) => {
            defs.iter()
                .any(|def| contains_temporal_or_enabled(&def.body.node))
                || contains_temporal_or_enabled(&body.node)
        }
        Expr::ModuleRef(_, _, _) | Expr::InstanceExpr(_, _) | Expr::SubstIn(_, _) => false,
    }
}

fn expand_expr_for_codegen(
    expr: Spanned<Expr>,
    module_env: &CodegenModuleEnv,
    state_vars: &HashSet<String>,
    module_name: &str,
) -> Spanned<Expr> {
    expand_expr_for_codegen_with_bound(expr, module_env, state_vars, module_name, &[])
}

fn expand_expr_for_codegen_with_bound(
    expr: Spanned<Expr>,
    module_env: &CodegenModuleEnv,
    state_vars: &HashSet<String>,
    module_name: &str,
    bound_names: &[String],
) -> Spanned<Expr> {
    let mut expander = ExpandOperatorsCodegen::new(module_env, state_vars, module_name);
    expander.bound.extend(bound_names.iter().cloned());
    expander.fold_expr(expr)
}

fn prepare_module_for_codegen(module: &Module, module_env: &CodegenModuleEnv) -> Module {
    let state_vars: HashSet<String> = module
        .units
        .iter()
        .filter_map(|unit| match &unit.node {
            Unit::Variable(vars) => Some(vars.iter().map(|var| var.node.clone())),
            _ => None,
        })
        .flatten()
        .collect();

    let mut existing_op_names: HashSet<String> = module
        .units
        .iter()
        .filter_map(|unit| match &unit.node {
            Unit::Operator(op) if !matches!(&op.body.node, Expr::InstanceExpr(..)) => {
                Some(op.name.node.clone())
            }
            _ => None,
        })
        .collect();

    let mut imported_ops = Vec::new();
    for unit in &module.units {
        let Unit::Instance(inst) = &unit.node else {
            continue;
        };

        for name in module_env.importable_operator_names(&inst.module.node) {
            if !existing_op_names.insert(name.clone()) {
                continue;
            }
            let Some(resolved) = module_env.resolve_exported_operator(&inst.module.node, &name)
            else {
                continue;
            };

            let instance_subs = module_env
                .materialize_module_substitutions(&module.name.node, inst.substitutions.as_slice());
            let effective_subs =
                compose_substitutions(&resolved.substitutions, Some(instance_subs.as_slice()));
            let mut body = expand_expr_for_codegen(
                resolved.def.body.clone(),
                module_env,
                &state_vars,
                &resolved.module_name,
            );
            if !effective_subs.is_empty() {
                body = apply_substitutions_v(&body, &effective_subs);
            }

            let mut imported = resolved.def.clone();
            imported.body = body;
            imported_ops.push(Spanned::new(Unit::Operator(imported), unit.span));
        }
    }

    let mut units = Vec::new();
    for unit in &module.units {
        match &unit.node {
            Unit::Operator(op) if matches!(&op.body.node, Expr::InstanceExpr(..)) => {}
            Unit::Operator(op) => {
                let mut op = op.clone();
                op.body = expand_expr_for_codegen(
                    op.body.clone(),
                    module_env,
                    &state_vars,
                    &module.name.node,
                );
                units.push(Spanned::new(Unit::Operator(op), unit.span));
            }
            _ => units.push(unit.clone()),
        }
    }
    units.extend(imported_ops);

    Module {
        name: module.name.clone(),
        extends: module.extends.clone(),
        units,
        action_subscript_spans: module.action_subscript_spans.clone(),
        span: module.span,
    }
}

fn is_recursive_codegen_helper(op: &OperatorDef) -> bool {
    op.is_recursive && !matches!(op.name.node.as_str(), "Init" | "Next" | "Spec" | "vars")
}

fn expr_references_state_vars(expr: &Expr, state_vars: &HashSet<String>) -> bool {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => state_vars.contains(name),
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => false,
        Expr::Apply(op, args) => {
            expr_references_state_vars(&op.node, state_vars)
                || args
                    .iter()
                    .any(|arg| expr_references_state_vars(&arg.node, state_vars))
        }
        Expr::Lambda(_, body)
        | Expr::Not(body)
        | Expr::Prime(body)
        | Expr::Always(body)
        | Expr::Eventually(body)
        | Expr::Enabled(body)
        | Expr::Unchanged(body)
        | Expr::Powerset(body)
        | Expr::BigUnion(body)
        | Expr::Domain(body)
        | Expr::Neg(body) => expr_references_state_vars(&body.node, state_vars),
        Expr::Label(label) => expr_references_state_vars(&label.body.node, state_vars),
        Expr::And(left, right)
        | Expr::Or(left, right)
        | Expr::Implies(left, right)
        | Expr::Equiv(left, right)
        | Expr::In(left, right)
        | Expr::NotIn(left, right)
        | Expr::Subseteq(left, right)
        | Expr::Union(left, right)
        | Expr::Intersect(left, right)
        | Expr::SetMinus(left, right)
        | Expr::FuncSet(left, right)
        | Expr::LeadsTo(left, right)
        | Expr::WeakFair(left, right)
        | Expr::StrongFair(left, right)
        | Expr::Eq(left, right)
        | Expr::Neq(left, right)
        | Expr::Lt(left, right)
        | Expr::Leq(left, right)
        | Expr::Gt(left, right)
        | Expr::Geq(left, right)
        | Expr::Add(left, right)
        | Expr::Sub(left, right)
        | Expr::Mul(left, right)
        | Expr::Div(left, right)
        | Expr::IntDiv(left, right)
        | Expr::Mod(left, right)
        | Expr::Pow(left, right)
        | Expr::Range(left, right)
        | Expr::FuncApply(left, right) => {
            expr_references_state_vars(&left.node, state_vars)
                || expr_references_state_vars(&right.node, state_vars)
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => elems
            .iter()
            .any(|elem| expr_references_state_vars(&elem.node, state_vars)),
        Expr::SetBuilder(body, bounds)
        | Expr::Forall(bounds, body)
        | Expr::Exists(bounds, body)
        | Expr::FuncDef(bounds, body) => {
            bounds.iter().any(|bound| {
                bound.domain.as_ref().map_or(false, |domain| {
                    expr_references_state_vars(&domain.node, state_vars)
                })
            }) || expr_references_state_vars(&body.node, state_vars)
        }
        Expr::SetFilter(bound, body) | Expr::Choose(bound, body) => {
            bound.domain.as_ref().map_or(false, |domain| {
                expr_references_state_vars(&domain.node, state_vars)
            }) || expr_references_state_vars(&body.node, state_vars)
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, value)| expr_references_state_vars(&value.node, state_vars)),
        Expr::RecordAccess(record, _) => expr_references_state_vars(&record.node, state_vars),
        Expr::Except(base, specs) => {
            expr_references_state_vars(&base.node, state_vars)
                || specs.iter().any(|spec| {
                    spec.path.iter().any(|elem| match elem {
                        ExceptPathElement::Field(_) => false,
                        ExceptPathElement::Index(idx) => {
                            expr_references_state_vars(&idx.node, state_vars)
                        }
                    }) || expr_references_state_vars(&spec.value.node, state_vars)
                })
        }
        Expr::If(cond, then_e, else_e) => {
            expr_references_state_vars(&cond.node, state_vars)
                || expr_references_state_vars(&then_e.node, state_vars)
                || expr_references_state_vars(&else_e.node, state_vars)
        }
        Expr::Case(arms, other) => {
            arms.iter().any(|arm| {
                expr_references_state_vars(&arm.guard.node, state_vars)
                    || expr_references_state_vars(&arm.body.node, state_vars)
            }) || other.as_ref().map_or(false, |expr| {
                expr_references_state_vars(&expr.node, state_vars)
            })
        }
        Expr::Let(defs, body) => {
            defs.iter()
                .any(|def| expr_references_state_vars(&def.body.node, state_vars))
                || expr_references_state_vars(&body.node, state_vars)
        }
        Expr::ModuleRef(_, _, args) => args
            .iter()
            .any(|arg| expr_references_state_vars(&arg.node, state_vars)),
        Expr::InstanceExpr(_, subs) => subs
            .iter()
            .any(|sub| expr_references_state_vars(&sub.to.node, state_vars)),
        Expr::SubstIn(subs, body) => {
            subs.iter()
                .any(|sub| expr_references_state_vars(&sub.to.node, state_vars))
                || expr_references_state_vars(&body.node, state_vars)
        }
    }
}

fn expr_calls_any_of(expr: &Expr, names: &HashSet<String>) -> bool {
    match expr {
        Expr::Apply(op, args) => {
            if let Expr::Ident(name, _) = &op.node {
                if names.contains(name) {
                    return true;
                }
            }
            expr_calls_any_of(&op.node, names)
                || args.iter().any(|arg| expr_calls_any_of(&arg.node, names))
        }
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _) => false,
        Expr::Lambda(_, body)
        | Expr::Not(body)
        | Expr::Prime(body)
        | Expr::Always(body)
        | Expr::Eventually(body)
        | Expr::Enabled(body)
        | Expr::Unchanged(body)
        | Expr::Powerset(body)
        | Expr::BigUnion(body)
        | Expr::Domain(body)
        | Expr::Neg(body) => expr_calls_any_of(&body.node, names),
        Expr::Label(label) => expr_calls_any_of(&label.body.node, names),
        Expr::And(left, right)
        | Expr::Or(left, right)
        | Expr::Implies(left, right)
        | Expr::Equiv(left, right)
        | Expr::In(left, right)
        | Expr::NotIn(left, right)
        | Expr::Subseteq(left, right)
        | Expr::Union(left, right)
        | Expr::Intersect(left, right)
        | Expr::SetMinus(left, right)
        | Expr::FuncSet(left, right)
        | Expr::LeadsTo(left, right)
        | Expr::WeakFair(left, right)
        | Expr::StrongFair(left, right)
        | Expr::Eq(left, right)
        | Expr::Neq(left, right)
        | Expr::Lt(left, right)
        | Expr::Leq(left, right)
        | Expr::Gt(left, right)
        | Expr::Geq(left, right)
        | Expr::Add(left, right)
        | Expr::Sub(left, right)
        | Expr::Mul(left, right)
        | Expr::Div(left, right)
        | Expr::IntDiv(left, right)
        | Expr::Mod(left, right)
        | Expr::Pow(left, right)
        | Expr::Range(left, right)
        | Expr::FuncApply(left, right) => {
            expr_calls_any_of(&left.node, names) || expr_calls_any_of(&right.node, names)
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => elems
            .iter()
            .any(|elem| expr_calls_any_of(&elem.node, names)),
        Expr::SetBuilder(body, bounds)
        | Expr::Forall(bounds, body)
        | Expr::Exists(bounds, body)
        | Expr::FuncDef(bounds, body) => {
            bounds.iter().any(|bound| {
                bound
                    .domain
                    .as_ref()
                    .map_or(false, |domain| expr_calls_any_of(&domain.node, names))
            }) || expr_calls_any_of(&body.node, names)
        }
        Expr::SetFilter(bound, body) | Expr::Choose(bound, body) => {
            bound
                .domain
                .as_ref()
                .map_or(false, |domain| expr_calls_any_of(&domain.node, names))
                || expr_calls_any_of(&body.node, names)
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, value)| expr_calls_any_of(&value.node, names)),
        Expr::RecordAccess(record, _) => expr_calls_any_of(&record.node, names),
        Expr::Except(base, specs) => {
            expr_calls_any_of(&base.node, names)
                || specs.iter().any(|spec| {
                    spec.path.iter().any(|elem| match elem {
                        ExceptPathElement::Field(_) => false,
                        ExceptPathElement::Index(idx) => expr_calls_any_of(&idx.node, names),
                    }) || expr_calls_any_of(&spec.value.node, names)
                })
        }
        Expr::If(cond, then_e, else_e) => {
            expr_calls_any_of(&cond.node, names)
                || expr_calls_any_of(&then_e.node, names)
                || expr_calls_any_of(&else_e.node, names)
        }
        Expr::Case(arms, other) => {
            arms.iter().any(|arm| {
                expr_calls_any_of(&arm.guard.node, names)
                    || expr_calls_any_of(&arm.body.node, names)
            }) || other
                .as_ref()
                .map_or(false, |expr| expr_calls_any_of(&expr.node, names))
        }
        Expr::Let(defs, body) => {
            defs.iter()
                .any(|def| expr_calls_any_of(&def.body.node, names))
                || expr_calls_any_of(&body.node, names)
        }
        Expr::ModuleRef(_, _, args) => args.iter().any(|arg| expr_calls_any_of(&arg.node, names)),
        Expr::InstanceExpr(_, subs) => subs
            .iter()
            .any(|sub| expr_calls_any_of(&sub.to.node, names)),
        Expr::SubstIn(subs, body) => {
            subs.iter()
                .any(|sub| expr_calls_any_of(&sub.to.node, names))
                || expr_calls_any_of(&body.node, names)
        }
        Expr::OpRef(_) => false,
    }
}

fn compute_recursive_helpers_needing_state(
    op_defs: &HashMap<String, OperatorDef>,
    state_vars: &HashSet<String>,
) -> HashSet<String> {
    let recursive_helpers: HashSet<String> = op_defs
        .values()
        .filter(|op| is_recursive_codegen_helper(op))
        .map(|op| op.name.node.clone())
        .collect();

    let mut needs_state: HashSet<String> = recursive_helpers
        .iter()
        .filter(|name| {
            op_defs.get(*name).map_or(false, |op| {
                expr_references_state_vars(&op.body.node, state_vars)
            })
        })
        .cloned()
        .collect();

    loop {
        let mut changed = false;
        for name in &recursive_helpers {
            if needs_state.contains(name) {
                continue;
            }
            if let Some(op) = op_defs.get(name) {
                if expr_calls_any_of(&op.body.node, &needs_state) {
                    needs_state.insert(name.clone());
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    needs_state
}

fn collect_unresolved_expr_errors(expr: &Expr, errors: &mut Vec<TypeInferError>) {
    match expr {
        Expr::ModuleRef(_, _, _) => errors.push(TypeInferError::Unsupported(
            "unresolved module reference (M!Op)".to_string(),
        )),
        Expr::InstanceExpr(_, _) => errors.push(TypeInferError::Unsupported(
            "unresolved INSTANCE expression".to_string(),
        )),
        Expr::SubstIn(_, _) => errors.push(TypeInferError::Unsupported(
            "unresolved SubstIn wrapper".to_string(),
        )),
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_) => {}
        Expr::Apply(op, args) => {
            collect_unresolved_expr_errors(&op.node, errors);
            for arg in args {
                collect_unresolved_expr_errors(&arg.node, errors);
            }
        }
        Expr::Lambda(_, body)
        | Expr::Not(body)
        | Expr::Prime(body)
        | Expr::Always(body)
        | Expr::Eventually(body)
        | Expr::Enabled(body)
        | Expr::Unchanged(body)
        | Expr::Powerset(body)
        | Expr::BigUnion(body)
        | Expr::Domain(body)
        | Expr::Neg(body) => collect_unresolved_expr_errors(&body.node, errors),
        Expr::Label(label) => collect_unresolved_expr_errors(&label.body.node, errors),
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::FuncSet(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b)
        | Expr::FuncApply(a, b) => {
            collect_unresolved_expr_errors(&a.node, errors);
            collect_unresolved_expr_errors(&b.node, errors);
        }
        Expr::RecordAccess(a, _) => collect_unresolved_expr_errors(&a.node, errors),
        Expr::Forall(bounds, body)
        | Expr::Exists(bounds, body)
        | Expr::FuncDef(bounds, body)
        | Expr::SetBuilder(body, bounds) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    collect_unresolved_expr_errors(&domain.node, errors);
                }
            }
            collect_unresolved_expr_errors(&body.node, errors);
        }
        Expr::Choose(bound, body) | Expr::SetFilter(bound, body) => {
            if let Some(domain) = &bound.domain {
                collect_unresolved_expr_errors(&domain.node, errors);
            }
            collect_unresolved_expr_errors(&body.node, errors);
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for elem in elems {
                collect_unresolved_expr_errors(&elem.node, errors);
            }
        }
        Expr::Except(base, specs) => {
            collect_unresolved_expr_errors(&base.node, errors);
            for spec in specs {
                for elem in &spec.path {
                    if let ExceptPathElement::Index(idx) = elem {
                        collect_unresolved_expr_errors(&idx.node, errors);
                    }
                }
                collect_unresolved_expr_errors(&spec.value.node, errors);
            }
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, value) in fields {
                collect_unresolved_expr_errors(&value.node, errors);
            }
        }
        Expr::If(c, t, e) => {
            collect_unresolved_expr_errors(&c.node, errors);
            collect_unresolved_expr_errors(&t.node, errors);
            collect_unresolved_expr_errors(&e.node, errors);
        }
        Expr::Case(arms, other) => {
            for arm in arms {
                collect_unresolved_expr_errors(&arm.guard.node, errors);
                collect_unresolved_expr_errors(&arm.body.node, errors);
            }
            if let Some(other) = other {
                collect_unresolved_expr_errors(&other.node, errors);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                collect_unresolved_expr_errors(&def.body.node, errors);
            }
            collect_unresolved_expr_errors(&body.node, errors);
        }
    }
}

fn collect_unresolved_module_constructs(module: &Module) -> Vec<TypeInferError> {
    let mut errors = Vec::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            collect_unresolved_expr_errors(&op.body.node, &mut errors);
        }
    }
    errors
}

/// Generate Rust code from a TLA+ module without external module context.
pub fn generate_rust(module: &Module, options: &CodeGenOptions) -> Result<String, CodegenError> {
    generate_rust_with_context(module, &CodeGenContext::default(), options)
}

/// Generate Rust code from a TLA+ module with loaded dependency modules.
pub fn generate_rust_with_context(
    module: &Module,
    context: &CodeGenContext<'_>,
    options: &CodeGenOptions,
) -> Result<String, CodegenError> {
    let module_env = CodegenModuleEnv::new(module, context);
    let prepared = prepare_module_for_codegen(module, &module_env);

    let unresolved_errors = collect_unresolved_module_constructs(&prepared);
    if !unresolved_errors.is_empty() {
        return Err(CodegenError::TypeInference(unresolved_errors));
    }

    let mut ctx = TypeContext::new();
    let var_types = ctx.infer_module(&prepared);
    let op_types = ctx.op_types().clone();
    let op_param_types = ctx.op_param_types().clone();

    let errors = ctx.take_errors();
    if !errors.is_empty() {
        return Err(CodegenError::TypeInference(errors));
    }

    let op_defs: HashMap<String, OperatorDef> = prepared
        .units
        .iter()
        .filter_map(|unit| match &unit.node {
            Unit::Operator(op) => Some((op.name.node.clone(), op.clone())),
            _ => None,
        })
        .collect();

    let mut out = String::new();
    let state_vars: HashSet<String> = prepared
        .units
        .iter()
        .filter_map(|unit| match &unit.node {
            Unit::Variable(vars) => Some(vars.iter().map(|var| var.node.clone())),
            _ => None,
        })
        .flatten()
        .collect();

    // Build struct registry for type-specialized record structs
    let struct_registry = build_struct_registry_from_var_types(&var_types);

    let emitter = RustEmitter::new(
        &mut out,
        &var_types,
        &op_types,
        &op_param_types,
        &op_defs,
        module_env,
        state_vars,
        prepared.name.node.clone(),
        struct_registry,
    );
    emitter.emit_module(&prepared, options)?;
    Ok(out)
}

/// Build a `StructRegistry` by scanning inferred variable types for record types
/// with statically-known, fully-resolved fields.
fn build_struct_registry_from_var_types(var_types: &HashMap<String, TlaType>) -> StructRegistry {
    let mut registry = StructRegistry::new();
    for ty in var_types.values() {
        register_record_types_recursive(ty, &mut registry);
    }
    registry
}

/// Recursively register Record types found inside a TlaType (including nested
/// types like Set<Record>, Seq<Record>, Func<K, Record>, etc.).
fn register_record_types_recursive(ty: &TlaType, registry: &mut StructRegistry) {
    match ty {
        TlaType::Record(fields) => {
            registry.try_register_record(fields);
            // Also scan field types for nested records
            for (_, field_type) in fields {
                register_record_types_recursive(field_type, registry);
            }
        }
        TlaType::Set(inner) | TlaType::Seq(inner) => {
            register_record_types_recursive(inner, registry);
        }
        TlaType::Func(k, v) => {
            register_record_types_recursive(k, registry);
            register_record_types_recursive(v, registry);
        }
        TlaType::Tuple(elems) => {
            for elem in elems {
                register_record_types_recursive(elem, registry);
            }
        }
        _ => {}
    }
}

/// Rust code emitter
struct RustEmitter<'a> {
    pub(super) out: &'a mut String,
    pub(super) var_types: &'a HashMap<String, TlaType>,
    pub(super) op_types: &'a HashMap<String, TlaType>,
    pub(super) op_param_types: &'a HashMap<String, Vec<TlaType>>,
    pub(super) op_defs: &'a HashMap<String, OperatorDef>,
    pub(super) module_env: CodegenModuleEnv,
    pub(super) state_vars: HashSet<String>,
    pub(super) recursive_helpers: HashSet<String>,
    pub(super) recursive_helpers_needing_state: HashSet<String>,
    pub(super) in_recursive_helper: Cell<bool>,
    pub(super) module_name: String,
    pub(super) indent: usize,
    pub(super) struct_registry: StructRegistry,
}

impl<'a> RustEmitter<'a> {
    fn new(
        out: &'a mut String,
        var_types: &'a HashMap<String, TlaType>,
        op_types: &'a HashMap<String, TlaType>,
        op_param_types: &'a HashMap<String, Vec<TlaType>>,
        op_defs: &'a HashMap<String, OperatorDef>,
        module_env: CodegenModuleEnv,
        state_vars: HashSet<String>,
        module_name: String,
        struct_registry: StructRegistry,
    ) -> Self {
        let recursive_helpers = op_defs
            .values()
            .filter(|op| is_recursive_codegen_helper(op))
            .map(|op| op.name.node.clone())
            .collect();
        let recursive_helpers_needing_state =
            compute_recursive_helpers_needing_state(op_defs, &state_vars);
        RustEmitter {
            out,
            var_types,
            op_types,
            op_param_types,
            op_defs,
            module_env,
            state_vars,
            recursive_helpers,
            recursive_helpers_needing_state,
            in_recursive_helper: Cell::new(false),
            module_name,
            indent: 0,
            struct_registry,
        }
    }

    /// Write indentation
    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            write!(self.out, "    ").expect(WRITE_TO_STRING_ERR);
        }
    }

    /// Write a line with current indentation
    fn writeln_indented(&mut self, s: &str) {
        self.write_indent();
        writeln!(self.out, "{}", s).expect(WRITE_TO_STRING_ERR);
    }

    fn choose_yield_state_fn_name(&self, variables: &[String]) -> String {
        let mut used: HashSet<String> = variables.iter().map(|v| to_snake_case(v)).collect();
        used.insert("state".to_string());

        let base = "__tla2_yield_state_fn";
        if !used.contains(base) {
            return base.to_string();
        }

        for i in 0usize.. {
            let candidate = format!("{base}_{i}");
            if !used.contains(&candidate) {
                return candidate;
            }
        }

        unreachable!("should always find a free identifier")
    }

    fn emit_module(mut self, module: &Module, options: &CodeGenOptions) -> CgResult {
        let mod_name = options
            .module_name
            .as_ref()
            .unwrap_or(&module.name.node)
            .clone();

        writeln!(
            self.out,
            "//! Generated from TLA+ module: {}",
            module.name.node
        )
        .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "//!").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "//! This file was auto-generated by tla-codegen.")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "//! Do not edit manually.").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "#![allow(unused)]").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "use tla_runtime::prelude::*;").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);

        let mut variables: Vec<String> = Vec::new();
        for unit in &module.units {
            if let Unit::Variable(vars) = &unit.node {
                for var in vars {
                    variables.push(var.node.clone());
                }
            }
        }

        let mut init_op: Option<&OperatorDef> = None;
        let mut next_op: Option<&OperatorDef> = None;
        let mut invariants: Vec<&OperatorDef> = Vec::new();
        let mut recursive_ops: Vec<&OperatorDef> = Vec::new();

        for unit in &module.units {
            if let Unit::Operator(op) = &unit.node {
                if is_recursive_codegen_helper(op) {
                    recursive_ops.push(op);
                }
                match op.name.node.as_str() {
                    "Init" => init_op = Some(op),
                    "Next" => next_op = Some(op),
                    name if name.starts_with("Inv") || name.ends_with("Invariant") => {
                        invariants.push(op);
                    }
                    _ => {}
                }
            }
        }

        // Emit type-specialized record structs (before the state struct so they can be referenced)
        if self.struct_registry.has_structs() {
            writeln!(self.out, "// Type-specialized record structs").expect(WRITE_TO_STRING_ERR);
            self.out
                .push_str(&self.struct_registry.emit_all_definitions());
        }

        self.emit_state_struct(&mod_name, &variables)?;
        self.emit_state_machine(
            &mod_name,
            &variables,
            init_op,
            next_op,
            &invariants,
            &recursive_ops,
        )?;

        if options.generate_checker {
            self.emit_checker_module(&mod_name, &invariants)?;
            if let Some(checker_map) = &options.checker_map {
                self.emit_checker_impls(&mod_name, &variables, checker_map)?;
            }
        } else if options.checker_map.is_some() {
            return Err(CodegenError::CheckerMapRequiresChecker);
        }

        if options.generate_proptest {
            self.emit_proptest(&mod_name, &invariants)?;
        }

        if options.generate_kani {
            self.emit_kani_harness(&mod_name, &invariants)?;
        }

        Ok(())
    }

    fn emit_state_struct(&mut self, name: &str, variables: &[String]) -> CgResult {
        writeln!(self.out, "/// State for {}", name).expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "#[derive(Clone, Debug, PartialEq, Eq, Hash)]")
            .expect(WRITE_TO_STRING_ERR);
        writeln!(self.out, "pub struct {}State {{", to_pascal_case(name))
            .expect(WRITE_TO_STRING_ERR);
        for var in variables {
            let rust_var = to_snake_case(var);
            let rust_type = self
                .var_types
                .get(var)
                .map(|t| t.to_rust_type_with_structs(&self.struct_registry))
                .unwrap_or_else(|| "TlaValue".to_string());
            writeln!(self.out, "    pub {}: {},", rust_var, rust_type).expect(WRITE_TO_STRING_ERR);
        }
        writeln!(self.out, "}}").expect(WRITE_TO_STRING_ERR);
        writeln!(self.out).expect(WRITE_TO_STRING_ERR);
        Ok(())
    }
}

#[cfg(test)]
pub(super) fn test_module_env() -> CodegenModuleEnv {
    CodegenModuleEnv::default()
}

#[cfg(test)]
pub(super) fn test_module_name() -> String {
    "Test".to_string()
}

#[cfg(test)]
fn test_op_types() -> &'static HashMap<String, TlaType> {
    static EMPTY: std::sync::OnceLock<HashMap<String, TlaType>> = std::sync::OnceLock::new();
    EMPTY.get_or_init(HashMap::new)
}

#[cfg(test)]
fn test_op_param_types() -> &'static HashMap<String, Vec<TlaType>> {
    static EMPTY: std::sync::OnceLock<HashMap<String, Vec<TlaType>>> = std::sync::OnceLock::new();
    EMPTY.get_or_init(HashMap::new)
}

#[cfg(test)]
fn build_test_emitter<'a>(
    out: &'a mut String,
    var_types: &'a HashMap<String, TlaType>,
    op_defs: &'a HashMap<String, OperatorDef>,
    state_vars: HashSet<String>,
) -> RustEmitter<'a> {
    RustEmitter {
        out,
        var_types,
        op_types: test_op_types(),
        op_param_types: test_op_param_types(),
        op_defs,
        module_env: test_module_env(),
        state_vars,
        recursive_helpers: HashSet::new(),
        recursive_helpers_needing_state: HashSet::new(),
        in_recursive_helper: Cell::new(false),
        module_name: test_module_name(),
        indent: 0,
        struct_registry: StructRegistry::new(),
    }
}

#[cfg(test)]
mod tests;
