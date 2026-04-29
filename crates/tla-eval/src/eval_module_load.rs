// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::implicit_instance_substitutions::collect_implicit_instance_targets;
use super::{EvalCtx, Expr, HashMap, InstanceInfo, Module, OperatorDef};
use std::sync::Arc;
use tla_core::ast::{Substitution, Unit};
use tla_core::name_intern::intern_name;
use tla_core::{apply_substitutions_v, expr_contains_prime_v};
use tla_core::{
    compute_contains_prime, compute_guards_depend_on_prime, compute_has_primed_param,
    compute_is_recursive,
};
// Module loading and instance registration methods for EvalCtx.
// Extracted from core.rs as part of #1219 decomposition.

use super::SharedCtx;

/// Register an operator definition, distinguishing simple instances, parametrized
/// instances, and regular operators. Part of #2969.
fn register_operator(shared: &mut SharedCtx, def: &OperatorDef) {
    if let Expr::InstanceExpr(module_name, substitutions) = &def.body.node {
        if def.params.is_empty() {
            // Simple instance: Buffer == INSTANCE Channel WITH ...
            shared.instances.insert(
                def.name.node.clone(),
                InstanceInfo {
                    module_name: module_name.clone(),
                    substitutions: substitutions.clone(),
                },
            );
        } else {
            // Parametrized instance: P(Succ) == INSTANCE ReachabilityProofs
            // Register as operator (not instance) to preserve formal params.
            // eval_module_ref_target uses def.params to build INSTANCE
            // substitutions from the actual argument expressions.
            shared
                .ops
                .insert(def.name.node.clone(), Arc::new(def.clone()));
        }
    } else {
        shared
            .ops
            .insert(def.name.node.clone(), Arc::new(def.clone()));
    }
}

fn materialize_expr_with_substitutions(
    body: &tla_core::Spanned<Expr>,
    substitutions: &[Substitution],
) -> tla_core::Spanned<Expr> {
    if matches!(body.node, Expr::InstanceExpr(..)) {
        apply_substitutions_v(body, substitutions)
    } else {
        EvalCtx::let_wrap_substitutions(body, substitutions)
    }
}

/// Clone a module and apply `INSTANCE ... WITH` substitutions to its importable bodies.
#[must_use]
pub fn materialize_module_with_substitutions(
    module: &Module,
    substitutions: &[Substitution],
) -> Module {
    if substitutions.is_empty() {
        return module.clone();
    }

    let mut materialized = module.clone();
    for unit in &mut materialized.units {
        match &mut unit.node {
            Unit::Operator(def) => {
                def.body = materialize_expr_with_substitutions(&def.body, substitutions);
            }
            Unit::Assume(assume) => {
                assume.expr = materialize_expr_with_substitutions(&assume.expr, substitutions);
            }
            Unit::Theorem(thm) => {
                thm.body = materialize_expr_with_substitutions(&thm.body, substitutions);
            }
            Unit::Instance(inst) => {
                for sub in &mut inst.substitutions {
                    sub.to = apply_substitutions_v(&sub.to, substitutions);
                }
            }
            Unit::Variable(_) | Unit::Constant(_) | Unit::Recursive(_) | Unit::Separator => {}
        }
    }

    compute_contains_prime(&mut materialized);
    compute_guards_depend_on_prime(&mut materialized);
    compute_has_primed_param(&mut materialized);
    compute_is_recursive(&mut materialized);
    materialized
}

fn register_action_subscript_spans(shared: &mut SharedCtx, module: &Module) {
    shared
        .action_subscript_spans
        .extend(module.action_subscript_spans.iter().copied());
}

impl EvalCtx {
    /// Register a named INSTANCE declaration
    ///
    /// For `InChan == INSTANCE Channel WITH Data <- Message, chan <- in`:
    /// - instance_name = "InChan"
    /// - module_name = "Channel"
    /// - substitutions = [(Data, Message), (chan, in)]
    pub fn register_instance(&mut self, instance_name: String, info: InstanceInfo) {
        Arc::make_mut(&mut self.stable_mut().shared)
            .instances
            .insert(instance_name, info);
    }

    /// Load operators from an instanced module
    ///
    /// Stores the operators separately so they can be looked up by instance reference
    pub fn load_instance_module(&mut self, module_name: String, module: &Module) {
        let shared = Arc::make_mut(&mut self.stable_mut().shared);
        // Part of #3148/#3150: named-instance property classification still needs
        // the original `[A]_v` / `<<A>>_v` provenance from the instanced module.
        register_action_subscript_spans(shared, module);
        let implicit_targets = collect_implicit_instance_targets(module);
        let mut ops = HashMap::new();
        for unit in &module.units {
            match &unit.node {
                tla_core::ast::Unit::Operator(def) => {
                    ops.insert(def.name.node.clone(), Arc::new(def.clone()));
                }
                tla_core::ast::Unit::Theorem(thm) => {
                    // Named theorems are registered as zero-arg operators so
                    // they can be referenced at runtime (e.g., MCVoting uses
                    // `ASSUME QuorumNonEmpty!:`). The parser fix for #2900
                    // handles the root cause (nested ASSUME/PROVE token leak);
                    // blanket-skipping theorems here broke specs like MCVoting.
                    if let Some(name) = &thm.name {
                        let def = OperatorDef {
                            name: name.clone(),
                            params: vec![],
                            body: thm.body.clone(),
                            local: false,
                            contains_prime: false,
                            guards_depend_on_prime: false,
                            has_primed_param: false,
                            is_recursive: false,
                            self_call_count: 0,
                        };
                        ops.insert(name.node.clone(), Arc::new(def));
                    }
                }
                _ => {}
            }
        }
        shared.instance_ops.insert(module_name, ops);
        shared
            .instance_implicit_targets
            .insert(module.name.node.clone(), implicit_targets);
    }

    /// Load operators from an instanced module INCLUDING operators from all
    /// modules it transitively EXTENDS.
    ///
    /// This is required for parametrized INSTANCE with EXTENDS. For example:
    ///   P(Succ) == INSTANCE ReachabilityProofs
    /// where ReachabilityProofs EXTENDS Reachability.
    /// When evaluating P(Succ)!Reachable0, operators from Reachability (like
    /// ReachableFrom) must be accessible.
    ///
    /// `module_by_name` should contain all loaded modules for EXTENDS resolution.
    pub fn load_instance_module_with_extends<'a>(
        &mut self,
        module_name: String,
        module: &'a Module,
        module_by_name: &rustc_hash::FxHashMap<&str, &'a Module>,
    ) {
        let shared = Arc::make_mut(&mut self.stable_mut().shared);
        let implicit_targets = collect_implicit_instance_targets(module);
        let mut ops = HashMap::new();

        // Collect the transitive EXTENDS chain using iterative DFS.
        // We need to process extended modules first (topological order).
        let mut extends_order: Vec<String> = Vec::new();
        let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();

        // Stack for iterative DFS: (module_name, phase)
        // phase=false: first visit - push extends, then revisit
        // phase=true: post-visit - add to order
        let mut stack: Vec<(String, bool)> = Vec::new();

        // Start with the module's direct extends
        for ext in module.extends.iter().rev() {
            stack.push((ext.node.clone(), false));
        }

        while let Some((name, post_visit)) = stack.pop() {
            if post_visit {
                extends_order.push(name);
            } else if visited.insert(name.clone()) {
                // Push post-visit marker
                stack.push((name.clone(), true));
                // Push extends in reverse order (so they're processed left-to-right)
                if let Some(m) = module_by_name.get(name.as_str()) {
                    for ext in m.extends.iter().rev() {
                        if !visited.contains(&ext.node) {
                            stack.push((ext.node.clone(), false));
                        }
                    }
                }
            }
        }

        // Load operators from extended modules first (so main module can override)
        for ext_name in &extends_order {
            if let Some(ext_mod) = module_by_name.get(ext_name.as_str()) {
                register_action_subscript_spans(shared, ext_mod);
                for unit in &ext_mod.units {
                    match &unit.node {
                        tla_core::ast::Unit::Operator(def) => {
                            ops.insert(def.name.node.clone(), Arc::new(def.clone()));
                        }
                        tla_core::ast::Unit::Theorem(thm) => {
                            if let Some(name) = &thm.name {
                                let def = OperatorDef {
                                    name: name.clone(),
                                    params: vec![],
                                    body: thm.body.clone(),
                                    local: false,
                                    contains_prime: false,
                                    guards_depend_on_prime: false,
                                    has_primed_param: false,
                                    is_recursive: false,
                                    self_call_count: 0,
                                };
                                ops.insert(name.node.clone(), Arc::new(def));
                            }
                        }
                        _ => {}
                    }
                }
                // Part of #2834: Also load operators from LOCAL INSTANCE declarations.
                // LOCAL INSTANCE brings the instanced module's operators into the
                // declaring module's scope. Without this, instance_ops for modules
                // with LOCAL INSTANCE miss those operators.
                for unit in &ext_mod.units {
                    if let tla_core::ast::Unit::Instance(inst) = &unit.node {
                        if inst.local {
                            if let Some(inst_mod) = module_by_name.get(inst.module.node.as_str()) {
                                register_action_subscript_spans(shared, inst_mod);
                                for inner_unit in &inst_mod.units {
                                    if let tla_core::ast::Unit::Operator(def) = &inner_unit.node {
                                        ops.entry(def.name.node.clone())
                                            .or_insert_with(|| Arc::new(def.clone()));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Load operators from the main module (can override extended)
        register_action_subscript_spans(shared, module);
        for unit in &module.units {
            match &unit.node {
                tla_core::ast::Unit::Operator(def) => {
                    ops.insert(def.name.node.clone(), Arc::new(def.clone()));
                }
                tla_core::ast::Unit::Theorem(thm) => {
                    if let Some(name) = &thm.name {
                        let def = OperatorDef {
                            name: name.clone(),
                            params: vec![],
                            body: thm.body.clone(),
                            local: false,
                            contains_prime: false,
                            guards_depend_on_prime: false,
                            has_primed_param: false,
                            is_recursive: false,
                            self_call_count: 0,
                        };
                        ops.insert(name.node.clone(), Arc::new(def));
                    }
                }
                _ => {}
            }
        }
        // Part of #2834: LOCAL INSTANCE operators from the main module itself
        for unit in &module.units {
            if let tla_core::ast::Unit::Instance(inst) = &unit.node {
                if inst.local {
                    if let Some(inst_mod) = module_by_name.get(inst.module.node.as_str()) {
                        register_action_subscript_spans(shared, inst_mod);
                        for inner_unit in &inst_mod.units {
                            if let tla_core::ast::Unit::Operator(def) = &inner_unit.node {
                                ops.entry(def.name.node.clone())
                                    .or_insert_with(|| Arc::new(def.clone()));
                            }
                        }
                    }
                }
            }
        }

        shared.instance_ops.insert(module_name, ops);
        shared
            .instance_implicit_targets
            .insert(module.name.node.clone(), implicit_targets);
    }

    /// Load operator definitions from a module
    ///
    /// This also detects named instances (operators with InstanceExpr body) and
    /// registers them in the instances map. To actually use those instances,
    /// you must also call `load_instance_module` for each instanced module.
    pub fn load_module(&mut self, module: &Module) {
        // Some call paths (notably tests) construct modules via `tla_core::lower()` directly,
        // which does not populate `OperatorDef.contains_prime` / `guards_depend_on_prime`.
        // These flags are required for correct next-state validation decisions (#188/#203).
        let mut module = module.clone();
        compute_contains_prime(&mut module);
        compute_guards_depend_on_prime(&mut module);
        compute_has_primed_param(&mut module);
        compute_is_recursive(&mut module);

        let shared = Arc::make_mut(&mut self.stable_mut().shared);
        register_action_subscript_spans(shared, &module);
        for unit in &module.units {
            match &unit.node {
                tla_core::ast::Unit::Operator(def) => {
                    register_operator(shared, def);
                }
                tla_core::ast::Unit::Theorem(thm) => {
                    // Named theorems are registered as zero-arg operators so
                    // they can be referenced at runtime (e.g., MCVoting uses
                    // `ASSUME QuorumNonEmpty!:`). The parser fix for #2900
                    // handles the root cause (nested ASSUME/PROVE token leak).
                    if let Some(name) = &thm.name {
                        let cp = expr_contains_prime_v(&thm.body.node);
                        let def = OperatorDef {
                            name: name.clone(),
                            params: vec![],
                            body: thm.body.clone(),
                            local: false,
                            contains_prime: cp,
                            guards_depend_on_prime: cp,
                            has_primed_param: false,
                            is_recursive: false,
                            self_call_count: 0,
                        };
                        shared.ops.insert(name.node.clone(), Arc::new(def));
                        // Track theorem origin to exclude from
                        // precompute_constant_operators (Part of #1105).
                        shared.theorem_op_names.insert(name.node.clone());
                    }
                }
                tla_core::ast::Unit::Assume(assume) => {
                    // Named assumes are accessible as zero-argument operators
                    // e.g., ASSUME PaxosAssume == /\ IsFiniteSet(Replicas) /\ ...
                    // can be referenced as PaxosAssume elsewhere
                    if let Some(name) = &assume.name {
                        let def = OperatorDef {
                            name: name.clone(),
                            params: vec![],
                            body: assume.expr.clone(),
                            local: false,
                            contains_prime: false,
                            guards_depend_on_prime: false,
                            has_primed_param: false,
                            is_recursive: false,
                            self_call_count: 0,
                        };
                        shared.ops.insert(name.node.clone(), Arc::new(def));
                    }
                }
                _ => {}
            }
        }
    }

    /// Load operator definitions from multiple modules (e.g., extended modules)
    ///
    /// Modules should be provided in dependency order (extended modules first, main module last).
    /// Later modules can override earlier definitions.
    pub fn load_modules(&mut self, modules: &[&Module]) {
        for module in modules {
            self.load_module(module);
        }
    }

    /// Get operator from an instanced module
    ///
    /// Looks up the operator in instance_ops only. For this to work, you must
    /// call `load_instance_module` for each module used in named instances.
    /// Returns reference through Arc (see #209 for why ops are Arc-wrapped).
    pub fn get_instance_op_arc(
        &self,
        module_name: &str,
        op_name: &str,
    ) -> Option<&Arc<OperatorDef>> {
        self.shared
            .instance_ops
            .get(module_name)
            .and_then(|ops| ops.get(op_name))
    }

    /// Looks up the operator in instance_ops only. For this to work, you must
    /// call `load_instance_module` for each module used in named instances.
    /// Returns reference through Arc (see #209 for why ops are Arc-wrapped).
    pub fn get_instance_op(&self, module_name: &str, op_name: &str) -> Option<&OperatorDef> {
        self.get_instance_op_arc(module_name, op_name)
            .map(Arc::as_ref)
    }

    /// Get instance info by name
    pub fn get_instance(&self, name: &str) -> Option<&InstanceInfo> {
        self.shared.instances.get(name)
    }

    /// Wrap an operator body in LET bindings that evaluate each INSTANCE
    /// substitution RHS exactly once, then rename references in the body.
    ///
    /// This preserves CSE: each substitution expression (e.g., `Node2Nat(active)`)
    /// is evaluated once per LET scope entry. References in the body become
    /// `__tla2_subst_{name}` which resolve via the evaluator's normal local_stack
    /// fast path — O(depth) with NameId integer comparison.
    fn let_wrap_substitutions(
        body: &tla_core::Spanned<Expr>,
        substitutions: &[tla_core::ast::Substitution],
    ) -> tla_core::Spanned<Expr> {
        use tla_core::ast::Substitution;
        use tla_core::Spanned;

        if substitutions.is_empty() {
            return body.clone();
        }

        // 1. Build LET definitions: __tla2_subst_{name} == <rhs_expr>
        let let_defs: Vec<OperatorDef> = substitutions
            .iter()
            .map(|sub| {
                let fresh_name = format!("__tla2_subst_{}", sub.from.node);
                OperatorDef {
                    name: Spanned {
                        node: fresh_name,
                        span: sub.from.span,
                    },
                    params: vec![],
                    body: sub.to.clone(),
                    local: true,
                    contains_prime: expr_contains_prime_v(&sub.to.node),
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                }
            })
            .collect();

        // 2. Build rename substitutions: original name -> Ident("__tla2_subst_{name}")
        let renames: Vec<Substitution> = substitutions
            .iter()
            .map(|sub| {
                let fresh_name = format!("__tla2_subst_{}", sub.from.node);
                // Part of #2993: Pre-intern synthetic rename to avoid runtime lookup_name_id().
                let name_id = intern_name(&fresh_name);
                Substitution {
                    from: sub.from.clone(),
                    to: Spanned {
                        node: Expr::Ident(fresh_name, name_id),
                        span: sub.to.span,
                    },
                }
            })
            .collect();

        // 3. Apply renames (identifier-to-identifier substitution — cheap, no expression duplication)
        let renamed_body = apply_substitutions_v(body, &renames);

        // 4. Wrap in LET ... IN renamed_body
        Spanned {
            node: Expr::Let(let_defs, Box::new(renamed_body)),
            span: body.span,
        }
    }
}
