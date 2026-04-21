// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EvalCtx registration and config mutation methods: operator replacement,
//! constant registration, variable registration, and state-var resolution.
//! Part of #2764 / #1643.

use crate::EvalCtx;
use std::sync::Arc;
use tla_core::ast::OperatorDef;

impl EvalCtx {
    // ---- Registration/config mutation methods ----

    /// Add an operator replacement (for config `CONSTANT Op <- Replacement`)
    pub fn add_op_replacement(&mut self, from: String, to: String) {
        Arc::make_mut(&mut self.stable_mut().shared)
            .op_replacements
            .insert(from, to);
    }

    /// Register a config-overridden constant.
    /// This marks the constant so that lookups check env bindings BEFORE operator definitions.
    pub fn add_config_constant(&mut self, name: String) {
        Arc::make_mut(&mut self.stable_mut().shared)
            .config_constants
            .insert(name);
    }

    /// Check if a name is a config-overridden constant.
    #[inline]
    pub fn is_config_constant(&self, name: &str) -> bool {
        self.shared.config_constants.contains(name)
    }
    /// Check if an operator name came from a THEOREM/LEMMA declaration (#1105).
    #[inline]
    pub fn is_theorem_op(&self, name: &str) -> bool {
        self.shared.theorem_op_names.contains(name)
    }

    /// Register a variable in the variable registry. Returns the assigned VarIndex.
    pub fn register_var(&mut self, name: impl Into<Arc<str>>) -> crate::var_index::VarIndex {
        Arc::make_mut(&mut self.stable_mut().shared)
            .var_registry
            .register(name)
    }

    /// Register multiple variables in the variable registry
    /// Call this once at module load time with all state variables
    pub fn register_vars(&mut self, names: impl IntoIterator<Item = impl Into<Arc<str>>>) {
        let registry = &mut Arc::make_mut(&mut self.stable_mut().shared).var_registry;
        for name in names {
            registry.register(name);
        }
    }

    /// Resolve state-variable identifiers in loaded operator bodies to `Expr::StateVar`.
    pub fn resolve_state_vars_in_loaded_ops(&mut self) {
        let registry = self.shared.var_registry.clone();
        if registry.is_empty() {
            return;
        }

        let shared = Arc::make_mut(&mut self.stable_mut().shared);

        let op_names: Vec<String> = shared.ops.keys().cloned().collect();
        for name in op_names {
            let Some(def) = shared.ops.get(&name).cloned() else {
                continue;
            };
            let mut def_cloned = (*def).clone();
            crate::state_var::resolve_state_vars_in_op_def(&mut def_cloned, &registry);
            shared.ops.insert(name, Arc::new(def_cloned));
        }

        let module_names: Vec<String> = shared.instance_ops.keys().cloned().collect();
        for module_name in module_names {
            let Some(mut ops) = shared.instance_ops.get(&module_name).cloned() else {
                continue;
            };
            let op_names: Vec<String> = ops.keys().cloned().collect();
            for op_name in op_names {
                let Some(def) = ops.get(&op_name).cloned() else {
                    continue;
                };
                let mut def_cloned = (*def).clone();
                crate::state_var::resolve_state_vars_in_op_def(&mut def_cloned, &registry);
                ops.insert(op_name, Arc::new(def_cloned));
            }
            shared.instance_ops.insert(module_name, ops);
        }

        let instance_names: Vec<String> = shared.instances.keys().cloned().collect();
        for instance_name in instance_names {
            let Some(mut info) = shared.instances.get(&instance_name).cloned() else {
                continue;
            };
            for sub in &mut info.substitutions {
                crate::state_var::resolve_state_vars_in_substitution(sub, &registry);
            }
            shared.instances.insert(instance_name, info);
        }
    }

    /// Add an operator definition
    pub fn define_op(&mut self, name: String, def: OperatorDef) {
        Arc::make_mut(&mut self.stable_mut().shared)
            .ops
            .insert(name, Arc::new(def));
    }
}
