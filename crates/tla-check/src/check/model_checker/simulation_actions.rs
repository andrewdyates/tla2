// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Action-plan helpers for simulation mode.
//!
//! Contains the action detection, template building, and per-action diff
//! generation used by `simulate()`. Also houses free functions for
//! trace record construction and the int-func interning guard.
//!
//! Extracted from simulation.rs to reduce file size.

use super::{ArrayState, CheckError, DiffSuccessor, ModelChecker, OperatorDef};
use crate::action_instance::ActionInstance;
use crate::EvalCheckError;

/// Convert an `ArrayState` to a TLA+ record value for trace recording.
pub(super) fn array_state_trace_record(
    state: &ArrayState,
    registry: &crate::var_index::VarRegistry,
) -> crate::Value {
    let mut builder = crate::value::RecordBuilder::new();
    for (idx, name) in registry.iter() {
        builder.insert(tla_core::intern_name(name), state.get(idx));
    }
    crate::Value::Record(builder.build())
}

/// Wrap trace records into a TLA+ tuple value.
pub(super) fn trace_records_value(records: &[crate::Value]) -> crate::Value {
    crate::Value::Tuple(records.to_vec().into())
}

/// RAII guard that disables `IntIntervalFunc` interning for simulation.
///
/// Part of #3316: Interning deduplicates small function values across states,
/// useful for BFS where many states share identical sub-values. In simulation
/// mode, states are on unique random traces — interning adds per-EXCEPT
/// overhead (hash all values + DashMap lookup) with minimal memory benefit.
pub(super) struct SimulationIntFuncInterningGuard;

impl SimulationIntFuncInterningGuard {
    pub(super) fn new() -> Self {
        tla_value::set_skip_int_func_interning(true);
        Self
    }
}

impl Drop for SimulationIntFuncInterningGuard {
    fn drop(&mut self) {
        tla_value::set_skip_int_func_interning(false);
    }
}

/// Action plan for split-action simulation.
///
/// Part of #3316: Pre-builds per-action `OperatorDef` ONCE. Previously,
/// `generate_diffs_for_action` cloned the template and recompiled on
/// EVERY simulation step.
///
/// Part of #3433: Removed `CompiledAction` field. Successor generation
/// now routes through the unified AST/TIR engine, same as sequential BFS.
pub(super) struct SimulationActionPlan {
    pub(super) instance: ActionInstance,
    pub(super) action_def: OperatorDef,
}

impl ModelChecker<'_> {
    /// Detect TLC-style split action instances from the Next relation.
    ///
    /// Part of #3316: Reuses the shared splitter so simulation chooses from the
    /// same witness-level action list as TLC and BFS. This keeps the random-walk
    /// action distribution aligned with `Tool.getActions()`.
    pub(super) fn detect_simulation_actions(&self, next_name: &str) -> Vec<ActionInstance> {
        let resolved_name = self.ctx.resolve_op_name(next_name).to_string();
        let next_def = match self.module.op_defs.get(&resolved_name) {
            Some(def) => def,
            None => return Vec::new(),
        };
        crate::action_instance::split_action_instances(&self.ctx, &next_def.body)
            .unwrap_or_default()
    }

    /// Build the OperatorDef template for single-action evaluation.
    ///
    /// Part of #3316: Creates a template with the Next def's metadata (name, params,
    /// contains_prime, etc.) whose body gets swapped for each action's expression.
    /// When the inline NEXT body is a single Ident reference, resolves through it
    /// to use the actual operator's definition as the template.
    pub(super) fn build_action_template(&self, next_name: &str) -> Option<OperatorDef> {
        let resolved_name = self.ctx.resolve_op_name(next_name).to_string();
        let next_def = self.module.op_defs.get(&resolved_name)?;

        // If the body is a single Ident reference, use the inner operator's def
        let def_to_use = if let tla_core::ast::Expr::Ident(ref inner_name, _) = next_def.body.node {
            let inner_resolved = self.ctx.resolve_op_name(inner_name).to_string();
            self.module.op_defs.get(&inner_resolved).unwrap_or(next_def)
        } else {
            next_def
        };

        Some(OperatorDef {
            name: def_to_use.name.clone(),
            params: def_to_use.params.clone(),
            body: def_to_use.body.clone(), // placeholder, swapped per action
            local: def_to_use.local,
            contains_prime: def_to_use.contains_prime,
            guards_depend_on_prime: false,
            has_primed_param: def_to_use.has_primed_param,
            is_recursive: false,
            self_call_count: 0,
        })
    }

    /// Generate successor diffs by evaluating a single detected action.
    ///
    /// Part of #3316: Returns lightweight DiffSuccessor objects instead of full States.
    /// Only the chosen successor needs materialization, avoiding N-1 allocations.
    ///
    /// Part of #3433: Routes through the unified AST/TIR engine directly,
    /// replacing the previous compiled-action-first + fallback pattern.
    pub(super) fn generate_diffs_for_action(
        &mut self,
        current_arr: &ArrayState,
        raw_next_name: &str,
        resolved_next_name: &str,
        action_def: &OperatorDef,
        bindings: &[(std::sync::Arc<str>, crate::Value)],
    ) -> Result<Vec<DiffSuccessor>, CheckError> {
        let _scope_guard = self.ctx.scope_guard();
        let stack_mark = self.ctx.mark_stack();
        for (name, value) in bindings {
            self.ctx
                .push_binding(std::sync::Arc::clone(name), value.clone());
        }
        let tir_program = self.tir_parity.as_ref().and_then(|tir| {
            tir.make_tir_program_for_selected_eval_name(raw_next_name, resolved_next_name)
        });
        let result = crate::enumerate::enumerate_successors_array_as_diffs(
            &mut self.ctx,
            action_def,
            current_arr,
            &self.module.vars,
            tir_program.as_ref(),
        );
        self.ctx.pop_to_mark(&stack_mark);
        match result {
            Ok(Some(diffs)) => Ok(diffs),
            Ok(None) => Ok(Vec::new()),
            Err(e) => Err(CheckError::from(EvalCheckError::Eval(e))),
        }
    }

    /// Build action plans for split-action simulation.
    ///
    /// Part of #3316: Pre-builds per-action `OperatorDef` ONCE at simulation start.
    ///
    /// Part of #3433: No longer compiles actions — plans are AST-native only.
    pub(super) fn build_action_plans(
        &self,
        next_name: &str,
        simulation_actions: Vec<ActionInstance>,
    ) -> Vec<SimulationActionPlan> {
        let template = match self.build_action_template(next_name) {
            Some(t) => t,
            None => return Vec::new(),
        };
        simulation_actions
            .into_iter()
            .map(|instance| {
                let action_def = OperatorDef {
                    name: template.name.clone(),
                    params: template.params.clone(),
                    body: instance.expr.clone(),
                    local: template.local,
                    contains_prime: template.contains_prime,
                    guards_depend_on_prime: false,
                    has_primed_param: template.has_primed_param,
                    is_recursive: false,
                    self_call_count: 0,
                };
                SimulationActionPlan {
                    instance,
                    action_def,
                }
            })
            .collect()
    }
}
