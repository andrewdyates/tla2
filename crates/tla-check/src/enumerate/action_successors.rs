// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::debug_enum;
use super::unified::EnumParams;
use super::{unified, EvalCtx, EvalError, Spanned, State};
use crate::state::{ArrayState, UndoEntry};
use crate::var_index::VarRegistry;
use std::sync::Arc;
use tla_core::ast::Expr;

debug_flag!(debug_liveness_enum, "TLA2_DEBUG_LIVENESS_ENUM");

/// Enumerate successors from an arbitrary action expression.
///
/// This is used for <code>ENABLED&lt;&lt;A&gt;&gt;_vars</code> evaluation in liveness checking, where we need
/// to check if the action produces any non-stuttering successor (vars' ≠ vars).
///
/// Unlike `enumerate_successors` which takes an `OperatorDef`, this function takes
/// a raw expression, making it suitable for evaluating sub-actions from fairness
/// constraints.
///
/// # Arguments
/// * `ctx` - Evaluation context with current state bound
/// * `action` - The action expression to enumerate
/// * `current_state` - The current state
/// * `vars` - Variable names for the spec
///
/// # Returns
/// Vector of successor states (may include stuttering - caller should filter if needed).
pub fn enumerate_action_successors(
    ctx: &mut EvalCtx,
    action: &Spanned<Expr>,
    current_state: &State,
    vars: &[Arc<str>],
) -> Result<Vec<State>, EvalError> {
    // Part of #575: Debug liveness enumeration
    debug_block!(debug_liveness_enum(), {
        eprintln!("[DEBUG LIVENESS ENUM] Starting enumerate_action_successors");
        eprintln!("[DEBUG LIVENESS ENUM] action={:?}", action.node);
    });
    // Bind current state variables to ctx.env so they can be accessed during enumeration.
    // This is required for correctness: enumerate_unified/extract_symbolic_assignments
    // evaluate IF conditions using `eval(ctx, cond)`, which looks up state vars in ctx.env.
    // Without this binding, guard expressions like `light = \"off\"` fail to find state vars.
    //
    // Note: enumerate_successors() already does this binding, but enumerate_action_successors
    // was missing it, causing bugs in liveness checking (#575) where fairness constraints
    // failed because IF conditions couldn't find state variable values.
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    // Part of #1262: Use unified enumeration path instead of legacy next_rec.
    // Build ArrayState from current State, run enumerate_unified, convert results.
    let registry = if !ctx.var_registry().is_empty() {
        ctx.var_registry().clone()
    } else {
        VarRegistry::from_names(vars.iter().cloned())
    };
    let current_array = ArrayState::from_state(current_state, &registry);

    let mut base = current_array.clone();
    base.ensure_fp_cache_with_value_fps(&registry);

    let mut working = current_array.clone_for_working();
    let mut undo_stack: Vec<UndoEntry> = Vec::with_capacity(vars.len() * 2);
    let mut diffs = Vec::with_capacity(8);

    let params = EnumParams::new(vars, &registry, &base);
    let mut rec = unified::RecState {
        working: &mut working,
        undo: &mut undo_stack,
        results: &mut diffs,
    };
    let enum_result = unified::enumerate_unified(ctx, action, &params, &mut rec);

    match enum_result {
        Ok(()) => {
            debug_eprintln!(
                debug_enum(),
                "enumerate_action_successors (unified): produced {} diffs, converting to State",
                diffs.len()
            );
            Ok(diffs
                .into_iter()
                .map(|d| {
                    let fp = d.fingerprint;
                    d.into_array_state(&current_array, &registry, Some(fp))
                        .to_state(&registry)
                })
                .collect())
        }
        Err(e) => {
            // Fix #1552: TLC propagates ALL errors from action evaluation fatally.
            // No suppression at the action level — errors terminate model checking.
            Err(e)
        }
    }
}
