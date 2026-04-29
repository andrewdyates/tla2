// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, DiffSuccessor, State};
use crate::var_index::VarRegistry;
use crate::Value;
use std::sync::Arc;

use super::successor_engine::{
    run_unified, run_unified_into, run_unified_into_with_options, run_unified_with_tir,
};
use super::{debug_enum, emit_debug_line, DiffSink};
use tla_core::VarIndex;

pub(crate) fn enumerate_successors(
    ctx: &mut EvalCtx,
    next_def: &tla_core::ast::OperatorDef,
    current_state: &State,
    vars: &[Arc<str>],
) -> Result<Vec<State>, EvalError> {
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    let registry = if !ctx.var_registry().is_empty() {
        ctx.var_registry().clone()
    } else {
        VarRegistry::from_names(vars.iter().cloned())
    };
    let current_array = ArrayState::from_state(current_state, &registry);

    let diffs = run_unified(ctx, &next_def.body, &current_array, vars, &registry)?;
    Ok(diffs
        .into_iter()
        .map(|d| {
            let fp = d.fingerprint;
            d.into_array_state(&current_array, &registry, Some(fp))
                .to_state(&registry)
        })
        .collect())
}

#[cfg(test)]
pub(crate) fn enumerate_successors_array(
    ctx: &mut EvalCtx,
    next_def: &tla_core::ast::OperatorDef,
    current_array: &ArrayState,
    vars: &[Arc<str>],
) -> Result<Vec<ArrayState>, EvalError> {
    enumerate_successors_array_with_tir(ctx, next_def, current_array, vars, None)
}

/// Enumerate successors with an optional TIR leaf evaluator.
///
/// Part of #3194: when `tir_leaf` is `Some`, leaf `eval` calls inside the
/// enumerator try TIR lowering + evaluation first, falling back to AST eval.
pub(crate) fn enumerate_successors_array_with_tir<'a>(
    ctx: &mut EvalCtx,
    next_def: &tla_core::ast::OperatorDef,
    current_array: &ArrayState,
    vars: &'a [Arc<str>],
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
) -> Result<Vec<ArrayState>, EvalError> {
    let registry = ctx.var_registry().clone();
    let diffs = run_unified_with_tir(
        ctx,
        &next_def.body,
        current_array,
        vars,
        &registry,
        tir_leaf,
    )?;
    Ok(diffs
        .into_iter()
        .map(|d| {
            let precomputed = if d.fingerprint.0 != 0 {
                Some(d.fingerprint)
            } else {
                None
            };
            d.into_array_state(current_array, &registry, precomputed)
        })
        .collect())
}

/// Enumerate successors as diffs with an optional TIR leaf evaluator.
pub(crate) fn enumerate_successors_array_as_diffs<'a>(
    ctx: &mut EvalCtx,
    next_def: &tla_core::ast::OperatorDef,
    current_array: &ArrayState,
    vars: &'a [Arc<str>],
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
) -> Result<Option<Vec<DiffSuccessor>>, EvalError> {
    let debug = debug_enum();
    let registry = ctx.var_registry().clone();
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());

    emit_debug_line(
        debug,
        format_args!(
            "enumerate_successors_array_as_diffs: next_def.body span={:?}",
            next_def.body.span
        ),
    );

    let diffs = run_unified_with_tir(
        ctx,
        &next_def.body,
        current_array,
        vars,
        &registry,
        tir_leaf,
    )?;
    Ok(Some(diffs))
}

pub(crate) fn enumerate_successors_array_as_diffs_with_current_values<'a>(
    ctx: &mut EvalCtx,
    next_def: &tla_core::ast::OperatorDef,
    current_array: &ArrayState,
    current_values: &[Value],
    vars: &'a [Arc<str>],
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
) -> Result<Option<Vec<DiffSuccessor>>, EvalError> {
    let debug = debug_enum();
    let registry = ctx.var_registry().clone();
    let _state_guard = ctx.bind_state_array_guard(current_values);

    emit_debug_line(
        debug,
        format_args!(
            "enumerate_successors_array_as_diffs: next_def.body span={:?}",
            next_def.body.span
        ),
    );

    let diffs = run_unified_with_tir(
        ctx,
        &next_def.body,
        current_array,
        vars,
        &registry,
        tir_leaf,
    )?;
    Ok(Some(diffs))
}

/// Enumerate successors as diffs into a DiffSink with an optional TIR leaf.
pub(crate) fn enumerate_successors_array_as_diffs_into<'a>(
    ctx: &mut EvalCtx,
    next_def: &tla_core::ast::OperatorDef,
    current_array: &ArrayState,
    vars: &'a [Arc<str>],
    sink: &mut dyn DiffSink,
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
) -> Result<(), EvalError> {
    let registry = ctx.var_registry().clone();
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());

    run_unified_into(
        ctx,
        &next_def.body,
        current_array,
        vars,
        &registry,
        sink,
        tir_leaf,
    )
}

pub(crate) fn enumerate_successors_array_as_diffs_into_with_current_values<'a>(
    ctx: &mut EvalCtx,
    next_def: &tla_core::ast::OperatorDef,
    current_array: &ArrayState,
    current_values: &[Value],
    vars: &'a [Arc<str>],
    sink: &mut dyn DiffSink,
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
) -> Result<(), EvalError> {
    let registry = ctx.var_registry().clone();
    let _state_guard = ctx.bind_state_array_guard(current_values);

    run_unified_into(
        ctx,
        &next_def.body,
        current_array,
        vars,
        &registry,
        sink,
        tir_leaf,
    )
}

/// Enumerate successors as diffs into a DiffSink with pc-guard hoisting.
///
/// Part of #3923: when `pc_var_idx` is `Some`, the unified enumerator skips
/// Or branches whose `pc = "label"` guard doesn't match the current state.
/// This avoids evaluating actions that are guaranteed to produce zero successors
/// in PlusCal-generated specs.
pub(crate) fn enumerate_successors_array_as_diffs_into_with_pc_hoist<'a>(
    ctx: &mut EvalCtx,
    next_def: &tla_core::ast::OperatorDef,
    current_array: &ArrayState,
    vars: &'a [Arc<str>],
    sink: &mut dyn DiffSink,
    tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
    pc_var_idx: Option<VarIndex>,
) -> Result<(), EvalError> {
    let registry = ctx.var_registry().clone();
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());

    run_unified_into_with_options(
        ctx,
        &next_def.body,
        current_array,
        vars,
        &registry,
        sink,
        tir_leaf,
        pc_var_idx,
    )
}

// Part of #3354 Slice 4: split-action test helpers removed —
// compiled_guard module and CompiledAction type are no longer available.
