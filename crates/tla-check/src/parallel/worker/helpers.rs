// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Worker helper functions: VIEW fingerprinting and context initialization.
//!
//! Part of #2016: extracted from the monolithic `worker.rs`.
//! Part of #2492: decomposed into `coordination.rs` and `successors/`.
//! Part of #2356 Phase 4: legacy re-exports removed — `run_unified.rs` now
//! delegates to `run_bfs_worker` via `ParallelTransport`, which imports
//! coordination and WorkerBfsCtx directly.

use super::super::{WorkerResult, WorkerStats};
use super::WorkerModelConfig;
use crate::check::CheckError;
use crate::constants::bind_constants_from_config;
use crate::eval::EvalCtx;
use crate::state::Fingerprint;
use crate::EvalCheckError;
use crossbeam_channel::Sender;
use std::sync::atomic::{AtomicBool, Ordering};

/// Compute VIEW fingerprint from ArrayState (avoids State/OrdMap construction).
///
/// Part of #3022: ArrayState variant eliminates redundant State conversion.
pub(in crate::parallel) fn compute_view_fingerprint_array(
    ctx: &mut EvalCtx,
    array_state: &crate::state::ArrayState,
    view_name: &str,
    bfs_level: u32,
) -> Result<Fingerprint, CheckError> {
    crate::checker_ops::compute_view_fingerprint_array(ctx, array_state, view_name, bfs_level)
}

/// Initialize worker evaluation context and bind constants.
///
/// Returns `Err(())` after reporting the error to `result_tx`.
pub(super) fn init_worker_ctx(
    model: &WorkerModelConfig,
    stop_flag: &AtomicBool,
    result_tx: &Sender<WorkerResult>,
    stats: &mut WorkerStats,
) -> Result<EvalCtx, ()> {
    let mut ctx = EvalCtx::new();
    // Part of #1102: Propagate input_base_dir so IO builtins (ndJsonDeserialize, etc.)
    // can resolve relative file paths against the spec directory.
    ctx.set_input_base_dir(model.input_base_dir.clone());

    // Shared module loading sequence: set extended_module_names, load unqualified
    // modules, load main module, then load instance modules (Part of #810).
    let ext_refs: Vec<&tla_core::ast::Module> = model.extended_modules.iter().collect();
    crate::checker_ops::load_modules_into_ctx(
        &mut ctx,
        &model.module,
        &ext_refs,
        &model.unqualified_modules,
        true, // load instances for I!Op references
    );

    // Register state variables in VarRegistry for efficient array-based state handling
    ctx.register_vars(model.vars.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();

    // Bind constants from config
    if let Err(e) = bind_constants_from_config(&mut ctx, &model.config) {
        stop_flag.store(true, Ordering::SeqCst);
        super::coordination::send_result(
            result_tx,
            WorkerResult::Error(EvalCheckError::Eval(e).into(), std::mem::take(stats)),
        );
        return Err(());
    }

    // Part of #2753: Pre-evaluate constant operators for O(1) lookup during BFS.
    // Workers build fresh EvalCtx, so this must run per-worker (not just in prepare_check).
    crate::check::precompute_constant_operators(&mut ctx);
    // Part of #2895: Promote env constants to precomputed_constants.
    crate::check::promote_env_constants_to_precomputed(&mut ctx);
    // Part of #3961: Build ident resolution hints for eval_ident fast-path dispatch.
    crate::check::build_ident_hints(&mut ctx);

    Ok(ctx)
}
