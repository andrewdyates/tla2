// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR expression interpreter.
//!
//! Evaluates `TirExpr` nodes from `tla-tir` using the existing `EvalCtx`
//! runtime and the shared value-layer helpers from `tla-eval`.
//!
//! This is the active TIR-side evaluation surface in `tla-eval`. It reuses
//! the existing binding stacks, runtime state, and value semantics rather than
//! maintaining a separate interpreter stack.
//!
//! # Architecture
//!
//! - `bytecode_integration.rs` — bytecode VM cache, stats, and `TirProgram` bridge
//! - `dispatch.rs` — `match` over `TirExpr` for expression evaluation
//! - `dispatch_bindings.rs` — Step 3: quantifiers, comprehensions, bindings
//! - `dispatch_functions.rs` — operator application, function sets, and EXCEPT
//! - `dispatch_structured.rs` — records, tuples, ranges, and other structured nodes
//! - `dispatch_values.rs` — sets, CASE, LET, and value-level helpers
//! - `program.rs` — `TirProgram` wrapper for lazy operator lowering
//! - `probe.rs` — instrumentation for TIR evaluation attempts and closure bodies
//! - `mod.rs` — public entry points (`eval_tir`, `TirProgram`)
//!
//! Recursive `try_resolve_operator_tir(...)` lowering remains optional and
//! guarded by `TLA2_TIR_RECURSIVE_RESOLVE=1`.

mod bytecode_integration;
mod dispatch;
mod dispatch_bindings;
mod dispatch_functions;
mod dispatch_structured;
mod dispatch_values;
mod probe;
mod program;
mod program_cache;

use std::cell::Cell;
use tla_core::Spanned;
use tla_tir::TirExpr;
use tla_value::ClosureValue;

pub(crate) use tla_tir::StoredTirBody;

pub(crate) fn closure_tir_body_expr(closure: &ClosureValue) -> Option<&Spanned<TirExpr>> {
    let tir_body = closure.tir_body()?;
    let stored = tir_body.as_any().downcast_ref::<StoredTirBody>();
    debug_assert!(
        stored.is_some(),
        "ClosureValue::tir_body stored a non-StoredTirBody implementation"
    );
    stored.map(StoredTirBody::expr)
}

/// Return the Arc-wrapped TIR body from a closure, if present.
///
/// Part of #4113: callers that need to clone or store a TIR body can use
/// `Arc::clone()` (O(1) refcount bump) instead of deep-cloning the
/// `Spanned<TirExpr>` tree.
#[allow(dead_code)]
pub(crate) fn closure_tir_body_arc(
    closure: &ClosureValue,
) -> Option<std::sync::Arc<Spanned<TirExpr>>> {
    let tir_body = closure.tir_body()?;
    let stored = tir_body.as_any().downcast_ref::<StoredTirBody>()?;
    Some(stored.arc())
}

// Part of #3392: dynamic-scope TirProgram resolver for recursive TIR evaluation.
//
// When a TirProgram is evaluating (via eval_named_op or try_eval_expr_detailed),
// it installs itself as the active resolver. Nested user-defined operator
// references in eval_tir_name / eval_tir_operator_ref can then lower and
// evaluate through TIR instead of bouncing back to the AST evaluator.

thread_local! {
    /// Pointer to the active `TirProgram` during TIR evaluation. Null when no
    /// TIR evaluation is in flight. The raw pointer avoids lifetime issues in
    /// the thread-local; the RAII `TirProgramGuard` ensures validity.
    static CURRENT_TIR_PROGRAM: Cell<*const ()> = const { Cell::new(std::ptr::null()) };
}

/// RAII guard that installs a `TirProgram` as the active resolver for nested
/// TIR evaluation. Restores the previous value on drop.
pub(crate) struct TirProgramGuard {
    prev: *const (),
}

impl Drop for TirProgramGuard {
    fn drop(&mut self) {
        CURRENT_TIR_PROGRAM.with(|c| c.set(self.prev));
    }
}

/// Install a `TirProgram` as the current dynamic-scope resolver.
///
/// While the returned guard is alive, `try_resolve_operator_tir()` can lower
/// user-defined operators through TIR instead of falling back to AST.
pub(crate) fn install_tir_program<'a>(program: &'a TirProgram<'a>) -> TirProgramGuard {
    let ptr = program as *const TirProgram<'a> as *const ();
    let prev = CURRENT_TIR_PROGRAM.with(|c| c.replace(ptr));
    TirProgramGuard { prev }
}

/// Try to lower a named operator to TIR using the currently-installed `TirProgram`.
///
/// Returns `Some(body)` if there is an active `TirProgram` and lowering succeeds.
/// Returns `None` if no program is active or lowering fails.
///
/// DISABLED (#3392 measurement): recursive TIR resolution regresses sunder_cargo_lock
/// from 6.68x to 9.15x (37% worse). TIR dispatch is slower than AST dispatch due to
/// two-level matching and quantifier EvalCtx cloning. Keeping operators in TIR is
/// counterproductive until TIR dispatch itself reaches AST parity. Infrastructure
/// preserved for re-enablement after dispatch optimization.
/// Enable: `TLA2_TIR_RECURSIVE_RESOLVE=1`
pub(crate) fn try_resolve_operator_tir(name: &str) -> Option<std::sync::Arc<Spanned<TirExpr>>> {
    static ENABLED: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
        std::env::var("TLA2_TIR_RECURSIVE_RESOLVE").map_or(false, |v| v == "1")
    });
    if !*ENABLED {
        return None;
    }
    let ptr = CURRENT_TIR_PROGRAM.with(|c| c.get());
    if ptr.is_null() {
        return None;
    }
    // SAFETY: pointer installed by `install_tir_program` which holds a reference
    // to a live TirProgram on the stack. The RAII guard ensures the pointer is
    // valid for exactly the scope where the TirProgram is alive.
    let program: &TirProgram<'_> = unsafe { &*(ptr as *const TirProgram<'_>) };
    program.get_or_lower(name).ok()
}

/// Defense-in-depth: null the `CURRENT_TIR_PROGRAM` thread-local.
///
/// Called from `clear_for_test_reset()` / `clear_for_run_reset()` to ensure no
/// stale TIR resolver pointer survives across independent model-checker runs.
/// The RAII `TirProgramGuard` should already null this, but if an error path
/// defeats the guard's drop, a stale pointer causes undefined behavior.
///
/// Part of #3402.
pub fn reset_current_tir_program() {
    CURRENT_TIR_PROGRAM.with(|c| c.set(std::ptr::null()));
}

pub(crate) use bytecode_integration::clear_bytecode_vm_stats;
pub use bytecode_integration::{
    aggregate_bytecode_vm_stats, bytecode_vm_enabled, bytecode_vm_stats,
    note_bytecode_vm_execution, note_bytecode_vm_fallback,
};
#[cfg(test)]
pub(crate) use bytecode_integration::{
    bytecode_vm_enabled_from_env_value, set_bytecode_vm_test_overrides,
    BytecodeVmTestOverridesGuard,
};
pub use dispatch::eval_tir;
pub(crate) use probe::record_closure_body_eval;
pub use probe::TirExprEvalAttempt;
#[doc(hidden)]
pub use probe::{
    enable_tir_eval_probe, tir_eval_probe_snapshot, TirEvalProbeCounts,
    TIR_CLOSURE_BODY_PROBE_LABEL,
};
pub use program::{TirProgram, TirProgramCaches};

/// Whether TIR preprocessing (NNF, keramelization, constant folding) is enabled.
///
/// Enabled by default. Set `TLA2_NO_PREPROCESS=1` or pass `--no-preprocess` to
/// the CLI to disable. The preprocessing pipeline normalizes TIR expression trees
/// after lowering and before evaluation/caching, enabling better short-circuit
/// evaluation and eliminating dead branches.
pub(crate) fn preprocess_enabled() -> bool {
    static ENABLED: std::sync::LazyLock<bool> =
        std::sync::LazyLock::new(|| std::env::var("TLA2_NO_PREPROCESS").map_or(true, |v| v != "1"));
    *ENABLED
}

/// Whether TIR partial evaluation of CONSTANTS is enabled.
///
/// Disabled by default. Set `TLA2_PARTIAL_EVAL=1` or pass `--partial-eval` to
/// the CLI to enable. When enabled AND a `ConstantEnv` is attached to the
/// `TirProgram`, references to module-level `CONSTANT` names are substituted
/// with their concrete `Value` at TIR preprocessing time — before the existing
/// preprocessing pipeline runs. Downstream passes (const_prop, inlining, tMIR
/// lowering) then see concrete literals instead of symbolic names.
///
/// This is the first "structural supremacy" pillar (see
/// `designs/2026-04-18-supremacy-pillar-partial-eval.md`): specialization per
/// concrete spec configuration is something TLC / HotSpot cannot perform by
/// construction, because the JVM does not know the CONSTANT assignment is
/// frozen after spec load.
///
/// Part of #4251.
pub(crate) fn partial_eval_enabled() -> bool {
    static ENABLED: std::sync::LazyLock<bool> =
        std::sync::LazyLock::new(|| std::env::var("TLA2_PARTIAL_EVAL").is_ok_and(|v| v == "1"));
    *ENABLED
}
