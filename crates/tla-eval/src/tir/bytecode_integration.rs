// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bytecode VM integration for `TirProgram`.
//!
//! Owns the `BytecodeCache` (lazy compilation), stats counters, and the
//! `try_bytecode_eval` method that bridges TIR evaluation to the register VM.
//!
//! Extracted from `program.rs` per #3593.

use rustc_hash::FxHashMap;
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};

use tla_tir::bytecode::{BytecodeChunk, BytecodeCompiler, CalleeInfo, Opcode};
use tla_tir::TirExpr;
use tla_value::error::{EvalError, EvalResult};
use tla_value::Value;

use crate::bytecode_vm::{resolved_constants_with_bytecode_stdlib, BytecodeVm, VmError};
use crate::core::EvalCtx;

use super::TirProgram;

/// Cached bytecode compilation results for the current model-checking run.
///
/// Compilation happens lazily on first eval of each operator. Results are
/// cached so that subsequent states reuse the same compiled bytecode.
///
/// Part of #3583: Sprint 1 bytecode VM wiring.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResolvedConstantsKey {
    shared_ctx_id: u64,
    precomputed_constants_version: u64,
}

impl ResolvedConstantsKey {
    fn from_ctx(ctx: &EvalCtx) -> Self {
        Self {
            shared_ctx_id: ctx.shared().id(),
            precomputed_constants_version: ctx.shared().precomputed_constants_version(),
        }
    }
}

pub(crate) struct BytecodeCache {
    compiler: BytecodeCompiler,
    /// operator name → Ok(func_idx) or Err(()) for "not compilable"
    results: FxHashMap<String, Result<u16, ()>>,
    /// Identity of the constant environment the cached bytecode was compiled against.
    resolved_constants_key: Option<ResolvedConstantsKey>,
}

impl BytecodeCache {
    pub(super) fn new() -> Self {
        Self {
            compiler: BytecodeCompiler::new(),
            results: FxHashMap::default(),
            resolved_constants_key: None,
        }
    }

    pub(super) fn clear(&mut self) {
        self.compiler = BytecodeCompiler::new();
        self.results.clear();
        self.resolved_constants_key = None;
    }

    fn sync_resolved_constants(&mut self, ctx: &EvalCtx) {
        let resolved_constants_key = ResolvedConstantsKey::from_ctx(ctx);
        if self.resolved_constants_key == Some(resolved_constants_key) {
            return;
        }
        let op_repl = ctx.op_replacements();
        let op_repl_opt = if op_repl.is_empty() {
            None
        } else {
            Some(op_repl)
        };
        let resolved_constants =
            resolved_constants_with_bytecode_stdlib(ctx.precomputed_constants(), op_repl_opt);
        self.compiler = BytecodeCompiler::with_resolved_constants(resolved_constants);
        // Thread operator replacements (CONSTANT Foo <- Bar) so the compiler
        // can resolve identifiers through the replacement chain.
        if !op_repl.is_empty() {
            let replacements: std::collections::HashMap<String, String> = op_repl
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            self.compiler.set_op_replacements(replacements);
        }
        // Thread state variable name→index mapping so the compiler can resolve
        // Ident names that are actually state vars (TIR bodies lowered from raw
        // Module AST without prior state-var resolution).
        let var_registry = ctx.var_registry();
        if !var_registry.is_empty() {
            let state_vars: std::collections::HashMap<String, u16> = var_registry
                .iter()
                .map(|(idx, name)| (name.to_string(), idx.0))
                .collect();
            self.compiler.set_state_vars(state_vars);
        }
        self.results.clear();
        self.resolved_constants_key = Some(resolved_constants_key);
    }
}

fn parse_bytecode_vm_enabled(value: Option<&str>) -> bool {
    !matches!(value, Some("0"))
}

fn parse_bytecode_vm_stats_enabled(value: Option<&str>) -> bool {
    matches!(value, Some("1"))
}

/// Whether bytecode VM execution is enabled.
/// Default: enabled. Set `TLA2_BYTECODE_VM=0` to disable.
/// Enabled by default since Sprint 3 achieved full compilation coverage
/// on tested specs. Unsupported patterns such as captured Lambda bodies fall
/// back gracefully to TIR tree-walking (#3670).
pub fn bytecode_vm_enabled() -> bool {
    if let Some(enabled) = BYTECODE_VM_ENABLED_OVERRIDE.with(Cell::get) {
        return enabled;
    }
    BYTECODE_VM_ENABLED.with(|cached| {
        if let Some(enabled) = cached.get() {
            return enabled;
        }
        let enabled = parse_bytecode_vm_enabled(std::env::var("TLA2_BYTECODE_VM").ok().as_deref());
        cached.set(Some(enabled));
        enabled
    })
}

thread_local! {
    static BYTECODE_VM_ENABLED: Cell<Option<bool>> = const { Cell::new(None) };
    static BYTECODE_VM_ENABLED_OVERRIDE: Cell<Option<bool>> = const { Cell::new(None) };
    static BYTECODE_VM_STATS_ENABLED: Cell<Option<bool>> = const { Cell::new(None) };
    static BYTECODE_VM_STATS_ENABLED_OVERRIDE: Cell<Option<bool>> = const { Cell::new(None) };
    static BYTECODE_VM_EXECUTIONS: Cell<u64> = const { Cell::new(0) };
    static BYTECODE_VM_FALLBACKS: Cell<u64> = const { Cell::new(0) };
    static BYTECODE_VM_COMPILE_FAILURES: Cell<u64> = const { Cell::new(0) };
}

static BYTECODE_VM_TOTAL_EXECUTIONS: AtomicU64 = AtomicU64::new(0);
static BYTECODE_VM_TOTAL_FALLBACKS: AtomicU64 = AtomicU64::new(0);
static BYTECODE_VM_TOTAL_COMPILE_FAILURES: AtomicU64 = AtomicU64::new(0);

fn bytecode_vm_stats_enabled() -> bool {
    if let Some(enabled) = BYTECODE_VM_STATS_ENABLED_OVERRIDE.with(Cell::get) {
        return enabled;
    }
    BYTECODE_VM_STATS_ENABLED.with(|cached| {
        if let Some(enabled) = cached.get() {
            return enabled;
        }
        let enabled = parse_bytecode_vm_stats_enabled(
            std::env::var("TLA2_BYTECODE_VM_STATS").ok().as_deref(),
        );
        cached.set(Some(enabled));
        enabled
    })
}

fn bytecode_vm_reason_logs_enabled() -> bool {
    bytecode_vm_stats_enabled() || crate::eval_debug::debug_bytecode_vm()
}

pub(crate) fn record_bytecode_vm_execution() {
    if !bytecode_vm_stats_enabled() {
        return;
    }
    BYTECODE_VM_EXECUTIONS.with(|counter| counter.set(counter.get().saturating_add(1)));
    BYTECODE_VM_TOTAL_EXECUTIONS.fetch_add(1, Ordering::Relaxed);
}

/// Public alias for bytecode execution accounting used by external telemetry hooks.
pub fn note_bytecode_vm_execution() {
    record_bytecode_vm_execution();
}

pub(crate) fn record_bytecode_vm_fallback() {
    if !bytecode_vm_stats_enabled() {
        return;
    }
    BYTECODE_VM_FALLBACKS.with(|counter| counter.set(counter.get().saturating_add(1)));
    BYTECODE_VM_TOTAL_FALLBACKS.fetch_add(1, Ordering::Relaxed);
}

/// Public alias for bytecode fallback accounting used by external telemetry hooks.
pub fn note_bytecode_vm_fallback() {
    record_bytecode_vm_fallback();
}

pub(crate) fn record_bytecode_vm_compile_failure() {
    if !bytecode_vm_stats_enabled() {
        return;
    }
    BYTECODE_VM_COMPILE_FAILURES.with(|counter| counter.set(counter.get().saturating_add(1)));
    BYTECODE_VM_TOTAL_COMPILE_FAILURES.fetch_add(1, Ordering::Relaxed);
}

/// Return `(executions, fallbacks, compile_failures)` for the current thread.
#[must_use]
pub fn bytecode_vm_stats() -> (u64, u64, u64) {
    let executions = BYTECODE_VM_EXECUTIONS.with(Cell::get);
    let fallbacks = BYTECODE_VM_FALLBACKS.with(Cell::get);
    let compile_failures = BYTECODE_VM_COMPILE_FAILURES.with(Cell::get);
    (executions, fallbacks, compile_failures)
}

/// Return `(executions, fallbacks, compile_failures)` aggregated across all threads.
#[must_use]
pub fn aggregate_bytecode_vm_stats() -> (u64, u64, u64) {
    (
        BYTECODE_VM_TOTAL_EXECUTIONS.load(Ordering::Relaxed),
        BYTECODE_VM_TOTAL_FALLBACKS.load(Ordering::Relaxed),
        BYTECODE_VM_TOTAL_COMPILE_FAILURES.load(Ordering::Relaxed),
    )
}

pub(crate) fn clear_bytecode_vm_stats() {
    BYTECODE_VM_ENABLED.with(|cached| cached.set(None));
    BYTECODE_VM_STATS_ENABLED.with(|cached| cached.set(None));
    BYTECODE_VM_EXECUTIONS.with(|counter| counter.set(0));
    BYTECODE_VM_FALLBACKS.with(|counter| counter.set(0));
    BYTECODE_VM_COMPILE_FAILURES.with(|counter| counter.set(0));
    BYTECODE_VM_TOTAL_EXECUTIONS.store(0, Ordering::Relaxed);
    BYTECODE_VM_TOTAL_FALLBACKS.store(0, Ordering::Relaxed);
    BYTECODE_VM_TOTAL_COMPILE_FAILURES.store(0, Ordering::Relaxed);
}

#[cfg(test)]
pub(crate) fn bytecode_vm_enabled_from_env_value(value: Option<&str>) -> bool {
    parse_bytecode_vm_enabled(value)
}

#[cfg(test)]
pub(crate) struct BytecodeVmTestOverridesGuard {
    previous_enabled_override: Option<bool>,
    previous_stats_enabled_override: Option<bool>,
}

#[cfg(test)]
pub(crate) fn set_bytecode_vm_test_overrides(
    enabled: Option<bool>,
    stats_enabled: Option<bool>,
) -> BytecodeVmTestOverridesGuard {
    let previous_enabled_override = BYTECODE_VM_ENABLED_OVERRIDE.with(|cached| {
        let previous = cached.get();
        cached.set(enabled);
        previous
    });
    let previous_stats_enabled_override = BYTECODE_VM_STATS_ENABLED_OVERRIDE.with(|cached| {
        let previous = cached.get();
        cached.set(stats_enabled);
        previous
    });
    BYTECODE_VM_ENABLED.with(|cached| cached.set(None));
    BYTECODE_VM_STATS_ENABLED.with(|cached| cached.set(None));
    BytecodeVmTestOverridesGuard {
        previous_enabled_override,
        previous_stats_enabled_override,
    }
}

#[cfg(test)]
impl Drop for BytecodeVmTestOverridesGuard {
    fn drop(&mut self) {
        BYTECODE_VM_ENABLED_OVERRIDE.with(|cached| cached.set(self.previous_enabled_override));
        BYTECODE_VM_STATS_ENABLED_OVERRIDE
            .with(|cached| cached.set(self.previous_stats_enabled_override));
        BYTECODE_VM_ENABLED.with(|cached| cached.set(None));
        BYTECODE_VM_STATS_ENABLED.with(|cached| cached.set(None));
    }
}

fn bytecode_function_needs_next_state(
    chunk: &BytecodeChunk,
    func_idx: u16,
    visited: &mut std::collections::HashSet<u16>,
) -> bool {
    if !visited.insert(func_idx) {
        return false;
    }

    chunk
        .get_function(func_idx)
        .instructions
        .iter()
        .any(|opcode| match opcode {
            Opcode::LoadPrime { .. } => true,
            Opcode::SetPrimeMode { enable } => *enable,
            Opcode::Call { op_idx, .. } => {
                bytecode_function_needs_next_state(chunk, *op_idx, visited)
            }
            _ => false,
        })
}

impl<'a> TirProgram<'a> {
    /// Try to evaluate an operator via the bytecode VM.
    ///
    /// Returns:
    /// - `Some(Ok(value))` — VM executed successfully
    /// - `Some(Err(e))` — VM hit a real eval error (propagate, don't retry via tree-walk)
    /// - `None` — operator not compilable or VM returned Unsupported (fall through)
    ///
    /// Part of #3583: Sprint 1 bytecode VM wiring.
    pub(super) fn try_bytecode_eval(
        &self,
        ctx: &EvalCtx,
        name: &str,
        tir_body: &tla_core::Spanned<TirExpr>,
    ) -> Option<EvalResult<Value>> {
        // Phase 1: compile (mutable borrow, then drop)
        let func_idx = {
            let mut cache = self.bytecode_cache.borrow_mut();
            cache.sync_resolved_constants(ctx);
            match cache.results.get(name) {
                Some(Ok(idx)) => *idx,
                Some(Err(())) => return None,
                None => {
                    self.seed_bytecode_namespace_cache();
                    // Export root-namespace callee bodies after seeding so that
                    // parameterized operator references can compile as closure
                    // values with the correct INSTANCE-substituted AST body.
                    let callee_bodies: std::collections::HashMap<String, CalleeInfo> =
                        self.export_callee_bodies().into_iter().collect();
                    // Get params for the entry-point operator from the seeded cache.
                    let params: Vec<String> = self
                        .cache
                        .borrow()
                        .get(name)
                        .map(|op| op.params.clone())
                        .unwrap_or_default();

                    match cache.compiler.compile_expression_with_callees(
                        name,
                        &params,
                        tir_body,
                        &callee_bodies,
                    ) {
                        Ok(idx) => {
                            cache.results.insert(name.to_string(), Ok(idx));
                            idx
                        }
                        Err(e) => {
                            if bytecode_vm_reason_logs_enabled() {
                                eprintln!("[bytecode] compile failed: operator={name}, reason={e}");
                            }
                            record_bytecode_vm_compile_failure();
                            cache.results.insert(name.to_string(), Err(()));
                            return None;
                        }
                    }
                }
            }
        };

        // Extract state arrays from EvalCtx.
        let state_env = ctx.state_env?;

        // Phase 2: execute (immutable borrow)
        let cache = self.bytecode_cache.borrow();
        let chunk = cache.compiler.chunk();
        if ctx.next_state_env.is_none()
            && bytecode_function_needs_next_state(
                chunk,
                func_idx,
                &mut std::collections::HashSet::new(),
            )
        {
            if bytecode_vm_reason_logs_enabled() {
                eprintln!(
                    "[bytecode] runtime fallback: operator={name}, reason=next-state array unavailable"
                );
            }
            return None;
        }
        let mut vm =
            BytecodeVm::from_state_env(chunk, state_env, ctx.next_state_env).with_eval_ctx(ctx);
        match vm.execute_function(func_idx) {
            Ok(value) => Some(Ok(value)),
            Err(VmError::Unsupported(_)) => None,
            Err(VmError::Eval(e)) => Some(Err(e)),
            Err(VmError::TypeError { expected, actual }) => Some(Err(EvalError::Internal {
                message: format!("bytecode VM type error: expected {expected}, got {actual}"),
                span: None,
            })),
            Err(VmError::ChooseFailed) => Some(Err(EvalError::ChooseFailed { span: None })),
            Err(VmError::Halted) => Some(Err(EvalError::CaseNoMatch { span: None })),
        }
    }
}
