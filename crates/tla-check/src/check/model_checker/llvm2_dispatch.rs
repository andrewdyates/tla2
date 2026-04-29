// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LLVM2 native compilation dispatch for the BFS model checker.
//!
//! Provides an alternative to the Cranelift JIT path by compiling TIR bytecode
//! through the LLVM2 native pipeline: BytecodeFunction -> tMIR -> LLVM2 ISel ->
//! RegAlloc -> AArch64/x86 encoding -> JIT executable memory. Zero C dependencies.
//! The resulting native functions share the same `extern "C"` ABI as Cranelift JIT,
//! so the BFS dispatch logic is compatible with both backends.
//!
//! # Design rationale (Part of #4251 Stream 6 / #4118)
//!
//! **(a) Spec shape eligibility.** The BFS path compiles the per-action
//! next-state function via `compile_next_state_native_with_constants`. The
//! next-state ABI is `fn(out, state_in, state_out, state_len)` with NO
//! parameters — so actions with `arity > 0` (EXISTS-bound parameters like
//! `\E i \in S : Action(i)`) are ineligible and routed to the interpreter.
//! In addition, we pre-screen with [`tla_llvm2::is_tir_eligible_with_state`]
//! to skip actions whose bytecode contains opcodes that are known to reach
//! unsupported paths (closures, builder lambdas, etc.). This is a soft
//! pre-screen only — the tMIR pipeline handles many more opcodes than the
//! direct TIR→LLVM fast path, so pre-screen rejection triggers a warning and
//! still attempts compilation. The pipeline itself is the source of truth
//! and returns [`tla_llvm2::Llvm2Error::UnsupportedInst`] when the action
//! cannot be compiled, at which point the action is permanently routed to
//! the interpreter for the remainder of the run.
//!
//! **(b) Per-action dispatch.** [`Llvm2NativeCache`] owns a
//! `FxHashMap<String, NativeNextStateFn>` keyed by action name. At BFS
//! setup, each action is compiled eagerly and the resulting function pointer
//! (plus its backing [`NativeLibrary`] mmap) is installed in the cache.
//! Inside the BFS action loop, dispatch flows interpreter-first-unless-compiled:
//! if `cache.contains_action(action_name)` is true the native path runs;
//! otherwise the interpreter runs. There is NO global switch once the cache
//! is built — every action picks its path independently each iteration.
//!
//! **(c) Fallback on compile failure / ineligibility.** Compile failures
//! are absorbed at `Llvm2NativeCache::build` time: the failure is logged
//! once (at cache construction), the failed action is omitted from
//! `next_state_fns`, and no retry is ever attempted. The interpreter then
//! handles every BFS visit of that action's (state, action) pair. This is
//! the "log once, interpreter forever" policy described in the Stream 6
//! handoff.
//!
//! # ABI Compatibility
//!
//! Both Cranelift JIT and LLVM2 use the same function signature:
//! - **Next-state**: `extern "C" fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32)`
//! - **Invariant**: `extern "C" fn(out: *mut JitCallOut, state: *const i64, state_len: u32)`
//!
//! # Activation
//!
//! Enable at compile time with `--features llvm2`, then at runtime with
//! either `TLA2_LLVM2=1` (global LLVM2 dispatch) or `TLA2_LLVM2_BFS=1`
//! (BFS-scoped dispatch — identical code path today; reserved as a
//! narrower switch so invariant / liveness LLVM2 wiring can activate
//! independently in the future). `TLA2_LLVM2_ENTRY_COUNTER_GATE=N` is an
//! opt-in diagnostics gate that routes an action back to the interpreter once
//! LLVM2 reports at least `N` JIT entry-counter hits for that action. No
//! system LLVM installation required — the LLVM2 backend is a pure-Rust JIT
//! compiler.
//!
//! # Pipeline
//!
//! ```text
//! BytecodeFunction (per action / invariant)
//!     |  (tla_tmir::lower -> tmir::Module)
//!     v
//! tmir::Module (SSA IR)
//!     |  (tla_llvm2::compile_module_native -> LLVM2 JIT pipeline)
//!     v
//! NativeLibrary (JIT executable buffer)
//!     |  (get_symbol -> transmute)
//!     v
//! Callable function pointers
//! ```
//!
//! Part of #4118: Wire tla-llvm2 into tla-check BFS loop.
//! Part of #4251 Stream 6: BFS-scoped activation via `TLA2_LLVM2_BFS`.

use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;
use std::sync::Mutex;
use tla_jit_abi::{BindingSpec, JitCallOut};
use tla_jit_runtime::{BfsStepError, FlatBfsStepOutput};

/// Type alias for the native next-state function pointer.
///
/// ABI: `extern "C" fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32)`
///
/// - `out`: caller-allocated result struct. On success, `out.status = Ok` and
///   `out.value = 1` (enabled) or `0` (disabled). On error, status is set
///   to RuntimeError with error details.
/// - `state_in`: flat i64 array of current state variable values.
/// - `state_out`: flat i64 array for successor state (pre-allocated by caller).
/// - `state_len`: number of state variables.
type NativeNextStateFn = unsafe extern "C" fn(*mut JitCallOut, *const i64, *mut i64, u32);

/// Type alias for the native invariant function pointer.
///
/// ABI: `extern "C" fn(out: *mut JitCallOut, state: *const i64, state_len: u32)`
type NativeInvariantFn = unsafe extern "C" fn(*mut JitCallOut, *const i64, u32);

const LLVM2_NATIVE_CALLOUT_SELFTEST_ENV: &str = "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST";
const LLVM2_NATIVE_CALLOUT_SELFTEST_FAIL_CLOSED_ENV: &str =
    "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST_FAIL_CLOSED";
const LLVM2_DUMP_ACTION_BYTECODE_ENV: &str = "TLA2_LLVM2_DUMP_ACTION_BYTECODE";
const LLVM2_NATIVE_CALLOUT_OPT_LEVEL_ENV: &str = "TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL";
const LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL_ENV: &str =
    "TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL";
const LLVM2_NATIVE_CALLOUT_SELFTEST_REDZONE_SLOTS: usize = 64;
const LLVM2_NATIVE_CALLOUT_SELFTEST_INPUT_CANARY: i64 = 0x4123_7b5a_19d0_6ec3;
const LLVM2_NATIVE_CALLOUT_SELFTEST_OUTPUT_CANARY: i64 = 0x2f4d_0619_7b5a_34c1;

fn llvm2_env_flag_enabled(name: &str) -> bool {
    std::env::var(name).map_or(false, |value| value.trim() == "1")
}

fn llvm2_native_callout_selftest_enabled() -> bool {
    llvm2_env_flag_enabled(LLVM2_NATIVE_CALLOUT_SELFTEST_FAIL_CLOSED_ENV)
        || std::env::var(LLVM2_NATIVE_CALLOUT_SELFTEST_ENV).map_or(false, |value| {
            let value = value.trim();
            value == "1"
                || value.eq_ignore_ascii_case("fail_closed")
                || value.eq_ignore_ascii_case("fail-closed")
                || value.eq_ignore_ascii_case("strict")
        })
}

fn llvm2_native_callout_selftest_fail_closed() -> bool {
    llvm2_env_flag_enabled(LLVM2_NATIVE_CALLOUT_SELFTEST_FAIL_CLOSED_ENV)
        || std::env::var(LLVM2_NATIVE_CALLOUT_SELFTEST_ENV).map_or(false, |value| {
            let value = value.trim();
            value.eq_ignore_ascii_case("fail_closed")
                || value.eq_ignore_ascii_case("fail-closed")
                || value.eq_ignore_ascii_case("strict")
        })
}

fn llvm2_native_callout_opt_level(requested: tla_llvm2::OptLevel) -> tla_llvm2::OptLevel {
    match std::env::var(LLVM2_NATIVE_CALLOUT_OPT_LEVEL_ENV) {
        Ok(value) if value.trim().eq_ignore_ascii_case("O3") => requested,
        Ok(value) if value.trim().eq_ignore_ascii_case("O1") => tla_llvm2::OptLevel::O1,
        Ok(value) => {
            eprintln!(
                "[llvm2] ignoring {LLVM2_NATIVE_CALLOUT_OPT_LEVEL_ENV}={value:?}; expected O1 or O3"
            );
            tla_llvm2::OptLevel::O1
        }
        Err(_) => tla_llvm2::OptLevel::O1,
    }
}

fn native_fused_callout_sentinel() -> JitCallOut {
    let mut out = JitCallOut::default();
    out.status = tla_jit_abi::JitStatus::RuntimeError;
    out
}

fn llvm2_dump_filter_matches(env_name: &str, name: &str) -> bool {
    std::env::var(env_name).is_ok_and(|value| {
        let value = value.trim();
        value == "1"
            || value.eq_ignore_ascii_case("all")
            || name.contains(value)
            || value.split(',').any(|part| {
                let part = part.trim();
                !part.is_empty() && name.contains(part)
            })
    })
}

/// Cache of LLVM2-compiled native functions for BFS dispatch.
///
/// LLVM2 counterpart of the former Cranelift `JitNextStateCache`, backed by native shared
/// libraries (`.dylib`/`.so`) instead of Cranelift JIT memory. Holds the
/// `NativeLibrary` handles to keep the dlopen'd code alive.
pub(in crate::check) struct Llvm2NativeCache {
    /// Per-action next-state function pointers, keyed by action name.
    next_state_fns: FxHashMap<String, NativeNextStateFn>,
    /// Expected native action keys produced by inner-EXISTS expansion, keyed by
    /// the unexpanded base action key. This tracks missing expanded siblings so
    /// coverage and compiled BFS eligibility fail closed after partial
    /// expansion compile failures.
    inner_exists_expansion_keys: FxHashMap<String, Vec<String>>,
    /// Per-invariant function pointers, indexed parallel to the spec's invariant list.
    /// Uses `Option` to maintain index alignment when compilation fails mid-sequence.
    /// `invariant_fns[i]` corresponds to the spec's invariant at index `i`.
    invariant_fns: Vec<Option<NativeInvariantFn>>,
    /// Per-state-constraint function pointers, indexed parallel to the spec's
    /// state constraint list. These use the same native ABI as invariants but
    /// are kept separate because state constraints prune successors rather than
    /// reporting safety violations.
    state_constraint_fns: Vec<Option<NativeInvariantFn>>,
    /// Native-library action entry points available for fused-level linking.
    native_action_entries: FxHashMap<String, Llvm2NativeActionEntry>,
    /// Native-library invariant entry points available for fused-level linking.
    ///
    /// This is indexed parallel to `invariant_fns` and the configured
    /// invariant list. A `None` slot means the invariant did not compile and
    /// the native fused level must stay action-only.
    native_invariant_entries: Vec<Option<Llvm2NativeInvariantEntry>>,
    /// Native-library state-constraint entries available for native fused
    /// successor pruning. Indexed parallel to `state_constraint_fns`.
    native_state_constraint_entries: Vec<Option<Llvm2NativeInvariantEntry>>,
    /// Number of state variables in the model.
    state_var_count: usize,
    /// Optimization level used for this cache's compiled entry points.
    opt_level: tla_llvm2::OptLevel,
    /// Keeps the native libraries alive (dlopen handles).
    /// Dropping these invalidates the function pointers above.
    _libraries: Vec<tla_llvm2::NativeLibrary>,
}

#[derive(Clone)]
struct Llvm2NativeActionEntry {
    library: tla_llvm2::NativeLibrary,
    symbol_name: String,
    binding_values: Vec<i64>,
    formal_values: Vec<i64>,
}

#[derive(Clone)]
struct Llvm2NativeInvariantEntry {
    library: tla_llvm2::NativeLibrary,
    symbol_name: String,
}

#[derive(Clone)]
struct Llvm2NativeCalloutSelftestAction {
    index: u32,
    name: String,
    symbol_name: String,
    func: NativeNextStateFn,
}

#[derive(Clone)]
struct Llvm2NativeCalloutSelftestPredicate {
    index: u32,
    name: String,
    symbol_name: String,
    func: NativeInvariantFn,
}

#[derive(Clone)]
struct Llvm2NativeCalloutSelftestMissing {
    kind: &'static str,
    index: u32,
    name: String,
    symbol_name: String,
}

struct Llvm2NativeCalloutGuardedState {
    slots: Vec<i64>,
    payload_start: usize,
    payload_len: usize,
    canary: i64,
}

impl Llvm2NativeCalloutGuardedState {
    fn new(payload: &[i64], canary: i64) -> Self {
        let payload_start = LLVM2_NATIVE_CALLOUT_SELFTEST_REDZONE_SLOTS;
        let payload_len = payload.len();
        let total_len = payload_start
            .checked_add(payload_len)
            .and_then(|len| len.checked_add(LLVM2_NATIVE_CALLOUT_SELFTEST_REDZONE_SLOTS))
            .expect("native callout selftest guarded buffer length overflow");
        let mut slots = vec![canary; total_len];
        slots[payload_start..payload_start + payload_len].copy_from_slice(payload);
        Self {
            slots,
            payload_start,
            payload_len,
            canary,
        }
    }

    fn payload(&self) -> &[i64] {
        &self.slots[self.payload_start..self.payload_start + self.payload_len]
    }

    fn payload_mut(&mut self) -> &mut [i64] {
        let payload_start = self.payload_start;
        let payload_end = payload_start + self.payload_len;
        &mut self.slots[payload_start..payload_end]
    }

    fn payload_ptr(&self) -> *const i64 {
        self.payload().as_ptr()
    }

    fn payload_mut_ptr(&mut self) -> *mut i64 {
        self.payload_mut().as_mut_ptr()
    }

    fn verify_read_only(
        &self,
        kind: &str,
        index: u32,
        symbol_name: &str,
        name: &str,
        expected_payload: &[i64],
    ) -> Result<(), String> {
        self.verify_canaries(kind, index, symbol_name, name)?;
        if self.payload() != expected_payload {
            return Err(format!(
                "{kind} callout mutated read-only state input: index={index} symbol={symbol_name} name={name}"
            ));
        }
        Ok(())
    }

    fn verify_canaries(
        &self,
        kind: &str,
        index: u32,
        symbol_name: &str,
        name: &str,
    ) -> Result<(), String> {
        for (slot, value) in self.slots[..self.payload_start].iter().enumerate() {
            if *value != self.canary {
                return Err(format!(
                    "{kind} callout wrote before selftest state buffer: index={index} symbol={symbol_name} name={name} redzone_slot={slot}"
                ));
            }
        }
        let suffix_start = self.payload_start + self.payload_len;
        for (offset, value) in self.slots[suffix_start..].iter().enumerate() {
            if *value != self.canary {
                return Err(format!(
                    "{kind} callout wrote past selftest state buffer: index={index} symbol={symbol_name} name={name} redzone_slot={offset}"
                ));
            }
        }
        Ok(())
    }
}

struct Llvm2NativeCalloutSelftest {
    actions: Vec<Llvm2NativeCalloutSelftestAction>,
    state_constraints: Vec<Llvm2NativeCalloutSelftestPredicate>,
    invariants: Vec<Llvm2NativeCalloutSelftestPredicate>,
    missing_expected: Vec<Llvm2NativeCalloutSelftestMissing>,
    fail_closed: bool,
}

impl Llvm2NativeCalloutSelftest {
    fn clear_tla_runtime_arenas_before_callout() {
        tla_llvm2::runtime_abi::tla_ops::clear_tla_iter_arena();
        tla_llvm2::runtime_abi::tla_ops::clear_tla_arena();
    }

    fn log_cache_build_without_sample(cache: &Llvm2NativeCache) {
        if !llvm2_native_callout_selftest_enabled() {
            return;
        }
        eprintln!(
            "[llvm2-selftest] {LLVM2_NATIVE_CALLOUT_SELFTEST_ENV} enabled after Llvm2NativeCache::build: compiled actions={}, state_constraints={}, invariants={}, but no real flat state sample is available in cache-build scope; deferring to the first native fused arena if one is built",
            cache.action_count(),
            cache.state_constraint_count(),
            cache.invariant_count(),
        );
    }

    fn log_fused_build_without_sample(state_len: usize) {
        if !llvm2_native_callout_selftest_enabled() {
            return;
        }
        eprintln!(
            "[llvm2-selftest] {LLVM2_NATIVE_CALLOUT_SELFTEST_ENV} enabled before native fused level build: no real flat parent state is in scope (state_len={state_len}); selftest will run on the first native fused arena parent",
        );
    }

    fn from_cache_if_enabled_or_required(
        cache: &Llvm2NativeCache,
        native_actions: &[tla_llvm2::Llvm2BfsLevelNativeAction],
        native_state_constraints: &[tla_llvm2::Llvm2BfsLevelNativeStateConstraint],
        native_invariants: &[tla_llvm2::Llvm2BfsLevelNativeInvariant],
        fail_closed_required: bool,
    ) -> Option<Self> {
        if !fail_closed_required && !llvm2_native_callout_selftest_enabled() {
            return None;
        }

        let mut missing_expected = Vec::new();

        let mut actions = Vec::with_capacity(native_actions.len());
        for action in native_actions {
            let Some(func) = cache.next_state_fns.get(&action.descriptor.name).copied() else {
                Self::record_missing_expected(
                    &mut missing_expected,
                    "action",
                    action.descriptor.action_idx,
                    &action.symbol_name,
                    &action.descriptor.name,
                );
                continue;
            };
            actions.push(Llvm2NativeCalloutSelftestAction {
                index: action.descriptor.action_idx,
                name: action.descriptor.name.clone(),
                symbol_name: action.symbol_name.clone(),
                func,
            });
        }

        let mut state_constraints = Vec::with_capacity(native_state_constraints.len());
        for constraint in native_state_constraints {
            let idx = constraint.constraint_idx as usize;
            let Some(func) = cache.state_constraint_fns.get(idx).and_then(|slot| *slot) else {
                Self::record_missing_expected(
                    &mut missing_expected,
                    "state-constraint",
                    constraint.constraint_idx,
                    &constraint.symbol_name,
                    &constraint.name,
                );
                continue;
            };
            state_constraints.push(Llvm2NativeCalloutSelftestPredicate {
                index: constraint.constraint_idx,
                name: constraint.name.clone(),
                symbol_name: constraint.symbol_name.clone(),
                func,
            });
        }

        let mut invariants = Vec::with_capacity(native_invariants.len());
        for invariant in native_invariants {
            let idx = invariant.descriptor.invariant_idx as usize;
            let Some(func) = cache.invariant_fns.get(idx).and_then(|slot| *slot) else {
                Self::record_missing_expected(
                    &mut missing_expected,
                    "invariant",
                    invariant.descriptor.invariant_idx,
                    &invariant.symbol_name,
                    &invariant.descriptor.name,
                );
                continue;
            };
            invariants.push(Llvm2NativeCalloutSelftestPredicate {
                index: invariant.descriptor.invariant_idx,
                name: invariant.descriptor.name.clone(),
                symbol_name: invariant.symbol_name.clone(),
                func,
            });
        }

        let fail_closed = fail_closed_required || llvm2_native_callout_selftest_fail_closed();
        eprintln!(
            "[llvm2-selftest] prepared native fused callout selftest: actions={}, state_constraints={}, invariants={}, missing_expected={}, fail_closed={fail_closed}",
            actions.len(),
            state_constraints.len(),
            invariants.len(),
            missing_expected.len(),
        );

        Some(Self {
            actions,
            state_constraints,
            invariants,
            missing_expected,
            fail_closed,
        })
    }

    fn run_on_first_parent(
        &self,
        arena: &[i64],
        parent_count: usize,
        state_len: usize,
    ) -> Result<(), String> {
        if self.fail_closed && !self.missing_expected.is_empty() {
            for missing in &self.missing_expected {
                eprintln!(
                    "[llvm2-selftest] fail-closed missing expected {} callout function pointer: index={} symbol={} name={}",
                    missing.kind, missing.index, missing.symbol_name, missing.name,
                );
            }
            return Err(format!(
                "missing expected native fused callout function pointer(s): {}",
                self.missing_expected_summary(),
            ));
        }
        if parent_count == 0 {
            return Err("no parent states in fused arena (parent_count=0)".to_string());
        }
        if state_len == 0 {
            return Err("zero-width flat state; no safe real state sample available".to_string());
        }
        let required_slots = parent_count.checked_mul(state_len).ok_or_else(|| {
            format!(
                "fused arena dimensions overflow: parent_count={parent_count}, state_len={state_len}"
            )
        })?;
        if arena.len() < required_slots {
            return Err(format!(
                "fused arena too short for declared parents: parent_count={parent_count}, state_len={state_len}, required_slots={required_slots}, arena_slots={}",
                arena.len()
            ));
        }
        let state_len_u32 = u32::try_from(state_len)
            .map_err(|_| format!("state_len={state_len} does not fit the native callout ABI"))?;
        let sample = &arena[..state_len];
        let mut unexpected_status = false;
        let mut fail_closed_false_predicate = false;

        eprintln!(
            "[llvm2-selftest] running native fused callout selftest on first real parent: state_len={state_len}, actions={}, state_constraints={}, invariants={}, fail_closed={}",
            self.actions.len(),
            self.state_constraints.len(),
            self.invariants.len(),
            self.fail_closed,
        );

        for action in &self.actions {
            let mut out = native_fused_callout_sentinel();
            let sample_in = Llvm2NativeCalloutGuardedState::new(
                sample,
                LLVM2_NATIVE_CALLOUT_SELFTEST_INPUT_CANARY,
            );
            let mut state_out = Llvm2NativeCalloutGuardedState::new(
                sample,
                LLVM2_NATIVE_CALLOUT_SELFTEST_OUTPUT_CANARY,
            );
            tla_llvm2::ensure_jit_execute_mode();
            Self::log_callout_start(
                "action",
                action.index,
                &action.symbol_name,
                &action.name,
                action.func as *const () as usize,
                state_len_u32,
                sample_in.payload(),
                Some(state_out.payload()),
            );
            // SAFETY: Function pointers and ABI metadata come from the same
            // compiled cache used by the native fused level. `sample` is a real
            // flat parent state and `state_out` is a same-width successor buffer.
            Self::clear_tla_runtime_arenas_before_callout();
            unsafe {
                (action.func)(
                    &mut out,
                    sample_in.payload_ptr(),
                    state_out.payload_mut_ptr(),
                    state_len_u32,
                );
            }
            Self::log_callout_out(
                "action",
                action.index,
                &action.symbol_name,
                &action.name,
                out,
            );
            sample_in.verify_read_only(
                "action",
                action.index,
                &action.symbol_name,
                &action.name,
                sample,
            )?;
            state_out.verify_canaries(
                "action state_out",
                action.index,
                &action.symbol_name,
                &action.name,
            )?;
            unexpected_status |= out.status != tla_jit_abi::JitStatus::Ok;

            let action_enabled = Self::decode_ok_boolean_callout(
                "action",
                action.index,
                &action.symbol_name,
                &action.name,
                out,
            )?
            .unwrap_or(false);

            if action_enabled {
                let mut constraints_passed = true;
                for constraint in &self.state_constraints {
                    eprintln!(
                        "[llvm2-selftest] checking state_constraint after action index={} symbol={} name={} constraint_index={} constraint_symbol={} constraint_name={}",
                        action.index,
                        action.symbol_name,
                        action.name,
                        constraint.index,
                        constraint.symbol_name,
                        constraint.name,
                    );
                    let out = self.run_predicate_callout(
                        "state_constraint_after_action",
                        constraint,
                        state_out.payload(),
                        state_len_u32,
                    )?;
                    unexpected_status |= out.status != tla_jit_abi::JitStatus::Ok;
                    let constraint_passed = Self::decode_ok_predicate_callout(
                        "state_constraint_after_action",
                        constraint,
                        out,
                    )?
                    .unwrap_or(false);
                    constraints_passed &= constraint_passed;
                }
                if constraints_passed {
                    for invariant in &self.invariants {
                        eprintln!(
                            "[llvm2-selftest] checking invariant after action index={} symbol={} name={} invariant_index={} invariant_symbol={} invariant_name={}",
                            action.index,
                            action.symbol_name,
                            action.name,
                            invariant.index,
                            invariant.symbol_name,
                            invariant.name,
                        );
                        let out = self.run_predicate_callout(
                            "invariant_after_action",
                            invariant,
                            state_out.payload(),
                            state_len_u32,
                        )?;
                        unexpected_status |= out.status != tla_jit_abi::JitStatus::Ok;
                        let _ = Self::decode_ok_predicate_callout(
                            "invariant_after_action",
                            invariant,
                            out,
                        )?;
                    }
                }
            }
        }

        for constraint in &self.state_constraints {
            let out =
                self.run_predicate_callout("state_constraint", constraint, sample, state_len_u32)?;
            unexpected_status |= out.status != tla_jit_abi::JitStatus::Ok;
            let predicate_result =
                Self::decode_ok_predicate_callout("state_constraint", constraint, out)?;
            if self.fail_closed
                && Self::standalone_predicate_failed_closed(
                    "state_constraint",
                    constraint,
                    predicate_result,
                )
            {
                fail_closed_false_predicate = true;
            }
        }

        for invariant in &self.invariants {
            let out = self.run_predicate_callout("invariant", invariant, sample, state_len_u32)?;
            unexpected_status |= out.status != tla_jit_abi::JitStatus::Ok;
            let predicate_result = Self::decode_ok_predicate_callout("invariant", invariant, out)?;
            if self.fail_closed
                && Self::standalone_predicate_failed_closed(
                    "invariant",
                    invariant,
                    predicate_result,
                )
            {
                fail_closed_false_predicate = true;
            }
        }

        if unexpected_status {
            return Err("one or more native fused callouts returned a non-Ok status".to_string());
        }
        if fail_closed_false_predicate {
            return Err(
                "one or more fail-closed standalone native fused predicate callouts returned Ok(value=0)"
                    .to_string(),
            );
        }
        Ok(())
    }

    fn record_missing_expected(
        missing_expected: &mut Vec<Llvm2NativeCalloutSelftestMissing>,
        kind: &'static str,
        index: u32,
        symbol_name: &str,
        name: &str,
    ) {
        eprintln!(
            "[llvm2-selftest] {kind} callout metadata missing function pointer: index={index} symbol={symbol_name} name={name}",
        );
        missing_expected.push(Llvm2NativeCalloutSelftestMissing {
            kind,
            index,
            name: name.to_string(),
            symbol_name: symbol_name.to_string(),
        });
    }

    fn missing_expected_summary(&self) -> String {
        self.missing_expected
            .iter()
            .map(|missing| {
                format!(
                    "{} index={} symbol={} name={}",
                    missing.kind, missing.index, missing.symbol_name, missing.name,
                )
            })
            .collect::<Vec<_>>()
            .join("; ")
    }

    fn run_predicate_callout(
        &self,
        kind: &str,
        callout: &Llvm2NativeCalloutSelftestPredicate,
        sample: &[i64],
        state_len: u32,
    ) -> Result<JitCallOut, String> {
        let mut out = native_fused_callout_sentinel();
        let guarded_sample =
            Llvm2NativeCalloutGuardedState::new(sample, LLVM2_NATIVE_CALLOUT_SELFTEST_INPUT_CANARY);
        tla_llvm2::ensure_jit_execute_mode();
        Self::log_callout_start(
            kind,
            callout.index,
            &callout.symbol_name,
            &callout.name,
            callout.func as *const () as usize,
            state_len,
            guarded_sample.payload(),
            None,
        );
        // SAFETY: Function pointer and ABI metadata come from the compiled
        // native cache. `sample` is a real flat parent state with `state_len`
        // addressable i64 slots.
        Self::clear_tla_runtime_arenas_before_callout();
        unsafe {
            (callout.func)(&mut out, guarded_sample.payload_ptr(), state_len);
        }
        Self::log_callout_out(
            kind,
            callout.index,
            &callout.symbol_name,
            &callout.name,
            out,
        );
        guarded_sample.verify_read_only(
            kind,
            callout.index,
            &callout.symbol_name,
            &callout.name,
            sample,
        )?;
        Ok(out)
    }

    fn decode_ok_predicate_callout(
        kind: &str,
        callout: &Llvm2NativeCalloutSelftestPredicate,
        out: JitCallOut,
    ) -> Result<Option<bool>, String> {
        Self::decode_ok_boolean_callout(
            kind,
            callout.index,
            &callout.symbol_name,
            &callout.name,
            out,
        )
    }

    fn decode_ok_boolean_callout(
        kind: &str,
        index: u32,
        symbol_name: &str,
        name: &str,
        out: JitCallOut,
    ) -> Result<Option<bool>, String> {
        if out.status != tla_jit_abi::JitStatus::Ok {
            return Ok(None);
        }
        match out.value {
            0 => Ok(Some(false)),
            1 => Ok(Some(true)),
            value => {
                let reason = format!(
                    "native fused {kind} callout returned noncanonical boolean value {value}: index={index} symbol={symbol_name} name={name}; strict ABI requires 0 or 1"
                );
                eprintln!("[llvm2-selftest] {reason}");
                Err(reason)
            }
        }
    }

    fn standalone_predicate_failed_closed(
        kind: &str,
        callout: &Llvm2NativeCalloutSelftestPredicate,
        predicate_result: Option<bool>,
    ) -> bool {
        if predicate_result == Some(false) {
            eprintln!(
                "[llvm2-selftest] fail-closed standalone {kind} callout returned Ok(value=0): index={} symbol={} name={}",
                callout.index, callout.symbol_name, callout.name,
            );
            return true;
        }
        false
    }

    fn log_callout_start(
        kind: &str,
        index: u32,
        symbol_name: &str,
        name: &str,
        func_addr: usize,
        state_len: u32,
        sample: &[i64],
        state_out: Option<&[i64]>,
    ) {
        let sample_head = &sample[..sample.len().min(16)];
        if let Some(state_out) = state_out {
            let out_head = &state_out[..state_out.len().min(16)];
            eprintln!(
                "[llvm2-selftest] entering {kind} callout index={index} symbol={symbol_name} name={name} fn=0x{func_addr:x} state_len={state_len} state_head={sample_head:?} out_head={out_head:?}",
            );
        } else {
            eprintln!(
                "[llvm2-selftest] entering {kind} callout index={index} symbol={symbol_name} name={name} fn=0x{func_addr:x} state_len={state_len} state_head={sample_head:?}",
            );
        }
        use std::io::Write as _;
        let _ = std::io::stderr().flush();
    }

    fn log_callout_out(kind: &str, index: u32, symbol_name: &str, name: &str, out: JitCallOut) {
        eprintln!(
            "[llvm2-selftest] {kind} callout index={index} symbol={symbol_name} name={name} status={:?} value={}",
            out.status, out.value,
        );
        if out.status == tla_jit_abi::JitStatus::RuntimeError {
            eprintln!(
                "[llvm2-selftest] {kind} callout runtime_error index={index} symbol={symbol_name} err_kind={:?} span={}..{} file_id={}",
                out.err_kind, out.err_span_start, out.err_span_end, out.err_file_id,
            );
        }
    }
}

// SAFETY: After construction, the cache is immutable. Function pointers target
// finalized native code in dlopen'd libraries that are retained for the cache
// lifetime. No interior mutation.
unsafe impl Send for Llvm2NativeCache {}
unsafe impl Sync for Llvm2NativeCache {}

fn count_arity_positive_action_failure(
    exists_enabled: bool,
    specialized_action_names: &FxHashSet<&str>,
    action_name: &str,
) -> bool {
    !(exists_enabled && specialized_action_names.contains(action_name))
}

fn entry_counter_gate_allows_dispatch(entry_count: Option<u64>, limit: u64) -> bool {
    match entry_count {
        Some(count) => count < limit,
        None => false,
    }
}

fn decode_strict_llvm2_boolean(value: i64, context: &str) -> Result<bool, ()> {
    match value {
        0 => Ok(false),
        1 => Ok(true),
        _ => {
            eprintln!(
                "[llvm2] {context} returned noncanonical boolean value {value}; strict ABI requires 0 or 1"
            );
            Err(())
        }
    }
}

/// Result of evaluating a single LLVM2-compiled action.
pub(in crate::check) enum Llvm2ActionResult {
    /// Action is enabled; `successor` contains the flat i64 output buffer.
    /// `jit_input` is a snapshot of the input state buffer, needed by
    /// `unflatten_i64_to_array_state_with_input` for compound value
    /// deserialization (offsets encoded in output reference the input buffer).
    Enabled {
        successor: Vec<i64>,
        jit_input: Vec<i64>,
    },
    /// Action guard evaluated to false; no successor state.
    Disabled,
}

/// Statistics from LLVM2 cache construction.
#[derive(Debug, Clone, Default)]
pub(in crate::check) struct Llvm2BuildStats {
    /// Number of actions successfully compiled.
    pub actions_compiled: usize,
    /// Number of actions that failed compilation (fell back to interpreter).
    pub actions_failed: usize,
    /// Number of invariants successfully compiled.
    pub invariants_compiled: usize,
    /// Number of invariants that failed compilation.
    pub invariants_failed: usize,
    /// Number of state constraints successfully compiled.
    pub state_constraints_compiled: usize,
    /// Number of state constraints that failed compilation.
    pub state_constraints_failed: usize,
    /// Total wall-clock time for all compilations.
    pub total_compile_ms: u64,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(in crate::check) struct Llvm2ActionDispatchStats {
    pub enabled: usize,
    pub disabled: usize,
    pub runtime_errors: usize,
}

impl Llvm2BuildStats {
    /// Total action instances represented by the telemetry counters.
    #[inline]
    pub(in crate::check) fn actions_total(&self) -> usize {
        self.actions_compiled + self.actions_failed
    }

    /// Total invariant slots represented by the telemetry counters.
    #[inline]
    pub(in crate::check) fn invariants_total(&self) -> usize {
        self.invariants_compiled + self.invariants_failed
    }

    /// Total state-constraint slots represented by the telemetry counters.
    #[inline]
    pub(in crate::check) fn state_constraints_total(&self) -> usize {
        self.state_constraints_compiled + self.state_constraints_failed
    }

    /// Replace raw action-attempt counters with executable split-action coverage.
    ///
    /// The LLVM2 builder may see arity-positive bytecode wrappers that are not
    /// BFS dispatch targets. Benchmark coverage gates need the action instances
    /// that compiled BFS would actually invoke, so `run_helpers` rewrites the
    /// action counters from split-action metadata before telemetry is emitted.
    #[inline]
    pub(in crate::check) fn record_executable_action_coverage(
        &mut self,
        compiled: usize,
        total: usize,
    ) {
        self.actions_compiled = compiled;
        self.actions_failed = total.saturating_sub(compiled);
    }
}

impl Llvm2NativeCache {
    /// Check whether EXISTS-binding specialization (#4270) is enabled.
    ///
    /// Enabled by default; set `TLA2_LLVM2_EXISTS=0` to opt out. When enabled,
    /// `Llvm2NativeCache::build` consumes `BindingSpec` entries extracted from
    /// `split_action_meta`, runs `tla_tir::bytecode::specialize_bytecode_function` to
    /// prepend `LoadImm` for each binding register, and compiles the resulting
    /// arity-0 function through the tMIR → LLVM2 pipeline. When disabled, the
    /// cache ignores specializations and behaves as before (binding-heavy
    /// actions fall back to the interpreter).
    pub(in crate::check) fn exists_enabled() -> bool {
        std::env::var("TLA2_LLVM2_EXISTS").map_or(true, |v| v != "0")
    }

    fn has_residual_exists_opcode(func: &tla_tir::bytecode::BytecodeFunction) -> bool {
        func.instructions.iter().any(|op| {
            matches!(
                op,
                tla_tir::bytecode::Opcode::ExistsBegin { .. }
                    | tla_tir::bytecode::Opcode::ExistsNext { .. }
            )
        })
    }

    fn specialization_formal_values<'a>(
        spec: &'a tla_jit_abi::BindingSpec,
        base_arity: u8,
        key: &str,
    ) -> Result<&'a [i64], String> {
        let formal_arity = usize::from(base_arity);
        if spec.formal_values.len() == formal_arity {
            Ok(&spec.formal_values)
        } else {
            Err(format!(
                "[llvm2] specialization '{key}': formal binding arity mismatch for base action '{}' ({} formal values, {} key values, arity {})",
                spec.action_name,
                spec.formal_values.len(),
                spec.binding_values.len(),
                base_arity,
            ))
        }
    }

    fn sorted_inner_exists_expansions(
        func: &tla_tir::bytecode::BytecodeFunction,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
    ) -> Option<Vec<tla_tir::bytecode::ExpandedAction>> {
        let mut expanded =
            tla_tir::bytecode::expand_inner_exists_preserving_offsets(func, const_pool)?;
        expanded.sort_by(|a, b| a.inner_binding_values.cmp(&b.inner_binding_values));
        Some(expanded)
    }

    fn compile_next_state_action_exact(
        action_name: &str,
        func: &tla_tir::bytecode::BytecodeFunction,
        state_layout: Option<&tla_jit_abi::StateLayout>,
        opt_level: tla_llvm2::OptLevel,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
        next_state_fns: &mut FxHashMap<String, NativeNextStateFn>,
        native_action_entries: &mut FxHashMap<String, Llvm2NativeActionEntry>,
        libraries: &mut Vec<tla_llvm2::NativeLibrary>,
        stats: &mut Llvm2BuildStats,
        binding_values: &[i64],
        formal_values: &[i64],
    ) {
        if next_state_fns.contains_key(action_name) {
            return;
        }

        // Pre-screen with `is_tir_eligible_with_state`: this is a soft
        // check. The tMIR pipeline handles more opcodes than the direct TIR
        // fast path, so a mismatch is advisory only.
        if !tla_llvm2::is_tir_eligible_with_state(func) {
            eprintln!(
                "[llvm2] action '{}' has opcodes outside the scalar+state-access set; attempting compile via tMIR anyway",
                action_name,
            );
        }

        match Self::compile_next_state_action(
            action_name,
            func,
            state_layout,
            opt_level,
            const_pool,
            chunk,
        ) {
            Ok((fn_ptr, lib, symbol_name)) => {
                next_state_fns.insert(action_name.to_string(), fn_ptr);
                native_action_entries.insert(
                    action_name.to_string(),
                    Llvm2NativeActionEntry {
                        library: lib.clone(),
                        symbol_name,
                        binding_values: binding_values.to_vec(),
                        formal_values: formal_values.to_vec(),
                    },
                );
                libraries.push(lib);
                stats.actions_compiled += 1;
                eprintln!("[llvm2] compiled next-state for action '{}'", action_name);
            }
            Err(e) => {
                // Log-once policy (#4251 Stream 6 requirement c): failed
                // compile marks this action as permanently interpreter-only
                // for the remainder of the run.
                stats.actions_failed += 1;
                eprintln!(
                    "[llvm2] failed to compile action '{}': {} (interpreter fallback permanent for this run)",
                    action_name, e,
                );
            }
        }
    }

    fn compile_next_state_action_entry(
        action_name: &str,
        func: &tla_tir::bytecode::BytecodeFunction,
        state_layout: Option<&tla_jit_abi::StateLayout>,
        opt_level: tla_llvm2::OptLevel,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
        next_state_fns: &mut FxHashMap<String, NativeNextStateFn>,
        inner_exists_expansion_keys: &mut FxHashMap<String, Vec<String>>,
        native_action_entries: &mut FxHashMap<String, Llvm2NativeActionEntry>,
        libraries: &mut Vec<tla_llvm2::NativeLibrary>,
        stats: &mut Llvm2BuildStats,
        binding_values: &[i64],
        formal_values: &[i64],
    ) {
        if !Self::has_residual_exists_opcode(func) {
            Self::compile_next_state_action_exact(
                action_name,
                func,
                state_layout,
                opt_level,
                const_pool,
                chunk,
                next_state_fns,
                native_action_entries,
                libraries,
                stats,
                binding_values,
                formal_values,
            );
            return;
        }

        let expansion_const_pool = const_pool.or_else(|| chunk.map(|chunk| &chunk.constants));
        let Some(expanded) = Self::sorted_inner_exists_expansions(func, expansion_const_pool)
        else {
            stats.actions_failed += 1;
            eprintln!(
                "[llvm2] skipping action '{action_name}': residual inner EXISTS domain could not be statically expanded (interpreter fallback permanent for this run)",
            );
            return;
        };

        eprintln!(
            "[llvm2] action '{action_name}': inner EXISTS expanded into {} native action function(s)",
            expanded.len(),
        );

        let expanded_keys: Vec<String> = expanded
            .iter()
            .map(|expansion| {
                tla_jit_abi::specialized_key(action_name, &expansion.inner_binding_values)
            })
            .collect();
        inner_exists_expansion_keys.insert(action_name.to_string(), expanded_keys.clone());

        for (expanded_key, expansion) in expanded_keys.into_iter().zip(expanded) {
            if next_state_fns.contains_key(&expanded_key) {
                continue;
            }
            if Self::has_residual_exists_opcode(&expansion.func) {
                stats.actions_failed += 1;
                eprintln!(
                    "[llvm2] failed to expand action '{expanded_key}': residual EXISTS opcode remained after expansion",
                );
                continue;
            }
            let mut expanded_binding_values =
                Vec::with_capacity(binding_values.len() + expansion.inner_binding_values.len());
            expanded_binding_values.extend_from_slice(binding_values);
            expanded_binding_values.extend_from_slice(&expansion.inner_binding_values);
            Self::compile_next_state_action_exact(
                &expanded_key,
                &expansion.func,
                state_layout,
                opt_level,
                const_pool,
                chunk,
                next_state_fns,
                native_action_entries,
                libraries,
                stats,
                &expanded_binding_values,
                formal_values,
            );
        }
    }

    /// Build an LLVM2 native cache from bytecode functions.
    ///
    /// For each action, compiles the next-state bytecode function through the
    /// full LLVM2 pipeline (BytecodeFunction -> tMIR -> LLVM IR -> llc -> .dylib).
    /// Actions that fail compilation are silently skipped (interpreter handles them).
    ///
    /// # Arguments
    ///
    /// * `action_bytecodes` - Map from action name to bytecode function.
    /// * `invariant_bytecodes` - Bytecode functions for each invariant.
    /// * `state_constraint_bytecodes` - Bytecode functions for each state constraint.
    /// * `state_var_count` - Number of state variables in the model.
    /// * `opt_level` - LLVM optimization level.
    /// * `const_pool` - Optional constant pool for resolving `LoadConst`/`Unchanged` opcodes.
    /// * `specializations` - `BindingSpec` entries (one per EXISTS-bound split
    ///   action instance) whose scalar binding values should be baked into a
    ///   specialized bytecode function. Only honored when
    ///   [`Llvm2NativeCache::exists_enabled`] returns true. Part of #4270.
    /// * `chunk` - Optional source bytecode chunk. When provided, action /
    ///   invariant compilation routes through the chunk-aware tMIR lowering
    ///   path so user-defined operator `Call` opcodes in the entry body
    ///   resolve to fully-defined callee functions instead of leaving
    ///   `__func_N` unresolved-symbol references in the output LLVM module.
    ///   Required to compile any action that calls into another operator
    ///   (DieHard, AsyncTerminationDetection, etc.). Part of #4280 Gap C.
    pub(in crate::check) fn build(
        action_bytecodes: &FxHashMap<String, &tla_tir::bytecode::BytecodeFunction>,
        invariant_bytecodes: &[Option<&tla_tir::bytecode::BytecodeFunction>],
        state_constraint_bytecodes: &[Option<&tla_tir::bytecode::BytecodeFunction>],
        state_var_count: usize,
        state_layout: Option<&tla_jit_abi::StateLayout>,
        opt_level: tla_llvm2::OptLevel,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        invariant_const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        state_constraint_const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        specializations: &[BindingSpec],
        chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
        invariant_chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
        state_constraint_chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
    ) -> (Self, Llvm2BuildStats) {
        let start = std::time::Instant::now();
        let mut stats = Llvm2BuildStats::default();
        let mut next_state_fns = FxHashMap::default();
        let mut inner_exists_expansion_keys = FxHashMap::default();
        let mut invariant_fns = Vec::new();
        let mut state_constraint_fns = Vec::new();
        let mut native_action_entries = FxHashMap::default();
        let mut native_invariant_entries = Vec::new();
        let mut native_state_constraint_entries = Vec::new();
        let mut libraries = Vec::new();
        let callout_opt_level = llvm2_native_callout_opt_level(opt_level);
        if callout_opt_level != opt_level {
            eprintln!(
                "[llvm2] native action/invariant/state-constraint callouts compiling at {} instead of requested {} ({LLVM2_NATIVE_CALLOUT_OPT_LEVEL_ENV}=O3 restores requested tier)",
                callout_opt_level.as_str(),
                opt_level.as_str(),
            );
        }

        let exists_enabled = Self::exists_enabled();
        if exists_enabled {
            eprintln!(
                "[llvm2] TLA2_LLVM2_EXISTS=1: specializing {} binding entries (#4270)",
                specializations.len(),
            );
        }
        let specialized_action_names: FxHashSet<&str> = specializations
            .iter()
            .map(|spec| spec.action_name.as_str())
            .collect();

        // Compile each action's next-state function.
        for (action_name, func) in action_bytecodes {
            // Skip actions with arity > 0 (they have EXISTS binding parameters
            // and cannot be lowered to the next-state ABI which expects arity 0).
            // When `TLA2_LLVM2_EXISTS=1`, the binding specialization loop below
            // handles arity-positive actions by prepending `LoadImm` for each
            // binding register and compiling the resulting arity-0 function.
            // Without specializations, EXISTS-bound actions stay interpreter-only.
            if func.arity != 0 {
                if !count_arity_positive_action_failure(
                    exists_enabled,
                    &specialized_action_names,
                    action_name,
                ) {
                    eprintln!(
                        "[llvm2] skipping action '{}' as arity-positive wrapper {}; executable BindingSpec specializations are counted separately",
                        action_name, func.arity,
                    );
                    continue;
                }
                stats.actions_failed += 1;
                eprintln!(
                    "[llvm2] skipping action '{}' as arity-positive {} (requires BindingSpec metadata/specialization via split_action_meta before LLVM2 dispatch)",
                    action_name, func.arity,
                );
                continue;
            }

            Self::compile_next_state_action_entry(
                action_name,
                func,
                state_layout,
                callout_opt_level,
                const_pool,
                chunk,
                &mut next_state_fns,
                &mut inner_exists_expansion_keys,
                &mut native_action_entries,
                &mut libraries,
                &mut stats,
                &[],
                &[],
            );
        }

        // Part of #4270: compile one specialized function per BindingSpec.
        // The base bytecode is fetched from `action_bytecodes`; the binding
        // formal values are prepended as `LoadImm` via
        // `specialize_bytecode_function` (the same transform Cranelift JIT uses in
        // `build_with_stats_and_specializations`). Specialized functions are
        // inserted under `tla_jit_abi::specialized_key(name, &values)` so the
        // dispatcher can look them up with the same key it uses for the
        // Cranelift JIT path. Specializations are enabled by default; users can
        // set `TLA2_LLVM2_EXISTS=0` to force interpreter fallback for this path.
        if exists_enabled {
            for spec in specializations {
                let key = tla_jit_abi::specialized_key(&spec.action_name, &spec.binding_values);
                if next_state_fns.contains_key(&key) {
                    continue; // Already compiled (duplicate spec).
                }

                let base = match action_bytecodes.get(spec.action_name.as_str()) {
                    Some(f) => *f,
                    None => {
                        eprintln!(
                            "[llvm2] specialization '{key}': base action '{}' not in bytecode map, skipping",
                            spec.action_name,
                        );
                        stats.actions_failed += 1;
                        continue;
                    }
                };

                let formal_values = match Self::specialization_formal_values(spec, base.arity, &key)
                {
                    Ok(values) => values,
                    Err(message) => {
                        eprintln!("{message}, skipping");
                        stats.actions_failed += 1;
                        continue;
                    }
                };

                let specialized =
                    tla_tir::bytecode::specialize_bytecode_function(base, formal_values, &key);

                if specialized.arity != 0 {
                    // Defensive: specialize_bytecode_function is required to
                    // return an arity-0 function. Any drift is a contract bug.
                    eprintln!(
                        "[llvm2] specialization '{key}': unexpected arity {}, skipping",
                        specialized.arity,
                    );
                    stats.actions_failed += 1;
                    continue;
                }

                Self::compile_next_state_action_entry(
                    &key,
                    &specialized,
                    state_layout,
                    callout_opt_level,
                    const_pool,
                    chunk,
                    &mut next_state_fns,
                    &mut inner_exists_expansion_keys,
                    &mut native_action_entries,
                    &mut libraries,
                    &mut stats,
                    &spec.binding_values,
                    formal_values,
                );
            }
        }

        // Compile each invariant function.
        // Use Option to maintain index alignment: invariant_fns[i] always
        // corresponds to spec invariant i, even when compilation fails.
        // This fixes #4197 where failed compilations caused index misalignment.
        for (idx, func) in invariant_bytecodes.iter().enumerate() {
            let Some(func) = *func else {
                stats.invariants_failed += 1;
                eprintln!(
                    "[llvm2] missing bytecode for invariant {idx}; compiled BFS will be ineligible"
                );
                invariant_fns.push(None);
                native_invariant_entries.push(None);
                continue;
            };
            let inv_name = format!("llvm2_inv_{idx}");
            match Self::compile_invariant_func(
                &inv_name,
                func,
                state_layout,
                callout_opt_level,
                invariant_const_pool,
                invariant_chunk,
            ) {
                Ok((fn_ptr, lib, symbol_name)) => {
                    invariant_fns.push(Some(fn_ptr));
                    native_invariant_entries.push(Some(Llvm2NativeInvariantEntry {
                        library: lib.clone(),
                        symbol_name: symbol_name.clone(),
                    }));
                    libraries.push(lib);
                    stats.invariants_compiled += 1;
                    eprintln!(
                        "[llvm2] compiled invariant {idx} ({symbol_name}); eligible for invariant-checking native fused level",
                    );
                }
                Err(e) => {
                    stats.invariants_failed += 1;
                    eprintln!("[llvm2] failed to compile invariant {idx}: {}", e,);
                    invariant_fns.push(None);
                    native_invariant_entries.push(None);
                }
            }
        }

        // Compile each state-constraint predicate separately from invariants.
        // The native ABI is identical to invariants, but the fused BFS loop
        // must use these as successor-pruning predicates, not safety checks.
        for (idx, func) in state_constraint_bytecodes.iter().enumerate() {
            let Some(func) = *func else {
                stats.state_constraints_failed += 1;
                eprintln!(
                    "[llvm2] missing bytecode for state constraint {idx}; constrained native fused BFS will be ineligible"
                );
                state_constraint_fns.push(None);
                native_state_constraint_entries.push(None);
                continue;
            };
            let constraint_name = format!("llvm2_state_constraint_{idx}");
            match Self::compile_invariant_func(
                &constraint_name,
                func,
                state_layout,
                callout_opt_level,
                state_constraint_const_pool,
                state_constraint_chunk,
            ) {
                Ok((fn_ptr, lib, symbol_name)) => {
                    state_constraint_fns.push(Some(fn_ptr));
                    native_state_constraint_entries.push(Some(Llvm2NativeInvariantEntry {
                        library: lib.clone(),
                        symbol_name: symbol_name.clone(),
                    }));
                    libraries.push(lib);
                    stats.state_constraints_compiled += 1;
                    eprintln!(
                        "[llvm2] compiled state constraint {idx} ({symbol_name}); eligible for native fused constraint pruning when backend hook is available",
                    );
                }
                Err(e) => {
                    stats.state_constraints_failed += 1;
                    eprintln!("[llvm2] failed to compile state constraint {idx}: {}", e);
                    state_constraint_fns.push(None);
                    native_state_constraint_entries.push(None);
                }
            }
        }

        stats.total_compile_ms = start.elapsed().as_millis() as u64;

        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys,
            invariant_fns,
            state_constraint_fns,
            native_action_entries,
            native_invariant_entries,
            native_state_constraint_entries,
            state_var_count,
            opt_level: callout_opt_level,
            _libraries: libraries,
        };

        Llvm2NativeCalloutSelftest::log_cache_build_without_sample(&cache);

        (cache, stats)
    }

    /// Compile a single next-state action through the LLVM2 native pipeline.
    ///
    /// Pipeline: BytecodeFunction -> tMIR -> LLVM2 JIT -> NativeLibrary.
    ///
    /// When `chunk` is `Some`, compilation routes through
    /// `compile_entry_next_state_native_with_chunk`, which drains pending
    /// `Call` opcodes so callee function bodies are emitted alongside the
    /// entry. This is required for any action that invokes another user-
    /// defined operator; without it, LLVM2 emits unresolved `__func_N`
    /// symbols. When `chunk` is `None`, falls back to the single-function
    /// path (legacy callers + JIT specialization of arity-0 functions that
    /// do not appear in the chunk's `functions` table).
    ///
    /// Part of #4280 Gap C.
    fn compile_next_state_action(
        action_name: &str,
        func: &tla_tir::bytecode::BytecodeFunction,
        state_layout: Option<&tla_jit_abi::StateLayout>,
        opt_level: tla_llvm2::OptLevel,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
    ) -> Result<(NativeNextStateFn, tla_llvm2::NativeLibrary, String), tla_llvm2::Llvm2Error> {
        // Sanitize the action name for use as an LLVM function name.
        let safe_name = sanitize_llvm_name(action_name);
        if llvm2_dump_filter_matches(LLVM2_DUMP_ACTION_BYTECODE_ENV, action_name)
            || llvm2_dump_filter_matches(LLVM2_DUMP_ACTION_BYTECODE_ENV, &safe_name)
        {
            eprintln!("[llvm2] action {action_name} bytecode: {func:#?}");
        }

        // Compile BytecodeFunction -> tMIR -> native code via LLVM2 JIT pipeline.
        let lib = if let Some((chunk, layout)) = chunk.zip(state_layout) {
            tla_llvm2::compile_entry_next_state_native_with_chunk_and_layout(
                func, chunk, &safe_name, layout, opt_level,
            )?
        } else if let Some(chunk) = chunk {
            // Chunk-aware path: drains `Call` callees from chunk.functions so
            // they are emitted alongside the entry. Fixes #4280 Gap C.
            tla_llvm2::compile_entry_next_state_native_with_chunk(
                func, chunk, &safe_name, opt_level,
            )?
        } else if let Some((pool, layout)) = const_pool.zip(state_layout) {
            tla_llvm2::compile_next_state_native_with_constants_and_layout(
                func, &safe_name, pool, layout, opt_level,
            )?
        } else if let Some(pool) = const_pool {
            tla_llvm2::compile_next_state_native_with_constants(func, &safe_name, pool, opt_level)?
        } else {
            tla_llvm2::compile_next_state_native(func, &safe_name, opt_level)?
        };

        // Look up the compiled function symbol.
        // SAFETY: We control the compilation pipeline and know the exact signature.
        let fn_ptr = unsafe {
            let raw = lib.get_symbol(&safe_name)?;
            std::mem::transmute::<*mut std::ffi::c_void, NativeNextStateFn>(raw)
        };

        Ok((fn_ptr, lib, safe_name))
    }

    /// Compile a single invariant function through the LLVM2 native pipeline.
    ///
    /// Pipeline: BytecodeFunction -> tMIR -> LLVM2 JIT -> NativeLibrary.
    ///
    /// `chunk` semantics match [`compile_next_state_action`]. Part of #4280 Gap C.
    fn compile_invariant_func(
        inv_name: &str,
        func: &tla_tir::bytecode::BytecodeFunction,
        state_layout: Option<&tla_jit_abi::StateLayout>,
        opt_level: tla_llvm2::OptLevel,
        const_pool: Option<&tla_tir::bytecode::ConstantPool>,
        chunk: Option<&tla_tir::bytecode::BytecodeChunk>,
    ) -> Result<(NativeInvariantFn, tla_llvm2::NativeLibrary, String), tla_llvm2::Llvm2Error> {
        let safe_name = sanitize_llvm_name(inv_name);

        if std::env::var("TLA2_LLVM2_DUMP_INVARIANT_BYTECODE").as_deref() == Ok("1") {
            eprintln!("[llvm2] invariant {inv_name} bytecode: {func:#?}");
        }

        // Compile BytecodeFunction -> tMIR -> native code via LLVM2 JIT pipeline.
        let lib = if let Some((chunk, layout)) = chunk.zip(state_layout) {
            tla_llvm2::compile::compile_entry_invariant_native_with_chunk_and_layout(
                func, chunk, &safe_name, layout, opt_level,
            )?
        } else if let Some(chunk) = chunk {
            // Chunk-aware path: emit callee bodies alongside the entry. #4280 Gap C.
            tla_llvm2::compile_entry_invariant_native_with_chunk(
                func, chunk, &safe_name, opt_level,
            )?
        } else if let Some((pool, layout)) = const_pool.zip(state_layout) {
            tla_llvm2::compile_invariant_native_with_constants_and_layout(
                func, &safe_name, pool, layout, opt_level,
            )?
        } else if let Some(pool) = const_pool {
            tla_llvm2::compile_invariant_native_with_constants(func, &safe_name, pool, opt_level)?
        } else {
            tla_llvm2::compile_invariant_native(func, &safe_name, opt_level)?
        };

        // SAFETY: We control the compilation pipeline and know the exact signature.
        let fn_ptr = unsafe {
            let raw = lib.get_symbol(&safe_name)?;
            std::mem::transmute::<*mut std::ffi::c_void, NativeInvariantFn>(raw)
        };

        Ok((fn_ptr, lib, safe_name))
    }

    /// Check whether LLVM2 native compilation is available.
    ///
    /// Returns `true` when the `native` feature is compiled into `tla-llvm2`.
    /// When `false`, [`Llvm2NativeCache::build`] will fail to compile any functions.
    pub(in crate::check) fn is_available() -> bool {
        tla_llvm2::is_native_available()
    }

    /// Check whether the LLVM2 BFS path is activated via environment variable.
    ///
    /// Accepted flags (either enables):
    /// - `TLA2_LLVM2=1` — general LLVM2 activation (covers invariants and
    ///   next-state actions where eligible).
    /// - `TLA2_LLVM2_BFS=1` — BFS-scoped alias (epic #4251 Stream 6). Reads
    ///   identically today; reserved so the BFS code path can be gated
    ///   independently of invariants in the future without a flag flip day.
    ///
    /// OFF by default — nothing changes for existing users unless one of
    /// these flags is explicitly set.
    pub(in crate::check) fn is_enabled() -> bool {
        let general = std::env::var("TLA2_LLVM2").map_or(false, |v| v == "1");
        let bfs = std::env::var("TLA2_LLVM2_BFS").map_or(false, |v| v == "1");
        general || bfs
    }

    /// Number of successfully compiled action functions.
    pub(in crate::check) fn action_count(&self) -> usize {
        self.next_state_fns.len()
    }

    /// Whether at least one next-state action was successfully compiled.
    ///
    /// Used by the fingerprint mixed-mode guard in
    /// `try_activate_compiled_fingerprinting`: when any compiled action can
    /// produce successors during BFS, the fingerprint pipeline must stay on a
    /// single hash domain so that compiled-emitted and interpreter-emitted
    /// successors of the same logical state dedup into the same `Fingerprint`.
    ///
    /// Part of #4319 (LLVM2 fingerprint unification) Phase 0.
    #[inline]
    pub(in crate::check) fn has_any_compiled_action(&self) -> bool {
        !self.next_state_fns.is_empty()
    }

    /// Number of successfully compiled invariant functions.
    pub(in crate::check) fn invariant_count(&self) -> usize {
        self.invariant_fns.iter().filter(|f| f.is_some()).count()
    }

    /// Number of invariant slots tracked by this cache.
    ///
    /// This is the total configured-invariant count observed at build time,
    /// including `None` entries for bytecode/lowering failures. It is distinct
    /// from [`Self::invariant_count`], which only counts successful native
    /// compiles.
    pub(in crate::check) fn invariant_slot_count(&self) -> usize {
        self.invariant_fns.len()
    }

    /// Number of successfully compiled state-constraint functions.
    pub(in crate::check) fn state_constraint_count(&self) -> usize {
        self.state_constraint_fns
            .iter()
            .filter(|f| f.is_some())
            .count()
    }

    /// Number of state-constraint slots tracked by this cache.
    pub(in crate::check) fn state_constraint_slot_count(&self) -> usize {
        self.state_constraint_fns.len()
    }

    /// Whether every configured invariant has a compiled LLVM2 function.
    ///
    /// The length check prevents treating a shorter partial vector as full
    /// coverage. Each slot remains parallel to `config.invariants`, so index
    /// `i` in failures and reports maps back to invariant `i` in the spec.
    pub(in crate::check) fn has_all_invariants(&self, invariant_count: usize) -> bool {
        self.invariant_fns.len() == invariant_count
            && self.invariant_fns.iter().all(Option::is_some)
    }

    /// Whether every configured state constraint has a compiled LLVM2 function.
    pub(in crate::check) fn has_all_state_constraints(&self, constraint_count: usize) -> bool {
        self.state_constraint_fns.len() == constraint_count
            && self.state_constraint_fns.iter().all(Option::is_some)
    }

    /// Names of configured state constraints that lack compiled native entries.
    pub(in crate::check) fn missing_state_constraint_names(
        &self,
        constraint_names: &[String],
    ) -> Vec<String> {
        constraint_names
            .iter()
            .enumerate()
            .filter_map(|(idx, name)| {
                let missing_fn = self
                    .state_constraint_fns
                    .get(idx)
                    .map_or(true, Option::is_none);
                let missing_native = self
                    .native_state_constraint_entries
                    .get(idx)
                    .map_or(true, Option::is_none);
                (missing_fn || missing_native).then(|| name.clone())
            })
            .collect()
    }

    /// Number of state variables.
    pub(in crate::check) fn state_var_count(&self) -> usize {
        self.state_var_count
    }

    /// Check if a specific action is compiled.
    pub(in crate::check) fn contains_action(&self, name: &str) -> bool {
        self.next_state_fns.contains_key(name)
    }

    fn entry_counter_allows_action_dispatch(&self, action_name: &str, limit: u64) -> bool {
        self.native_action_entries
            .get(action_name)
            .map(|entry| entry.library.entry_count(&entry.symbol_name))
            .map_or(false, |entry_count| {
                entry_counter_gate_allows_dispatch(entry_count, limit)
            })
    }

    /// Find compiled native action keys produced by inner-EXISTS expansion.
    ///
    /// The returned order is deterministic so fused BFS action descriptor
    /// ordering is stable across runs.
    pub(in crate::check) fn inner_exists_expansion_keys(&self, base_name: &str) -> Vec<String> {
        self.inner_exists_expansion_keys
            .get(base_name)
            .cloned()
            .unwrap_or_default()
    }

    /// Resolve action keys to native function pointers in caller-provided order.
    pub(in crate::check) fn resolve_actions_ordered(
        &self,
        action_keys: &[String],
    ) -> Option<Vec<NativeNextStateFn>> {
        let mut resolved = Vec::with_capacity(action_keys.len());
        for key in action_keys {
            resolved.push(*self.next_state_fns.get(key)?);
        }
        Some(resolved)
    }

    fn action_descriptor_for_key(
        &self,
        key: &str,
        action_idx: usize,
    ) -> tla_llvm2::ActionDescriptor {
        let (binding_values, formal_values) = self
            .native_action_entries
            .get(key)
            .map(|entry| (entry.binding_values.clone(), entry.formal_values.clone()))
            .unwrap_or_else(|| (Vec::new(), Vec::new()));
        tla_llvm2::ActionDescriptor {
            name: key.to_string(),
            action_idx: action_idx as u32,
            binding_values,
            formal_values,
            read_vars: Vec::new(),
            write_vars: Vec::new(),
        }
    }

    /// Resolve action keys to native-library entries in caller-provided order.
    pub(in crate::check) fn resolve_native_actions_ordered(
        &self,
        action_keys: &[String],
    ) -> Option<Vec<tla_llvm2::Llvm2BfsLevelNativeAction>> {
        let mut resolved = Vec::with_capacity(action_keys.len());
        for (idx, key) in action_keys.iter().enumerate() {
            let entry = self.native_action_entries.get(key)?;
            resolved.push(tla_llvm2::Llvm2BfsLevelNativeAction::new(
                self.action_descriptor_for_key(key, idx),
                entry.library.clone(),
                entry.symbol_name.clone(),
            ));
        }
        Some(resolved)
    }

    /// Resolve native-library invariant entries in stable spec-index order.
    pub(in crate::check) fn resolve_native_invariants_ordered(
        &self,
        invariant_names: &[String],
    ) -> Option<Vec<tla_llvm2::Llvm2BfsLevelNativeInvariant>> {
        if self.native_invariant_entries.len() != invariant_names.len()
            || self.native_invariant_entries.iter().any(Option::is_none)
        {
            return None;
        }

        let mut resolved = Vec::with_capacity(invariant_names.len());
        for (idx, name) in invariant_names.iter().enumerate() {
            let entry = self.native_invariant_entries.get(idx)?.as_ref()?;
            resolved.push(tla_llvm2::Llvm2BfsLevelNativeInvariant::new(
                tla_llvm2::InvariantDescriptor {
                    name: name.clone(),
                    invariant_idx: idx as u32,
                },
                entry.library.clone(),
                entry.symbol_name.clone(),
            ));
        }
        Some(resolved)
    }

    /// Resolve native-library state-constraint entries in stable config order.
    pub(in crate::check) fn resolve_native_state_constraints_ordered(
        &self,
        constraint_names: &[String],
    ) -> Option<Vec<tla_llvm2::Llvm2BfsLevelNativeStateConstraint>> {
        if self.native_state_constraint_entries.len() != constraint_names.len()
            || self
                .native_state_constraint_entries
                .iter()
                .any(Option::is_none)
        {
            return None;
        }

        let mut resolved = Vec::with_capacity(constraint_names.len());
        for (idx, name) in constraint_names.iter().enumerate() {
            let entry = self.native_state_constraint_entries.get(idx)?.as_ref()?;
            let constraint_idx = u32::try_from(idx).ok()?;
            resolved.push(tla_llvm2::Llvm2BfsLevelNativeStateConstraint::new(
                name.clone(),
                constraint_idx,
                entry.library.clone(),
                entry.symbol_name.clone(),
            ));
        }
        Some(resolved)
    }

    /// Resolve invariant function pointers in stable spec-index order.
    pub(in crate::check) fn resolve_invariants_ordered(
        &self,
        invariant_count: usize,
    ) -> Option<Vec<NativeInvariantFn>> {
        if !self.has_all_invariants(invariant_count) {
            return None;
        }
        let mut resolved = Vec::with_capacity(invariant_count);
        for slot in &self.invariant_fns {
            resolved.push((*slot)?);
        }
        Some(resolved)
    }

    /// Evaluate a compiled next-state action on a flat i64 state buffer.
    ///
    /// Returns `Some(Ok(result))` if the action is compiled and evaluation
    /// succeeded. Returns `Some(Err(()))` on runtime error. Returns `None`
    /// if the action is not compiled.
    ///
    /// The `state_in` buffer is snapshotted into the `Enabled` result as
    /// `jit_input`, because compound value deserialization needs the input
    /// buffer to resolve offsets written by native FuncExcept operations.
    /// Fixes #4193: previously `None` was passed making compound states unsound.
    pub(in crate::check) fn eval_action(
        &self,
        action_name: &str,
        state_in: &[i64],
    ) -> Option<Result<Llvm2ActionResult, ()>> {
        self.eval_action_with_state_len(action_name, state_in, self.state_var_count)
    }

    /// Evaluate a compiled next-state action with an explicit state-buffer width.
    ///
    /// Most non-fused callers use the logical state-variable count. Flat-slot
    /// callers must instead pass the fully flattened slot count so native code
    /// sees the same width used by the input and output buffers.
    pub(in crate::check) fn eval_action_with_state_len(
        &self,
        action_name: &str,
        state_in: &[i64],
        state_len: usize,
    ) -> Option<Result<Llvm2ActionResult, ()>> {
        let fn_ptr = self.next_state_fns.get(action_name)?;
        if let Some(limit) = tla_llvm2::llvm2_entry_counter_dispatch_gate_limit() {
            if !self.entry_counter_allows_action_dispatch(action_name, limit) {
                return None;
            }
        }
        let state_len = match u32::try_from(state_len) {
            Ok(state_len) if state_in.len() >= state_len as usize => state_len,
            _ => return Some(Err(())),
        };

        let mut out = JitCallOut::default();
        // Transformed next-state actions keep `Unchanged` checks and only write
        // primed slots they touch. Mirror the Cranelift contract by seeding the
        // successor buffer from the predecessor state before native execution.
        let mut state_out = state_in.to_vec();

        // SAFETY: fn_ptr was obtained from our compilation pipeline with the
        // correct ABI. state_in/state_out are valid i64 buffers. out is
        // caller-allocated. state_len matches the model's variable count.
        tla_llvm2::ensure_jit_execute_mode();
        unsafe {
            fn_ptr(
                &mut out,
                state_in.as_ptr(),
                state_out.as_mut_ptr(),
                state_len,
            );
        }

        match out.status {
            tla_jit_abi::JitStatus::Ok => {
                let enabled = match decode_strict_llvm2_boolean(
                    out.value,
                    &format!("action {action_name}"),
                ) {
                    Ok(enabled) => enabled,
                    Err(()) => return Some(Err(())),
                };
                if enabled {
                    // Snapshot the input buffer for compound value deserialization.
                    // The native function may encode offsets into the input buffer
                    // for compound variables (FuncExcept pattern).
                    let jit_input = state_in.to_vec();
                    Some(Ok(Llvm2ActionResult::Enabled {
                        successor: state_out,
                        jit_input,
                    }))
                } else {
                    Some(Ok(Llvm2ActionResult::Disabled))
                }
            }
            tla_jit_abi::JitStatus::RuntimeError => Some(Err(())),
            // PartialPass or other status -- fall back to interpreter.
            _ => None,
        }
    }

    /// Evaluate a compiled invariant on a flat i64 state buffer.
    ///
    /// Returns `Some(Ok(true))` if the invariant holds, `Some(Ok(false))` if
    /// violated, `Some(Err(()))` on runtime error, `None` if not compiled
    /// (either index out of range or compilation failed for this invariant).
    pub(in crate::check) fn eval_invariant(
        &self,
        invariant_idx: usize,
        state: &[i64],
    ) -> Option<Result<bool, ()>> {
        self.eval_invariant_with_state_len(invariant_idx, state, self.state_var_count)
    }

    /// Evaluate a compiled invariant with an explicit state-buffer width.
    pub(in crate::check) fn eval_invariant_with_state_len(
        &self,
        invariant_idx: usize,
        state: &[i64],
        state_len: usize,
    ) -> Option<Result<bool, ()>> {
        // Double-unwrap: first get the slot (bounds check), then check if compiled.
        let fn_ptr = (*self.invariant_fns.get(invariant_idx)?)?;
        let state_len = match u32::try_from(state_len) {
            Ok(state_len) if state.len() >= state_len as usize => state_len,
            _ => return Some(Err(())),
        };

        let mut out = JitCallOut::default();

        // SAFETY: fn_ptr was obtained from our compilation pipeline with the
        // correct ABI. state is a valid i64 buffer. out is caller-allocated.
        tla_llvm2::ensure_jit_execute_mode();
        unsafe {
            fn_ptr(&mut out, state.as_ptr(), state_len);
        }

        match out.status {
            tla_jit_abi::JitStatus::Ok => {
                match decode_strict_llvm2_boolean(
                    out.value,
                    &format!("invariant index {invariant_idx}"),
                ) {
                    Ok(holds) => Some(Ok(holds)),
                    Err(()) => Some(Err(())),
                }
            }
            tla_jit_abi::JitStatus::RuntimeError => Some(Err(())),
            _ => None,
        }
    }
}

impl std::fmt::Debug for Llvm2NativeCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Llvm2NativeCache")
            .field("actions", &self.next_state_fns.len())
            .field("invariants", &self.invariant_fns.len())
            .field("state_constraints", &self.state_constraint_fns.len())
            .field("state_var_count", &self.state_var_count)
            .field("libraries", &self._libraries.len())
            .finish()
    }
}

/// Sanitize a TLA+ action name into a valid LLVM function name.
///
/// LLVM identifiers must match `[a-zA-Z._][a-zA-Z._0-9]*`. Replace invalid
/// characters with underscores.
fn sanitize_llvm_name(name: &str) -> String {
    let mut result = String::with_capacity(name.len());
    for (i, ch) in name.chars().enumerate() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '.' {
            result.push(ch);
        } else if i == 0 {
            result.push('_');
        } else {
            result.push('_');
        }
    }
    if result.is_empty() {
        result.push_str("_unnamed");
    }
    result
}

/// Check whether LLVM2 dispatch should be active for the current run.
///
/// Returns `true` when:
/// 1. The `llvm2` feature is compiled in (checked at compile time by cfg gate).
/// 2. `TLA2_LLVM2=1` environment variable is set.
/// 3. The `native` feature is compiled into `tla-llvm2` (always true when
///    `tla-check/llvm2` feature is enabled).
pub(in crate::check) fn should_use_llvm2() -> bool {
    Llvm2NativeCache::is_enabled() && Llvm2NativeCache::is_available()
}

/// Thread-safe wrapper for parallel BFS access.
pub(in crate::check) type SharedLlvm2Cache = Arc<Llvm2NativeCache>;

/// First LLVM2-backed adapter for the backend-agnostic compiled BFS step trait.
///
/// This milestone reuses separately compiled LLVM2 action and invariant
/// function pointers. It does not yet generate a fused LLVM2 BFS function; the
/// existing Rust compiled-BFS loop calls this adapter once per parent state.
pub(in crate::check) struct Llvm2CompiledBfsStep {
    action_fns: Vec<NativeNextStateFn>,
    invariant_fns: Vec<NativeInvariantFn>,
    state_len: usize,
}

impl Llvm2CompiledBfsStep {
    /// Build a per-parent LLVM2 compiled BFS step from an existing native cache.
    ///
    /// Returns `None` unless every requested action key and every configured
    /// invariant resolves to a native LLVM2 function. That all-or-nothing guard
    /// is what keeps missing invariant coverage from entering compiled BFS.
    pub(in crate::check) fn from_cache(
        cache: &Llvm2NativeCache,
        action_keys: &[String],
        invariant_count: usize,
    ) -> Option<Self> {
        Self::from_cache_with_state_len(
            cache,
            action_keys,
            invariant_count,
            cache.state_var_count(),
        )
    }

    pub(in crate::check) fn from_cache_with_state_len(
        cache: &Llvm2NativeCache,
        action_keys: &[String],
        invariant_count: usize,
        state_len: usize,
    ) -> Option<Self> {
        let action_fns = cache.resolve_actions_ordered(action_keys)?;
        let invariant_fns = cache.resolve_invariants_ordered(invariant_count)?;
        Some(Self {
            action_fns,
            invariant_fns,
            state_len,
        })
    }

    pub(in crate::check) fn state_len(&self) -> usize {
        self.state_len
    }

    fn run_step_scoped<'a>(
        &self,
        state: &[i64],
        scratch: &'a mut super::bfs::compiled_step_trait::CompiledBfsStepScratch,
    ) -> Result<super::bfs::compiled_step_trait::CompiledStepOutput<'a>, BfsStepError> {
        if state.len() != self.state_len {
            return Err(BfsStepError::RuntimeError);
        }
        let state_len_u32 =
            u32::try_from(self.state_len).map_err(|_| BfsStepError::RuntimeError)?;

        let mut successor_count = 0usize;
        let mut generated_count = 0u32;
        let mut invariant_ok = true;
        let mut failed_invariant_idx = None;
        let mut failed_successor_idx = None;
        scratch.clear();

        for (action_idx, action_fn) in self.action_fns.iter().enumerate() {
            let mut out = JitCallOut::default();
            let successor_start = scratch.append_successor_template(state)?;

            // SAFETY: Function pointers come from `Llvm2NativeCache` after
            // native compilation with the next-state ABI. Buffers are valid for
            // `state_len` i64 slots and `out` is caller-allocated.
            tla_llvm2::ensure_jit_execute_mode();
            unsafe {
                let state_out = scratch.successor_mut(successor_start, self.state_len)?;
                action_fn(
                    &mut out,
                    state.as_ptr(),
                    state_out.as_mut_ptr(),
                    state_len_u32,
                );
            }

            match out.status {
                tla_jit_abi::JitStatus::Ok => {
                    if !decode_strict_llvm2_boolean(
                        out.value,
                        &format!("compiled BFS action index {action_idx}"),
                    )
                    .map_err(|()| BfsStepError::RuntimeError)?
                    {
                        scratch.truncate_slots(successor_start);
                        continue;
                    }
                    generated_count = generated_count
                        .checked_add(1)
                        .ok_or(BfsStepError::RuntimeError)?;
                    let current_successor_idx = successor_count;
                    let state_out = scratch.successor(successor_start, self.state_len)?;

                    for (idx, invariant_fn) in self.invariant_fns.iter().enumerate() {
                        let mut inv_out = JitCallOut::default();
                        // SAFETY: Invariant function pointers come from
                        // `Llvm2NativeCache` with the invariant ABI. The
                        // successor buffer is valid for `state_len` i64 slots.
                        tla_llvm2::ensure_jit_execute_mode();
                        unsafe {
                            invariant_fn(&mut inv_out, state_out.as_ptr(), state_len_u32);
                        }

                        match inv_out.status {
                            tla_jit_abi::JitStatus::Ok => {
                                if decode_strict_llvm2_boolean(
                                    inv_out.value,
                                    &format!("compiled BFS invariant index {idx}"),
                                )
                                .map_err(|()| BfsStepError::RuntimeError)?
                                {
                                    continue;
                                }
                                invariant_ok = false;
                                failed_invariant_idx = Some(
                                    u32::try_from(idx).map_err(|_| BfsStepError::RuntimeError)?,
                                );
                                failed_successor_idx = Some(
                                    u32::try_from(current_successor_idx)
                                        .map_err(|_| BfsStepError::RuntimeError)?,
                                );
                                break;
                            }
                            tla_jit_abi::JitStatus::RuntimeError => {
                                return Err(BfsStepError::RuntimeError);
                            }
                            _ => return Err(BfsStepError::RuntimeError),
                        }
                    }

                    successor_count += 1;

                    if !invariant_ok {
                        break;
                    }
                }
                tla_jit_abi::JitStatus::RuntimeError => return Err(BfsStepError::RuntimeError),
                _ => return Err(BfsStepError::RuntimeError),
            }
        }

        let output = scratch.output_ref(
            self.state_len,
            successor_count,
            generated_count,
            invariant_ok,
            failed_invariant_idx,
            failed_successor_idx,
        )?;
        Ok(
            super::bfs::compiled_step_trait::CompiledStepOutput::from_borrowed(
                output,
                self.state_len,
            ),
        )
    }
}

impl super::bfs::compiled_step_trait::CompiledBfsStep for Llvm2CompiledBfsStep {
    fn state_len(&self) -> usize {
        self.state_len
    }

    fn preserves_state_graph_successor_edges(&self) -> bool {
        true
    }

    fn step_flat(&self, state: &[i64]) -> Result<FlatBfsStepOutput, BfsStepError> {
        let mut scratch =
            super::bfs::compiled_step_trait::CompiledBfsStepScratch::new(self.state_len);
        self.run_step_scoped(state, &mut scratch)
            .map(|output| output.to_owned_flat())
    }

    fn step_flat_scoped<'a>(
        &self,
        state: &[i64],
        scratch: &'a mut super::bfs::compiled_step_trait::CompiledBfsStepScratch,
    ) -> Result<super::bfs::compiled_step_trait::CompiledStepOutput<'a>, BfsStepError> {
        self.run_step_scoped(state, scratch)
    }
}

/// LLVM2-backed adapter for the backend-agnostic compiled BFS level trait.
///
/// This currently wraps `tla_llvm2::Llvm2BfsLevelPrototype`: action and
/// invariant calls are native LLVM2 function pointers, while the parent
/// frontier loop is still Rust. That makes the level path available to
/// `compiled_bfs_loop.rs` without pretending that LLVM2 has generated a native
/// fused parent-loop function yet.
pub(in crate::check) struct Llvm2CompiledBfsLevel {
    implementation: Llvm2CompiledBfsLevelImplementation,
    state_len: usize,
    native_fused_loop: bool,
    native_fused_state_constraint_count: usize,
    native_fused_invariant_count: usize,
    regular_invariants_checked_by_backend: bool,
    state_graph_successors_complete: bool,
}

fn native_fused_parent_loop_opt_level(
    _cache_opt_level: tla_llvm2::OptLevel,
) -> tla_llvm2::OptLevel {
    match std::env::var(LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL_ENV) {
        Ok(value) if value.trim().eq_ignore_ascii_case("O1") => tla_llvm2::OptLevel::O1,
        Ok(value) if value.trim().eq_ignore_ascii_case("O3") => tla_llvm2::OptLevel::O3,
        Ok(value) => {
            eprintln!(
                "[llvm2] ignoring {LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL_ENV}={value:?}; expected O1 or O3"
            );
            tla_llvm2::OptLevel::O1
        }
        Err(_) => tla_llvm2::OptLevel::O1,
    }
}

enum Llvm2CompiledBfsLevelImplementation {
    Prototype(Mutex<tla_llvm2::CompiledBfsLevel>),
    Native {
        level: Mutex<tla_llvm2::Llvm2BfsLevelNative>,
        action_count: usize,
        successor_arena_pool: super::bfs::compiled_step_trait::Llvm2SuccessorArenaPool,
        callout_selftest: Mutex<Option<Llvm2NativeCalloutSelftest>>,
    },
    #[cfg(test)]
    MockNative {
        entrypoint: tla_llvm2::Llvm2FusedLevelFn,
        action_count: usize,
        scratch: Mutex<Vec<i64>>,
    },
}

impl Llvm2CompiledBfsLevel {
    /// Build a full-frontier LLVM2 level adapter from an existing native cache.
    ///
    /// Returns `None` unless every requested action key resolves to native
    /// LLVM2 code. The production native path is action-only: the generated
    /// parent loop emits successors and the Rust BFS loop checks invariants
    /// after flat dedup. The prototype fallback still requires compiled
    /// invariants because it performs invariant checks inside the prototype
    /// level object.
    pub(in crate::check) fn from_cache(
        cache: &Llvm2NativeCache,
        action_keys: &[String],
        invariant_names: &[String],
        state_constraint_names: &[String],
        expected_states: usize,
        native_fused_state_len: Option<usize>,
    ) -> Option<Self> {
        let action_fns = cache.resolve_actions_ordered(action_keys)?;

        let actions: Vec<tla_llvm2::Llvm2CompiledAction> = action_keys
            .iter()
            .cloned()
            .enumerate()
            .zip(action_fns)
            .map(|((idx, name), func)| {
                tla_llvm2::Llvm2CompiledAction::new(
                    cache.action_descriptor_for_key(&name, idx),
                    func,
                )
            })
            .collect();

        if let Some(native_fused_state_len) = native_fused_state_len {
            if let Some(native_actions) = cache.resolve_native_actions_ordered(action_keys) {
                Llvm2NativeCalloutSelftest::log_fused_build_without_sample(native_fused_state_len);

                if !state_constraint_names.is_empty() {
                    let Some(native_state_constraints) =
                        cache.resolve_native_state_constraints_ordered(state_constraint_names)
                    else {
                        let missing = state_constraint_names
                            .iter()
                            .enumerate()
                            .filter_map(|(idx, name)| {
                                cache
                                    .native_state_constraint_entries
                                    .get(idx)
                                    .and_then(|entry| entry.as_ref())
                                    .is_none()
                                    .then(|| name.as_str())
                            })
                            .collect::<Vec<_>>();
                        let first_missing = missing.first().copied().unwrap_or("<unknown>");
                        eprintln!(
                            "[llvm2] native fused CompiledBfsLevel not eligible: {}/{} state constraints missing native entries (first missing: {first_missing})",
                            missing.len(),
                            state_constraint_names.len(),
                        );
                        return None;
                    };

                    let native_invariants =
                        cache.resolve_native_invariants_ordered(invariant_names);
                    let regular_invariants_checked_by_backend = native_invariants.is_some();
                    if !invariant_names.is_empty() && !regular_invariants_checked_by_backend {
                        eprintln!(
                            "[llvm2] state-constrained native fused CompiledBfsLevel using Rust invariant fallback: not all regular invariants have native entries"
                        );
                    }
                    let native_invariants = native_invariants.unwrap_or_default();
                    let callout_selftest =
                        Llvm2NativeCalloutSelftest::from_cache_if_enabled_or_required(
                            cache,
                            &native_actions,
                            &native_state_constraints,
                            &native_invariants,
                            true,
                        );

                    match tla_llvm2::compile_bfs_level_native_with_state_constraints(
                        native_fused_state_len,
                        &native_actions,
                        &native_state_constraints,
                        &native_invariants,
                        native_fused_parent_loop_opt_level(cache.opt_level),
                    ) {
                        Ok(native_level)
                            if native_level.state_constraint_count()
                                == state_constraint_names.len() =>
                        {
                            return Self::from_native_with_callout_selftest(
                                native_level,
                                action_keys.len(),
                                regular_invariants_checked_by_backend,
                                callout_selftest,
                            );
                        }
                        Ok(native_level) => {
                            eprintln!(
                                "[llvm2] state-constrained native fused CompiledBfsLevel rejected: backend reported {}/{} active state constraints",
                                native_level.state_constraint_count(),
                                state_constraint_names.len(),
                            );
                            return None;
                        }
                        Err(err) => {
                            eprintln!(
                                "[llvm2] state-constrained native fused CompiledBfsLevel unavailable: {err}"
                            );
                            return None;
                        }
                    }
                }

                if let Some(native_invariants) =
                    cache.resolve_native_invariants_ordered(invariant_names)
                {
                    let callout_selftest =
                        Llvm2NativeCalloutSelftest::from_cache_if_enabled_or_required(
                            cache,
                            &native_actions,
                            &[],
                            &native_invariants,
                            false,
                        );
                    match tla_llvm2::compile_bfs_level_native(
                        native_fused_state_len,
                        &native_actions,
                        &native_invariants,
                        native_fused_parent_loop_opt_level(cache.opt_level),
                    ) {
                        Ok(native_level) => {
                            return Self::from_native_with_callout_selftest(
                                native_level,
                                action_keys.len(),
                                true,
                                callout_selftest,
                            );
                        }
                        Err(err) => {
                            eprintln!(
                                "[llvm2] invariant-checking native fused CompiledBfsLevel unavailable, falling back to action-only native/prototype: {err}"
                            );
                        }
                    }
                } else if !invariant_names.is_empty() {
                    eprintln!(
                        "[llvm2] native fused CompiledBfsLevel using action-only fallback: not all invariants have native entries"
                    );
                }

                let callout_selftest =
                    Llvm2NativeCalloutSelftest::from_cache_if_enabled_or_required(
                        cache,
                        &native_actions,
                        &[],
                        &[],
                        false,
                    );
                match tla_llvm2::compile_bfs_level_native_actions_only(
                    native_fused_state_len,
                    &native_actions,
                    native_fused_parent_loop_opt_level(cache.opt_level),
                ) {
                    Ok(native_level) => {
                        return Self::from_native_with_callout_selftest(
                            native_level,
                            action_keys.len(),
                            invariant_names.is_empty(),
                            callout_selftest,
                        );
                    }
                    Err(err) => {
                        eprintln!(
                            "[llvm2] action-only native fused CompiledBfsLevel unavailable, falling back to prototype: {err}"
                        );
                    }
                }
            }
        }

        let prototype_state_len = native_fused_state_len.unwrap_or_else(|| cache.state_var_count());
        let invariant_fns = cache.resolve_invariants_ordered(invariant_names.len())?;
        let invariants: Vec<tla_llvm2::Llvm2CompiledInvariant> = invariant_names
            .iter()
            .cloned()
            .enumerate()
            .zip(invariant_fns)
            .map(|((idx, name), func)| {
                tla_llvm2::Llvm2CompiledInvariant::new(
                    tla_llvm2::InvariantDescriptor {
                        name,
                        invariant_idx: idx as u32,
                    },
                    func,
                )
            })
            .collect();

        let prototype = tla_llvm2::CompiledBfsLevel::new(
            prototype_state_len,
            actions,
            invariants,
            expected_states,
        )
        .ok()?;
        let capabilities = prototype.capabilities();

        Some(Self {
            implementation: Llvm2CompiledBfsLevelImplementation::Prototype(Mutex::new(prototype)),
            state_len: prototype_state_len,
            native_fused_loop: capabilities.native_fused_loop,
            native_fused_state_constraint_count: 0,
            native_fused_invariant_count: 0,
            regular_invariants_checked_by_backend: true,
            state_graph_successors_complete: !capabilities.local_dedup,
        })
    }

    /// Wrap a native LLVM2 fused parent-loop object once the LLVM2 compiler
    /// surface can produce one.
    #[allow(dead_code)]
    pub(in crate::check) fn from_native(
        native_level: tla_llvm2::Llvm2BfsLevelNative,
        action_count: usize,
        regular_invariants_checked_by_backend: bool,
    ) -> Option<Self> {
        Self::from_native_with_callout_selftest(
            native_level,
            action_count,
            regular_invariants_checked_by_backend,
            None,
        )
    }

    fn from_native_with_callout_selftest(
        native_level: tla_llvm2::Llvm2BfsLevelNative,
        action_count: usize,
        regular_invariants_checked_by_backend: bool,
        callout_selftest: Option<Llvm2NativeCalloutSelftest>,
    ) -> Option<Self> {
        let capabilities = native_level.capabilities();
        if !capabilities.native_fused_loop {
            return None;
        }
        let state_len = native_level.state_len();
        let native_fused_state_constraint_count = native_level.state_constraint_count();
        let native_fused_invariant_count = native_level.invariant_count();

        Some(Self {
            state_len,
            implementation: Llvm2CompiledBfsLevelImplementation::Native {
                level: Mutex::new(native_level),
                action_count,
                successor_arena_pool: Arc::new(Mutex::new(Some(
                    tla_llvm2::Llvm2SuccessorArena::new(state_len),
                ))),
                callout_selftest: Mutex::new(callout_selftest),
            },
            native_fused_loop: true,
            native_fused_state_constraint_count,
            native_fused_invariant_count,
            regular_invariants_checked_by_backend,
            state_graph_successors_complete: !capabilities.local_dedup,
        })
    }

    #[cfg(test)]
    fn from_mock_native_fn(
        state_len: usize,
        action_count: usize,
        entrypoint: tla_llvm2::Llvm2FusedLevelFn,
    ) -> Self {
        Self::from_mock_native_fn_with_metadata(state_len, action_count, entrypoint, 0, false)
    }

    #[cfg(test)]
    fn from_mock_native_fn_with_metadata(
        state_len: usize,
        action_count: usize,
        entrypoint: tla_llvm2::Llvm2FusedLevelFn,
        native_fused_invariant_count: usize,
        regular_invariants_checked_by_backend: bool,
    ) -> Self {
        Self::from_mock_native_fn_with_counts(
            state_len,
            action_count,
            entrypoint,
            0,
            native_fused_invariant_count,
            regular_invariants_checked_by_backend,
        )
    }

    #[cfg(test)]
    fn from_mock_native_fn_with_counts(
        state_len: usize,
        action_count: usize,
        entrypoint: tla_llvm2::Llvm2FusedLevelFn,
        native_fused_state_constraint_count: usize,
        native_fused_invariant_count: usize,
        regular_invariants_checked_by_backend: bool,
    ) -> Self {
        let scratch_len = state_len
            .max(1)
            .checked_add(64)
            .expect("mock native fused level scratch layout");
        Self {
            state_len,
            implementation: Llvm2CompiledBfsLevelImplementation::MockNative {
                entrypoint,
                action_count,
                scratch: Mutex::new(vec![0; scratch_len]),
            },
            native_fused_loop: true,
            native_fused_state_constraint_count,
            native_fused_invariant_count,
            regular_invariants_checked_by_backend,
            state_graph_successors_complete: true,
        }
    }

    pub(in crate::check) fn state_len(&self) -> usize {
        self.state_len
    }

    pub(in crate::check) fn is_native_fused_loop(&self) -> bool {
        self.native_fused_loop
    }

    pub(in crate::check) fn native_fused_invariant_count(&self) -> usize {
        self.native_fused_invariant_count
    }

    pub(in crate::check) fn native_fused_state_constraint_count(&self) -> usize {
        self.native_fused_state_constraint_count
    }

    pub(in crate::check) fn native_fused_mode(&self) -> &'static str {
        if !self.native_fused_loop {
            "prototype"
        } else if self.native_fused_state_constraint_count > 0 {
            "state_constraint_checking"
        } else if self.native_fused_invariant_count == 0 {
            "action_only"
        } else {
            "invariant_checking"
        }
    }

    pub(in crate::check) fn loop_kind_label(&self) -> &'static str {
        match self.native_fused_mode() {
            "state_constraint_checking" => "state-constrained native fused LLVM2 parent loop",
            "action_only" => "action-only native fused LLVM2 parent loop",
            "invariant_checking" => "invariant-checking native fused LLVM2 parent loop",
            _ => "prototype Rust parent loop over LLVM2 action/invariant pointers",
        }
    }

    pub(in crate::check) fn loop_kind_telemetry(&self) -> &'static str {
        match self.native_fused_mode() {
            "action_only" | "invariant_checking" | "state_constraint_checking" => {
                "native_fused_llvm2_parent_loop"
            }
            _ => "prototype_rust_parent_loop_over_llvm2_action_invariant_pointers",
        }
    }

    pub(in crate::check) fn native_fused_state_constraints_checked_by_backend(
        &self,
        expected_count: usize,
    ) -> bool {
        expected_count == 0
            || (self.native_fused_loop
                && self.native_fused_state_constraint_count == expected_count)
    }

    pub(in crate::check) fn native_fused_regular_invariants_checked_by_backend(&self) -> bool {
        self.native_fused_loop && self.regular_invariants_checked_by_backend
    }

    pub(in crate::check) fn native_fused_local_dedup(&self) -> bool {
        self.native_fused_loop && !self.state_graph_successors_complete
    }

    fn map_fused_level_error(error: tla_llvm2::Llvm2BfsLevelError) -> Option<BfsStepError> {
        match error {
            tla_llvm2::Llvm2BfsLevelError::FallbackNeeded => {
                eprintln!(
                    "[llvm2] CompiledBfsLevel requested interpreter fallback; using non-fused fallback path"
                );
                None
            }
            tla_llvm2::Llvm2BfsLevelError::BufferOverflow { partial_count } => {
                Some(BfsStepError::BufferOverflow { partial_count })
            }
            _ => Some(BfsStepError::RuntimeError),
        }
    }

    fn map_fused_level_error_for_level(
        &self,
        error: tla_llvm2::Llvm2BfsLevelError,
    ) -> Option<BfsStepError> {
        if self.native_fused_loop && self.native_fused_state_constraint_count > 0 {
            eprintln!(
                "[llvm2] state-constrained native fused CompiledBfsLevel failed closed: {error}"
            );
            return Some(BfsStepError::FatalRuntimeError);
        }
        Self::map_fused_level_error(error)
    }

    fn map_error(error: tla_llvm2::Llvm2BfsLevelError) -> BfsStepError {
        Self::map_fused_level_error(error).unwrap_or(BfsStepError::RuntimeError)
    }

    fn level_result_from_llvm2(
        successors: tla_llvm2::Llvm2SuccessorArena,
        outcome: tla_llvm2::Llvm2BfsLevelOutcome,
        regular_invariants_checked_by_backend: bool,
        state_graph_successors_complete: bool,
    ) -> super::bfs::compiled_step_trait::CompiledLevelResult {
        let (invariant_ok, failed_parent_idx, failed_invariant_idx, failed_successor_idx) =
            match outcome.invariant {
                tla_llvm2::Llvm2InvariantStatus::Passed => (true, None, None, None),
                tla_llvm2::Llvm2InvariantStatus::Failed {
                    parent_index,
                    invariant_index,
                    successor_index,
                } => (
                    false,
                    Some(parent_index as usize),
                    Some(invariant_index),
                    Some(successor_index as usize),
                ),
            };

        super::bfs::compiled_step_trait::CompiledLevelResult::from_llvm2_successor_arena_with_failed_successor_idx(
            successors,
            outcome.parents_processed,
            outcome.total_generated,
            outcome.total_new,
            invariant_ok,
            failed_parent_idx,
            failed_invariant_idx,
            None,
            failed_successor_idx,
            regular_invariants_checked_by_backend,
        )
        .with_state_graph_successors_complete(state_graph_successors_complete)
    }

    fn level_result_from_reusable_llvm2(
        successors: tla_llvm2::Llvm2SuccessorArena,
        pool: super::bfs::compiled_step_trait::Llvm2SuccessorArenaPool,
        outcome: tla_llvm2::Llvm2BfsLevelOutcome,
        regular_invariants_checked_by_backend: bool,
        state_graph_successors_complete: bool,
    ) -> super::bfs::compiled_step_trait::CompiledLevelResult {
        let (invariant_ok, failed_parent_idx, failed_invariant_idx, failed_successor_idx) =
            match outcome.invariant {
                tla_llvm2::Llvm2InvariantStatus::Passed => (true, None, None, None),
                tla_llvm2::Llvm2InvariantStatus::Failed {
                    parent_index,
                    invariant_index,
                    successor_index,
                } => (
                    false,
                    Some(parent_index as usize),
                    Some(invariant_index),
                    Some(successor_index as usize),
                ),
            };

        super::bfs::compiled_step_trait::CompiledLevelResult::from_reusable_llvm2_successor_arena_with_failed_successor_idx(
            successors,
            pool,
            outcome.parents_processed,
            outcome.total_generated,
            outcome.total_new,
            invariant_ok,
            failed_parent_idx,
            failed_invariant_idx,
            None,
            failed_successor_idx,
            regular_invariants_checked_by_backend,
        )
        .with_state_graph_successors_complete(state_graph_successors_complete)
    }

    fn recycle_successor_arena(
        pool: &super::bfs::compiled_step_trait::Llvm2SuccessorArenaPool,
        mut successors: tla_llvm2::Llvm2SuccessorArena,
    ) {
        successors.clear();
        if let Ok(mut pooled) = pool.lock() {
            if pooled.is_none() {
                *pooled = Some(successors);
            }
        }
    }

    fn maybe_run_native_callout_selftest(
        callout_selftest: &Mutex<Option<Llvm2NativeCalloutSelftest>>,
        arena: &[i64],
        parent_count: usize,
        state_len: usize,
    ) -> Result<(), BfsStepError> {
        let selftest = match callout_selftest.lock() {
            Ok(mut guard) => guard.take(),
            Err(_) => return Err(BfsStepError::RuntimeError),
        };
        let Some(selftest) = selftest else {
            return Ok(());
        };

        let fail_closed = selftest.fail_closed;
        match selftest.run_on_first_parent(arena, parent_count, state_len) {
            Ok(()) => {
                eprintln!("[llvm2-selftest] native fused callout selftest complete");
                Ok(())
            }
            Err(reason) => {
                eprintln!("[llvm2-selftest] native fused callout selftest failed: {reason}");
                if fail_closed {
                    eprintln!(
                        "[llvm2-selftest] failing closed because {LLVM2_NATIVE_CALLOUT_SELFTEST_FAIL_CLOSED_ENV}=1 or {LLVM2_NATIVE_CALLOUT_SELFTEST_ENV}=strict/fail_closed"
                    );
                    Err(BfsStepError::FatalRuntimeError)
                } else {
                    Ok(())
                }
            }
        }
    }

    #[cfg(test)]
    fn run_mock_native(
        &self,
        entrypoint: tla_llvm2::Llvm2FusedLevelFn,
        action_count: usize,
        scratch: &mut [i64],
        arena: &[i64],
        parent_count: usize,
    ) -> Option<Result<super::bfs::compiled_step_trait::CompiledLevelResult, BfsStepError>> {
        let parent_abi = match tla_llvm2::Llvm2BfsParentArenaAbi::new(
            arena,
            parent_count,
            self.state_len,
            scratch,
        ) {
            Ok(parent_abi) => parent_abi,
            Err(error) => return Some(Err(Self::map_error(error))),
        };
        let mut successors = tla_llvm2::Llvm2SuccessorArena::with_capacity(
            self.state_len,
            parent_count.saturating_mul(action_count),
        );
        let mut successor_abi =
            match successors.prepare_abi(parent_count.saturating_mul(action_count)) {
                Ok(successor_abi) => successor_abi,
                Err(error) => return Some(Err(Self::map_error(error))),
            };
        let returned_status = unsafe { entrypoint(&parent_abi, &mut successor_abi) };
        if returned_status != successor_abi.status {
            return Some(Err(BfsStepError::RuntimeError));
        }
        let outcome = match unsafe { successors.commit_abi(&successor_abi) } {
            Ok(outcome) => outcome,
            Err(error) => return self.map_fused_level_error_for_level(error).map(Err),
        };
        Some(Ok(Self::level_result_from_llvm2(
            successors,
            outcome,
            self.regular_invariants_checked_by_backend,
            self.state_graph_successors_complete,
        )))
    }
}

impl super::bfs::compiled_step_trait::CompiledBfsLevel for Llvm2CompiledBfsLevel {
    fn has_fused_level(&self) -> bool {
        true
    }

    fn has_native_fused_level(&self) -> bool {
        self.native_fused_loop
    }

    fn skip_global_pre_seen_lookup(&self) -> bool {
        self.native_fused_loop
            && self.native_fused_invariant_count > 0
            && self.regular_invariants_checked_by_backend
    }

    fn preflight_fused_arena(
        &self,
        arena: &[i64],
        parent_count: usize,
    ) -> Result<(), BfsStepError> {
        match &self.implementation {
            Llvm2CompiledBfsLevelImplementation::Native {
                callout_selftest, ..
            } => Self::maybe_run_native_callout_selftest(
                callout_selftest,
                arena,
                parent_count,
                self.state_len,
            ),
            _ => Ok(()),
        }
    }

    fn run_level_fused_arena(
        &self,
        arena: &[i64],
        parent_count: usize,
    ) -> Option<Result<super::bfs::compiled_step_trait::CompiledLevelResult, BfsStepError>> {
        match &self.implementation {
            Llvm2CompiledBfsLevelImplementation::Prototype(prototype) => {
                let mut prototype = match prototype.lock() {
                    Ok(guard) => guard,
                    Err(_) => return Some(Err(BfsStepError::RuntimeError)),
                };
                let mut successors = tla_llvm2::Llvm2SuccessorArena::with_capacity(
                    self.state_len,
                    parent_count.saturating_mul(prototype.action_count()),
                );

                let outcome = match prototype.run_level_arena(arena, parent_count, &mut successors)
                {
                    Ok(outcome) => outcome,
                    Err(error) => return Self::map_fused_level_error(error).map(Err),
                };

                Some(Ok(Self::level_result_from_llvm2(
                    successors,
                    outcome,
                    self.regular_invariants_checked_by_backend,
                    self.state_graph_successors_complete,
                )))
            }
            Llvm2CompiledBfsLevelImplementation::Native {
                level,
                action_count,
                successor_arena_pool,
                callout_selftest,
            } => {
                if let Err(error) = Self::maybe_run_native_callout_selftest(
                    callout_selftest,
                    arena,
                    parent_count,
                    self.state_len,
                ) {
                    return Some(Err(error));
                }

                let mut level = match level.lock() {
                    Ok(guard) => guard,
                    Err(_) => return Some(Err(BfsStepError::RuntimeError)),
                };
                let pool = successor_arena_pool.clone();
                let mut successors = match pool.lock() {
                    Ok(mut pooled) => pooled
                        .take()
                        .unwrap_or_else(|| tla_llvm2::Llvm2SuccessorArena::new(self.state_len)),
                    Err(_) => return Some(Err(BfsStepError::RuntimeError)),
                };
                let outcome = match level.run_level_arena_with_capacity(
                    arena,
                    parent_count,
                    parent_count.saturating_mul(*action_count),
                    &mut successors,
                ) {
                    Ok(outcome) => outcome,
                    Err(error) => {
                        Self::recycle_successor_arena(&pool, successors);
                        return self.map_fused_level_error_for_level(error).map(Err);
                    }
                };

                Some(Ok(Self::level_result_from_reusable_llvm2(
                    successors,
                    pool,
                    outcome,
                    self.regular_invariants_checked_by_backend,
                    self.state_graph_successors_complete,
                )))
            }
            #[cfg(test)]
            Llvm2CompiledBfsLevelImplementation::MockNative {
                entrypoint,
                action_count,
                scratch,
            } => {
                let mut scratch = match scratch.lock() {
                    Ok(guard) => guard,
                    Err(_) => return Some(Err(BfsStepError::RuntimeError)),
                };
                self.run_mock_native(
                    *entrypoint,
                    *action_count,
                    &mut scratch,
                    arena,
                    parent_count,
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::model_checker::bfs::compiled_step_trait::{
        CompiledBfsLevel as _, CompiledBfsStep as _, CompiledBfsStepScratch,
    };
    use crate::check::model_checker::ModelChecker;
    use crate::config::Config;
    use crate::test_support::parse_module;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use tla_core::ast::Unit;
    use tla_jit_abi::{CompoundLayout, StateLayout, VarLayout};
    use tla_value::Value;

    #[test]
    fn test_sanitize_llvm_name_simple() {
        assert_eq!(sanitize_llvm_name("InitiateProbe"), "InitiateProbe");
    }

    #[test]
    fn test_sanitize_llvm_name_with_spaces() {
        assert_eq!(sanitize_llvm_name("Send Msg"), "Send_Msg");
    }

    #[test]
    fn test_sanitize_llvm_name_with_special_chars() {
        assert_eq!(sanitize_llvm_name("a->b"), "a__b");
    }

    #[test]
    fn test_sanitize_llvm_name_empty() {
        assert_eq!(sanitize_llvm_name(""), "_unnamed");
    }

    #[test]
    fn test_sanitize_llvm_name_dots_and_underscores() {
        assert_eq!(sanitize_llvm_name("foo.bar_baz"), "foo.bar_baz");
    }

    #[test]
    fn test_is_enabled_returns_false_by_default() {
        // TLA2_LLVM2 is not set in the test environment (usually).
        // This test verifies the function doesn't panic.
        let _ = Llvm2NativeCache::is_enabled();
    }

    unsafe extern "C" fn fake_partial_next_state(
        out: *mut JitCallOut,
        _state_in: *const i64,
        state_out: *mut i64,
        _state_len: u32,
    ) {
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 1;
            *state_out.add(0) = 123;
        }
    }

    unsafe extern "C" fn fake_partial_next_state_disabled(
        out: *mut JitCallOut,
        _state_in: *const i64,
        _state_out: *mut i64,
        _state_len: u32,
    ) {
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 0;
        }
    }

    unsafe extern "C" fn fake_next_state_noncanonical_true(
        out: *mut JitCallOut,
        _state_in: *const i64,
        state_out: *mut i64,
        _state_len: u32,
    ) {
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 2;
            *state_out.add(0) = 123;
        }
    }

    unsafe extern "C" fn fake_next_state_leaves_sentinel_status(
        _out: *mut JitCallOut,
        _state_in: *const i64,
        _state_out: *mut i64,
        _state_len: u32,
    ) {
    }

    static ACTION_OUTPUT_STATE_CONSTRAINT_HITS: AtomicUsize = AtomicUsize::new(0);
    static ACTION_OUTPUT_INVARIANT_CALLS: AtomicUsize = AtomicUsize::new(0);
    static ACTION_OUTPUT_INVARIANT_HITS: AtomicUsize = AtomicUsize::new(0);
    static CALLOUT_SELFTEST_FAIL_CLOSED_ACTION_HITS: AtomicUsize = AtomicUsize::new(0);
    static CALLOUT_SELFTEST_NON_STRICT_ACTION_HITS: AtomicUsize = AtomicUsize::new(0);
    static CALLOUT_SELFTEST_ARENA_ACTION_CALLS: AtomicUsize = AtomicUsize::new(0);
    static CALLOUT_SELFTEST_ARENA_CONSTRAINT_CALLS: AtomicUsize = AtomicUsize::new(0);
    static CALLOUT_SELFTEST_ARENA_INVARIANT_CALLS: AtomicUsize = AtomicUsize::new(0);
    static CALLOUT_SELFTEST_ARENA_STALE_ENTRY: AtomicUsize = AtomicUsize::new(0);

    struct TlaRuntimeArenaClearGuard;

    impl TlaRuntimeArenaClearGuard {
        fn new() -> Self {
            clear_tla_runtime_arenas_for_selftest_test();
            Self
        }
    }

    impl Drop for TlaRuntimeArenaClearGuard {
        fn drop(&mut self) {
            clear_tla_runtime_arenas_for_selftest_test();
        }
    }

    fn clear_tla_runtime_arenas_for_selftest_test() {
        tla_llvm2::runtime_abi::tla_ops::clear_tla_iter_arena();
        tla_llvm2::runtime_abi::tla_ops::clear_tla_arena();
    }

    fn seed_tla_runtime_arenas_for_selftest_test() {
        let set = Value::empty_set();
        let set_handle = tla_llvm2::runtime_abi::tla_ops::handle_from_value(&set);
        let _iter = tla_llvm2::runtime_abi::tla_ops::tla_quantifier_iter_new(set_handle);
    }

    fn record_callout_selftest_arena_entry() {
        let set = Value::empty_set();
        let set_handle = tla_llvm2::runtime_abi::tla_ops::handle_from_value(&set);
        let iter = tla_llvm2::runtime_abi::tla_ops::tla_quantifier_iter_new(set_handle);
        if set_handle != tla_llvm2::runtime_abi::tla_ops::H_TAG_ARENA || iter != 0 {
            CALLOUT_SELFTEST_ARENA_STALE_ENTRY.fetch_add(1, Ordering::SeqCst);
        }
    }

    unsafe extern "C" fn fake_next_state_records_fail_closed_selftest_hit(
        out: *mut JitCallOut,
        _state_in: *const i64,
        _state_out: *mut i64,
        _state_len: u32,
    ) {
        CALLOUT_SELFTEST_FAIL_CLOSED_ACTION_HITS.fetch_add(1, Ordering::SeqCst);
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 0;
        }
    }

    unsafe extern "C" fn fake_next_state_records_non_strict_selftest_hit(
        out: *mut JitCallOut,
        _state_in: *const i64,
        _state_out: *mut i64,
        _state_len: u32,
    ) {
        CALLOUT_SELFTEST_NON_STRICT_ACTION_HITS.fetch_add(1, Ordering::SeqCst);
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 0;
        }
    }

    unsafe extern "C" fn fake_next_state_writes_seven(
        out: *mut JitCallOut,
        _state_in: *const i64,
        state_out: *mut i64,
        _state_len: u32,
    ) {
        unsafe {
            *state_out.add(0) = 7;
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 1;
        }
    }

    unsafe extern "C" fn fake_next_state_writes_past_state_out(
        out: *mut JitCallOut,
        _state_in: *const i64,
        state_out: *mut i64,
        state_len: u32,
    ) {
        unsafe {
            *state_out.add(state_len as usize) = 99;
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 1;
        }
    }

    unsafe extern "C" fn fake_invariant_mutates_state_input(
        out: *mut JitCallOut,
        state: *const i64,
        _state_len: u32,
    ) {
        unsafe {
            *(state as *mut i64) = 99;
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 1;
        }
    }

    unsafe extern "C" fn fake_next_state_records_arena_lifecycle(
        out: *mut JitCallOut,
        state_in: *const i64,
        state_out: *mut i64,
        _state_len: u32,
    ) {
        CALLOUT_SELFTEST_ARENA_ACTION_CALLS.fetch_add(1, Ordering::SeqCst);
        record_callout_selftest_arena_entry();
        unsafe {
            *state_out = *state_in + 1;
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 1;
        }
    }

    unsafe extern "C" fn fake_state_constraint_errors_on_seven(
        out: *mut JitCallOut,
        state: *const i64,
        _state_len: u32,
    ) {
        unsafe {
            if *state == 7 {
                ACTION_OUTPUT_STATE_CONSTRAINT_HITS.fetch_add(1, Ordering::SeqCst);
                (*out).status = tla_jit_abi::JitStatus::RuntimeError;
                (*out).value = 0;
            } else {
                (*out).status = tla_jit_abi::JitStatus::Ok;
                (*out).value = 1;
            }
        }
    }

    unsafe extern "C" fn fake_state_constraint_false_on_seven(
        out: *mut JitCallOut,
        state: *const i64,
        _state_len: u32,
    ) {
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = i64::from(*state != 7);
        }
    }

    unsafe extern "C" fn fake_state_constraint_records_arena_lifecycle(
        out: *mut JitCallOut,
        _state: *const i64,
        _state_len: u32,
    ) {
        CALLOUT_SELFTEST_ARENA_CONSTRAINT_CALLS.fetch_add(1, Ordering::SeqCst);
        record_callout_selftest_arena_entry();
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 1;
        }
    }

    unsafe extern "C" fn fake_invariant_false_on_seven_records_hit(
        out: *mut JitCallOut,
        state: *const i64,
        _state_len: u32,
    ) {
        ACTION_OUTPUT_INVARIANT_CALLS.fetch_add(1, Ordering::SeqCst);
        unsafe {
            if *state == 7 {
                ACTION_OUTPUT_INVARIANT_HITS.fetch_add(1, Ordering::SeqCst);
            }
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = i64::from(*state != 7);
        }
    }

    unsafe extern "C" fn fake_invariant_records_arena_lifecycle(
        out: *mut JitCallOut,
        _state: *const i64,
        _state_len: u32,
    ) {
        CALLOUT_SELFTEST_ARENA_INVARIANT_CALLS.fetch_add(1, Ordering::SeqCst);
        record_callout_selftest_arena_entry();
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 1;
        }
    }

    unsafe extern "C" fn fake_invariant_true(
        out: *mut JitCallOut,
        _state: *const i64,
        _state_len: u32,
    ) {
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 1;
        }
    }

    unsafe extern "C" fn fake_invariant_false(
        out: *mut JitCallOut,
        _state: *const i64,
        _state_len: u32,
    ) {
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 0;
        }
    }

    unsafe extern "C" fn fake_invariant_noncanonical_true(
        out: *mut JitCallOut,
        _state: *const i64,
        _state_len: u32,
    ) {
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = 2;
        }
    }

    unsafe extern "C" fn fake_invariant_requires_len_two(
        out: *mut JitCallOut,
        _state: *const i64,
        state_len: u32,
    ) {
        unsafe {
            (*out).status = tla_jit_abi::JitStatus::Ok;
            (*out).value = i64::from(state_len == 2);
        }
    }

    unsafe extern "C" fn fake_native_fused_level(
        parents: *const tla_llvm2::Llvm2BfsParentArenaAbi,
        successors: *mut tla_llvm2::Llvm2BfsSuccessorArenaAbi,
    ) -> u32 {
        unsafe {
            let parents = &*parents;
            let successors = &mut *successors;
            if parents.abi_version != tla_llvm2::LLVM2_BFS_LEVEL_ABI_VERSION
                || successors.abi_version != tla_llvm2::LLVM2_BFS_LEVEL_ABI_VERSION
                || parents.state_len != successors.state_len
                || successors.state_capacity < parents.parent_count
                || (parents.parent_count > 0
                    && (successors.parent_index.is_null() || successors.fingerprints.is_null()))
                || (parents.parent_count > 0
                    && parents.state_len > 0
                    && (parents.parents.is_null() || successors.states.is_null()))
            {
                successors.status = tla_llvm2::Llvm2BfsLevelStatus::InvalidAbi.as_raw();
                return successors.status;
            }

            let state_len = parents.state_len as usize;
            for parent_idx in 0..parents.parent_count as usize {
                let parent_start = parent_idx * state_len;
                let successor_start = parent_idx * state_len;
                for slot in 0..state_len {
                    *successors.states.add(successor_start + slot) =
                        *parents.parents.add(parent_start + slot) + 10;
                }
                *successors.parent_index.add(parent_idx) = parent_idx as u32;
                let fingerprint = if state_len == 0 {
                    tla_jit_runtime::tla2_compiled_fp_u64(std::ptr::null(), 0)
                } else {
                    let byte_len = state_len * std::mem::size_of::<i64>();
                    tla_jit_runtime::tla2_compiled_fp_u64(
                        successors.states.add(successor_start).cast::<u8>(),
                        byte_len,
                    )
                };
                *successors.fingerprints.add(parent_idx) = fingerprint;
            }
            successors.state_count = parents.parent_count;
            successors.generated = parents.parent_count as u64;
            successors.parents_processed = parents.parent_count;
            successors.invariant_ok = 1;
            successors.status = tla_llvm2::Llvm2BfsLevelStatus::Ok.as_raw();
            successors.status
        }
    }

    unsafe extern "C" fn fake_native_fused_fallback_level(
        _parents: *const tla_llvm2::Llvm2BfsParentArenaAbi,
        successors: *mut tla_llvm2::Llvm2BfsSuccessorArenaAbi,
    ) -> u32 {
        unsafe {
            let successors = &mut *successors;
            successors.status = tla_llvm2::Llvm2BfsLevelStatus::FallbackNeeded.as_raw();
            successors.status
        }
    }

    unsafe extern "C" fn fake_native_fused_runtime_error_level(
        _parents: *const tla_llvm2::Llvm2BfsParentArenaAbi,
        successors: *mut tla_llvm2::Llvm2BfsSuccessorArenaAbi,
    ) -> u32 {
        unsafe {
            let successors = &mut *successors;
            successors.status = tla_llvm2::Llvm2BfsLevelStatus::RuntimeError.as_raw();
            successors.status
        }
    }

    unsafe extern "C" fn fake_native_fused_invalid_abi_level(
        _parents: *const tla_llvm2::Llvm2BfsParentArenaAbi,
        successors: *mut tla_llvm2::Llvm2BfsSuccessorArenaAbi,
    ) -> u32 {
        unsafe {
            let successors = &mut *successors;
            successors.status = tla_llvm2::Llvm2BfsLevelStatus::InvalidAbi.as_raw();
            successors.status
        }
    }

    unsafe extern "C" fn fake_native_fused_buffer_overflow_level(
        _parents: *const tla_llvm2::Llvm2BfsParentArenaAbi,
        successors: *mut tla_llvm2::Llvm2BfsSuccessorArenaAbi,
    ) -> u32 {
        unsafe {
            let successors = &mut *successors;
            successors.state_count = 1;
            successors.generated = 1;
            successors.status = tla_llvm2::Llvm2BfsLevelStatus::BufferOverflow.as_raw();
            successors.status
        }
    }

    fn minimal_module() -> tla_core::ast::Module {
        parse_module(
            r#"
---- MODULE Llvm2DispatchTest ----
EXTENDS Naturals

VARIABLE x

Step == x' = x
Init == x = 0
Next == Step
====
"#,
        )
    }

    #[cfg(feature = "llvm2")]
    fn resolve_module_state_vars(module: &mut tla_core::ast::Module, config: &Config) {
        let registry = {
            let checker = ModelChecker::new(module, config);
            checker.ctx.var_registry().clone()
        };

        for unit in &mut module.units {
            if let Unit::Operator(def) = &mut unit.node {
                tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
            }
        }
    }

    #[cfg(feature = "llvm2")]
    fn assert_single_invariant_compiles_native(
        mut module: tla_core::ast::Module,
        invariant_name: &str,
        layout: StateLayout,
    ) {
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec![invariant_name.to_string()],
            ..Default::default()
        };
        resolve_module_state_vars(&mut module, &config);

        let bytecode =
            tla_eval::bytecode_vm::compile_operators_to_bytecode(&module, &[], &config.invariants);
        assert!(
            bytecode.failed.is_empty(),
            "{invariant_name} should compile to bytecode without fallback: {:?}",
            bytecode.failed
        );
        let entry_idx = *bytecode
            .op_indices
            .get(invariant_name)
            .expect("invariant bytecode entry should be present");
        let invariant_func = bytecode.chunk.get_function(entry_idx);
        let invariant_bytecodes = vec![Some(invariant_func)];
        let actions: FxHashMap<String, &tla_tir::bytecode::BytecodeFunction> = FxHashMap::default();

        let (cache, stats) = Llvm2NativeCache::build(
            &actions,
            &invariant_bytecodes,
            &[],
            layout.var_count(),
            Some(&layout),
            tla_llvm2::OptLevel::O1,
            None,
            Some(&bytecode.chunk.constants),
            None,
            &[],
            None,
            Some(&bytecode.chunk),
            None,
        );

        assert_eq!(
            stats.invariants_compiled, 1,
            "{invariant_name} should compile through the native LLVM2 invariant path"
        );
        assert_eq!(
            stats.invariants_failed, 0,
            "{invariant_name} should not fall back during native invariant compilation"
        );
        assert_eq!(cache.invariant_count(), 1);
        assert!(
            cache
                .resolve_native_invariants_ordered(&[invariant_name.to_string()])
                .is_some(),
            "{invariant_name} should expose a native invariant entry for fused LLVM2 dispatch"
        );
    }

    #[test]
    fn test_eval_action_prefills_successor_buffer_for_partial_writes() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Partial".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: 2,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        let state_in = vec![41, 99];
        let result = cache
            .eval_action("Partial", &state_in)
            .expect("action should be compiled")
            .expect("native dispatch should succeed");

        match result {
            Llvm2ActionResult::Enabled {
                successor,
                jit_input,
            } => {
                assert_eq!(
                    successor,
                    vec![123, 99],
                    "untouched slots must preserve the predecessor state"
                );
                assert_eq!(jit_input, state_in);
            }
            Llvm2ActionResult::Disabled => panic!("fake action should be enabled"),
        }
    }

    #[test]
    fn test_eval_action_with_state_len_accepts_compound_tail_buffer() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Partial".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: 2,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        let state_in = vec![41, 99, 777];
        let result = cache
            .eval_action_with_state_len("Partial", &state_in, 2)
            .expect("action should be compiled")
            .expect("native dispatch should accept tail slots");

        match result {
            Llvm2ActionResult::Enabled {
                successor,
                jit_input,
            } => {
                assert_eq!(successor, vec![123, 99, 777]);
                assert_eq!(jit_input, state_in);
            }
            Llvm2ActionResult::Disabled => panic!("fake action should be enabled"),
        }
    }

    #[test]
    fn test_eval_action_with_state_len_rejects_short_buffer() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Partial".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: 2,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        assert!(
            matches!(
                cache.eval_action_with_state_len("Partial", &[41], 2),
                Some(Err(()))
            ),
            "short explicit state buffer must be rejected before native dispatch"
        );
    }

    #[test]
    fn test_eval_action_rejects_noncanonical_boolean_return() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Noncanonical".to_string(),
            fake_next_state_noncanonical_true as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        assert!(
            matches!(cache.eval_action("Noncanonical", &[41]), Some(Err(()))),
            "direct LLVM2 action eval must reject Ok(value=2), not treat it as true"
        );
    }

    #[cfg(feature = "llvm2")]
    struct EnvVarGuard {
        key: &'static str,
        previous: Option<std::ffi::OsString>,
    }

    #[cfg(feature = "llvm2")]
    impl EnvVarGuard {
        fn set(key: &'static str, value: &str) -> Self {
            let previous = std::env::var_os(key);
            unsafe {
                std::env::set_var(key, value);
            }
            Self { key, previous }
        }

        fn unset(key: &'static str) -> Self {
            let previous = std::env::var_os(key);
            unsafe {
                std::env::remove_var(key);
            }
            Self { key, previous }
        }
    }

    #[cfg(feature = "llvm2")]
    impl Drop for EnvVarGuard {
        fn drop(&mut self) {
            unsafe {
                if let Some(previous) = &self.previous {
                    std::env::set_var(self.key, previous);
                } else {
                    std::env::remove_var(self.key);
                }
            }
        }
    }

    #[cfg(feature = "llvm2")]
    fn llvm2_dispatch_env_lock() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
            .lock()
            .expect("llvm2 dispatch env lock poisoned")
    }

    #[cfg(feature = "llvm2")]
    fn mcl_request_1_1_native_fixture() -> (tla_tir::bytecode::BytecodeChunk, u16, StateLayout) {
        use tla_tir::bytecode::{BuiltinOp, BytecodeChunk, BytecodeFunction, Opcode};

        let mut chunk = BytecodeChunk::new();
        let fields_start = chunk.constants.add_value(Value::String("type".into()));
        chunk.constants.add_value(Value::String("clock".into()));
        let req_const_idx = chunk.constants.add_value(Value::String("req".into()));
        let unchanged_start = chunk.constants.add_value(Value::SmallInt(1));
        chunk.constants.add_value(Value::SmallInt(2));

        let mut req_message = BytecodeFunction::new("ReqMessage".to_string(), 1);
        req_message.emit(Opcode::LoadConst {
            rd: 1,
            idx: req_const_idx,
        });
        req_message.emit(Opcode::Move { rd: 2, rs: 0 });
        req_message.emit(Opcode::RecordNew {
            rd: 3,
            fields_start,
            values_start: 1,
            count: 2,
        });
        req_message.emit(Opcode::Ret { rs: 3 });
        let req_message_idx = chunk.add_function(req_message);

        let mut broadcast = BytecodeFunction::new("Broadcast".to_string(), 2);
        broadcast.emit(Opcode::LoadVar { rd: 2, var_idx: 3 });
        broadcast.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 0,
        });
        broadcast.emit(Opcode::LoadImm { rd: 4, value: 1 });
        broadcast.emit(Opcode::LoadImm { rd: 5, value: 3 });
        broadcast.emit(Opcode::Range {
            rd: 6,
            lo: 4,
            hi: 5,
        });
        let begin_pc = broadcast.emit(Opcode::FuncDefBegin {
            rd: 7,
            r_binding: 8,
            r_domain: 6,
            loop_end: 0,
        });
        broadcast.emit(Opcode::FuncApply {
            rd: 9,
            func: 3,
            arg: 8,
        });
        broadcast.emit(Opcode::Move { rd: 10, rs: 1 });
        broadcast.emit(Opcode::CallBuiltin {
            rd: 11,
            builtin: BuiltinOp::Append,
            args_start: 9,
            argc: 2,
        });
        broadcast.emit(Opcode::Eq {
            rd: 12,
            r1: 0,
            r2: 8,
        });
        broadcast.emit(Opcode::CondMove {
            rd: 11,
            cond: 12,
            rs: 9,
        });
        let next_pc = broadcast.emit(Opcode::LoopNext {
            r_binding: 8,
            r_body: 11,
            loop_begin: 0,
        });
        broadcast.patch_jump(begin_pc, next_pc + 1);
        broadcast.patch_jump(next_pc, begin_pc + 1);
        broadcast.emit(Opcode::Ret { rs: 7 });
        let broadcast_idx = chunk.add_function(broadcast);

        let mut entry = BytecodeFunction::new("Request__1_1".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadVar { rd: 1, var_idx: 4 });
        entry.emit(Opcode::FuncApply {
            rd: 2,
            func: 1,
            arg: 0,
        });
        entry.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 4, value: 0 });
        entry.emit(Opcode::Eq {
            rd: 5,
            r1: 3,
            r2: 4,
        });
        let guard_false = entry.emit(Opcode::JumpFalse { rs: 5, offset: 0 });
        entry.emit(Opcode::LoadVar { rd: 6, var_idx: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 7,
            func: 6,
            arg: 0,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 8,
            func: 2,
            path: 0,
            val: 7,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 9,
            func: 1,
            path: 0,
            val: 8,
        });
        entry.emit(Opcode::StoreVar { var_idx: 4, rs: 9 });
        entry.emit(Opcode::Move { rd: 10, rs: 7 });
        entry.emit(Opcode::Call {
            rd: 11,
            op_idx: req_message_idx,
            args_start: 10,
            argc: 1,
        });
        entry.emit(Opcode::Move { rd: 12, rs: 0 });
        entry.emit(Opcode::Move { rd: 13, rs: 11 });
        entry.emit(Opcode::Call {
            rd: 14,
            op_idx: broadcast_idx,
            args_start: 12,
            argc: 2,
        });
        entry.emit(Opcode::LoadVar { rd: 15, var_idx: 3 });
        entry.emit(Opcode::FuncExcept {
            rd: 16,
            func: 15,
            path: 0,
            val: 14,
        });
        entry.emit(Opcode::StoreVar { var_idx: 3, rs: 16 });
        entry.emit(Opcode::LoadVar { rd: 17, var_idx: 0 });
        entry.emit(Opcode::SetEnum {
            rd: 18,
            start: 0,
            count: 1,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 19,
            func: 17,
            path: 0,
            val: 18,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 19 });
        entry.emit(Opcode::Unchanged {
            rd: 20,
            start: unchanged_start,
            count: 2,
        });
        entry.emit(Opcode::Ret { rs: 20 });
        let guard_false_pc = entry.emit(Opcode::LoadBool {
            rd: 21,
            value: false,
        });
        entry.emit(Opcode::Ret { rs: 21 });
        entry.patch_jump(guard_false, guard_false_pc);
        let entry_idx = chunk.add_function(entry);

        let proc_set_bitmask = || CompoundLayout::SetBitmask {
            universe: vec![
                tla_jit_abi::SetBitmaskElement::Int(1),
                tla_jit_abi::SetBitmaskElement::Int(2),
                tla_jit_abi::SetBitmaskElement::Int(3),
            ],
        };
        let proc_int_sequence = || CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        };
        let req_layout = CompoundLayout::Sequence {
            element_layout: Box::new(proc_int_sequence()),
            element_count: Some(3),
        };
        let ack_layout = CompoundLayout::Sequence {
            element_layout: Box::new(proc_set_bitmask()),
            element_count: Some(3),
        };
        let message_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("clock"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let channel_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(message_layout()),
            element_count: Some(3),
        };
        let row_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(channel_layout()),
            element_count: Some(3),
        };
        let network_layout = CompoundLayout::Sequence {
            element_layout: Box::new(row_layout()),
            element_count: Some(3),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(ack_layout),
            VarLayout::Compound(proc_int_sequence()),
            VarLayout::Compound(proc_set_bitmask()),
            VarLayout::Compound(network_layout),
            VarLayout::Compound(req_layout),
        ]);

        (chunk, entry_idx, layout)
    }

    #[cfg(feature = "llvm2")]
    fn mcl_typeok_native_module() -> tla_core::ast::Module {
        parse_module(
            r#"
---- MODULE Llvm2MclFullTypeOkNativeCanary ----
EXTENDS Sequences

Proc == 1..3
NatOverride == 0..7
Clock == NatOverride \ {0}

VARIABLE ack, clock, crit, network, req

AckMessage == [clock |-> 0, type |-> "ack"]
RelMessage == [clock |-> 0, type |-> "rel"]
ReqMessage(c) == [clock |-> c, type |-> "req"]
Message == {AckMessage, RelMessage, ReqMessage(1), ReqMessage(2), ReqMessage(3),
            ReqMessage(4), ReqMessage(5), ReqMessage(6), ReqMessage(7)}

Init == /\ ack = <<{}, {}, {}>>
        /\ clock = <<1, 1, 1>>
        /\ crit = {}
        /\ network = << <<<<>>, <<>>, <<>>>>,
                       <<<<>>, <<>>, <<>>>>,
                       <<<<>>, <<>>, <<>>>> >>
        /\ req = << <<0, 0, 0>>, <<0, 0, 0>>, <<0, 0, 0>> >>

Next == /\ ack' = ack
        /\ clock' = clock
        /\ crit' = crit
        /\ network' = network
        /\ req' = req

ClockLookup1OK == clock[1] = 1
ProcQuantifierValuesOK == \A p \in Proc : p \in 1..3
ProcInlineQuantifierValuesOK == \A p \in 1..3 : p \in 1..3
ClockInNatOverride == \A p \in Proc : clock[p] \in NatOverride
ClockInNatOverrideInlineProc == \A p \in 1..3 : clock[p] \in NatOverride
ClockInInlineNatOverride == \A p \in Proc : clock[p] \in 0..7
ClockInFullyInlineRange == \A p \in 1..3 : clock[p] \in 0..7
ClockNonZero == \A p \in Proc : clock[p] # 0
ClockInClock1 == clock[1] \in Clock
ClockTypeOK == \A p \in Proc : clock[p] \in Clock
ReqTypeOK == \A p \in Proc : \A q \in Proc : req[p][q] \in NatOverride
AckTypeOK == \A p \in Proc : ack[p] \in SUBSET Proc
NetworkTypeOK == \A p \in Proc : \A q \in Proc : network[p][q] \in Seq(Message)
CritTypeOK == crit \in SUBSET Proc

TypeOK == /\ ClockTypeOK
          /\ ReqTypeOK
          /\ AckTypeOK
          /\ NetworkTypeOK
          /\ CritTypeOK
====
"#,
        )
    }

    #[cfg(feature = "llvm2")]
    fn clear_tla_runtime_arenas_for_native_canary() {
        tla_llvm2::runtime_abi::tla_ops::clear_tla_iter_arena();
        tla_llvm2::runtime_abi::tla_ops::clear_tla_arena();
    }

    #[cfg(feature = "llvm2")]
    fn mcl_receive_request_1_2_native_fixture(
    ) -> (tla_tir::bytecode::BytecodeChunk, u16, StateLayout) {
        use tla_tir::bytecode::{BuiltinOp, BytecodeChunk, BytecodeFunction, Opcode};

        let mut chunk = BytecodeChunk::new();
        let req_const_idx = chunk.constants.add_value(Value::String("req".into()));
        let ack_message_idx = chunk.constants.add_value(Value::record([
            ("clock", Value::SmallInt(0)),
            ("type", Value::String("ack".into())),
        ]));
        let unchanged_start = chunk.constants.add_value(Value::SmallInt(0));
        chunk.constants.add_value(Value::SmallInt(2));

        let mut entry = BytecodeFunction::new("ReceiveRequest__1_2_1_2".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::LoadVar { rd: 2, var_idx: 3 });
        entry.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 1,
        });
        entry.emit(Opcode::FuncApply {
            rd: 4,
            func: 3,
            arg: 0,
        });
        entry.emit(Opcode::TupleNew {
            rd: 5,
            start: 5,
            count: 0,
        });
        entry.emit(Opcode::Neq {
            rd: 6,
            r1: 4,
            r2: 5,
        });
        entry.emit(Opcode::Move { rd: 7, rs: 6 });
        entry.emit(Opcode::JumpFalse { rs: 7, offset: 64 });
        entry.emit(Opcode::LoadVar { rd: 9, var_idx: 3 });
        entry.emit(Opcode::FuncApply {
            rd: 10,
            func: 9,
            arg: 1,
        });
        entry.emit(Opcode::FuncApply {
            rd: 11,
            func: 10,
            arg: 0,
        });
        entry.emit(Opcode::Move { rd: 8, rs: 11 });
        entry.emit(Opcode::CallBuiltin {
            rd: 12,
            builtin: BuiltinOp::Head,
            args_start: 8,
            argc: 1,
        });
        entry.emit(Opcode::RecordGet {
            rd: 13,
            rs: 12,
            field_idx: 0,
        });
        entry.emit(Opcode::RecordGet {
            rd: 14,
            rs: 12,
            field_idx: 1,
        });
        entry.emit(Opcode::LoadConst {
            rd: 15,
            idx: req_const_idx,
        });
        entry.emit(Opcode::Eq {
            rd: 16,
            r1: 14,
            r2: 15,
        });
        entry.emit(Opcode::Move { rd: 17, rs: 16 });
        entry.emit(Opcode::JumpFalse { rs: 17, offset: 9 });
        entry.emit(Opcode::LoadBool {
            rd: 24,
            value: true,
        });
        entry.emit(Opcode::LoadVar { rd: 19, var_idx: 4 });
        entry.emit(Opcode::FuncApply {
            rd: 20,
            func: 19,
            arg: 0,
        });
        entry.emit(Opcode::FuncApply {
            rd: 21,
            func: 20,
            arg: 1,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 22,
            func: 20,
            path: 1,
            val: 13,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 23,
            func: 19,
            path: 0,
            val: 22,
        });
        entry.emit(Opcode::StoreVar { var_idx: 4, rs: 23 });
        entry.emit(Opcode::Move { rd: 17, rs: 24 });
        entry.emit(Opcode::Move { rd: 25, rs: 17 });
        entry.emit(Opcode::JumpFalse { rs: 25, offset: 18 });
        entry.emit(Opcode::LoadBool {
            rd: 38,
            value: true,
        });
        entry.emit(Opcode::LoadVar { rd: 27, var_idx: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 28,
            func: 27,
            arg: 0,
        });
        entry.emit(Opcode::LoadVar { rd: 29, var_idx: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 30,
            func: 29,
            arg: 0,
        });
        entry.emit(Opcode::GtInt {
            rd: 31,
            r1: 13,
            r2: 30,
        });
        entry.emit(Opcode::JumpFalse { rs: 31, offset: 5 });
        entry.emit(Opcode::LoadImm { rd: 33, value: 1 });
        entry.emit(Opcode::AddInt {
            rd: 34,
            r1: 13,
            r2: 33,
        });
        entry.emit(Opcode::Move { rd: 32, rs: 34 });
        entry.emit(Opcode::Jump { offset: 4 });
        entry.emit(Opcode::LoadImm { rd: 35, value: 1 });
        entry.emit(Opcode::AddInt {
            rd: 36,
            r1: 28,
            r2: 35,
        });
        entry.emit(Opcode::Move { rd: 32, rs: 36 });
        entry.emit(Opcode::FuncExcept {
            rd: 37,
            func: 27,
            path: 0,
            val: 32,
        });
        entry.emit(Opcode::StoreVar { var_idx: 1, rs: 37 });
        entry.emit(Opcode::Move { rd: 25, rs: 38 });
        entry.emit(Opcode::Move { rd: 39, rs: 25 });
        entry.emit(Opcode::JumpFalse { rs: 39, offset: 19 });
        entry.emit(Opcode::LoadBool {
            rd: 56,
            value: true,
        });
        entry.emit(Opcode::LoadVar { rd: 41, var_idx: 3 });
        entry.emit(Opcode::FuncApply {
            rd: 42,
            func: 41,
            arg: 1,
        });
        entry.emit(Opcode::FuncApply {
            rd: 43,
            func: 42,
            arg: 0,
        });
        entry.emit(Opcode::Move { rd: 44, rs: 43 });
        entry.emit(Opcode::CallBuiltin {
            rd: 45,
            builtin: BuiltinOp::Tail,
            args_start: 44,
            argc: 1,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 46,
            func: 42,
            path: 0,
            val: 45,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 47,
            func: 41,
            path: 1,
            val: 46,
        });
        entry.emit(Opcode::FuncApply {
            rd: 48,
            func: 47,
            arg: 0,
        });
        entry.emit(Opcode::FuncApply {
            rd: 49,
            func: 48,
            arg: 1,
        });
        entry.emit(Opcode::Move { rd: 50, rs: 49 });
        entry.emit(Opcode::LoadConst {
            rd: 52,
            idx: ack_message_idx,
        });
        entry.emit(Opcode::Move { rd: 51, rs: 52 });
        entry.emit(Opcode::CallBuiltin {
            rd: 53,
            builtin: BuiltinOp::Append,
            args_start: 50,
            argc: 2,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 54,
            func: 48,
            path: 1,
            val: 53,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 55,
            func: 47,
            path: 0,
            val: 54,
        });
        entry.emit(Opcode::StoreVar { var_idx: 3, rs: 55 });
        entry.emit(Opcode::Move { rd: 39, rs: 56 });
        entry.emit(Opcode::Move { rd: 57, rs: 39 });
        entry.emit(Opcode::JumpFalse { rs: 57, offset: 3 });
        entry.emit(Opcode::Unchanged {
            rd: 58,
            start: unchanged_start,
            count: 2,
        });
        entry.emit(Opcode::Move { rd: 57, rs: 58 });
        entry.emit(Opcode::Move { rd: 7, rs: 57 });
        entry.emit(Opcode::Move { rd: 0, rs: 7 });
        entry.emit(Opcode::Ret { rs: 0 });
        let entry_idx = chunk.add_function(entry);

        let (_, _, layout) = mcl_request_1_1_native_fixture();
        (chunk, entry_idx, layout)
    }

    #[cfg(feature = "llvm2")]
    fn mcl_receive_ack_1_2_native_fixture() -> (tla_tir::bytecode::BytecodeChunk, u16, StateLayout)
    {
        use tla_tir::bytecode::{BuiltinOp, BytecodeChunk, BytecodeFunction, Opcode};

        let mut chunk = BytecodeChunk::new();
        let ack_const_idx = chunk.constants.add_value(Value::String("ack".into()));
        let unchanged_start = chunk.constants.add_value(Value::SmallInt(1));
        chunk.constants.add_value(Value::SmallInt(4));
        chunk.constants.add_value(Value::SmallInt(2));

        let mut entry = BytecodeFunction::new("ReceiveAck__1_2_1_2".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::LoadVar { rd: 2, var_idx: 3 });
        entry.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 1,
        });
        entry.emit(Opcode::FuncApply {
            rd: 4,
            func: 3,
            arg: 0,
        });
        entry.emit(Opcode::TupleNew {
            rd: 5,
            start: 5,
            count: 0,
        });
        entry.emit(Opcode::Neq {
            rd: 6,
            r1: 4,
            r2: 5,
        });
        let empty_guard_false = entry.emit(Opcode::JumpFalse { rs: 6, offset: 0 });
        entry.emit(Opcode::Move { rd: 7, rs: 4 });
        entry.emit(Opcode::CallBuiltin {
            rd: 8,
            builtin: BuiltinOp::Head,
            args_start: 7,
            argc: 1,
        });
        entry.emit(Opcode::RecordGet {
            rd: 9,
            rs: 8,
            field_idx: 1,
        });
        entry.emit(Opcode::LoadConst {
            rd: 10,
            idx: ack_const_idx,
        });
        entry.emit(Opcode::Eq {
            rd: 11,
            r1: 9,
            r2: 10,
        });
        let type_guard_false = entry.emit(Opcode::JumpFalse { rs: 11, offset: 0 });
        entry.emit(Opcode::LoadVar { rd: 12, var_idx: 0 });
        entry.emit(Opcode::FuncApply {
            rd: 13,
            func: 12,
            arg: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 14, value: 2 });
        entry.emit(Opcode::SetEnum {
            rd: 15,
            start: 14,
            count: 1,
        });
        entry.emit(Opcode::SetUnion {
            rd: 16,
            r1: 13,
            r2: 15,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 17,
            func: 12,
            path: 0,
            val: 16,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 17 });
        entry.emit(Opcode::LoadVar { rd: 18, var_idx: 3 });
        entry.emit(Opcode::FuncApply {
            rd: 19,
            func: 18,
            arg: 1,
        });
        entry.emit(Opcode::FuncApply {
            rd: 20,
            func: 19,
            arg: 0,
        });
        entry.emit(Opcode::Move { rd: 21, rs: 20 });
        entry.emit(Opcode::CallBuiltin {
            rd: 22,
            builtin: BuiltinOp::Tail,
            args_start: 21,
            argc: 1,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 23,
            func: 19,
            path: 0,
            val: 22,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 24,
            func: 18,
            path: 1,
            val: 23,
        });
        entry.emit(Opcode::StoreVar { var_idx: 3, rs: 24 });
        entry.emit(Opcode::Unchanged {
            rd: 25,
            start: unchanged_start,
            count: 3,
        });
        entry.emit(Opcode::Ret { rs: 25 });
        let guard_false_pc = entry.emit(Opcode::LoadBool {
            rd: 26,
            value: false,
        });
        entry.emit(Opcode::Ret { rs: 26 });
        entry.patch_jump(empty_guard_false, guard_false_pc);
        entry.patch_jump(type_guard_false, guard_false_pc);
        let entry_idx = chunk.add_function(entry);

        let (_, _, layout) = mcl_request_1_1_native_fixture();
        (chunk, entry_idx, layout)
    }

    #[cfg(feature = "llvm2")]
    fn mcl_receive_release_1_2_native_fixture(
    ) -> (tla_tir::bytecode::BytecodeChunk, u16, StateLayout) {
        use tla_tir::bytecode::{BuiltinOp, BytecodeChunk, BytecodeFunction, Opcode};

        let mut chunk = BytecodeChunk::new();
        let rel_const_idx = chunk.constants.add_value(Value::String("rel".into()));
        let unchanged_start = chunk.constants.add_value(Value::SmallInt(1));
        chunk.constants.add_value(Value::SmallInt(0));
        chunk.constants.add_value(Value::SmallInt(2));

        let mut entry = BytecodeFunction::new("ReceiveRelease__1_2_1_2".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::LoadVar { rd: 2, var_idx: 3 });
        entry.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 1,
        });
        entry.emit(Opcode::FuncApply {
            rd: 4,
            func: 3,
            arg: 0,
        });
        entry.emit(Opcode::TupleNew {
            rd: 5,
            start: 5,
            count: 0,
        });
        entry.emit(Opcode::Neq {
            rd: 6,
            r1: 4,
            r2: 5,
        });
        let empty_guard_false = entry.emit(Opcode::JumpFalse { rs: 6, offset: 0 });
        entry.emit(Opcode::Move { rd: 7, rs: 4 });
        entry.emit(Opcode::CallBuiltin {
            rd: 8,
            builtin: BuiltinOp::Head,
            args_start: 7,
            argc: 1,
        });
        entry.emit(Opcode::RecordGet {
            rd: 9,
            rs: 8,
            field_idx: 1,
        });
        entry.emit(Opcode::LoadConst {
            rd: 10,
            idx: rel_const_idx,
        });
        entry.emit(Opcode::Eq {
            rd: 11,
            r1: 9,
            r2: 10,
        });
        let type_guard_false = entry.emit(Opcode::JumpFalse { rs: 11, offset: 0 });
        entry.emit(Opcode::LoadVar { rd: 12, var_idx: 4 });
        entry.emit(Opcode::FuncApply {
            rd: 13,
            func: 12,
            arg: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 14, value: 0 });
        entry.emit(Opcode::FuncExcept {
            rd: 15,
            func: 13,
            path: 1,
            val: 14,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 16,
            func: 12,
            path: 0,
            val: 15,
        });
        entry.emit(Opcode::StoreVar { var_idx: 4, rs: 16 });
        entry.emit(Opcode::LoadVar { rd: 17, var_idx: 3 });
        entry.emit(Opcode::FuncApply {
            rd: 18,
            func: 17,
            arg: 1,
        });
        entry.emit(Opcode::FuncApply {
            rd: 19,
            func: 18,
            arg: 0,
        });
        entry.emit(Opcode::Move { rd: 20, rs: 19 });
        entry.emit(Opcode::CallBuiltin {
            rd: 21,
            builtin: BuiltinOp::Tail,
            args_start: 20,
            argc: 1,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 22,
            func: 18,
            path: 0,
            val: 21,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 23,
            func: 17,
            path: 1,
            val: 22,
        });
        entry.emit(Opcode::StoreVar { var_idx: 3, rs: 23 });
        entry.emit(Opcode::Unchanged {
            rd: 24,
            start: unchanged_start,
            count: 3,
        });
        entry.emit(Opcode::Ret { rs: 24 });
        let guard_false_pc = entry.emit(Opcode::LoadBool {
            rd: 25,
            value: false,
        });
        entry.emit(Opcode::Ret { rs: 25 });
        entry.patch_jump(empty_guard_false, guard_false_pc);
        entry.patch_jump(type_guard_false, guard_false_pc);
        let entry_idx = chunk.add_function(entry);

        let (_, _, layout) = mcl_request_1_1_native_fixture();
        (chunk, entry_idx, layout)
    }

    #[cfg(feature = "llvm2")]
    fn mcl_enter_1_1_native_fixture() -> (tla_tir::bytecode::BytecodeChunk, u16, StateLayout) {
        use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};

        let mut chunk = BytecodeChunk::new();
        let unchanged_start = chunk.constants.add_value(Value::SmallInt(1));
        chunk.constants.add_value(Value::SmallInt(4));
        chunk.constants.add_value(Value::SmallInt(0));
        chunk.constants.add_value(Value::SmallInt(3));

        let mut entry = BytecodeFunction::new("Enter__1_1".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::LoadImm { rd: 2, value: 3 });
        entry.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        entry.emit(Opcode::LoadVar { rd: 4, var_idx: 0 });
        entry.emit(Opcode::FuncApply {
            rd: 5,
            func: 4,
            arg: 0,
        });
        entry.emit(Opcode::Eq {
            rd: 6,
            r1: 5,
            r2: 3,
        });
        let ack_guard_false = entry.emit(Opcode::JumpFalse { rs: 6, offset: 0 });
        entry.emit(Opcode::LoadVar { rd: 7, var_idx: 4 });
        entry.emit(Opcode::FuncApply {
            rd: 8,
            func: 7,
            arg: 0,
        });
        entry.emit(Opcode::FuncApply {
            rd: 9,
            func: 8,
            arg: 0,
        });
        entry.emit(Opcode::FuncApply {
            rd: 10,
            func: 8,
            arg: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 11, value: 0 });
        entry.emit(Opcode::Eq {
            rd: 12,
            r1: 10,
            r2: 11,
        });
        entry.emit(Opcode::LtInt {
            rd: 13,
            r1: 9,
            r2: 10,
        });
        entry.emit(Opcode::Eq {
            rd: 14,
            r1: 9,
            r2: 10,
        });
        entry.emit(Opcode::LtInt {
            rd: 15,
            r1: 0,
            r2: 1,
        });
        entry.emit(Opcode::And {
            rd: 16,
            r1: 14,
            r2: 15,
        });
        entry.emit(Opcode::Or {
            rd: 17,
            r1: 13,
            r2: 16,
        });
        entry.emit(Opcode::Or {
            rd: 18,
            r1: 12,
            r2: 17,
        });
        let beats_2_false = entry.emit(Opcode::JumpFalse { rs: 18, offset: 0 });
        entry.emit(Opcode::FuncApply {
            rd: 19,
            func: 8,
            arg: 2,
        });
        entry.emit(Opcode::Eq {
            rd: 20,
            r1: 19,
            r2: 11,
        });
        entry.emit(Opcode::LtInt {
            rd: 21,
            r1: 9,
            r2: 19,
        });
        entry.emit(Opcode::Eq {
            rd: 22,
            r1: 9,
            r2: 19,
        });
        entry.emit(Opcode::LtInt {
            rd: 23,
            r1: 0,
            r2: 2,
        });
        entry.emit(Opcode::And {
            rd: 24,
            r1: 22,
            r2: 23,
        });
        entry.emit(Opcode::Or {
            rd: 25,
            r1: 21,
            r2: 24,
        });
        entry.emit(Opcode::Or {
            rd: 26,
            r1: 20,
            r2: 25,
        });
        let beats_3_false = entry.emit(Opcode::JumpFalse { rs: 26, offset: 0 });
        entry.emit(Opcode::LoadVar { rd: 27, var_idx: 2 });
        entry.emit(Opcode::SetEnum {
            rd: 28,
            start: 0,
            count: 1,
        });
        entry.emit(Opcode::SetUnion {
            rd: 29,
            r1: 27,
            r2: 28,
        });
        entry.emit(Opcode::StoreVar { var_idx: 2, rs: 29 });
        entry.emit(Opcode::Unchanged {
            rd: 30,
            start: unchanged_start,
            count: 4,
        });
        entry.emit(Opcode::Ret { rs: 30 });
        let guard_false_pc = entry.emit(Opcode::LoadBool {
            rd: 31,
            value: false,
        });
        entry.emit(Opcode::Ret { rs: 31 });
        entry.patch_jump(ack_guard_false, guard_false_pc);
        entry.patch_jump(beats_2_false, guard_false_pc);
        entry.patch_jump(beats_3_false, guard_false_pc);
        let entry_idx = chunk.add_function(entry);

        let (_, _, layout) = mcl_request_1_1_native_fixture();
        (chunk, entry_idx, layout)
    }

    #[cfg(feature = "llvm2")]
    fn mcl_exit_1_1_native_fixture() -> (tla_tir::bytecode::BytecodeChunk, u16, StateLayout) {
        use tla_tir::bytecode::{BuiltinOp, BytecodeChunk, BytecodeFunction, Opcode};

        let mut chunk = BytecodeChunk::new();
        let rel_message_idx = chunk.constants.add_value(Value::record([
            ("clock", Value::SmallInt(0)),
            ("type", Value::String("rel".into())),
        ]));
        let unchanged_start = chunk.constants.add_value(Value::SmallInt(1));

        let mut broadcast = BytecodeFunction::new("Broadcast".to_string(), 2);
        broadcast.emit(Opcode::LoadVar { rd: 2, var_idx: 3 });
        broadcast.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 0,
        });
        broadcast.emit(Opcode::LoadImm { rd: 4, value: 1 });
        broadcast.emit(Opcode::LoadImm { rd: 5, value: 3 });
        broadcast.emit(Opcode::Range {
            rd: 6,
            lo: 4,
            hi: 5,
        });
        let begin_pc = broadcast.emit(Opcode::FuncDefBegin {
            rd: 7,
            r_binding: 8,
            r_domain: 6,
            loop_end: 0,
        });
        broadcast.emit(Opcode::FuncApply {
            rd: 9,
            func: 3,
            arg: 8,
        });
        broadcast.emit(Opcode::Move { rd: 10, rs: 1 });
        broadcast.emit(Opcode::CallBuiltin {
            rd: 11,
            builtin: BuiltinOp::Append,
            args_start: 9,
            argc: 2,
        });
        broadcast.emit(Opcode::Eq {
            rd: 12,
            r1: 0,
            r2: 8,
        });
        broadcast.emit(Opcode::CondMove {
            rd: 11,
            cond: 12,
            rs: 9,
        });
        let next_pc = broadcast.emit(Opcode::LoopNext {
            r_binding: 8,
            r_body: 11,
            loop_begin: 0,
        });
        broadcast.patch_jump(begin_pc, next_pc + 1);
        broadcast.patch_jump(next_pc, begin_pc + 1);
        broadcast.emit(Opcode::Ret { rs: 7 });
        let broadcast_idx = chunk.add_function(broadcast);

        let mut entry = BytecodeFunction::new("Exit__1_1".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadVar { rd: 1, var_idx: 2 });
        entry.emit(Opcode::SetIn {
            rd: 2,
            elem: 0,
            set: 1,
        });
        let guard_false = entry.emit(Opcode::JumpFalse { rs: 2, offset: 0 });
        entry.emit(Opcode::LoadVar { rd: 3, var_idx: 2 });
        entry.emit(Opcode::Move { rd: 4, rs: 0 });
        entry.emit(Opcode::SetEnum {
            rd: 5,
            start: 4,
            count: 1,
        });
        entry.emit(Opcode::SetDiff {
            rd: 6,
            r1: 3,
            r2: 5,
        });
        entry.emit(Opcode::StoreVar { var_idx: 2, rs: 6 });
        entry.emit(Opcode::LoadVar { rd: 7, var_idx: 3 });
        entry.emit(Opcode::Move { rd: 8, rs: 0 });
        entry.emit(Opcode::LoadConst {
            rd: 9,
            idx: rel_message_idx,
        });
        entry.emit(Opcode::Move { rd: 10, rs: 9 });
        entry.emit(Opcode::Call {
            rd: 11,
            op_idx: broadcast_idx,
            args_start: 8,
            argc: 2,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 12,
            func: 7,
            path: 0,
            val: 11,
        });
        entry.emit(Opcode::StoreVar { var_idx: 3, rs: 12 });
        entry.emit(Opcode::LoadVar { rd: 13, var_idx: 4 });
        entry.emit(Opcode::FuncApply {
            rd: 14,
            func: 13,
            arg: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 15, value: 0 });
        entry.emit(Opcode::FuncExcept {
            rd: 16,
            func: 14,
            path: 0,
            val: 15,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 17,
            func: 13,
            path: 0,
            val: 16,
        });
        entry.emit(Opcode::StoreVar { var_idx: 4, rs: 17 });
        entry.emit(Opcode::LoadVar { rd: 18, var_idx: 0 });
        entry.emit(Opcode::SetEnum {
            rd: 19,
            start: 0,
            count: 0,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 20,
            func: 18,
            path: 0,
            val: 19,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 20 });
        entry.emit(Opcode::Unchanged {
            rd: 21,
            start: unchanged_start,
            count: 1,
        });
        entry.emit(Opcode::Ret { rs: 21 });
        let guard_false_pc = entry.emit(Opcode::LoadBool {
            rd: 22,
            value: false,
        });
        entry.emit(Opcode::Ret { rs: 22 });
        entry.patch_jump(guard_false, guard_false_pc);
        let entry_idx = chunk.add_function(entry);

        let (_, _, layout) = mcl_request_1_1_native_fixture();
        (chunk, entry_idx, layout)
    }

    #[cfg(feature = "llvm2")]
    fn mcl_bounded_network_native_fixture() -> (tla_tir::bytecode::BytecodeChunk, u16, StateLayout)
    {
        let mut module = parse_module(
            r#"
---- MODULE Llvm2MclBoundedNetworkNativeCanary ----
EXTENDS Naturals, Sequences

Proc == 1..3

VARIABLE ack, clock, crit, network, req

Init == /\ ack = <<{}, {}, {}>>
        /\ clock = <<1, 1, 1>>
        /\ crit = {}
        /\ network = << <<<<>>, <<>>, <<>>>>,
                       <<<<>>, <<>>, <<>>>>,
                       <<<<>>, <<>>, <<>>>> >>
        /\ req = << <<0, 0, 0>>, <<0, 0, 0>>, <<0, 0, 0>> >>

Next == /\ ack' = ack
        /\ clock' = clock
        /\ crit' = crit
        /\ network' = network
        /\ req' = req

BoundedNetwork == \A p \in Proc : \A q \in Proc : Len(network[p][q]) <= 3
====
"#,
        );
        let invariant_names = vec!["BoundedNetwork".to_string()];
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: invariant_names.clone(),
            ..Default::default()
        };
        resolve_module_state_vars(&mut module, &config);

        let bytecode =
            tla_eval::bytecode_vm::compile_operators_to_bytecode(&module, &[], &invariant_names);
        assert!(
            bytecode.failed.is_empty(),
            "BoundedNetwork should compile to bytecode without fallback: {:?}",
            bytecode.failed
        );
        let entry_idx = *bytecode
            .op_indices
            .get("BoundedNetwork")
            .expect("BoundedNetwork bytecode entry should be present");

        let (_, _, layout) = mcl_request_1_1_native_fixture();
        (bytecode.chunk, entry_idx, layout)
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_request_1_1_native_callout_returns_ok() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_request_1_1_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_ACK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + MCL_ACK_SLOT_COUNT;
        const MCL_CLOCK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + MCL_CLOCK_SLOT_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_MESSAGE_SLOT_COUNT: usize = 2;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_MESSAGE_SLOT_COUNT;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        const MCL_REQ_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_REQ_ROW_SLOT_COUNT;
        assert_eq!(MCL_ACK_OFFSET, 0);
        assert_eq!(MCL_CLOCK_OFFSET, 4);
        assert_eq!(MCL_CRIT_OFFSET, 8);
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);
        assert_eq!(MCL_REQ_OFFSET + MCL_REQ_SLOT_COUNT, state_len);

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 1;
        state_in[MCL_CLOCK_OFFSET + 2] = 1;
        state_in[MCL_CLOCK_OFFSET + 3] = 1;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }
        assert_eq!(
            &state_in[..16],
            &[3, 0, 0, 0, 3, 1, 1, 1, 0, 3, 3, 0, 0, 0, 0, 0],
            "fixture head should match the real MCL first-parent flat layout"
        );

        for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
            tla_llvm2::compile::clear_jit_cache();
            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling Request__1_1 at {opt_level:?}");
            let (func, _library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
                "Request__1_1",
                entry,
                Some(&layout),
                opt_level,
                None,
                Some(&chunk),
            )
            .expect("Request__1_1 should compile through the native LLVM2 action path");

            let mut state_out = state_in.clone();
            let mut out = native_fused_callout_sentinel();

            tla_llvm2::ensure_jit_execute_mode();
            eprintln!("[llvm2-canary] calling {symbol_name} at {opt_level:?}");
            // Mirror the strict native-fused selftest and parent-loop action boundary.
            Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
            unsafe {
                func(
                    &mut out,
                    state_in.as_ptr(),
                    state_out.as_mut_ptr(),
                    u32::try_from(state_len).expect("fixture state width should fit native ABI"),
                );
            }
            eprintln!("[llvm2-canary] returned {symbol_name} at {opt_level:?}: {out:?}");

            assert_eq!(
                out.status,
                tla_jit_abi::JitStatus::Ok,
                "native MCL {symbol_name} {opt_level:?} callout returned a bad status: {out:?}",
            );
            assert_eq!(
                out.value, 1,
                "native MCL {symbol_name} {opt_level:?} action should be enabled"
            );
            let channel_base = |from: usize, to: usize| {
                MCL_NETWORK_OFFSET
                    + 1
                    + (from - 1) * MCL_NETWORK_ROW_SLOT_COUNT
                    + 1
                    + (to - 1) * MCL_CHANNEL_SLOT_COUNT
            };
            let ack_slot = |proc: usize| MCL_ACK_OFFSET + proc;
            let req_slot = |proc: usize, from: usize| {
                MCL_REQ_OFFSET + 1 + (proc - 1) * MCL_REQ_ROW_SLOT_COUNT + from
            };
            let req_name_id = tla_core::intern_name("req").0 as i64;
            let self_channel_base = channel_base(1, 1);
            let changed_channels: Vec<_> = (1..=MCL_PROC_COUNT)
                .flat_map(|from| (1..=MCL_PROC_COUNT).map(move |to| (from, to)))
                .filter_map(|(from, to)| {
                    let base = channel_base(from, to);
                    let before = &state_in[base..base + MCL_CHANNEL_SLOT_COUNT];
                    let after = &state_out[base..base + MCL_CHANNEL_SLOT_COUNT];
                    (before != after).then_some((from, to, base, after.to_vec()))
                })
                .collect();
            eprintln!(
                "[llvm2-canary] {symbol_name} {opt_level:?} changed_channels={changed_channels:?}"
            );
            assert_eq!(
                &state_out[self_channel_base..self_channel_base + MCL_CHANNEL_SLOT_COUNT],
                &state_in[self_channel_base..self_channel_base + MCL_CHANNEL_SLOT_COUNT],
                "native MCL {symbol_name} {opt_level:?} should leave self-channel network[1][1] unchanged at compact slots {}..{}",
                self_channel_base,
                self_channel_base + MCL_CHANNEL_SLOT_COUNT,
            );
            let mut expected_state_out = state_in.clone();
            expected_state_out[ack_slot(1)] = 1;
            expected_state_out[req_slot(1, 1)] = 1;
            assert_eq!(
                state_out[ack_slot(1)],
                1,
                "native MCL {symbol_name} {opt_level:?} should set ack[1] compact bitmask slot {}",
                ack_slot(1),
            );
            assert_eq!(
                state_out[req_slot(1, 1)],
                1,
                "native MCL {symbol_name} {opt_level:?} should set req[1][1] compact slot {}",
                req_slot(1, 1),
            );
            for to in [2, 3] {
                let base = channel_base(1, to);
                expected_state_out[base] = 1;
                expected_state_out[base + 1] = 1;
                expected_state_out[base + 2] = req_name_id;
                assert_eq!(
                    state_out[base], 1,
                    "native MCL {symbol_name} {opt_level:?} should set network[1][{to}] compact length slot {base}"
                );
                assert_eq!(
                    state_out[base + 1],
                    1,
                    "native MCL {symbol_name} {opt_level:?} should set network[1][{to}][1].clock compact slot {}",
                    base + 1,
                );
                assert_eq!(
                    state_out[base + 2],
                    req_name_id,
                    "native MCL {symbol_name} {opt_level:?} should set network[1][{to}][1].type compact slot {}",
                    base + 2,
                );
            }
            assert_eq!(
                state_out[MCL_NETWORK_OFFSET - 1],
                state_in[MCL_NETWORK_OFFSET - 1],
                "native MCL {symbol_name} {opt_level:?} should leave the slot immediately before real network offset unchanged"
            );
            assert_eq!(
                state_out[MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT],
                state_in[MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT],
                "native MCL {symbol_name} {opt_level:?} should leave the req slot immediately after network unchanged"
            );
            assert_eq!(
                state_out, expected_state_out,
                "native MCL {symbol_name} {opt_level:?} compact successor should exactly match the Request(1, 1) update"
            );

            let typeok_invariant_names = vec![
                "ClockLookup1OK".to_string(),
                "ProcQuantifierValuesOK".to_string(),
                "ProcInlineQuantifierValuesOK".to_string(),
                "ClockInNatOverride".to_string(),
                "ClockInNatOverrideInlineProc".to_string(),
                "ClockInInlineNatOverride".to_string(),
                "ClockInFullyInlineRange".to_string(),
                "ClockNonZero".to_string(),
                "ClockInClock1".to_string(),
                "ClockTypeOK".to_string(),
                "ReqTypeOK".to_string(),
                "AckTypeOK".to_string(),
                "NetworkTypeOK".to_string(),
                "CritTypeOK".to_string(),
                "TypeOK".to_string(),
            ];
            let typeok_config = Config {
                init: Some("Init".to_string()),
                next: Some("Next".to_string()),
                invariants: typeok_invariant_names.clone(),
                ..Default::default()
            };
            let mut typeok_module = mcl_typeok_native_module();
            resolve_module_state_vars(&mut typeok_module, &typeok_config);
            let typeok_bytecode = tla_eval::bytecode_vm::compile_operators_to_bytecode(
                &typeok_module,
                &[],
                &typeok_config.invariants,
            );
            assert!(
                typeok_bytecode.failed.is_empty(),
                "decomposed MCL TypeOK should compile to bytecode without fallback: {:?}",
                typeok_bytecode.failed
            );
            let invariant_bytecodes: Vec<_> = typeok_invariant_names
                .iter()
                .map(|name| {
                    let entry_idx = *typeok_bytecode
                        .op_indices
                        .get(name.as_str())
                        .unwrap_or_else(|| panic!("MCL {name} bytecode entry should be present"));
                    Some(typeok_bytecode.chunk.get_function(entry_idx))
                })
                .collect();
            let actions: FxHashMap<String, &tla_tir::bytecode::BytecodeFunction> =
                FxHashMap::default();

            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling decomposed MCL TypeOK at {opt_level:?}");
            let (typeok_cache, typeok_stats) = Llvm2NativeCache::build(
                &actions,
                &invariant_bytecodes,
                &[],
                layout.var_count(),
                Some(&layout),
                opt_level,
                None,
                Some(&typeok_bytecode.chunk.constants),
                None,
                &[],
                None,
                Some(&typeok_bytecode.chunk),
                None,
            );
            let known_native_fallback = |name: &str| matches!(name, "NetworkTypeOK" | "TypeOK");
            let expected_fallbacks = typeok_invariant_names
                .iter()
                .filter(|name| known_native_fallback(name))
                .count();
            assert_eq!(
                typeok_stats.invariants_compiled + typeok_stats.invariants_failed,
                typeok_invariant_names.len(),
                "decomposed MCL TypeOK invariants should be classified as compiled or known native fallbacks at {opt_level:?}"
            );
            assert_eq!(
                typeok_stats.invariants_compiled,
                typeok_invariant_names.len() - expected_fallbacks,
                "decomposed MCL TypeOK invariants should compile all native-supported invariant fragments at {opt_level:?}"
            );
            assert_eq!(
                typeok_stats.invariants_failed, expected_fallbacks,
                "decomposed MCL TypeOK should fall back only for aggregate-return fragments at {opt_level:?}"
            );

            for (idx, invariant_name) in typeok_invariant_names.iter().enumerate() {
                let Some(typeok_fn) = typeok_cache.invariant_fns[idx] else {
                    assert!(
                        known_native_fallback(invariant_name),
                        "MCL {invariant_name} native invariant function should be present"
                    );
                    continue;
                };
                assert!(
                    !known_native_fallback(invariant_name),
                    "MCL {invariant_name} unexpectedly compiled despite being classified as a known native fallback"
                );
                let mut typeok_out = JitCallOut::default();
                Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
                unsafe {
                    typeok_fn(
                        &mut typeok_out,
                        state_out.as_ptr(),
                        u32::try_from(state_len)
                            .expect("fixture state width should fit native ABI"),
                    );
                }
                eprintln!(
                    "[llvm2-canary] MCL {invariant_name} at {opt_level:?} returned {typeok_out:?}"
                );
                assert_eq!(
                    typeok_out.status,
                    tla_jit_abi::JitStatus::Ok,
                    "native MCL {invariant_name} callout should return Ok for Request(1, 1) compact successor at {opt_level:?}"
                );
                assert_eq!(
                    typeok_out.value, 1,
                    "native MCL {invariant_name} should hold for Request(1, 1) compact successor at {opt_level:?}"
                );
            }

            clear_tla_runtime_arenas_for_native_canary();
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_receive_request_1_2_native_empty_channel_guard_returns_false() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_receive_request_1_2_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_ACK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + MCL_ACK_SLOT_COUNT;
        const MCL_CLOCK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + MCL_CLOCK_SLOT_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * 2;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 1;
        state_in[MCL_CLOCK_OFFSET + 2] = 1;
        state_in[MCL_CLOCK_OFFSET + 3] = 1;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }
        assert_eq!(
            &state_in[..16],
            &[3, 0, 0, 0, 3, 1, 1, 1, 0, 3, 3, 0, 0, 0, 0, 0],
            "fixture head should match the real MCL first-parent flat layout"
        );

        for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
            tla_llvm2::compile::clear_jit_cache();
            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling ReceiveRequest__1_2_1_2 at {opt_level:?}");
            let (func, _library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
                "ReceiveRequest__1_2_1_2",
                entry,
                Some(&layout),
                opt_level,
                None,
                Some(&chunk),
            )
            .expect("ReceiveRequest__1_2_1_2 should compile through the native LLVM2 action path");

            let mut state_out = state_in.clone();
            let mut out = native_fused_callout_sentinel();

            tla_llvm2::ensure_jit_execute_mode();
            eprintln!("[llvm2-canary] calling {symbol_name} at {opt_level:?}");
            Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
            unsafe {
                func(
                    &mut out,
                    state_in.as_ptr(),
                    state_out.as_mut_ptr(),
                    u32::try_from(state_len).expect("fixture state width should fit native ABI"),
                );
            }
            eprintln!("[llvm2-canary] returned {symbol_name} at {opt_level:?}: {out:?}");

            assert_eq!(
                out.status,
                tla_jit_abi::JitStatus::Ok,
                "native MCL {symbol_name} {opt_level:?} callout returned a bad status: {out:?}",
            );
            assert_eq!(
                out.value, 0,
                "native MCL {symbol_name} {opt_level:?} empty-channel guard should disable the action"
            );
            assert_eq!(
                state_out, state_in,
                "native MCL {symbol_name} {opt_level:?} disabled ReceiveRequest should leave state_out unchanged"
            );

            clear_tla_runtime_arenas_for_native_canary();
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_bounded_network_native_accepts_full_capacity_channels() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_bounded_network_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * 2;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);

        let channel_base = |from: usize, to: usize| {
            MCL_NETWORK_OFFSET
                + 1
                + (from - 1) * MCL_NETWORK_ROW_SLOT_COUNT
                + 1
                + (to - 1) * MCL_CHANNEL_SLOT_COUNT
        };

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 1;
        state_in[MCL_CLOCK_OFFSET + 2] = 1;
        state_in[MCL_CLOCK_OFFSET + 3] = 1;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        for from in 1..=MCL_PROC_COUNT {
            for to in 1..=MCL_PROC_COUNT {
                state_in[channel_base(from, to)] = 3;
            }
        }
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }

        for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
            tla_llvm2::compile::clear_jit_cache();
            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling BoundedNetwork at {opt_level:?}");
            let (func, _library, symbol_name) = Llvm2NativeCache::compile_invariant_func(
                "BoundedNetwork",
                entry,
                Some(&layout),
                opt_level,
                Some(&chunk.constants),
                Some(&chunk),
            )
            .expect("BoundedNetwork should compile through the native LLVM2 invariant path");

            let mut out = JitCallOut::default();
            tla_llvm2::ensure_jit_execute_mode();
            eprintln!("[llvm2-canary] calling {symbol_name} at {opt_level:?}");
            Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
            unsafe {
                func(
                    &mut out,
                    state_in.as_ptr(),
                    u32::try_from(state_len).expect("fixture state width should fit native ABI"),
                );
            }
            eprintln!("[llvm2-canary] returned {symbol_name} at {opt_level:?}: {out:?}");

            assert_eq!(
                out.status,
                tla_jit_abi::JitStatus::Ok,
                "native MCL {symbol_name} {opt_level:?} callout returned a bad status: {out:?}",
            );
            assert_eq!(
                out.value, 1,
                "native MCL {symbol_name} {opt_level:?} should accept channel length 3"
            );
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_exit_1_1_native_appends_release_to_nonempty_channels() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_exit_1_1_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * 2;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);

        let channel_base = |from: usize, to: usize| {
            MCL_NETWORK_OFFSET
                + 1
                + (from - 1) * MCL_NETWORK_ROW_SLOT_COUNT
                + 1
                + (to - 1) * MCL_CHANNEL_SLOT_COUNT
        };
        let req_slot = |proc: usize, from: usize| {
            MCL_REQ_OFFSET + 1 + (proc - 1) * MCL_REQ_ROW_SLOT_COUNT + from
        };

        let req_name_id = tla_core::intern_name("req").0 as i64;
        let rel_name_id = tla_core::intern_name("rel").0 as i64;

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_ACK_OFFSET + 1] = 7;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 2;
        state_in[MCL_CLOCK_OFFSET + 2] = 1;
        state_in[MCL_CLOCK_OFFSET + 3] = 1;
        state_in[MCL_CRIT_OFFSET] = 1;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        let from_1_to_2 = channel_base(1, 2);
        state_in[from_1_to_2] = 1;
        state_in[from_1_to_2 + 1] = 1;
        state_in[from_1_to_2 + 2] = req_name_id;
        let from_1_to_3 = channel_base(1, 3);
        state_in[from_1_to_3] = 1;
        state_in[from_1_to_3 + 1] = 1;
        state_in[from_1_to_3 + 2] = req_name_id;
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }
        state_in[req_slot(1, 1)] = 2;

        for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
            tla_llvm2::compile::clear_jit_cache();
            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling Exit__1_1 at {opt_level:?}");
            let (func, _library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
                "Exit__1_1",
                entry,
                Some(&layout),
                opt_level,
                Some(&chunk.constants),
                Some(&chunk),
            )
            .expect("Exit__1_1 should compile through the native LLVM2 action path");

            let mut state_out = state_in.clone();
            let mut out = native_fused_callout_sentinel();

            tla_llvm2::ensure_jit_execute_mode();
            eprintln!("[llvm2-canary] calling {symbol_name} at {opt_level:?}");
            Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
            unsafe {
                func(
                    &mut out,
                    state_in.as_ptr(),
                    state_out.as_mut_ptr(),
                    u32::try_from(state_len).expect("fixture state width should fit native ABI"),
                );
            }
            eprintln!("[llvm2-canary] returned {symbol_name} at {opt_level:?}: {out:?}");

            assert_eq!(
                out.status,
                tla_jit_abi::JitStatus::Ok,
                "native MCL {symbol_name} {opt_level:?} callout returned a bad status: {out:?}",
            );
            assert_eq!(
                out.value, 1,
                "native MCL {symbol_name} {opt_level:?} crit-member guard should enable the action"
            );

            let mut expected_state_out = state_in.clone();
            expected_state_out[MCL_CRIT_OFFSET] = 0;
            expected_state_out[MCL_ACK_OFFSET + 1] = 0;
            expected_state_out[req_slot(1, 1)] = 0;
            for base in [from_1_to_2, from_1_to_3] {
                expected_state_out[base] = 2;
                expected_state_out[base + 3] = 0;
                expected_state_out[base + 4] = rel_name_id;
            }

            assert_eq!(
                state_out, expected_state_out,
                "native MCL {symbol_name} {opt_level:?} compact successor should exactly match Exit(1)"
            );

            clear_tla_runtime_arenas_for_native_canary();
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_receive_release_1_2_native_tails_nonempty_channel() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_receive_release_1_2_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * 2;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);

        let channel_base = |from: usize, to: usize| {
            MCL_NETWORK_OFFSET
                + 1
                + (from - 1) * MCL_NETWORK_ROW_SLOT_COUNT
                + 1
                + (to - 1) * MCL_CHANNEL_SLOT_COUNT
        };
        let req_slot = |proc: usize, from: usize| {
            MCL_REQ_OFFSET + 1 + (proc - 1) * MCL_REQ_ROW_SLOT_COUNT + from
        };

        let rel_name_id = tla_core::intern_name("rel").0 as i64;
        let req_name_id = tla_core::intern_name("req").0 as i64;

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 2;
        state_in[MCL_CLOCK_OFFSET + 2] = 1;
        state_in[MCL_CLOCK_OFFSET + 3] = 1;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }
        state_in[req_slot(1, 2)] = 1;

        let from_2_to_1 = channel_base(2, 1);
        state_in[from_2_to_1] = 2;
        state_in[from_2_to_1 + 1] = 0;
        state_in[from_2_to_1 + 2] = rel_name_id;
        state_in[from_2_to_1 + 3] = 1;
        state_in[from_2_to_1 + 4] = req_name_id;

        for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
            tla_llvm2::compile::clear_jit_cache();
            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling ReceiveRelease__1_2_1_2 at {opt_level:?}");
            let (func, _library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
                "ReceiveRelease__1_2_1_2",
                entry,
                Some(&layout),
                opt_level,
                Some(&chunk.constants),
                Some(&chunk),
            )
            .expect("ReceiveRelease__1_2_1_2 should compile through the native LLVM2 action path");

            let mut state_out = state_in.clone();
            let mut out = native_fused_callout_sentinel();

            tla_llvm2::ensure_jit_execute_mode();
            eprintln!("[llvm2-canary] calling {symbol_name} at {opt_level:?}");
            Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
            unsafe {
                func(
                    &mut out,
                    state_in.as_ptr(),
                    state_out.as_mut_ptr(),
                    u32::try_from(state_len).expect("fixture state width should fit native ABI"),
                );
            }
            eprintln!("[llvm2-canary] returned {symbol_name} at {opt_level:?}: {out:?}");

            assert_eq!(
                out.status,
                tla_jit_abi::JitStatus::Ok,
                "native MCL {symbol_name} {opt_level:?} callout returned a bad status: {out:?}",
            );
            assert_eq!(
                out.value, 1,
                "native MCL {symbol_name} {opt_level:?} release-message guard should enable the action"
            );

            let mut expected_state_out = state_in.clone();
            expected_state_out[req_slot(1, 2)] = 0;
            expected_state_out[from_2_to_1] = 1;
            expected_state_out[from_2_to_1 + 1] = 1;
            expected_state_out[from_2_to_1 + 2] = req_name_id;
            expected_state_out[from_2_to_1 + 3] = 0;
            expected_state_out[from_2_to_1 + 4] = 0;

            assert_eq!(
                state_out, expected_state_out,
                "native MCL {symbol_name} {opt_level:?} compact successor should exactly match ReceiveRelease(1, 2)"
            );

            clear_tla_runtime_arenas_for_native_canary();
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_enter_1_1_native_accepts_depth5_enabled_state() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_enter_1_1_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * 2;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);

        let req_slot = |proc: usize, from: usize| {
            MCL_REQ_OFFSET + 1 + (proc - 1) * MCL_REQ_ROW_SLOT_COUNT + from
        };

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_ACK_OFFSET + 1] = 7;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 1;
        state_in[MCL_CLOCK_OFFSET + 2] = 2;
        state_in[MCL_CLOCK_OFFSET + 3] = 2;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }
        state_in[req_slot(1, 1)] = 1;
        state_in[req_slot(1, 2)] = 2;
        state_in[req_slot(1, 3)] = 2;
        assert_eq!(
            state_in[req_slot(1, 1)],
            1,
            "Enter(1) fixture must model req[1][1]"
        );
        assert_eq!(
            state_in[req_slot(1, 2)],
            2,
            "Enter(1) fixture must exercise beats(1, 2) through req[1][1] < req[1][2]"
        );
        assert_eq!(
            state_in[req_slot(1, 3)],
            2,
            "Enter(1) fixture must exercise beats(1, 3) through req[1][1] < req[1][3]"
        );

        for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
            tla_llvm2::compile::clear_jit_cache();
            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling Enter__1_1 at {opt_level:?}");
            let (func, _library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
                "Enter__1_1",
                entry,
                Some(&layout),
                opt_level,
                Some(&chunk.constants),
                Some(&chunk),
            )
            .expect("Enter__1_1 should compile through the native LLVM2 action path");

            let run_enter = |label: &str, input: &[i64]| {
                let mut state_out = input.to_vec();
                let mut out = native_fused_callout_sentinel();

                tla_llvm2::ensure_jit_execute_mode();
                eprintln!("[llvm2-canary] calling {symbol_name} at {opt_level:?} ({label})");
                Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
                unsafe {
                    func(
                        &mut out,
                        input.as_ptr(),
                        state_out.as_mut_ptr(),
                        u32::try_from(state_len)
                            .expect("fixture state width should fit native ABI"),
                    );
                }
                eprintln!(
                    "[llvm2-canary] returned {symbol_name} at {opt_level:?} ({label}): {out:?}"
                );
                (out, state_out)
            };

            let (out, state_out) = run_enter("enabled_ack_all_beats_true", &state_in);

            assert_eq!(
                out.status,
                tla_jit_abi::JitStatus::Ok,
                "native MCL {symbol_name} {opt_level:?} callout returned a bad status: {out:?}",
            );
            assert_eq!(
                out.value, 1,
                "native MCL {symbol_name} {opt_level:?} should enable Enter(1)"
            );

            let mut expected_state_out = state_in.clone();
            expected_state_out[MCL_CRIT_OFFSET] = 1;
            assert_eq!(
                state_out, expected_state_out,
                "native MCL {symbol_name} {opt_level:?} compact successor should exactly match Enter(1)"
            );

            let mut ack_guard_false_state = state_in.clone();
            ack_guard_false_state[MCL_ACK_OFFSET + 1] = 3;
            let (ack_false_out, ack_false_state_out) =
                run_enter("disabled_ack_1_missing_proc_3", &ack_guard_false_state);
            assert_eq!(ack_false_out.status, tla_jit_abi::JitStatus::Ok);
            assert_eq!(
                ack_false_out.value, 0,
                "native MCL {symbol_name} {opt_level:?} must disable Enter(1) when ack[1] != Proc"
            );
            assert_eq!(
                ack_false_state_out, ack_guard_false_state,
                "disabled Enter(1) ack guard must leave state_out unchanged"
            );

            let mut beats_2_false_state = state_in.clone();
            beats_2_false_state[req_slot(1, 1)] = 2;
            beats_2_false_state[req_slot(1, 2)] = 1;
            beats_2_false_state[req_slot(1, 3)] = 3;
            let (beats_2_false_out, beats_2_false_state_out) =
                run_enter("disabled_beats_1_2_false", &beats_2_false_state);
            assert_eq!(beats_2_false_out.status, tla_jit_abi::JitStatus::Ok);
            assert_eq!(
                beats_2_false_out.value, 0,
                "native MCL {symbol_name} {opt_level:?} must disable Enter(1) when beats(1, 2) is false"
            );
            assert_eq!(
                beats_2_false_state_out, beats_2_false_state,
                "disabled Enter(1) beats(1, 2) guard must leave state_out unchanged"
            );

            let mut beats_3_false_state = state_in.clone();
            beats_3_false_state[req_slot(1, 1)] = 2;
            beats_3_false_state[req_slot(1, 2)] = 3;
            beats_3_false_state[req_slot(1, 3)] = 1;
            let (beats_3_false_out, beats_3_false_state_out) =
                run_enter("disabled_beats_1_3_false", &beats_3_false_state);
            assert_eq!(beats_3_false_out.status, tla_jit_abi::JitStatus::Ok);
            assert_eq!(
                beats_3_false_out.value, 0,
                "native MCL {symbol_name} {opt_level:?} must disable Enter(1) when beats(1, 3) is false"
            );
            assert_eq!(
                beats_3_false_state_out, beats_3_false_state,
                "disabled Enter(1) beats(1, 3) guard must leave state_out unchanged"
            );

            clear_tla_runtime_arenas_for_native_canary();
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_native_fused_deadlock_report_state_emits_enter_successor() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_enter_1_1_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * 2;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);

        let req_slot = |proc: usize, from: usize| {
            MCL_REQ_OFFSET + 1 + (proc - 1) * MCL_REQ_ROW_SLOT_COUNT + from
        };

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_ACK_OFFSET + 1] = 7;
        state_in[MCL_ACK_OFFSET + 2] = 7;
        state_in[MCL_ACK_OFFSET + 3] = 7;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 3;
        state_in[MCL_CLOCK_OFFSET + 2] = 3;
        state_in[MCL_CLOCK_OFFSET + 3] = 3;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }
        for proc in 1..=MCL_PROC_COUNT {
            for from in 1..=MCL_PROC_COUNT {
                state_in[req_slot(proc, from)] = 1;
            }
        }

        let opt_level = tla_llvm2::OptLevel::O3;
        let (func, library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
            "Enter__1_1",
            entry,
            Some(&layout),
            opt_level,
            Some(&chunk.constants),
            Some(&chunk),
        )
        .expect("Enter__1_1 should compile through the native LLVM2 action path");
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert("Enter__1_1".to_string(), func);
        let mut native_action_entries = FxHashMap::default();
        native_action_entries.insert(
            "Enter__1_1".to_string(),
            Llvm2NativeActionEntry {
                library: library.clone(),
                symbol_name,
                binding_values: Vec::new(),
                formal_values: Vec::new(),
            },
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries,
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: state_len,
            opt_level,
            _libraries: vec![library],
        };
        let action_keys = vec!["Enter__1_1".to_string()];
        let level =
            Llvm2CompiledBfsLevel::from_cache(&cache, &action_keys, &[], &[], 1, Some(state_len))
                .expect("native fused level should build from the production LLVM2 cache path");
        assert!(
            level.is_native_fused_loop(),
            "canary must exercise the native fused parent loop"
        );

        let result = level
            .run_level_fused_arena(&state_in, 1)
            .expect("native fused level should be available")
            .expect("native fused level should run");

        assert!(result.invariant_ok);
        assert_eq!(result.parents_processed, 1);
        assert_eq!(result.total_generated, 1);
        assert_eq!(result.total_new, 1);
        assert_eq!(result.successor_count(), 1);
        assert_eq!(
            result.successor_parent_indices().and_then(|idx| idx.get(0)),
            Some(0)
        );

        let mut expected_successor = state_in.clone();
        expected_successor[MCL_CRIT_OFFSET] = 1;
        assert_eq!(
            result.successor_at(0),
            Some(expected_successor.as_slice()),
            "native fused Enter__1_1 successor must match the enabled report-state transition"
        );
        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_receive_ack_1_2_native_nonempty_channel_updates_state() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_receive_ack_1_2_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * 2;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);

        let channel_base = |from: usize, to: usize| {
            MCL_NETWORK_OFFSET
                + 1
                + (from - 1) * MCL_NETWORK_ROW_SLOT_COUNT
                + 1
                + (to - 1) * MCL_CHANNEL_SLOT_COUNT
        };
        let req_slot = |proc: usize, from: usize| {
            MCL_REQ_OFFSET + 1 + (proc - 1) * MCL_REQ_ROW_SLOT_COUNT + from
        };

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_ACK_OFFSET + 1] = 1;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 2;
        state_in[MCL_CLOCK_OFFSET + 2] = 1;
        state_in[MCL_CLOCK_OFFSET + 3] = 1;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }
        state_in[req_slot(1, 1)] = 1;
        state_in[req_slot(1, 2)] = 1;
        state_in[req_slot(2, 2)] = 1;

        let ack_name_id = tla_core::intern_name("ack").0 as i64;
        let from_2_to_1 = channel_base(2, 1);
        state_in[from_2_to_1] = 1;
        state_in[from_2_to_1 + 1] = 0;
        state_in[from_2_to_1 + 2] = ack_name_id;

        for opt_level in [tla_llvm2::OptLevel::O3] {
            tla_llvm2::compile::clear_jit_cache();
            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling ReceiveAck__1_2_1_2 at {opt_level:?}");
            let (func, _library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
                "ReceiveAck__1_2_1_2",
                entry,
                Some(&layout),
                opt_level,
                Some(&chunk.constants),
                Some(&chunk),
            )
            .expect("ReceiveAck__1_2_1_2 should compile through the native LLVM2 action path");

            let mut state_out = state_in.clone();
            let mut out = native_fused_callout_sentinel();

            tla_llvm2::ensure_jit_execute_mode();
            eprintln!("[llvm2-canary] calling {symbol_name} at {opt_level:?}");
            Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
            unsafe {
                func(
                    &mut out,
                    state_in.as_ptr(),
                    state_out.as_mut_ptr(),
                    u32::try_from(state_len).expect("fixture state width should fit native ABI"),
                );
            }
            eprintln!("[llvm2-canary] returned {symbol_name} at {opt_level:?}: {out:?}");

            assert_eq!(
                out.status,
                tla_jit_abi::JitStatus::Ok,
                "native MCL {symbol_name} {opt_level:?} callout returned a bad status: {out:?}",
            );
            assert_eq!(
                out.value, 1,
                "native MCL {symbol_name} {opt_level:?} non-empty ack channel should enable the action"
            );

            let mut expected_state_out = state_in.clone();
            expected_state_out[MCL_ACK_OFFSET + 1] = 3;
            expected_state_out[from_2_to_1] = 0;
            expected_state_out[from_2_to_1 + 1] = 0;
            expected_state_out[from_2_to_1 + 2] = 0;

            assert_eq!(
                state_out, expected_state_out,
                "native MCL {symbol_name} {opt_level:?} compact successor should exactly match ReceiveAck(1, 2)"
            );

            clear_tla_runtime_arenas_for_native_canary();
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_receive_request_1_2_native_nonempty_channel_updates_state() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let (chunk, entry_idx, layout) = mcl_receive_request_1_2_native_fixture();
        let entry = chunk.get_function(entry_idx);
        let state_len = layout.compact_slot_count();
        assert_eq!(
            state_len, 89,
            "real MCL Proc=1..3 five-variable fixture width changed"
        );

        const MCL_PROC_COUNT: usize = 3;
        const MCL_ACK_OFFSET: usize = 0;
        const MCL_CLOCK_OFFSET: usize = MCL_ACK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_CRIT_OFFSET: usize = MCL_CLOCK_OFFSET + 1 + MCL_PROC_COUNT;
        const MCL_NETWORK_OFFSET: usize = MCL_CRIT_OFFSET + 1;
        const MCL_CHANNEL_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * 2;
        const MCL_NETWORK_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_CHANNEL_SLOT_COUNT;
        const MCL_NETWORK_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT * MCL_NETWORK_ROW_SLOT_COUNT;
        const MCL_REQ_OFFSET: usize = MCL_NETWORK_OFFSET + MCL_NETWORK_SLOT_COUNT;
        const MCL_REQ_ROW_SLOT_COUNT: usize = 1 + MCL_PROC_COUNT;
        assert_eq!(MCL_NETWORK_OFFSET, 9);
        assert_eq!(MCL_REQ_OFFSET, 76);

        let channel_base = |from: usize, to: usize| {
            MCL_NETWORK_OFFSET
                + 1
                + (from - 1) * MCL_NETWORK_ROW_SLOT_COUNT
                + 1
                + (to - 1) * MCL_CHANNEL_SLOT_COUNT
        };
        let req_slot = |proc: usize, from: usize| {
            MCL_REQ_OFFSET + 1 + (proc - 1) * MCL_REQ_ROW_SLOT_COUNT + from
        };

        let mut state_in = vec![0_i64; state_len];
        state_in[MCL_ACK_OFFSET] = 3;
        state_in[MCL_ACK_OFFSET + 2] = 2;
        state_in[MCL_CLOCK_OFFSET] = 3;
        state_in[MCL_CLOCK_OFFSET + 1] = 1;
        state_in[MCL_CLOCK_OFFSET + 2] = 1;
        state_in[MCL_CLOCK_OFFSET + 3] = 1;
        state_in[MCL_NETWORK_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_NETWORK_OFFSET + 1 + proc_idx * MCL_NETWORK_ROW_SLOT_COUNT] = 3;
        }
        state_in[MCL_REQ_OFFSET] = 3;
        for proc_idx in 0..MCL_PROC_COUNT {
            state_in[MCL_REQ_OFFSET + 1 + proc_idx * MCL_REQ_ROW_SLOT_COUNT] = 3;
        }
        state_in[req_slot(2, 2)] = 1;

        let req_name_id = tla_core::intern_name("req").0 as i64;
        let ack_name_id = tla_core::intern_name("ack").0 as i64;
        let from_2_to_1 = channel_base(2, 1);
        state_in[from_2_to_1] = 1;
        state_in[from_2_to_1 + 1] = 1;
        state_in[from_2_to_1 + 2] = req_name_id;
        let from_2_to_3 = channel_base(2, 3);
        state_in[from_2_to_3] = 1;
        state_in[from_2_to_3 + 1] = 1;
        state_in[from_2_to_3 + 2] = req_name_id;

        for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
            tla_llvm2::compile::clear_jit_cache();
            clear_tla_runtime_arenas_for_native_canary();
            eprintln!("[llvm2-canary] compiling ReceiveRequest__1_2_1_2 at {opt_level:?}");
            let (func, _library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
                "ReceiveRequest__1_2_1_2",
                entry,
                Some(&layout),
                opt_level,
                None,
                Some(&chunk),
            )
            .expect("ReceiveRequest__1_2_1_2 should compile through the native LLVM2 action path");

            let mut state_out = state_in.clone();
            let mut out = native_fused_callout_sentinel();

            tla_llvm2::ensure_jit_execute_mode();
            eprintln!("[llvm2-canary] calling {symbol_name} at {opt_level:?}");
            Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
            unsafe {
                func(
                    &mut out,
                    state_in.as_ptr(),
                    state_out.as_mut_ptr(),
                    u32::try_from(state_len).expect("fixture state width should fit native ABI"),
                );
            }
            eprintln!("[llvm2-canary] returned {symbol_name} at {opt_level:?}: {out:?}");

            assert_eq!(
                out.status,
                tla_jit_abi::JitStatus::Ok,
                "native MCL {symbol_name} {opt_level:?} callout returned a bad status: {out:?}",
            );
            assert_eq!(
                out.value, 1,
                "native MCL {symbol_name} {opt_level:?} non-empty req channel should enable the action"
            );

            let mut expected_state_out = state_in.clone();
            expected_state_out[req_slot(1, 2)] = 1;
            expected_state_out[MCL_CLOCK_OFFSET + 1] = 2;
            expected_state_out[from_2_to_1] = 0;
            expected_state_out[from_2_to_1 + 1] = 0;
            expected_state_out[from_2_to_1 + 2] = 0;
            let from_1_to_2 = channel_base(1, 2);
            expected_state_out[from_1_to_2] = 1;
            expected_state_out[from_1_to_2 + 1] = 0;
            expected_state_out[from_1_to_2 + 2] = ack_name_id;

            assert_eq!(
                state_out, expected_state_out,
                "native MCL {symbol_name} {opt_level:?} compact successor should exactly match ReceiveRequest(1, 2)"
            );

            clear_tla_runtime_arenas_for_native_canary();
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_native_fused_parent_loop_opt_level_defaults_to_o1() {
        let _lock = llvm2_dispatch_env_lock();
        let _env = EnvVarGuard::unset(LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL_ENV);

        assert_eq!(
            native_fused_parent_loop_opt_level(tla_llvm2::OptLevel::O1),
            tla_llvm2::OptLevel::O1
        );
        assert_eq!(
            native_fused_parent_loop_opt_level(tla_llvm2::OptLevel::O3),
            tla_llvm2::OptLevel::O1
        );
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_native_fused_parent_loop_opt_level_allows_o1_env_value() {
        let _lock = llvm2_dispatch_env_lock();
        let _env = EnvVarGuard::set(LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL_ENV, "o1");

        assert_eq!(
            native_fused_parent_loop_opt_level(tla_llvm2::OptLevel::O3),
            tla_llvm2::OptLevel::O1
        );
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_native_fused_parent_loop_opt_level_allows_o3_env_value() {
        let _lock = llvm2_dispatch_env_lock();
        let _env = EnvVarGuard::set(LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL_ENV, "O3");

        assert_eq!(
            native_fused_parent_loop_opt_level(tla_llvm2::OptLevel::O1),
            tla_llvm2::OptLevel::O3
        );
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_native_fused_parent_loop_opt_level_invalid_value_falls_back_to_o1() {
        let _lock = llvm2_dispatch_env_lock();
        let _env = EnvVarGuard::set(LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL_ENV, "bad");

        assert_eq!(
            native_fused_parent_loop_opt_level(tla_llvm2::OptLevel::O1),
            tla_llvm2::OptLevel::O1
        );
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_eval_action_entry_counter_gate_uses_llvm2_counter_for_dispatch() {
        let _lock = llvm2_dispatch_env_lock();
        let _gate = EnvVarGuard::set(tla_llvm2::LLVM2_ENTRY_COUNTER_DISPATCH_GATE_ENV, "1");
        tla_llvm2::compile::clear_jit_cache();

        let action_name = "CounterGateAction";
        let mut func = tla_tir::bytecode::BytecodeFunction::new(action_name.to_string(), 0);
        func.emit(tla_tir::bytecode::Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(tla_tir::bytecode::Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(tla_tir::bytecode::Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(tla_tir::bytecode::Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(tla_tir::bytecode::Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(tla_tir::bytecode::Opcode::Ret { rs: 3 });

        let lib = tla_llvm2::compile_next_state_native(&func, action_name, tla_llvm2::OptLevel::O1)
            .expect("LLVM2 next-state action should compile with entry counters enabled");
        let observed_lib = lib.clone();
        assert_eq!(observed_lib.entry_count(action_name), Some(0));

        let fn_ptr: NativeNextStateFn = unsafe {
            std::mem::transmute(
                lib.get_symbol(action_name)
                    .expect("compiled action symbol should exist"),
            )
        };

        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(action_name.to_string(), fn_ptr);
        let mut native_action_entries = FxHashMap::default();
        native_action_entries.insert(
            action_name.to_string(),
            Llvm2NativeActionEntry {
                library: lib.clone(),
                symbol_name: action_name.to_string(),
                binding_values: Vec::new(),
                formal_values: Vec::new(),
            },
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries,
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: vec![lib],
        };

        let first = cache
            .eval_action(action_name, &[41])
            .expect("gate should allow the first native dispatch")
            .expect("native dispatch should succeed");
        match first {
            Llvm2ActionResult::Enabled { successor, .. } => assert_eq!(successor, vec![42]),
            Llvm2ActionResult::Disabled => panic!("compiled action should be enabled"),
        }
        assert_eq!(observed_lib.entry_count(action_name), Some(1));

        assert!(
            cache.eval_action(action_name, &[41]).is_none(),
            "after one LLVM2 entry-counter hit, the opt-in gate must fall back to interpreter"
        );
        assert_eq!(observed_lib.entry_count(action_name), Some(1));

        tla_llvm2::compile::clear_jit_cache();
    }

    #[test]
    fn test_eval_invariant_preserves_failed_slot_alignment() {
        let cache = Llvm2NativeCache {
            next_state_fns: FxHashMap::default(),
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![
                Some(fake_invariant_true as NativeInvariantFn),
                None,
                Some(fake_invariant_false as NativeInvariantFn),
            ],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None, None, None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        assert_eq!(cache.invariant_slot_count(), 3);
        assert_eq!(cache.invariant_count(), 2);
        assert!(
            !cache.has_all_invariants(3),
            "a None slot must block full invariant coverage"
        );
        assert_eq!(cache.eval_invariant(0, &[0]), Some(Ok(true)));
        assert_eq!(
            cache.eval_invariant(1, &[0]),
            None,
            "failed compilation slot must stay at its original index"
        );
        assert_eq!(cache.eval_invariant(2, &[0]), Some(Ok(false)));
        assert_eq!(cache.eval_invariant(3, &[0]), None);
    }

    #[test]
    fn test_eval_invariant_with_state_len_accepts_tail_and_rejects_short_buffer() {
        let cache = Llvm2NativeCache {
            next_state_fns: FxHashMap::default(),
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![Some(fake_invariant_requires_len_two as NativeInvariantFn)],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 2,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        assert_eq!(
            cache.eval_invariant_with_state_len(0, &[1, 2, 3], 2),
            Some(Ok(true))
        );
        assert_eq!(
            cache.eval_invariant_with_state_len(0, &[1], 2),
            Some(Err(()))
        );
        assert_eq!(cache.eval_invariant(0, &[1, 2, 3]), Some(Ok(true)));
    }

    #[test]
    fn test_eval_invariant_rejects_noncanonical_boolean_return() {
        let cache = Llvm2NativeCache {
            next_state_fns: FxHashMap::default(),
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![Some(fake_invariant_noncanonical_true as NativeInvariantFn)],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        assert!(
            matches!(cache.eval_invariant(0, &[0]), Some(Err(()))),
            "direct LLVM2 invariant eval must reject Ok(value=2), not treat it as true"
        );
    }

    #[test]
    fn test_arity_positive_wrappers_do_not_count_against_specialized_action_coverage() {
        let specialized_action_names = FxHashSet::from_iter(["PassToken"]);

        assert!(
            !count_arity_positive_action_failure(true, &specialized_action_names, "PassToken"),
            "a wrapper with executable BindingSpec specializations is not itself an action coverage failure",
        );
        assert!(
            count_arity_positive_action_failure(false, &specialized_action_names, "PassToken"),
            "without specialization enabled, the arity-positive wrapper is interpreter-only",
        );
        assert!(
            count_arity_positive_action_failure(true, &specialized_action_names, "RecvMsg"),
            "a wrapper with no scalar BindingSpec specialization still blocks full LLVM2 coverage",
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_step_uses_invariant_spec_index() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Step".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![
                Some(fake_invariant_true as NativeInvariantFn),
                Some(fake_invariant_false as NativeInvariantFn),
            ],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None, None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        let step = Llvm2CompiledBfsStep::from_cache(&cache, &[String::from("Step")], 2)
            .expect("full action and invariant coverage should build");
        let output = step
            .step_flat(&[7])
            .expect("fake LLVM2 compiled BFS step should run");

        assert_eq!(output.generated_count, 1);
        assert_eq!(output.successor_count(), 1);
        assert!(!output.invariant_ok);
        assert_eq!(output.failed_invariant_idx, Some(1));
        assert_eq!(output.failed_successor_idx, Some(0));
        assert_eq!(
            output.iter_successors().collect::<Vec<_>>(),
            vec![&[123][..]]
        );

        assert!(
            Llvm2CompiledBfsStep::from_cache(&cache, &[String::from("Step")], 3).is_none(),
            "missing invariant slot must prevent compiled BFS construction"
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_step_can_use_flat_slot_state_len() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Step".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![Some(fake_invariant_true as NativeInvariantFn)],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        let step =
            Llvm2CompiledBfsStep::from_cache_with_state_len(&cache, &[String::from("Step")], 1, 3)
                .expect("full action and invariant coverage should build");
        let output = step
            .step_flat(&[7, 8, 9])
            .expect("fake LLVM2 compiled BFS step should accept flat slot width");

        assert_eq!(step.state_len(), 3);
        assert_eq!(output.successor_count(), 1);
        assert_eq!(
            output.iter_successors().collect::<Vec<_>>(),
            vec![&[123, 8, 9][..]]
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_step_scoped_reuses_successor_scratch() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "StepA".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        next_state_fns.insert(
            "StepB".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![Some(fake_invariant_true as NativeInvariantFn)],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };
        let step = Llvm2CompiledBfsStep::from_cache(
            &cache,
            &[String::from("StepA"), String::from("StepB")],
            1,
        )
        .expect("full action and invariant coverage should build");
        let mut scratch = CompiledBfsStepScratch::new(step.state_len());

        {
            let output = step
                .step_flat_scoped(&[7], &mut scratch)
                .expect("scoped LLVM2 step should run");
            assert_eq!(output.generated_count(), 2);
            assert_eq!(output.successor_count(), 2);
            assert!(output.invariant_ok());
            assert_eq!(output.successor_at(0), Some(&[123][..]));
            assert_eq!(output.successor_at(1), Some(&[123][..]));
        }
        let capacity_after_first = scratch.slot_capacity();

        {
            let output = step
                .step_flat_scoped(&[8], &mut scratch)
                .expect("second scoped LLVM2 step should reuse scratch");
            assert_eq!(output.generated_count(), 2);
            assert_eq!(output.successor_count(), 2);
        }
        assert_eq!(
            scratch.slot_capacity(),
            capacity_after_first,
            "same-size scoped steps should retain and reuse the successor arena"
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_step_rejects_noncanonical_action_boolean() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Step".to_string(),
            fake_next_state_noncanonical_true as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![Some(fake_invariant_true as NativeInvariantFn)],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        let step = Llvm2CompiledBfsStep::from_cache(&cache, &[String::from("Step")], 1)
            .expect("full action and invariant coverage should build");

        assert!(
            matches!(step.step_flat(&[7]), Err(BfsStepError::RuntimeError)),
            "per-parent LLVM2 compiled BFS must reject noncanonical action bools"
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_step_rejects_noncanonical_invariant_boolean() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Step".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![Some(fake_invariant_noncanonical_true as NativeInvariantFn)],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };

        let step = Llvm2CompiledBfsStep::from_cache(&cache, &[String::from("Step")], 1)
            .expect("full action and invariant coverage should build");

        assert!(
            matches!(step.step_flat(&[7]), Err(BfsStepError::RuntimeError)),
            "per-parent LLVM2 compiled BFS must reject noncanonical invariant bools"
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_level_moves_packed_successor_arena() {
        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "Step".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );
        let cache = Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: vec![Some(fake_invariant_true as NativeInvariantFn)],
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: vec![None],
            native_state_constraint_entries: Vec::new(),
            state_var_count: 2,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        };
        let level = Llvm2CompiledBfsLevel::from_cache(
            &cache,
            &[String::from("Step")],
            &[String::from("Inv")],
            &[],
            8,
            Some(5),
        )
        .expect("LLVM2 level adapter should build");

        assert_eq!(
            level.state_len(),
            5,
            "prototype LLVM2 fallback must use the requested native fused flat slot count",
        );
        assert!(
            !level.is_native_fused_loop(),
            "hand-built test caches without NativeLibrary entries must stay on the prototype path",
        );
        assert_eq!(level.native_fused_mode(), "prototype");
        assert_eq!(
            level.loop_kind_telemetry(),
            "prototype_rust_parent_loop_over_llvm2_action_invariant_pointers"
        );
        assert!(
            !level.has_native_fused_level(),
            "strict native-fused mode must not accept prototype Rust parent loops"
        );
        assert!(
            !level.skip_global_pre_seen_lookup(),
            "prototype fused levels must retain the Rust pre-seen lookup"
        );

        let result = level
            .run_level_fused_arena(&[7, 1, 10, 11, 12, 8, 2, 20, 21, 22], 2)
            .expect("LLVM2 fused-level adapter should be available")
            .expect("LLVM2 fused-level adapter should run");

        assert!(result.invariant_ok);
        assert_eq!(result.parents_processed, 2);
        assert_eq!(result.total_generated, 2);
        assert_eq!(result.total_new, 2);
        assert_eq!(result.successor_count(), 2);
        assert_eq!(
            result.iter_successors().collect::<Vec<_>>(),
            vec![&[123, 1, 10, 11, 12][..], &[123, 2, 20, 21, 22][..]]
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_level_consumes_native_fused_level_object() {
        let level = Llvm2CompiledBfsLevel::from_mock_native_fn(2, 1, fake_native_fused_level);

        assert!(
            level.is_native_fused_loop(),
            "native fused-level objects must report native_fused_loop=true",
        );
        assert_eq!(level.native_fused_mode(), "action_only");
        assert_eq!(
            level.loop_kind_telemetry(),
            "native_fused_llvm2_parent_loop"
        );
        assert!(
            level.has_native_fused_level(),
            "strict native-fused mode should accept generated native parent loops"
        );
        assert_eq!(level.native_fused_invariant_count(), 0);
        assert!(
            !level.native_fused_regular_invariants_checked_by_backend(),
            "action-only native fused levels do not check regular invariants in LLVM2"
        );
        assert!(
            !level.skip_global_pre_seen_lookup(),
            "action-only native fused levels need the pre-seen lookup before Rust invariants"
        );

        let result = level
            .run_level_fused_arena(&[7, 1, 8, 2], 2)
            .expect("mock native LLVM2 fused-level adapter should be available")
            .expect("mock native LLVM2 fused-level adapter should run");

        assert!(result.invariant_ok);
        assert!(
            !result.regular_invariants_checked_by_backend(),
            "action-only mock native levels should report Rust-side invariant checking"
        );
        assert_eq!(result.parents_processed, 2);
        assert_eq!(result.total_generated, 2);
        assert_eq!(result.total_new, 2);
        assert_eq!(result.successor_count(), 2);
        assert_eq!(
            result.iter_successors().collect::<Vec<_>>(),
            vec![&[17, 11][..], &[18, 12][..]],
        );
        assert!(result.successor_parent_indices_complete());
        assert_eq!(
            result
                .iter_successors_with_parent_indices()
                .collect::<Vec<_>>(),
            vec![(Some(0), &[17, 11][..]), (Some(1), &[18, 12][..])]
        );
        assert_eq!(
            result.successor_fingerprint_at(0),
            Some(crate::check::model_checker::invariants::fingerprint_flat_compiled(&[17, 11])),
        );
        assert_eq!(
            result.successor_fingerprint_at(1),
            Some(crate::check::model_checker::invariants::fingerprint_flat_compiled(&[18, 12])),
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_level_mock_native_invariant_checking_skips_pre_seen_lookup() {
        let level = Llvm2CompiledBfsLevel::from_mock_native_fn_with_metadata(
            2,
            1,
            fake_native_fused_level,
            1,
            true,
        );

        assert!(level.is_native_fused_loop());
        assert_eq!(level.native_fused_invariant_count(), 1);
        assert_eq!(level.native_fused_mode(), "invariant_checking");
        assert_eq!(
            level.loop_kind_label(),
            "invariant-checking native fused LLVM2 parent loop"
        );
        assert!(level.native_fused_regular_invariants_checked_by_backend());
        assert!(
            level.skip_global_pre_seen_lookup(),
            "invariant-checking native fused levels may rely on mark_state_seen for dedup"
        );

        let result = level
            .run_level_fused_arena(&[7, 1, 8, 2], 2)
            .expect("mock native LLVM2 fused-level adapter should be available")
            .expect("mock native LLVM2 fused-level adapter should run");

        assert!(result.invariant_ok);
        assert!(
            result.regular_invariants_checked_by_backend(),
            "invariant-checking native fused levels must report backend invariant checking"
        );
        assert_eq!(result.parents_processed, 2);
        assert_eq!(result.total_generated, 2);
        assert_eq!(result.total_new, 2);
        assert_eq!(result.successor_count(), 2);
        assert!(result.successor_parent_indices_complete());
        assert_eq!(
            result
                .iter_successors_with_parent_indices()
                .collect::<Vec<_>>(),
            vec![(Some(0), &[17, 11][..]), (Some(1), &[18, 12][..])]
        );
    }

    #[test]
    fn test_llvm2_compiled_bfs_level_requires_native_invariant_count_to_skip_pre_seen_lookup() {
        let level = Llvm2CompiledBfsLevel::from_mock_native_fn_with_metadata(
            2,
            1,
            fake_native_fused_level,
            0,
            true,
        );

        assert!(level.is_native_fused_loop());
        assert_eq!(level.native_fused_mode(), "action_only");
        assert!(level.native_fused_regular_invariants_checked_by_backend());
        assert!(
            !level.skip_global_pre_seen_lookup(),
            "regular-invariant telemetry alone is not enough without native invariant entries"
        );
    }

    #[test]
    fn test_llvm2_native_fused_fallback_stays_distinguishable() {
        let level =
            Llvm2CompiledBfsLevel::from_mock_native_fn(1, 1, fake_native_fused_fallback_level);

        assert!(
            level.run_level_fused_arena(&[7], 1).is_none(),
            "FallbackNeeded from native fused level should request fallback, not a runtime error"
        );
    }

    #[test]
    fn test_state_constrained_native_fused_fallback_fails_closed() {
        let level = Llvm2CompiledBfsLevel::from_mock_native_fn_with_counts(
            1,
            1,
            fake_native_fused_fallback_level,
            1,
            0,
            true,
        );

        assert_eq!(
            level.run_level_fused_arena(&[7], 1),
            Some(Err(BfsStepError::FatalRuntimeError))
        );
    }

    #[test]
    fn test_state_constrained_native_fused_exposes_successor_parent_indices() {
        let level = Llvm2CompiledBfsLevel::from_mock_native_fn_with_counts(
            2,
            1,
            fake_native_fused_level,
            1,
            0,
            true,
        );

        assert!(level.is_native_fused_loop());
        assert_eq!(level.native_fused_mode(), "state_constraint_checking");
        assert_eq!(level.native_fused_state_constraint_count(), 1);
        assert_eq!(
            level.loop_kind_label(),
            "state-constrained native fused LLVM2 parent loop"
        );
        assert!(level.native_fused_state_constraints_checked_by_backend(1));

        let result = level
            .run_level_fused_arena(&[7, 1, 8, 2], 2)
            .expect("mock state-constrained native fused level should be available")
            .expect("mock state-constrained native fused level should run");

        assert!(result.invariant_ok);
        assert_eq!(result.parents_processed, 2);
        assert_eq!(result.total_generated, 2);
        assert_eq!(result.total_new, 2);
        assert_eq!(result.successor_count(), 2);
        assert!(result.successor_parent_indices_complete());
        assert_eq!(
            result
                .iter_successors_with_parent_indices()
                .collect::<Vec<_>>(),
            vec![(Some(0), &[17, 11][..]), (Some(1), &[18, 12][..])]
        );
    }

    #[test]
    fn test_state_constrained_native_fused_runtime_error_fails_closed() {
        let level = Llvm2CompiledBfsLevel::from_mock_native_fn_with_counts(
            1,
            1,
            fake_native_fused_runtime_error_level,
            1,
            0,
            true,
        );

        assert_eq!(
            level.run_level_fused_arena(&[7], 1),
            Some(Err(BfsStepError::FatalRuntimeError))
        );
    }

    #[test]
    fn test_state_constrained_native_fused_invalid_abi_fails_closed() {
        let level = Llvm2CompiledBfsLevel::from_mock_native_fn_with_counts(
            1,
            1,
            fake_native_fused_invalid_abi_level,
            1,
            0,
            true,
        );

        assert_eq!(
            level.run_level_fused_arena(&[7], 1),
            Some(Err(BfsStepError::FatalRuntimeError))
        );
    }

    #[test]
    fn test_state_constrained_native_fused_buffer_overflow_fails_closed() {
        let level = Llvm2CompiledBfsLevel::from_mock_native_fn_with_counts(
            1,
            1,
            fake_native_fused_buffer_overflow_level,
            1,
            0,
            true,
        );

        assert_eq!(
            level.run_level_fused_arena(&[7], 1),
            Some(Err(BfsStepError::FatalRuntimeError))
        );
    }

    #[test]
    fn test_native_callout_selftest_fail_closed_maps_to_fatal_runtime_error() {
        let selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "Step".to_string(),
                symbol_name: "tla2_step".to_string(),
                func: fake_next_state_leaves_sentinel_status as NativeNextStateFn,
            }],
            state_constraints: Vec::new(),
            invariants: Vec::new(),
            missing_expected: Vec::new(),
            fail_closed: true,
        };
        let callout_selftest = Mutex::new(Some(selftest));

        let result = Llvm2CompiledBfsLevel::maybe_run_native_callout_selftest(
            &callout_selftest,
            &[42],
            1,
            1,
        );

        assert_eq!(result, Err(BfsStepError::FatalRuntimeError));
        assert!(
            callout_selftest
                .lock()
                .expect("selftest mutex should remain available")
                .is_none(),
            "selftest should be consumed after the first parent sample"
        );
    }

    #[test]
    fn test_native_callout_selftest_fail_closed_missing_expected_stops_before_execution() {
        CALLOUT_SELFTEST_FAIL_CLOSED_ACTION_HITS.store(0, Ordering::SeqCst);
        let selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "Step".to_string(),
                symbol_name: "tla2_step".to_string(),
                func: fake_next_state_records_fail_closed_selftest_hit as NativeNextStateFn,
            }],
            state_constraints: Vec::new(),
            invariants: Vec::new(),
            missing_expected: vec![Llvm2NativeCalloutSelftestMissing {
                kind: "invariant",
                index: 1,
                name: "TypeOk".to_string(),
                symbol_name: "tla2_inv_1".to_string(),
            }],
            fail_closed: true,
        };

        let reason = selftest
            .run_on_first_parent(&[42], 1, 1)
            .expect_err("fail-closed selftest should reject missing expected callouts");

        assert!(
            reason.contains("invariant index=1")
                && reason.contains("symbol=tla2_inv_1")
                && reason.contains("name=TypeOk"),
            "{reason}"
        );
        assert_eq!(
            CALLOUT_SELFTEST_FAIL_CLOSED_ACTION_HITS.load(Ordering::SeqCst),
            0,
            "fail-closed missing coverage must stop before executing action callouts"
        );
    }

    #[test]
    fn test_native_callout_selftest_non_strict_missing_expected_continues() {
        CALLOUT_SELFTEST_NON_STRICT_ACTION_HITS.store(0, Ordering::SeqCst);
        let selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "Step".to_string(),
                symbol_name: "tla2_step".to_string(),
                func: fake_next_state_records_non_strict_selftest_hit as NativeNextStateFn,
            }],
            state_constraints: Vec::new(),
            invariants: Vec::new(),
            missing_expected: vec![Llvm2NativeCalloutSelftestMissing {
                kind: "action",
                index: 1,
                name: "OtherStep".to_string(),
                symbol_name: "tla2_other_step".to_string(),
            }],
            fail_closed: false,
        };

        assert_eq!(selftest.run_on_first_parent(&[42], 1, 1), Ok(()));
        assert_eq!(
            CALLOUT_SELFTEST_NON_STRICT_ACTION_HITS.load(Ordering::SeqCst),
            1,
            "non-strict selftest should continue to executable callouts"
        );
    }

    #[test]
    fn test_native_callout_selftest_rejects_short_declared_parent_arena() {
        let selftest = Llvm2NativeCalloutSelftest {
            actions: Vec::new(),
            state_constraints: Vec::new(),
            invariants: Vec::new(),
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        let reason = selftest
            .run_on_first_parent(&[1, 2], 2, 2)
            .expect_err("selftest should reject arenas shorter than parent_count * state_len");

        assert!(reason.contains("parent_count=2"), "{reason}");
        assert!(reason.contains("required_slots=4"), "{reason}");
        assert!(reason.contains("arena_slots=2"), "{reason}");
    }

    #[test]
    fn test_native_callout_selftest_detects_action_state_out_overrun() {
        let selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "Step".to_string(),
                symbol_name: "tla2_step".to_string(),
                func: fake_next_state_writes_past_state_out as NativeNextStateFn,
            }],
            state_constraints: Vec::new(),
            invariants: Vec::new(),
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        let reason = selftest
            .run_on_first_parent(&[1, 2], 1, 2)
            .expect_err("selftest should reject state_out writes past state_len");

        assert!(reason.contains("state_out"), "{reason}");
        assert!(
            reason.contains("wrote past selftest state buffer"),
            "{reason}"
        );
    }

    #[test]
    fn test_native_callout_selftest_detects_predicate_state_input_mutation() {
        let selftest = Llvm2NativeCalloutSelftest {
            actions: Vec::new(),
            state_constraints: Vec::new(),
            invariants: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 0,
                name: "Inv".to_string(),
                symbol_name: "tla2_inv".to_string(),
                func: fake_invariant_mutates_state_input as NativeInvariantFn,
            }],
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        let reason = selftest
            .run_on_first_parent(&[1, 2], 1, 2)
            .expect_err("selftest should reject predicate mutation of read-only state");

        assert!(reason.contains("mutated read-only state input"), "{reason}");
        assert!(reason.contains("symbol=tla2_inv"), "{reason}");
    }

    #[test]
    fn test_native_callout_selftest_clears_tla_runtime_arenas_before_each_callout() {
        let _arena_guard = TlaRuntimeArenaClearGuard::new();
        CALLOUT_SELFTEST_ARENA_ACTION_CALLS.store(0, Ordering::SeqCst);
        CALLOUT_SELFTEST_ARENA_CONSTRAINT_CALLS.store(0, Ordering::SeqCst);
        CALLOUT_SELFTEST_ARENA_INVARIANT_CALLS.store(0, Ordering::SeqCst);
        CALLOUT_SELFTEST_ARENA_STALE_ENTRY.store(0, Ordering::SeqCst);
        seed_tla_runtime_arenas_for_selftest_test();

        let selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "Step".to_string(),
                symbol_name: "tla2_step".to_string(),
                func: fake_next_state_records_arena_lifecycle as NativeNextStateFn,
            }],
            state_constraints: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 0,
                name: "TypeOk".to_string(),
                symbol_name: "tla2_typeok".to_string(),
                func: fake_state_constraint_records_arena_lifecycle as NativeInvariantFn,
            }],
            invariants: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 0,
                name: "Inv".to_string(),
                symbol_name: "tla2_inv".to_string(),
                func: fake_invariant_records_arena_lifecycle as NativeInvariantFn,
            }],
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        assert_eq!(selftest.run_on_first_parent(&[41], 1, 1), Ok(()));
        assert_eq!(
            CALLOUT_SELFTEST_ARENA_ACTION_CALLS.load(Ordering::SeqCst),
            1
        );
        assert_eq!(
            CALLOUT_SELFTEST_ARENA_CONSTRAINT_CALLS.load(Ordering::SeqCst),
            2
        );
        assert_eq!(
            CALLOUT_SELFTEST_ARENA_INVARIANT_CALLS.load(Ordering::SeqCst),
            2
        );
        assert_eq!(
            CALLOUT_SELFTEST_ARENA_STALE_ENTRY.load(Ordering::SeqCst),
            0,
            "each selftest callout should enter with empty LLVM2 value and iterator arenas"
        );
    }

    #[test]
    fn test_native_callout_selftest_fail_closed_rejects_standalone_state_constraint_false() {
        let selftest = Llvm2NativeCalloutSelftest {
            actions: Vec::new(),
            state_constraints: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 0,
                name: "TypeOk".to_string(),
                symbol_name: "tla2_typeok".to_string(),
                func: fake_invariant_false as NativeInvariantFn,
            }],
            invariants: Vec::new(),
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        let reason = selftest
            .run_on_first_parent(&[42], 1, 1)
            .expect_err("fail-closed selftest should reject a false standalone state constraint");

        assert!(reason.contains("Ok(value=0)"), "{reason}");
    }

    #[test]
    fn test_native_callout_selftest_fail_closed_rejects_standalone_invariant_false() {
        let selftest = Llvm2NativeCalloutSelftest {
            actions: Vec::new(),
            state_constraints: Vec::new(),
            invariants: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 0,
                name: "Inv".to_string(),
                symbol_name: "tla2_inv".to_string(),
                func: fake_invariant_false as NativeInvariantFn,
            }],
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        let reason = selftest
            .run_on_first_parent(&[42], 1, 1)
            .expect_err("fail-closed selftest should reject a false standalone invariant");

        assert!(reason.contains("Ok(value=0)"), "{reason}");
    }

    #[test]
    fn test_native_callout_selftest_rejects_noncanonical_action_boolean() {
        let selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 7,
                name: "BadStep".to_string(),
                symbol_name: "tla2_bad_step".to_string(),
                func: fake_next_state_noncanonical_true as NativeNextStateFn,
            }],
            state_constraints: Vec::new(),
            invariants: Vec::new(),
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        let reason = selftest
            .run_on_first_parent(&[42], 1, 1)
            .expect_err("selftest must reject noncanonical action boolean values");

        assert!(
            reason.contains(
                "native fused action callout returned noncanonical boolean value 2: index=7 symbol=tla2_bad_step name=BadStep"
            ),
            "{reason}"
        );
    }

    #[test]
    fn test_native_callout_selftest_rejects_noncanonical_predicate_boolean() {
        let selftest = Llvm2NativeCalloutSelftest {
            actions: Vec::new(),
            state_constraints: Vec::new(),
            invariants: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 3,
                name: "BadInv".to_string(),
                symbol_name: "tla2_bad_inv".to_string(),
                func: fake_invariant_noncanonical_true as NativeInvariantFn,
            }],
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        let reason = selftest
            .run_on_first_parent(&[42], 1, 1)
            .expect_err("selftest must reject noncanonical predicate boolean values");

        assert!(
            reason.contains(
                "native fused invariant callout returned noncanonical boolean value 2: index=3 symbol=tla2_bad_inv name=BadInv"
            ),
            "{reason}"
        );
    }

    #[test]
    fn test_native_callout_selftest_accepts_zero_values_in_status_only_contexts() {
        let disabled_action_selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "DisabledStep".to_string(),
                symbol_name: "tla2_disabled_step".to_string(),
                func: fake_partial_next_state_disabled as NativeNextStateFn,
            }],
            state_constraints: Vec::new(),
            invariants: Vec::new(),
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        assert_eq!(
            disabled_action_selftest.run_on_first_parent(&[42], 1, 1),
            Ok(()),
            "disabled action callouts should be valid selftest results"
        );

        let after_action_constraint_selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "Step".to_string(),
                symbol_name: "tla2_step".to_string(),
                func: fake_next_state_writes_seven as NativeNextStateFn,
            }],
            state_constraints: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 0,
                name: "TypeOk".to_string(),
                symbol_name: "tla2_typeok".to_string(),
                func: fake_state_constraint_false_on_seven as NativeInvariantFn,
            }],
            invariants: Vec::new(),
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        assert_eq!(
            after_action_constraint_selftest.run_on_first_parent(&[0], 1, 1),
            Ok(()),
            "post-action state-constraint probes should remain status-only"
        );
    }

    #[test]
    fn test_invariant_after_action_uses_generated_state_and_zero_is_nonfatal() {
        ACTION_OUTPUT_INVARIANT_CALLS.store(0, Ordering::SeqCst);
        ACTION_OUTPUT_INVARIANT_HITS.store(0, Ordering::SeqCst);
        let selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "Step".to_string(),
                symbol_name: "tla2_step".to_string(),
                func: fake_next_state_writes_seven as NativeNextStateFn,
            }],
            state_constraints: Vec::new(),
            invariants: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 0,
                name: "Inv".to_string(),
                symbol_name: "tla2_inv".to_string(),
                func: fake_invariant_false_on_seven_records_hit as NativeInvariantFn,
            }],
            missing_expected: Vec::new(),
            fail_closed: true,
        };

        assert_eq!(
            selftest.run_on_first_parent(&[0], 1, 1),
            Ok(()),
            "invariant_after_action Ok(value=0) should be nonfatal"
        );
        assert_eq!(
            ACTION_OUTPUT_INVARIANT_HITS.load(Ordering::SeqCst),
            1,
            "invariant_after_action must evaluate the action-generated successor state"
        );
        assert_eq!(
            ACTION_OUTPUT_INVARIANT_CALLS.load(Ordering::SeqCst),
            2,
            "selftest should run the invariant once after the action and once standalone"
        );
    }

    #[test]
    fn test_native_callout_selftest_fail_closed_on_action_output_state_constraint_error() {
        ACTION_OUTPUT_STATE_CONSTRAINT_HITS.store(0, Ordering::SeqCst);
        let selftest = Llvm2NativeCalloutSelftest {
            actions: vec![Llvm2NativeCalloutSelftestAction {
                index: 0,
                name: "Step".to_string(),
                symbol_name: "tla2_step".to_string(),
                func: fake_next_state_writes_seven as NativeNextStateFn,
            }],
            state_constraints: vec![Llvm2NativeCalloutSelftestPredicate {
                index: 0,
                name: "TypeOk".to_string(),
                symbol_name: "tla2_typeok".to_string(),
                func: fake_state_constraint_errors_on_seven as NativeInvariantFn,
            }],
            invariants: Vec::new(),
            missing_expected: Vec::new(),
            fail_closed: true,
        };
        let callout_selftest = Mutex::new(Some(selftest));

        let result =
            Llvm2CompiledBfsLevel::maybe_run_native_callout_selftest(&callout_selftest, &[0], 1, 1);

        assert_eq!(result, Err(BfsStepError::FatalRuntimeError));
        assert_eq!(
            ACTION_OUTPUT_STATE_CONSTRAINT_HITS.load(Ordering::SeqCst),
            1,
            "state constraints must be checked once against the enabled action output"
        );
        assert!(
            callout_selftest
                .lock()
                .expect("selftest mutex should remain available")
                .is_none(),
            "selftest should be consumed after the first parent sample"
        );
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_coffeecan_type_invariant_compiles_native_with_record_set_interval_domains() {
        assert_single_invariant_compiles_native(
            parse_module(
                r#"
---- MODULE Llvm2CoffeeCanNativeInvariantCompile ----
VARIABLE beans

Init == beans = [black |-> 0, white |-> 0]
Next == beans' = beans
TypeInvariant == beans \in [black : 0..1000, white : 0..1000]
====
"#,
            ),
            "TypeInvariant",
            StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("black"), CompoundLayout::Int),
                    (tla_core::intern_name("white"), CompoundLayout::Int),
                ],
            })]),
        );
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_coffeecan_boundary_native_action_truth_values() {
        let _lock = llvm2_dispatch_env_lock();
        tla_llvm2::compile::clear_jit_cache();
        clear_tla_runtime_arenas_for_native_canary();

        let mut module = parse_module(
            r#"
---- MODULE Llvm2CoffeeCanNativeActionTruth ----
EXTENDS Naturals

VARIABLE can

BeanCount == can.black + can.white

Init == can = [black |-> 0, white |-> 1000]

PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        resolve_module_state_vars(&mut module, &config);

        let action_names = vec![
            "PickSameColorWhite".to_string(),
            "PickSameColorBlack".to_string(),
            "PickDifferentColor".to_string(),
            "Termination".to_string(),
        ];
        let bytecode =
            tla_eval::bytecode_vm::compile_operators_to_bytecode(&module, &[], &action_names);
        assert!(
            bytecode.failed.is_empty(),
            "CoffeeCan boundary actions should compile to bytecode without fallback: {:?}",
            bytecode.failed
        );

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("black"), CompoundLayout::Int),
                (tla_core::intern_name("white"), CompoundLayout::Int),
            ],
        })]);
        let state_in = vec![0_i64, 1000_i64];
        let state_len = layout.compact_slot_count();
        assert_eq!(state_len, 2);

        for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
            for action_name in ["PickSameColorBlack", "PickDifferentColor"] {
                tla_llvm2::compile::clear_jit_cache();
                clear_tla_runtime_arenas_for_native_canary();
                let entry_idx = *bytecode
                    .op_indices
                    .get(action_name)
                    .unwrap_or_else(|| panic!("{action_name} bytecode entry should be present"));
                let entry = bytecode.chunk.get_function(entry_idx);
                let (func, _library, symbol_name) = Llvm2NativeCache::compile_next_state_action(
                    action_name,
                    entry,
                    Some(&layout),
                    opt_level,
                    Some(&bytecode.chunk.constants),
                    Some(&bytecode.chunk),
                )
                .unwrap_or_else(|err| {
                    panic!(
                        "{action_name} should compile through native LLVM2 at {opt_level:?}: {err}"
                    )
                });

                let mut state_out = state_in.clone();
                let mut out = native_fused_callout_sentinel();

                tla_llvm2::ensure_jit_execute_mode();
                Llvm2NativeCalloutSelftest::clear_tla_runtime_arenas_before_callout();
                unsafe {
                    func(
                        &mut out,
                        state_in.as_ptr(),
                        state_out.as_mut_ptr(),
                        u32::try_from(state_len)
                            .expect("CoffeeCan state width should fit native ABI"),
                    );
                }

                assert_eq!(
                    out.status,
                    tla_jit_abi::JitStatus::Ok,
                    "native CoffeeCan {symbol_name} {opt_level:?} returned bad status: {out:?}",
                );
                assert_eq!(
                    out.value, 0,
                    "native CoffeeCan {symbol_name} {opt_level:?} action truth mismatch",
                );
                assert_eq!(
                    state_out, state_in,
                    "native CoffeeCan {symbol_name} {opt_level:?} disabled action should leave state_out unchanged",
                );
            }
        }

        clear_tla_runtime_arenas_for_native_canary();
        tla_llvm2::compile::clear_jit_cache();
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_typeok_compiles_native_with_subset_proc_range() {
        assert_single_invariant_compiles_native(
            parse_module(
                r#"
---- MODULE Llvm2MclNativeInvariantCompile ----
Proc == 1..3
VARIABLE crit, ack

Init == /\ crit = {}
        /\ ack = [p \in Proc |-> {}]
Next == /\ crit' = crit
        /\ ack' = ack
TypeOK == /\ crit \in SUBSET Proc
          /\ ack \in [Proc -> SUBSET Proc]
====
"#,
            ),
            "TypeOK",
            StateLayout::new(vec![
                // Checker setup sorts variables before assigning state slots,
                // so `ack` precedes `crit` here.
                VarLayout::Compound(CompoundLayout::Function {
                    key_layout: Box::new(CompoundLayout::Int),
                    value_layout: Box::new(CompoundLayout::SetBitmask {
                        universe: vec![
                            tla_jit_abi::SetBitmaskElement::Int(1),
                            tla_jit_abi::SetBitmaskElement::Int(2),
                            tla_jit_abi::SetBitmaskElement::Int(3),
                        ],
                    }),
                    pair_count: Some(3),
                    domain_lo: Some(1),
                }),
                VarLayout::Compound(CompoundLayout::SetBitmask {
                    universe: vec![
                        tla_jit_abi::SetBitmaskElement::Int(1),
                        tla_jit_abi::SetBitmaskElement::Int(2),
                        tla_jit_abi::SetBitmaskElement::Int(3),
                    ],
                }),
            ]),
        );
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_mcl_typeok_compiles_native_with_seq_subset_proc_range() {
        assert_single_invariant_compiles_native(
            parse_module(
                r#"
---- MODULE Llvm2MclSeqSubsetNativeInvariantCompile ----
EXTENDS Sequences
Proc == 1..3
VARIABLE ack

Init == ack = <<{}, {}, {}>>
Next == ack' = ack
TypeOK == ack \in Seq(SUBSET Proc)
====
"#,
            ),
            "TypeOK",
            StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::SetBitmask {
                    universe: vec![
                        tla_jit_abi::SetBitmaskElement::Int(1),
                        tla_jit_abi::SetBitmaskElement::Int(2),
                        tla_jit_abi::SetBitmaskElement::Int(3),
                    ],
                }),
                element_count: Some(3),
            })]),
        );
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_ewd998_inv_compiles_native_with_set_filter_fold_sum() {
        assert_single_invariant_compiles_native(
            parse_module(
                r#"
---- MODULE Llvm2Ewd998NativeInvariantCompile ----
EXTENDS Integers, FiniteSets, Functions

N == 3
Node == 0..N-1
Color == {"white", "black"}
Token == [pos : Node, q : Int, color : Color]

VARIABLES active, color, counter, pending, token

Init ==
  /\ active = [i \in Node |-> FALSE]
  /\ color = [i \in Node |-> "white"]
  /\ counter = [i \in Node |-> 0]
  /\ pending = [i \in Node |-> 0]
  /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

Next == UNCHANGED <<active, color, counter, pending, token>>

Sum(f, S) == FoldFunctionOnSet(+, 0, f, S)
B == Sum(pending, Node)
Rng(a,b) == { i \in Node : a <= i /\ i <= b }

Inv ==
  /\ B = Sum(counter, Node)
  /\ \/ /\ \A i \in Rng(token.pos+1, N-1) : active[i] = FALSE
        /\ IF token.pos = N-1
           THEN token.q = 0
           ELSE token.q = Sum(counter, Rng(token.pos+1, N-1))
     \/ Sum(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"
====
"#,
            ),
            "Inv",
            StateLayout::new(vec![
                VarLayout::Compound(CompoundLayout::Function {
                    key_layout: Box::new(CompoundLayout::Int),
                    value_layout: Box::new(CompoundLayout::Bool),
                    pair_count: Some(3),
                    domain_lo: Some(0),
                }),
                VarLayout::Compound(CompoundLayout::Function {
                    key_layout: Box::new(CompoundLayout::Int),
                    value_layout: Box::new(CompoundLayout::String),
                    pair_count: Some(3),
                    domain_lo: Some(0),
                }),
                VarLayout::Compound(CompoundLayout::Function {
                    key_layout: Box::new(CompoundLayout::Int),
                    value_layout: Box::new(CompoundLayout::Int),
                    pair_count: Some(3),
                    domain_lo: Some(0),
                }),
                VarLayout::Compound(CompoundLayout::Function {
                    key_layout: Box::new(CompoundLayout::Int),
                    value_layout: Box::new(CompoundLayout::Int),
                    pair_count: Some(3),
                    domain_lo: Some(0),
                }),
                VarLayout::Compound(CompoundLayout::Record {
                    fields: vec![
                        (tla_core::intern_name("color"), CompoundLayout::String),
                        (tla_core::intern_name("pos"), CompoundLayout::Int),
                        (tla_core::intern_name("q"), CompoundLayout::Int),
                    ],
                }),
            ]),
        );
    }

    #[test]
    fn test_try_llvm2_action_uses_split_action_meta_name_for_specializations() {
        let module = minimal_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.jit_state_scratch = vec![7];
        checker.compiled.split_action_meta =
            Some(vec![crate::check::model_checker::ActionInstanceMeta {
                name: Some("CanonicalAction".to_string()),
                bindings: vec![(Arc::from("n"), Value::int(7))],
                formal_bindings: vec![(Arc::from("n"), Value::int(7))],
                expr: None,
            }]);

        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            tla_jit_abi::specialized_key("CanonicalAction", &[7_i64]),
            fake_partial_next_state as NativeNextStateFn,
        );
        checker.llvm2_cache = Some(Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        });

        let result = checker
            .try_llvm2_action(0, "CoverageAction")
            .expect("split-action metadata name should drive the specialization lookup")
            .expect("fake LLVM2 action should execute successfully");

        match result {
            Llvm2ActionResult::Enabled { successor, .. } => {
                assert_eq!(successor, vec![123]);
            }
            Llvm2ActionResult::Disabled => panic!("fake LLVM2 action should be enabled"),
        }
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_llvm2_inner_exists_expansion_does_not_compile_residual_exists_action() {
        use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};

        let mut func = BytecodeFunction::new("SetVal".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 3, value: 10 }); // PC 0
        func.emit(Opcode::LoadImm { rd: 4, value: 20 }); // PC 1
        func.emit(Opcode::LoadImm { rd: 5, value: 30 }); // PC 2
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 3,
            count: 3,
        }); // PC 3
        func.emit(Opcode::ExistsBegin {
            rd: 0,
            r_binding: 1,
            r_domain: 2,
            loop_end: 4, // -> PC 8
        }); // PC 4
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 }); // PC 5
        func.emit(Opcode::LoadBool { rd: 4, value: true }); // PC 6
        func.emit(Opcode::ExistsNext {
            rd: 0,
            r_binding: 1,
            r_body: 4,
            loop_begin: -2, // -> PC 5
        }); // PC 7
        func.emit(Opcode::Ret { rs: 0 }); // PC 8

        let mut chunk = BytecodeChunk::new();
        let func_idx = chunk.add_function(func);
        let set_val = chunk.get_function(func_idx);
        let mut actions = FxHashMap::default();
        actions.insert("SetVal".to_string(), set_val);

        let (cache, stats) = Llvm2NativeCache::build(
            &actions,
            &[],
            &[],
            1,
            None,
            tla_llvm2::OptLevel::O1,
            Some(&chunk.constants),
            None,
            None,
            &[],
            Some(&chunk),
            None,
            None,
        );

        let expected_keys = vec![
            "SetVal__10".to_string(),
            "SetVal__20".to_string(),
            "SetVal__30".to_string(),
        ];
        assert_eq!(
            cache.inner_exists_expansion_keys("SetVal"),
            expected_keys,
            "LLVM2 cache should expose deterministic final executable inner-EXISTS keys",
        );
        assert!(
            !cache.contains_action("SetVal"),
            "residual EXISTS action must not be compiled under the base key",
        );
        assert_eq!(stats.actions_compiled, 3);
        assert_eq!(stats.actions_failed, 0);

        for (key, expected) in [("SetVal__10", 10), ("SetVal__20", 20), ("SetVal__30", 30)] {
            let result = cache
                .eval_action(key, &[0])
                .unwrap_or_else(|| panic!("{key} should be compiled"))
                .unwrap_or_else(|()| panic!("{key} should execute without runtime error"));
            match result {
                Llvm2ActionResult::Enabled { successor, .. } => {
                    assert_eq!(successor, vec![expected]);
                }
                Llvm2ActionResult::Disabled => panic!("{key} should be enabled"),
            }
        }
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_llvm2_native_action_descriptors_preserve_binding_and_formal_values() {
        use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};

        let mut func = BytecodeFunction::new("SetVal".to_string(), 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let mut chunk = BytecodeChunk::new();
        let func_idx = chunk.add_function(func);
        let set_val = chunk.get_function(func_idx);
        let mut actions = FxHashMap::default();
        actions.insert("SetVal".to_string(), set_val);
        let specializations = [tla_jit_abi::BindingSpec {
            action_name: "SetVal".to_string(),
            binding_values: vec![42, 7],
            formal_values: vec![7],
        }];

        let (cache, stats) = Llvm2NativeCache::build(
            &actions,
            &[],
            &[],
            1,
            None,
            tla_llvm2::OptLevel::O1,
            Some(&chunk.constants),
            None,
            None,
            &specializations,
            Some(&chunk),
            None,
            None,
        );

        assert_eq!(stats.actions_compiled, 1);
        assert_eq!(stats.actions_failed, 0);

        let key = tla_jit_abi::specialized_key("SetVal", &[42, 7]);
        let descriptor = cache.action_descriptor_for_key(&key, 3);
        assert_eq!(descriptor.name, key);
        assert_eq!(descriptor.action_idx, 3);
        assert_eq!(descriptor.binding_values, vec![42, 7]);
        assert_eq!(descriptor.formal_values, vec![7]);

        let native_actions = cache
            .resolve_native_actions_ordered(&[descriptor.name.clone()])
            .expect("specialized native action should resolve");
        assert_eq!(native_actions[0].descriptor.action_idx, 0);
        assert_eq!(native_actions[0].descriptor.binding_values, vec![42, 7]);
        assert_eq!(native_actions[0].descriptor.formal_values, vec![7]);
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_try_llvm2_action_expanded_handles_all_matching_bindings_for_coverage_action() {
        let module = minimal_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.jit_state_scratch = vec![7];
        checker.compiled.split_action_meta = Some(vec![
            crate::check::model_checker::ActionInstanceMeta {
                name: Some("CanonicalAction".to_string()),
                bindings: vec![(Arc::from("n"), Value::int(1))],
                formal_bindings: vec![(Arc::from("n"), Value::int(1))],
                expr: None,
            },
            crate::check::model_checker::ActionInstanceMeta {
                name: Some("CanonicalAction".to_string()),
                bindings: vec![(Arc::from("n"), Value::int(2))],
                formal_bindings: vec![(Arc::from("n"), Value::int(2))],
                expr: None,
            },
            crate::check::model_checker::ActionInstanceMeta {
                name: Some("OtherAction".to_string()),
                bindings: vec![(Arc::from("n"), Value::int(3))],
                formal_bindings: vec![(Arc::from("n"), Value::int(3))],
                expr: None,
            },
        ]);

        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            tla_jit_abi::specialized_key("CanonicalAction", &[1_i64]),
            fake_partial_next_state as NativeNextStateFn,
        );
        next_state_fns.insert(
            tla_jit_abi::specialized_key("CanonicalAction", &[2_i64]),
            fake_partial_next_state_disabled as NativeNextStateFn,
        );

        checker.llvm2_cache = Some(Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        });

        let result = checker
            .try_llvm2_action_expanded("CanonicalAction")
            .expect("coverage action with matching metadata should be LLVM2-compiled")
            .expect("fake LLVM2 action should execute without runtime error");

        assert_eq!(
            result.len(),
            1,
            "one specialized successor should be returned for mixed enabled/disabled bindings",
        );

        match &result[0] {
            Llvm2ActionResult::Enabled {
                successor,
                jit_input,
            } => {
                assert_eq!(successor, &vec![123]);
                assert_eq!(jit_input, &vec![7]);
            }
            Llvm2ActionResult::Disabled => panic!("fake expanded LLVM2 action should be enabled"),
        }
    }

    #[cfg(feature = "llvm2")]
    #[test]
    fn test_try_llvm2_action_expanded_preserves_arity_zero_direct_lookup() {
        let module = minimal_module();
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let mut checker = ModelChecker::new(&module, &config);
        checker.jit_state_scratch = vec![0];
        checker.compiled.split_action_meta =
            Some(vec![crate::check::model_checker::ActionInstanceMeta {
                name: Some("CanonicalAction".to_string()),
                bindings: Vec::new(),
                formal_bindings: Vec::new(),
                expr: None,
            }]);

        let mut next_state_fns = FxHashMap::default();
        next_state_fns.insert(
            "CanonicalAction".to_string(),
            fake_partial_next_state as NativeNextStateFn,
        );

        checker.llvm2_cache = Some(Llvm2NativeCache {
            next_state_fns,
            inner_exists_expansion_keys: FxHashMap::default(),
            invariant_fns: Vec::new(),
            state_constraint_fns: Vec::new(),
            native_action_entries: FxHashMap::default(),
            native_invariant_entries: Vec::new(),
            native_state_constraint_entries: Vec::new(),
            state_var_count: 1,
            opt_level: tla_llvm2::OptLevel::O1,
            _libraries: Vec::new(),
        });

        let result = checker
            .try_llvm2_action_expanded("CanonicalAction")
            .expect("coverage action should hit LLVM2 cache")
            .expect("fake LLVM2 action should execute without runtime error");

        assert_eq!(
            result.len(),
            1,
            "arity-0 coverage action should still use single direct dispatch",
        );
        assert!(matches!(result[0], Llvm2ActionResult::Enabled { .. }));
    }
}
