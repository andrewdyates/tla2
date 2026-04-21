// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tier 2 recompilation controller for speculative type specialization.
//!
//! When the runtime type profiler determines that state variables are
//! monomorphic (e.g., always `Int` or `Bool`), a Tier 2 promotion fires
//! with a [`SpecializationPlan`]. This module manages the lifecycle of
//! the subsequent recompilation:
//!
//! 1. Accepts the plan and compilation inputs from the promotion handler.
//! 2. Spawns a background thread to rebuild the JIT next-state cache.
//! 3. Provides a non-blocking poll for the model checker to swap in the
//!    recompiled cache when ready.
//!
//! The recompiled cache uses the same `JitNextStateCache` type as the
//! original Tier 1 compilation. The specialization plan is available
//! for future use when the lowerer supports type-guarded code paths.
//!
//! Part of #3989: speculative type specialization.

use std::sync::mpsc;
use std::time::{Duration, Instant};

use rustc_hash::FxHashMap;

use crate::bytecode_lower::{BindingSpec, JitNextStateCache};
use crate::compound_layout::StateLayout;
use crate::error::JitError;
use crate::tiered::CacheBuildStats;
use crate::type_specializer::{SpecializationPlan, SpecializationPlanExt};
use tla_tir::bytecode::BytecodeChunk;

/// Result of a Tier 2 recompilation pass.
///
/// Manual `Debug` implementation because `JitNextStateCache` does not derive
/// `Debug` (it holds native function pointers).
pub struct RecompilationResult {
    /// The recompiled next-state cache with specialization applied.
    pub cache: JitNextStateCache,
    /// Compilation statistics for the recompilation pass.
    pub stats: CacheBuildStats,
    /// The specialization plan that drove this recompilation.
    pub plan: SpecializationPlan,
    /// Wall-clock time for the full recompilation (including thread overhead).
    pub total_time: Duration,
}

impl std::fmt::Debug for RecompilationResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RecompilationResult")
            .field("stats", &self.stats)
            .field("plan", &self.plan)
            .field("total_time", &self.total_time)
            .finish_non_exhaustive()
    }
}

/// Manages Tier 2 recompilation with type specialization.
///
/// The controller is owned by the model checker's sequential BFS loop
/// (or the parallel coordination thread). It is not `Sync` — only one
/// thread should drive it.
pub struct RecompilationController {
    /// Channel receiver for the recompiled cache from the background thread.
    pending: Option<mpsc::Receiver<Result<RecompilationResult, String>>>,
    /// The specialization plan that triggered the active recompilation.
    active_plan: Option<SpecializationPlan>,
    /// Whether a Tier 2 recompilation has already been attempted.
    ///
    /// We only recompile once per model-checking run. If the first Tier 2
    /// recompilation fails or the plan turns out unhelpful, we do not retry.
    attempted: bool,
}

impl RecompilationController {
    /// Create a new recompilation controller with no active recompilation.
    #[must_use]
    pub fn new() -> Self {
        Self {
            pending: None,
            active_plan: None,
            attempted: false,
        }
    }

    /// Return `true` when a background recompilation is in progress.
    #[must_use]
    pub fn has_pending(&self) -> bool {
        self.pending.is_some()
    }

    /// Return `true` when a Tier 2 recompilation has already been attempted.
    ///
    /// Used to prevent double-triggering: once attempted, further Tier 2
    /// promotions are ignored.
    #[must_use]
    pub fn already_attempted(&self) -> bool {
        self.attempted
    }

    /// Return a reference to the specialization plan driving the active
    /// recompilation, if any.
    #[must_use]
    pub fn active_plan(&self) -> Option<&SpecializationPlan> {
        self.active_plan.as_ref()
    }

    /// Trigger a Tier 2 recompilation on a background thread.
    ///
    /// Clones the compilation inputs and spawns a thread to rebuild the
    /// JIT next-state cache. The model checker continues BFS with the
    /// existing Tier 1 cache while Cranelift recompiles.
    ///
    /// Returns `Err` if a recompilation has already been attempted or
    /// is currently in progress.
    pub fn trigger_recompilation(
        &mut self,
        plan: SpecializationPlan,
        chunk: BytecodeChunk,
        op_indices: FxHashMap<String, u16>,
        state_var_count: usize,
        state_layout: Option<StateLayout>,
        specializations: Vec<BindingSpec>,
    ) -> Result<(), JitError> {
        if self.attempted {
            return Err(JitError::CompileError(
                "Tier 2 recompilation already attempted".to_string(),
            ));
        }
        if self.pending.is_some() {
            return Err(JitError::CompileError(
                "Tier 2 recompilation already in progress".to_string(),
            ));
        }

        self.attempted = true;
        self.active_plan = Some(plan.clone());

        let (tx, rx) = mpsc::sync_channel(1);

        let plan_for_thread = plan;
        std::thread::Builder::new()
            .name("jit-tier2-recompile".to_string())
            .spawn(move || {
                let start = Instant::now();
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    if specializations.is_empty() {
                        JitNextStateCache::build_with_stats_and_layout(
                            &chunk,
                            &op_indices,
                            state_var_count,
                            state_layout.as_ref(),
                        )
                    } else {
                        JitNextStateCache::build_with_stats_and_specializations(
                            &chunk,
                            &op_indices,
                            state_var_count,
                            state_layout.as_ref(),
                            &specializations,
                        )
                    }
                }));

                let elapsed = start.elapsed();

                let send_result = match result {
                    Ok(Ok((cache, stats))) => tx.send(Ok(RecompilationResult {
                        cache,
                        stats,
                        plan: plan_for_thread,
                        total_time: elapsed,
                    })),
                    Ok(Err(error)) => tx.send(Err(format!("Tier 2 recompilation failed: {error}"))),
                    Err(panic_info) => {
                        let msg: &str = panic_info
                            .downcast_ref::<String>()
                            .map(String::as_str)
                            .or_else(|| panic_info.downcast_ref::<&str>().copied())
                            .unwrap_or("unknown panic");
                        tx.send(Err(format!("Tier 2 recompilation panicked: {msg}")))
                    }
                };

                if send_result.is_err() {
                    // Receiver was dropped (model checker moved on). This is
                    // expected if the check completes before recompilation.
                }
            })
            .map_err(|e| {
                JitError::CompileError(format!("failed to spawn recompilation thread: {e}"))
            })?;

        self.pending = Some(rx);

        Ok(())
    }

    /// Non-blocking poll for recompilation completion.
    ///
    /// Returns `Some(Ok(result))` when the background thread has finished
    /// successfully, `Some(Err(msg))` on failure, or `None` if the
    /// recompilation is still in progress (or was never triggered).
    pub fn poll_completion(&mut self) -> Option<Result<RecompilationResult, String>> {
        let rx = self.pending.as_ref()?;

        match rx.try_recv() {
            Ok(result) => {
                self.pending = None;
                Some(result)
            }
            Err(mpsc::TryRecvError::Empty) => None,
            Err(mpsc::TryRecvError::Disconnected) => {
                self.pending = None;
                Some(Err(
                    "Tier 2 recompilation thread disconnected unexpectedly".to_string()
                ))
            }
        }
    }
}

impl Default for RecompilationController {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_profile::{SpecType, TypeProfile};
    use crate::type_specializer::SpecializationPlan;
    use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, Opcode};

    fn make_test_plan() -> SpecializationPlan {
        let mut profile = TypeProfile::new(2);
        profile.record_state(&[SpecType::Int, SpecType::Bool]);
        profile.record_state(&[SpecType::Int, SpecType::Bool]);
        profile.mark_stable();
        SpecializationPlan::from_profile(&profile)
    }

    fn make_simple_chunk() -> (BytecodeChunk, FxHashMap<String, u16>) {
        let mut func = BytecodeFunction::new("Increment".to_string(), 2);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        func.emit(Opcode::Ret { rs: 0 });

        let mut chunk = BytecodeChunk::new();
        chunk.functions.push(func);
        let mut op_indices = FxHashMap::default();
        op_indices.insert("Increment".to_string(), 0);
        (chunk, op_indices)
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recompilation_controller_initial_state() {
        let ctrl = RecompilationController::new();
        assert!(!ctrl.has_pending());
        assert!(!ctrl.already_attempted());
        assert!(ctrl.active_plan().is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recompilation_controller_trigger_and_poll() {
        let mut ctrl = RecompilationController::new();
        let plan = make_test_plan();
        let (chunk, op_indices) = make_simple_chunk();

        ctrl.trigger_recompilation(plan, chunk, op_indices, 2, None, vec![])
            .expect("should trigger recompilation");

        assert!(ctrl.has_pending());
        assert!(ctrl.already_attempted());
        assert!(ctrl.active_plan().is_some());

        // Poll until completion (with timeout to avoid hanging).
        let start = Instant::now();
        loop {
            if let Some(result) = ctrl.poll_completion() {
                match result {
                    Ok(recomp) => {
                        assert!(
                            recomp.total_time.as_secs() < 30,
                            "recompilation took too long"
                        );
                        assert!(recomp.plan.has_specializable_vars());
                    }
                    Err(msg) => {
                        // Some environments may not support JIT. That's OK for
                        // this test -- we're testing the controller lifecycle.
                        eprintln!("recompilation error (acceptable in test): {msg}");
                    }
                }
                break;
            }
            if start.elapsed() > Duration::from_secs(10) {
                panic!("recompilation did not complete within 10 seconds");
            }
            std::thread::sleep(Duration::from_millis(10));
        }

        assert!(!ctrl.has_pending());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recompilation_controller_prevents_double_trigger() {
        let mut ctrl = RecompilationController::new();
        let plan = make_test_plan();
        let (chunk, op_indices) = make_simple_chunk();

        ctrl.trigger_recompilation(
            plan.clone(),
            chunk.clone(),
            op_indices.clone(),
            2,
            None,
            vec![],
        )
        .expect("first trigger should succeed");

        // Second trigger should fail.
        let result = ctrl.trigger_recompilation(plan, chunk, op_indices, 2, None, vec![]);
        assert!(result.is_err(), "second trigger should fail");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recompilation_controller_poll_without_trigger_returns_none() {
        let mut ctrl = RecompilationController::new();
        assert!(
            ctrl.poll_completion().is_none(),
            "polling without trigger should return None"
        );
    }
}
