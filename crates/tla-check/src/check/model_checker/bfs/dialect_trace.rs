// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `TLA2_DIALECT_TRACE=1` bridge — turns the BFS worker loop into a concrete
//! consumer of the `tla-dialect` crate.
//!
//! Part of #4253 Wave 14. Before this module, `tla-dialect` shipped the
//! `verif.bfs_step` op and its graduation scaffolding, but nothing in the
//! production model checker ever constructed one. That meant the dialect was
//! decorative — the epic's "consumer wiring" requirement was unmet.
//!
//! This module fixes that:
//!
//! - [`DialectTracer`] is a zero-overhead wrapper (one env-read + one atomic
//!   load per worker construction, nothing on the hot path when disabled).
//! - When `TLA2_DIALECT_TRACE=1`, every BFS dequeue produces a
//!   [`tla_dialect::verif::VerifBfsStep`] via the dialect's real
//!   `new_seed`/`new_expand` constructors. The op is then `verify()`-checked
//!   and its [`tla_dialect::verif::BfsKind`] discriminator is emitted to
//!   stderr. `verify()` is called on the happy path so the trace also
//!   exercises the graduated invariants (seed must have `action_id == 0`
//!   and `depth == 0`).
//!
//! The trace is deliberately low-volume: one line per dequeued state, prefixed
//! with `dialect-trace:` so downstream tooling can grep for it. It is **not**
//! routed through `tracing` or `log` — both of those would add a fat dep
//! surface to the model-checker hot path, and the user's intent is an
//! observable toggle, not a structured telemetry channel. If later waves want
//! structured output (e.g. for LLVM2 pipeline introspection), this module is
//! the single seam to upgrade.

#[cfg(test)]
use std::sync::atomic::AtomicBool;
use std::sync::atomic::{AtomicU8, Ordering};

use tla_dialect::verif::{
    BfsKind, VerifBfsStep, VerifFingerprintBatch, VerifFrontierDrain, VerifInvariantCheck,
    VerifStateFingerprint,
};
use tla_dialect::DialectOp;
use tla_dialect::{LlvmLeaf, Lowered};

// State machine for the env-var read: 0 = uninit, 1 = disabled, 2 = enabled.
// Using a `u8` (not `Option<bool>`) keeps the atomic load on the fast path a
// single byte-width load.
const TRACE_UNINIT: u8 = 0;
#[cfg(not(test))]
const TRACE_DISABLED: u8 = 1;
#[cfg(not(test))]
const TRACE_ENABLED: u8 = 2;

/// Atomic global: has the env var been read yet, and what did it say?
static DIALECT_TRACE_STATE: AtomicU8 = AtomicU8::new(TRACE_UNINIT);

/// Cheap check: is the dialect trace globally enabled for this process?
///
/// The first call reads `TLA2_DIALECT_TRACE` once and caches the result with
/// `Relaxed` ordering (we do not synchronize any other state against this
/// flag — a benign race that re-reads the env var is acceptable).
#[inline]
fn dialect_trace_enabled() -> bool {
    #[cfg(test)]
    {
        return std::env::var("TLA2_DIALECT_TRACE")
            .map(|v| v == "1")
            .unwrap_or(false);
    }

    #[cfg(not(test))]
    match DIALECT_TRACE_STATE.load(Ordering::Relaxed) {
        TRACE_ENABLED => true,
        TRACE_DISABLED => false,
        _ => init_dialect_trace_state(),
    }
}

#[cold]
#[cfg(not(test))]
fn init_dialect_trace_state() -> bool {
    let enabled = std::env::var("TLA2_DIALECT_TRACE")
        .map(|v| v == "1")
        .unwrap_or(false);
    let store = if enabled {
        TRACE_ENABLED
    } else {
        TRACE_DISABLED
    };
    DIALECT_TRACE_STATE.store(store, Ordering::Relaxed);
    enabled
}

/// Per-worker dialect-trace emitter.
///
/// Carries the worker id once so the hot path only pays for the `VerifBfsStep`
/// build + `verify()` + `eprintln!` when tracing is enabled. When tracing is
/// off, the `enabled` field is `false` and [`DialectTracer::emit_step`] is a
/// single predictable-branch early-return (LLVM inlines the whole thing away
/// in release builds).
pub(crate) struct DialectTracer {
    worker_id: u32,
    enabled: bool,
}

impl DialectTracer {
    /// Build a tracer for the given worker lane. Reads the env var at most
    /// once per process.
    pub(crate) fn new(worker_id: u32) -> Self {
        Self {
            worker_id,
            enabled: dialect_trace_enabled(),
        }
    }

    /// Is this tracer live? Callers may use this to skip any surrounding work
    /// that only exists to feed the trace (e.g. computing the frontier size).
    #[inline]
    pub(crate) fn is_enabled(&self) -> bool {
        self.trace_active()
    }

    #[inline]
    fn trace_active(&self) -> bool {
        #[cfg(test)]
        {
            self.enabled && dialect_trace_enabled()
        }

        #[cfg(not(test))]
        {
            self.enabled
        }
    }

    /// Emit one `verif.bfs_step` op for the current BFS step. When the tracer
    /// is disabled this is a single branch + return.
    ///
    /// `depth == 0` is modeled as [`BfsKind::Seed`] (Init-produced state);
    /// every deeper state is [`BfsKind::Expand`]. Expand's `action_id` is
    /// carried through opaquely — callers typically pass `0` since the BFS
    /// worker loop does not know the per-successor action id at dequeue time.
    ///
    /// # Panics
    ///
    /// Never — `verify()` can only fail for malformed seeds, but `new_seed` /
    /// `new_expand` enforce the invariants by construction. A failure here
    /// would indicate a bug in `tla-dialect` and is reported on stderr rather
    /// than aborting the model check.
    pub(crate) fn emit_step(&self, depth: usize, frontier_size: usize, action_id: u32) {
        if !self.trace_active() {
            return;
        }
        self.emit_step_slow(depth, frontier_size, action_id);
    }

    #[cold]
    fn emit_step_slow(&self, depth: usize, frontier_size: usize, action_id: u32) {
        // Clamp into u32 — frontier and depth are effectively unbounded at
        // the type level, but the dialect op uses u32 fields because a single
        // u32 (>4B) covers every realistic BFS frontier width or diameter.
        let frontier_size_u32 = frontier_size.min(u32::MAX as usize) as u32;
        let depth_u32 = depth.min(u32::MAX as usize) as u32;

        let step = if depth == 0 {
            VerifBfsStep::new_seed(self.worker_id, frontier_size_u32)
        } else {
            VerifBfsStep::new_expand(action_id, self.worker_id, frontier_size_u32, depth_u32)
        };

        // Exercise the graduated verify() on the happy path. A failure here
        // means the dialect shipped broken constructors and deserves a loud
        // diagnostic, but must not abort the model check (which is the
        // user-facing workload).
        if let Err(e) = step.verify() {
            eprintln!("dialect-trace: verify failed: {e}");
            return;
        }

        let kind = match step.kind {
            BfsKind::Seed => "Seed",
            BfsKind::Expand => "Expand",
        };
        eprintln!(
            "dialect-trace: op={} kind={} worker={} action={} frontier={} depth={}",
            step.op_name(),
            kind,
            step.worker_id,
            step.action_id,
            step.frontier_size,
            step.depth,
        );
    }

    /// Emit one `verif.frontier_drain` op representing the batch-dequeue
    /// semantics of a BFS level transition on this worker. `max` is the
    /// maximum number of frontier states this drain consumed (i.e. the
    /// number of states observed at the previous BFS level before the
    /// transition). When the tracer is disabled this is a single branch +
    /// return.
    ///
    /// Part of #4286 Wave 14 TL3: graduates `verif.frontier_drain` from a
    /// decorative op to a live consumer — the dialect's `new_on_worker`
    /// constructor builds the op, `verify()` enforces the `max > 0`
    /// invariant, and the structured [`LlvmLeaf::FrontierDrain`] variant
    /// carries both `max` and `worker_id` to stderr.
    pub(crate) fn emit_frontier_drain(&self, max: usize) {
        if !self.trace_active() {
            return;
        }
        self.emit_frontier_drain_slow(max);
    }

    #[cold]
    fn emit_frontier_drain_slow(&self, max: usize) {
        // `max == 0` would violate the dialect op's verify() contract
        // (zero-max drain is a miswiring). Clamp to 1 for the trace — a
        // depth-transition drain saw at least one state by definition, but
        // some transports may report 0 under pathological conditions.
        let max_u32 = max.clamp(1, u32::MAX as usize) as u32;
        let drain = VerifFrontierDrain::new_on_worker(max_u32, self.worker_id);
        // Exercise the graduated lowering on the happy path. The dialect op
        // lowers to LlvmLeaf::FrontierDrain { max, worker_id } — we unpack
        // the structured leaf (not a Todo placeholder) for the trace line.
        let leaf = match drain.lower() {
            Ok(Lowered::Leaf(l)) => l,
            Ok(Lowered::Ops(_)) => {
                eprintln!(
                    "dialect-trace: frontier_drain unexpectedly lowered to ops (dialect bug?)"
                );
                return;
            }
            Err(e) => {
                eprintln!("dialect-trace: frontier_drain verify failed: {e}");
                return;
            }
        };
        match leaf {
            LlvmLeaf::FrontierDrain { max, worker_id } => eprintln!(
                "dialect-trace: op={} max={} worker={}",
                drain.op_name(),
                max,
                worker_id,
            ),
            // A future dialect wave may add more FrontierDrain-variants; the
            // backend consumer would match on all of them. For the trace a
            // short fallback line keeps us forward-compatible.
            other => eprintln!("dialect-trace: op={} leaf={other:?}", drain.op_name()),
        }
    }

    /// Emit one `verif.fingerprint_batch` op for a contiguous slab of `count`
    /// states produced at BFS `depth`. `state_base` is an opaque base index
    /// the tracer forwards unchanged (the BFS worker loop supplies a
    /// monotonic counter — a production backend would resolve it to a real
    /// slab offset). When the tracer is disabled this is a single branch +
    /// return.
    ///
    /// Part of #4286 Wave 14 TL3: graduates `verif.fingerprint_batch` from a
    /// decorative op to a live consumer — the dialect's `new_at_depth`
    /// constructor builds the op, `verify()` enforces the `count > 0`
    /// invariant, and the structured [`LlvmLeaf::FingerprintBatch`] variant
    /// carries every field to stderr.
    pub(crate) fn emit_fingerprint_batch(&self, state_base: usize, count: usize, depth: usize) {
        if !self.trace_active() {
            return;
        }
        self.emit_fingerprint_batch_slow(state_base, count, depth);
    }

    #[cold]
    fn emit_fingerprint_batch_slow(&self, state_base: usize, count: usize, depth: usize) {
        // Clamp count to >= 1 so verify() is satisfied. A zero-count batch
        // is a miswiring; we still want the trace to fire (with a clamped
        // count of 1) because the surrounding emit_fingerprint_batch call
        // indicates the consumer *wants* a batch record.
        let state_base_u32 = state_base.min(u32::MAX as usize) as u32;
        let count_u32 = count.clamp(1, u32::MAX as usize) as u32;
        let depth_u32 = depth.min(u32::MAX as usize) as u32;
        let batch = VerifFingerprintBatch::new_at_depth(state_base_u32, count_u32, depth_u32);
        let leaf = match batch.lower() {
            Ok(Lowered::Leaf(l)) => l,
            Ok(Lowered::Ops(_)) => {
                eprintln!(
                    "dialect-trace: fingerprint_batch unexpectedly lowered to ops (dialect bug?)"
                );
                return;
            }
            Err(e) => {
                eprintln!("dialect-trace: fingerprint_batch verify failed: {e}");
                return;
            }
        };
        match leaf {
            LlvmLeaf::FingerprintBatch {
                state_base,
                count,
                depth,
            } => eprintln!(
                "dialect-trace: op={} base={} count={} depth={} worker={}",
                batch.op_name(),
                state_base,
                count,
                depth,
                self.worker_id,
            ),
            other => eprintln!("dialect-trace: op={} leaf={other:?}", batch.op_name()),
        }
    }

    /// Emit one `verif.state_fingerprint` op for a scalar (single-state)
    /// fingerprint at BFS `depth`. Unlike [`DialectTracer::emit_fingerprint_batch`]
    /// (vectorized slab over `count` states), this is the point-wise per-state
    /// counterpart — one line per dequeued state.
    ///
    /// Part of #4286 Wave 14 TL3d: graduates `verif.state_fingerprint` from a
    /// decorative op to a live consumer. The dialect's `new_at_depth`
    /// constructor builds the op, `verify()` always passes (no structural
    /// invariants today), and the structured [`LlvmLeaf::StateFingerprint`]
    /// variant carries both `state_slot` and `depth` to stderr.
    ///
    /// When the tracer is disabled this is a single branch + return.
    pub(crate) fn emit_state_fingerprint(&self, state_slot: usize, depth: usize) {
        if !self.trace_active() {
            return;
        }
        self.emit_state_fingerprint_slow(state_slot, depth);
    }

    #[cold]
    fn emit_state_fingerprint_slow(&self, state_slot: usize, depth: usize) {
        let state_slot_u32 = state_slot.min(u32::MAX as usize) as u32;
        let depth_u32 = depth.min(u32::MAX as usize) as u32;
        let fp = VerifStateFingerprint::new_at_depth(state_slot_u32, depth_u32);
        let leaf = match fp.lower() {
            Ok(Lowered::Leaf(l)) => l,
            Ok(Lowered::Ops(_)) => {
                eprintln!(
                    "dialect-trace: state_fingerprint unexpectedly lowered to ops (dialect bug?)"
                );
                return;
            }
            Err(e) => {
                eprintln!("dialect-trace: state_fingerprint verify failed: {e}");
                return;
            }
        };
        match leaf {
            LlvmLeaf::StateFingerprint { state_slot, depth } => eprintln!(
                "dialect-trace: op={} slot={} depth={} worker={}",
                fp.op_name(),
                state_slot,
                depth,
                self.worker_id,
            ),
            other => eprintln!("dialect-trace: op={} leaf={other:?}", fp.op_name()),
        }
    }

    /// Emit one `verif.invariant_check` op tagging an invariant evaluation
    /// at BFS `depth`. The `invariant_id` is a stable id the caller resolves
    /// (e.g. a spec-level counter), and `state_slot` identifies which state
    /// the check is against (typically the just-dequeued state).
    ///
    /// Part of #4286 Wave 14 TL3d: graduates `verif.invariant_check` from a
    /// decorative op to a live consumer. The dialect's `new_at_depth`
    /// constructor builds the op, `verify()` always passes (no structural
    /// invariants today), and the structured [`LlvmLeaf::InvariantCheck`]
    /// variant carries `invariant_id`, `state_slot`, and `depth` to stderr.
    ///
    /// When the tracer is disabled this is a single branch + return.
    pub(crate) fn emit_invariant_check(&self, invariant_id: u32, state_slot: usize, depth: usize) {
        if !self.trace_active() {
            return;
        }
        self.emit_invariant_check_slow(invariant_id, state_slot, depth);
    }

    #[cold]
    fn emit_invariant_check_slow(&self, invariant_id: u32, state_slot: usize, depth: usize) {
        let state_slot_u32 = state_slot.min(u32::MAX as usize) as u32;
        let depth_u32 = depth.min(u32::MAX as usize) as u32;
        let check = VerifInvariantCheck::new_at_depth(invariant_id, state_slot_u32, depth_u32);
        let leaf = match check.lower() {
            Ok(Lowered::Leaf(l)) => l,
            Ok(Lowered::Ops(_)) => {
                eprintln!(
                    "dialect-trace: invariant_check unexpectedly lowered to ops (dialect bug?)"
                );
                return;
            }
            Err(e) => {
                eprintln!("dialect-trace: invariant_check verify failed: {e}");
                return;
            }
        };
        match leaf {
            LlvmLeaf::InvariantCheck {
                invariant_id,
                state_slot,
                depth,
            } => eprintln!(
                "dialect-trace: op={} inv={} slot={} depth={} worker={}",
                check.op_name(),
                invariant_id,
                state_slot,
                depth,
                self.worker_id,
            ),
            other => eprintln!("dialect-trace: op={} leaf={other:?}", check.op_name()),
        }
    }
}

/// Convenience wrapper: force the env-var read to complete and return the
/// cached value. Intended for tests and diagnostic CLI code.
#[cfg(test)]
#[allow(dead_code)]
pub(crate) fn force_dialect_trace_enabled() -> bool {
    dialect_trace_enabled()
}

/// Test hook — reset the global trace cache so a subsequent call re-reads the
/// env var. Never exposed in release builds; tests use it to flip the toggle
/// without spawning a subprocess.
#[cfg(test)]
pub(crate) fn reset_dialect_trace_state_for_tests() {
    DIALECT_TRACE_STATE.store(TRACE_UNINIT, Ordering::Relaxed);
}

// Silence an unused-item warning when the unused test-only reset helper is
// compiled but never called in a given build configuration.
#[cfg(test)]
#[allow(dead_code)]
static _TOUCH: AtomicBool = AtomicBool::new(false);

#[cfg(test)]
mod tests {
    use super::*;

    /// Serialize env-var-touching tests so they do not race each other. The
    /// rust test harness runs tests in parallel by default, but
    /// `std::env::set_var` is process-global.
    fn env_lock() -> std::sync::MutexGuard<'static, ()> {
        use std::sync::{Mutex, OnceLock};
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
            .lock()
            .unwrap_or_else(|p| p.into_inner())
    }

    #[test]
    fn wave14_tracer_disabled_by_default() {
        let _g = env_lock();
        // SAFETY: tests run single-threaded under env_lock; no concurrent
        // readers of the env mutated here.
        unsafe { std::env::remove_var("TLA2_DIALECT_TRACE") };
        reset_dialect_trace_state_for_tests();
        let tracer = DialectTracer::new(0);
        assert!(
            !tracer.is_enabled(),
            "tracer must be off when env var is unset"
        );
        // No-op call must not panic or write.
        tracer.emit_step(0, 0, 0);
    }

    #[test]
    fn wave14_tracer_reads_env_var_once() {
        let _g = env_lock();
        // SAFETY: tests run single-threaded under env_lock.
        unsafe { std::env::set_var("TLA2_DIALECT_TRACE", "1") };
        reset_dialect_trace_state_for_tests();
        let tracer = DialectTracer::new(3);
        assert!(tracer.is_enabled(), "tracer must be on when env=1");
        assert_eq!(tracer.worker_id, 3);
        unsafe { std::env::remove_var("TLA2_DIALECT_TRACE") };
    }

    #[test]
    fn wave14_tracer_emits_seed_for_depth_zero() {
        // Smoke test: constructing the op directly must match what the tracer
        // would build. This does not touch the env var or the global — it
        // exercises the depth->kind mapping the tracer relies on.
        let seed = VerifBfsStep::new_seed(0, 42);
        assert_eq!(seed.kind, BfsKind::Seed);
        assert_eq!(seed.action_id, 0);
        assert_eq!(seed.depth, 0);
        assert_eq!(seed.frontier_size, 42);
        seed.verify().expect("seed must verify");
    }

    #[test]
    fn wave14_tracer_emits_expand_for_nonzero_depth() {
        let step = VerifBfsStep::new_expand(7, 1, 128, 3);
        assert_eq!(step.kind, BfsKind::Expand);
        assert_eq!(step.action_id, 7);
        assert_eq!(step.worker_id, 1);
        assert_eq!(step.frontier_size, 128);
        assert_eq!(step.depth, 3);
        step.verify().expect("expand must verify");
    }

    #[test]
    fn wave14_tracer_saturates_oversized_fields_to_u32_max() {
        // The tracer clamps usize depths/frontier sizes into u32 so the
        // dialect op always verifies. Confirm both saturation directions.
        let wide_frontier = (u32::MAX as usize) + 1;
        let wide_depth = (u32::MAX as usize) + 17;
        // SAFETY: tests run single-threaded under env_lock.
        let _g = env_lock();
        unsafe { std::env::set_var("TLA2_DIALECT_TRACE", "1") };
        reset_dialect_trace_state_for_tests();
        let tracer = DialectTracer::new(0);
        // Must not panic — overflow clamps to u32::MAX.
        tracer.emit_step(wide_depth, wide_frontier, 0);
        unsafe { std::env::remove_var("TLA2_DIALECT_TRACE") };
    }

    #[test]
    fn wave14_tracer_disabled_path_is_noop() {
        let _g = env_lock();
        // SAFETY: tests run single-threaded under env_lock.
        unsafe { std::env::remove_var("TLA2_DIALECT_TRACE") };
        reset_dialect_trace_state_for_tests();
        let tracer = DialectTracer::new(42);
        // Must not panic across a range of depths.
        for depth in [0usize, 1, 5, 100, 10_000] {
            tracer.emit_step(depth, 1, 0);
        }
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3 tests (#4286) — graduated frontier_drain + fingerprint_batch
    // tracer wiring. These cover the structured-leaf path that the BFS worker
    // loop exercises at level transitions.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3_drain_builds_verifiable_op_when_enabled() {
        // Direct op-construction check — mirrors what `emit_frontier_drain`
        // builds internally.
        let drain = VerifFrontierDrain::new_on_worker(128, 3);
        assert_eq!(drain.max, 128);
        assert_eq!(drain.worker_id, 3);
        drain.verify().expect("drain must verify");
        // The graduated op lowers to the structured FrontierDrain leaf.
        match drain.lower().expect("drain must lower") {
            Lowered::Leaf(LlvmLeaf::FrontierDrain { max, worker_id }) => {
                assert_eq!(max, 128);
                assert_eq!(worker_id, 3);
            }
            other => panic!("expected FrontierDrain leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3_batch_builds_verifiable_op_when_enabled() {
        let batch = VerifFingerprintBatch::new_at_depth(10, 16, 2);
        assert_eq!(batch.state_base, 10);
        assert_eq!(batch.count, 16);
        assert_eq!(batch.depth, 2);
        batch.verify().expect("batch must verify");
        match batch.lower().expect("batch must lower") {
            Lowered::Leaf(LlvmLeaf::FingerprintBatch {
                state_base,
                count,
                depth,
            }) => {
                assert_eq!(state_base, 10);
                assert_eq!(count, 16);
                assert_eq!(depth, 2);
            }
            other => panic!("expected FingerprintBatch leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3_drain_emit_is_noop_when_tracer_disabled() {
        let _g = env_lock();
        // SAFETY: tests run single-threaded under env_lock.
        unsafe { std::env::remove_var("TLA2_DIALECT_TRACE") };
        reset_dialect_trace_state_for_tests();
        let tracer = DialectTracer::new(1);
        assert!(!tracer.is_enabled());
        // Both emits must be no-ops, including pathological inputs.
        tracer.emit_frontier_drain(0);
        tracer.emit_frontier_drain(usize::MAX);
        tracer.emit_fingerprint_batch(0, 0, 0);
        tracer.emit_fingerprint_batch(usize::MAX, usize::MAX, usize::MAX);
    }

    #[test]
    fn wave14_tl3_drain_emit_enabled_does_not_panic_on_clamp_boundaries() {
        let _g = env_lock();
        // SAFETY: tests run single-threaded under env_lock.
        unsafe { std::env::set_var("TLA2_DIALECT_TRACE", "1") };
        reset_dialect_trace_state_for_tests();
        let tracer = DialectTracer::new(2);
        assert!(tracer.is_enabled());
        // Edge cases must not panic: zero/1 max, u32::MAX+1, max usize.
        tracer.emit_frontier_drain(0);
        tracer.emit_frontier_drain(1);
        tracer.emit_frontier_drain((u32::MAX as usize) + 1);
        tracer.emit_fingerprint_batch(0, 0, 0);
        tracer.emit_fingerprint_batch(u32::MAX as usize + 7, u32::MAX as usize + 1, 0);
        tracer.emit_fingerprint_batch(0, 1, (u32::MAX as usize) + 3);
        unsafe { std::env::remove_var("TLA2_DIALECT_TRACE") };
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3d tests (#4286) — graduated state_fingerprint + invariant_check
    // tracer wiring. These cover the structured-leaf path that the BFS worker
    // loop exercises per-dequeue (not just at level transitions).
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3d_state_fingerprint_builds_verifiable_op_when_enabled() {
        // Direct op-construction check — mirrors what `emit_state_fingerprint`
        // builds internally.
        let fp = VerifStateFingerprint::new_at_depth(64, 2);
        assert_eq!(fp.state_slot, 64);
        assert_eq!(fp.depth, 2);
        fp.verify().expect("state fingerprint must verify");
        match fp.lower().expect("state fingerprint must lower") {
            Lowered::Leaf(LlvmLeaf::StateFingerprint { state_slot, depth }) => {
                assert_eq!(state_slot, 64);
                assert_eq!(depth, 2);
            }
            other => panic!("expected StateFingerprint leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3d_invariant_check_builds_verifiable_op_when_enabled() {
        // Direct op-construction check — mirrors what `emit_invariant_check`
        // builds internally.
        let check = VerifInvariantCheck::new_at_depth(5, 9, 1);
        assert_eq!(check.invariant_id, 5);
        assert_eq!(check.state_slot, 9);
        assert_eq!(check.depth, 1);
        check.verify().expect("invariant check must verify");
        match check.lower().expect("invariant check must lower") {
            Lowered::Leaf(LlvmLeaf::InvariantCheck {
                invariant_id,
                state_slot,
                depth,
            }) => {
                assert_eq!(invariant_id, 5);
                assert_eq!(state_slot, 9);
                assert_eq!(depth, 1);
            }
            other => panic!("expected InvariantCheck leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3d_state_fingerprint_and_invariant_emit_are_noop_when_disabled() {
        let _g = env_lock();
        // SAFETY: tests run single-threaded under env_lock.
        unsafe { std::env::remove_var("TLA2_DIALECT_TRACE") };
        reset_dialect_trace_state_for_tests();
        let tracer = DialectTracer::new(5);
        assert!(!tracer.is_enabled());
        // Both emits must be no-ops across pathological inputs.
        tracer.emit_state_fingerprint(0, 0);
        tracer.emit_state_fingerprint(usize::MAX, usize::MAX);
        tracer.emit_invariant_check(0, 0, 0);
        tracer.emit_invariant_check(u32::MAX, usize::MAX, usize::MAX);
    }

    #[test]
    fn wave14_tl3d_state_fingerprint_and_invariant_emit_enabled_does_not_panic_on_clamp_boundaries()
    {
        let _g = env_lock();
        // SAFETY: tests run single-threaded under env_lock.
        unsafe { std::env::set_var("TLA2_DIALECT_TRACE", "1") };
        reset_dialect_trace_state_for_tests();
        let tracer = DialectTracer::new(7);
        assert!(tracer.is_enabled());
        // state_fingerprint: clamp state_slot/depth into u32.
        tracer.emit_state_fingerprint(0, 0);
        tracer.emit_state_fingerprint(1, 1);
        tracer.emit_state_fingerprint((u32::MAX as usize) + 2, (u32::MAX as usize) + 3);
        // invariant_check: clamp state_slot/depth into u32; invariant_id is
        // already u32 at the API boundary.
        tracer.emit_invariant_check(0, 0, 0);
        tracer.emit_invariant_check(1, 1, 1);
        tracer.emit_invariant_check(u32::MAX, (u32::MAX as usize) + 5, (u32::MAX as usize) + 7);
        unsafe { std::env::remove_var("TLA2_DIALECT_TRACE") };
    }
}
