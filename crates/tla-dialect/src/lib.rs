// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! # tla-dialect — progressive lowering framework for TLA2 / LLVM2
//!
//! This crate is the skeleton for the multi-dialect lowering tower planned in
//! [`designs/2026-04-19-llvm2-dialect-framework.md`](../../../designs/2026-04-19-llvm2-dialect-framework.md)
//! (epic #4251, issue #4253).
//!
//! Today `tla-llvm2` consumes `tmir::Module` produced by `tla-tmir` directly
//! from TLA+ bytecode. There is no intermediate IR that names *verification*
//! concepts (states, actions, fingerprints, invariants, frontiers). MLIR
//! demonstrated that a tower of dialects, each lowering to the next, enables
//! verification-aware optimization and backend pluggability.
//!
//! This crate defines the **framework** — the `DialectOp` trait, the
//! `Dialect` trait, a `DialectPass` + `PassManager`, and two toy dialects:
//! `tla::` (TLA+ operators) and `verif::` (verification primitives). It does
//! NOT rewire any existing lowering paths. Those migrations happen in
//! follow-up issues filed under the epic.
//!
//! # Architecture
//!
//! ```text
//!     tla::   (TLA+ operators: TlaInit, TlaAction, TlaInvariant, ...)
//!       |  TlaToVerifPass
//!       v
//!     verif:: (verification primitives: VerifBfsStep, VerifStateFingerprint, ...)
//!       |  VerifToLlvmPass
//!       v
//!     LlvmLeaf (terminal — consumed by tla-llvm2 in a follow-up)
//! ```
//!
//! # Scope
//!
//! - Framework traits only. No tMIR or LLVM IR emission.
//! - One end-to-end concrete path: `TlaInit` → `VerifBfsStep` → `LlvmLeaf`.
//! - All other ops are stubs that pin the namespace.
//!
//! See the design doc for the full plan and the non-goals list.

#![forbid(unsafe_code)]

pub mod interface;
mod pass;
pub mod tla;
pub mod verif;

pub use interface::{
    is_gpu_eligible, op_is_gpu_eligible, Capabilities, Divergence, DivergenceClass,
    HasCapabilities, HasParallelism, Pure,
};
pub use pass::{PassManager, TlaToVerifPass, VerifToLlvmPass};

use thiserror::Error;

// -----------------------------------------------------------------------------
// Error type
// -----------------------------------------------------------------------------

/// Errors produced by dialect verification and lowering.
///
/// Kept intentionally small. Individual dialects may attach more context via
/// the `message` field on `VerifyFailed` / `LoweringFailed`.
#[derive(Debug, Error)]
pub enum DialectError {
    /// Op failed its structural verification predicate.
    #[error("dialect `{dialect}` op `{op}` verify failed: {message}")]
    VerifyFailed {
        dialect: &'static str,
        op: &'static str,
        message: String,
    },
    /// Op could not be lowered — typically because it's a stub in the skeleton
    /// or because lowering hasn't been wired yet.
    #[error("dialect `{dialect}` op `{op}` lowering failed: {message}")]
    LoweringFailed {
        dialect: &'static str,
        op: &'static str,
        message: String,
    },
    /// A pass was asked to consume ops from the wrong dialect.
    #[error("pass expected dialect `{expected}` but received op from `{actual}`")]
    DialectMismatch {
        expected: &'static str,
        actual: &'static str,
    },
    /// Op doesn't have a concrete implementation in the skeleton yet.
    #[error("dialect `{dialect}` op `{op}` is not yet implemented (skeleton stub)")]
    NotImplemented {
        dialect: &'static str,
        op: &'static str,
    },
}

// -----------------------------------------------------------------------------
// Op kind and leaf
// -----------------------------------------------------------------------------

/// Coarse categorization of dialect ops for routing / dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpKind {
    /// Pure expression — no state side-effects.
    Expression,
    /// State-producing or state-observing op.
    StateTransform,
    /// Verification assertion / predicate check.
    Invariant,
    /// Control flow (branch, sequence, loop).
    Control,
}

/// A terminal-dialect leaf — represents the boundary between `verif::` and the
/// concrete backend (initially `tla-llvm2`, future: GPU shader emitter, WASM,
/// etc.).
///
/// Most ops still lower to the placeholder [`LlvmLeaf::Todo`] variant, which
/// carries a debug tag only. Graduated ops (see [`FrontierDrain`] and
/// [`FingerprintBatch`]) lower to structured variants that carry every field
/// the backend needs to emit real code — no re-parsing of a debug tag.
///
/// # Graduation pattern
///
/// An op is "graduated" when:
/// 1. Its `verif::` struct carries enough structured fields to emit real code.
/// 2. Its `lower()` produces a structured [`LlvmLeaf`] variant (not `Todo`).
/// 3. At least one production consumer (e.g. the BFS worker loop via
///    `TLA2_DIALECT_TRACE=1`) constructs and [`DialectOp::verify`]s it on the
///    live code path.
///
/// Part of epic #4251 / issue #4286.
///
/// [`FrontierDrain`]: LlvmLeaf::FrontierDrain
/// [`FingerprintBatch`]: LlvmLeaf::FingerprintBatch
/// [`StateFingerprint`]: LlvmLeaf::StateFingerprint
/// [`InvariantCheck`]: LlvmLeaf::InvariantCheck
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LlvmLeaf {
    /// Placeholder leaf — carries an operation tag for debugging only.
    /// Real backends will replace `Todo` with structured emit records.
    Todo(&'static str),
    /// Graduated lowering of [`crate::verif::VerifFrontierDrain`]. The
    /// backend emits a bounded pop-loop over the BFS frontier queue that
    /// dequeues up to `max` states on worker lane `worker_id`.
    ///
    /// - `max`: upper bound on dequeues per drain. `0` is forbidden by the
    ///   `verif::` op's `verify()`; the leaf inherits that invariant.
    /// - `worker_id`: zero-based BFS worker lane. Single-threaded BFS emits
    ///   `0`; parallel BFS routes the crossbeam-deque worker index.
    FrontierDrain {
        /// Maximum number of states to drain in one op (>= 1).
        max: u32,
        /// Zero-based worker lane id.
        worker_id: u32,
    },
    /// Graduated lowering of [`crate::verif::VerifFingerprintBatch`]. The
    /// backend emits a vectorized / SIMD-unrolled fingerprint kernel call over
    /// the contiguous state slab `[state_base, state_base + count)` tagged
    /// with `depth` (the BFS level at which the batch was produced).
    ///
    /// - `state_base`: inclusive base index of the state slab.
    /// - `count`: number of states in the batch. `0` is forbidden by the
    ///   `verif::` op's `verify()`; the leaf inherits that invariant.
    /// - `depth`: BFS depth (TLC level). `0` = Init-produced seed level.
    FingerprintBatch {
        /// Base state slot (inclusive).
        state_base: u32,
        /// Number of states in the batch (>= 1).
        count: u32,
        /// BFS depth of the batch.
        depth: u32,
    },
    /// Graduated lowering of [`crate::verif::VerifStateFingerprint`]. The
    /// backend emits a single-state fingerprint kernel call over the state at
    /// `state_slot`, tagged with `depth` (the BFS level at which the state
    /// was observed). Unlike [`LlvmLeaf::FingerprintBatch`] (which is a
    /// vectorized slab over `count` states), this leaf is a scalar
    /// per-state kernel — the point-wise per-dequeue counterpart.
    ///
    /// - `state_slot`: slot index of the state slab to fingerprint.
    /// - `depth`: BFS depth (TLC level) at which the state was observed.
    ///   `0` = Init-produced seed level.
    StateFingerprint {
        /// Slot index of the state slab to fingerprint.
        state_slot: u32,
        /// BFS depth (TLC level) at which the fingerprint was computed.
        depth: u32,
    },
    /// Graduated lowering of [`crate::verif::VerifInvariantCheck`]. The
    /// backend emits a call to the compiled invariant predicate
    /// `invariant_id` against the state at `state_slot`, tagged with
    /// `depth` for trace/debug attribution. A failing check is reported
    /// by the backend as a violation + counterexample trace; the leaf
    /// itself has no value (check-only).
    ///
    /// - `invariant_id`: stable id of the invariant being checked.
    /// - `state_slot`: slot index of the state slab to check.
    /// - `depth`: BFS depth (TLC level) at which the check was run.
    InvariantCheck {
        /// Stable id of the invariant being checked.
        invariant_id: u32,
        /// Slot index of the state slab to check.
        state_slot: u32,
        /// BFS depth (TLC level) at which the check was run.
        depth: u32,
    },
    /// Graduated lowering of [`crate::verif::VerifActionEval`]. The
    /// backend emits a call to the compiled action evaluator for
    /// `action_id` against the source state at `source_slot`, tagged
    /// with `depth` and `worker_id` for trace/debug attribution. The
    /// evaluator expands the source state into zero or more successor
    /// states (enumerated by TLC-style successor expansion); the leaf
    /// itself carries no successor count — backends resolve expansion
    /// through the action's compiled bytecode.
    ///
    /// - `action_id`: stable id of the TLA+ action being evaluated. `0`
    ///   is reserved for Init (seed-level) evaluation; Next-level
    ///   evaluators use ids `>= 1`.
    /// - `source_slot`: slot index of the source state slab that drives
    ///   the evaluator.
    /// - `depth`: BFS depth (TLC level) at which the evaluator ran.
    ///   `0` = Init-produced seed level.
    /// - `worker_id`: zero-based BFS worker lane id.
    ActionEval {
        /// Stable id of the action being evaluated (`0` reserved for Init).
        action_id: u32,
        /// Slot index of the source state driving evaluation.
        source_slot: u32,
        /// BFS depth (TLC level) at which the evaluator ran.
        depth: u32,
        /// Zero-based BFS worker lane id.
        worker_id: u32,
    },
    /// Graduated lowering of [`crate::verif::VerifEnabledCheck`]. The
    /// backend emits a call to the compiled `ENABLED A` predicate for
    /// action `action_id` against the state at `state_slot`, tagged
    /// with `depth` for trace/debug attribution. Unlike
    /// [`LlvmLeaf::InvariantCheck`] (which aborts on failure), an
    /// ENABLED check is a pure predicate — the result is the value
    /// `TRUE` iff the action has at least one successor.
    ///
    /// - `action_id`: stable id of the action whose enabledness is being
    ///   queried. `0` is forbidden by the `verif::` op's `verify()` (an
    ///   ENABLED check over "Init" is nonsensical — Init always fires).
    /// - `state_slot`: slot index of the state slab to check against.
    /// - `depth`: BFS depth (TLC level) at which the check was run.
    EnabledCheck {
        /// Stable id of the action whose enabledness is queried (>= 1).
        action_id: u32,
        /// Slot index of the state slab to check.
        state_slot: u32,
        /// BFS depth (TLC level) at which the check was run.
        depth: u32,
    },
    /// Graduated lowering of [`crate::verif::VerifBfsStep`]. The backend
    /// emits a BFS-step scheduler record tagged with every field the worker
    /// loop tracks at dequeue time: seed-vs-expand discriminator, producing
    /// `action_id`, worker lane, frontier width hint, and BFS depth.
    ///
    /// Unlike [`LlvmLeaf::ActionEval`] (which names *which action* to
    /// evaluate against a source state) or [`LlvmLeaf::StateFingerprint`]
    /// (which fingerprints a single state), `BfsStep` is the
    /// worker-loop-boundary record — backends consume a stream of these to
    /// model BFS scheduling (work-stealing lane assignment, frontier
    /// distribution, depth bookkeeping).
    ///
    /// - `kind`: `0` = Seed (Init-produced) / `1` = Expand (Next-produced).
    ///   Encoded as `u8` at the leaf so the record is trivially serializable
    ///   (no external enum dependency from the backend).
    /// - `action_id`: stable id of the producing action. `0` when
    ///   `kind == 0` (seeds have no action dispatch); any value when
    ///   `kind == 1`.
    /// - `worker_id`: zero-based BFS worker lane id.
    /// - `frontier_size`: frontier width hint at emit time (`0` = unknown).
    /// - `depth`: BFS depth (TLC level). `0` when `kind == 0`.
    BfsStep {
        /// `0` = Seed, `1` = Expand. Matches [`crate::verif::BfsKind`]
        /// discriminant order.
        kind: u8,
        /// Stable id of the producing action (`0` for seeds).
        action_id: u32,
        /// Zero-based BFS worker lane id.
        worker_id: u32,
        /// Frontier width hint at emit time (`0` = unknown).
        frontier_size: u32,
        /// BFS depth (TLC level).
        depth: u32,
    },
    /// Graduated lowering of [`crate::verif::VerifScalarInt`]. The backend
    /// emits a 64-bit signed integer immediate. TLA+ integers are
    /// unbounded; the `i64` range is the representable subset at the
    /// `verif::` boundary. Backends that target narrower word widths clamp
    /// or trap at emit time.
    ScalarInt {
        /// The literal value.
        value: i64,
    },
    /// Graduated lowering of [`crate::verif::VerifScalarBool`]. The
    /// backend emits a 1-bit boolean immediate (TLA+ `TRUE` / `FALSE`).
    ScalarBool {
        /// The literal value.
        value: bool,
    },
    /// Graduated lowering of [`crate::verif::VerifStateSuccessors`]. The
    /// backend emits a worker-loop record for the *batch* of successor
    /// states produced by evaluating a single action on a single source
    /// state. This is the companion to [`LlvmLeaf::ActionEval`]: where
    /// `ActionEval` says "call action `A` on source `S`", `StateSuccessors`
    /// describes the *output* of that call — `count` successors enqueued
    /// onto worker `worker_id` at `target_depth`, originating from the
    /// source state at `source_slot`.
    ///
    /// Backends consume `StateSuccessors` to model successor enqueuing:
    /// - The state admission pipeline (dedup + seen-set insertion) runs
    ///   against exactly `count` states.
    /// - Work distribution (work-stealing, frontier partitioning) sees a
    ///   batch of `count` items landing on `worker_id`.
    /// - BFS depth bookkeeping advances from `target_depth - 1`
    ///   (the source's depth) to `target_depth`.
    ///
    /// - `action_id`: stable id of the action that produced the successors.
    ///   `0` is reserved for Init (seed-level enqueue); Next-level
    ///   enqueues use ids `>= 1`.
    /// - `source_slot`: slot index of the source state that was expanded.
    /// - `count`: number of successors produced. `0` is forbidden —
    ///   expanding with zero successors is a disabled-action signal and
    ///   belongs on the separate [`LlvmLeaf::EnabledCheck`] path.
    /// - `target_depth`: BFS depth at which the successors are enqueued.
    ///   `0` would mean "enqueue back at the Init level" which is a
    ///   miswiring — forbidden by the `verif::` op's `verify()`.
    /// - `worker_id`: zero-based BFS worker lane id enqueuing the batch.
    StateSuccessors {
        /// Stable id of the producing action (`0` reserved for Init).
        action_id: u32,
        /// Slot index of the source state that was expanded.
        source_slot: u32,
        /// Number of successors produced (>= 1).
        count: u32,
        /// BFS depth at which successors are enqueued (>= 1).
        target_depth: u32,
        /// Zero-based BFS worker lane id enqueuing the batch.
        worker_id: u32,
    },
    /// Graduated lowering of [`crate::verif::VerifIntAdd`]. Linear-sequence
    /// marker for integer addition — the top two values on the evaluation
    /// stack are the operands. Target of `tla.add` lowering.
    ///
    /// Unit variant: the Wave 12 ops are linear-sequence markers and carry
    /// no operand fields (see `verif` module docs). Graduation replaces the
    /// decorative `Todo("int_add")` debug tag with a dispatch-ready enum
    /// variant — backends can `match` on it exhaustively.
    IntAdd,
    /// Graduated lowering of [`crate::verif::VerifIntSub`]. Linear-sequence
    /// marker for integer subtraction. Target of `tla.sub` lowering.
    IntSub,
    /// Graduated lowering of [`crate::verif::VerifIntMul`]. Linear-sequence
    /// marker for integer multiplication. Target of `tla.mul` lowering.
    IntMul,
    /// Graduated lowering of [`crate::verif::VerifIntDiv`]. Linear-sequence
    /// marker for Euclidean integer division. Target of `tla.div` lowering.
    IntDiv,
    /// Graduated lowering of [`crate::verif::VerifIntMod`]. Linear-sequence
    /// marker for Euclidean integer modulus. Target of `tla.mod` lowering.
    IntMod,
    /// Graduated lowering of [`crate::verif::VerifIntLt`]. Linear-sequence
    /// marker for integer less-than comparison. Target of `tla.lt` lowering.
    IntLt,
    /// Graduated lowering of [`crate::verif::VerifIntLe`]. Linear-sequence
    /// marker for integer less-or-equal comparison. Target of `tla.le`
    /// lowering.
    IntLe,
    /// Graduated lowering of [`crate::verif::VerifIntGt`]. Linear-sequence
    /// marker for integer greater-than comparison. Target of `tla.gt`
    /// lowering.
    IntGt,
    /// Graduated lowering of [`crate::verif::VerifIntGe`]. Linear-sequence
    /// marker for integer greater-or-equal comparison. Target of `tla.ge`
    /// lowering.
    IntGe,
    /// Graduated lowering of [`crate::verif::VerifIntEq`]. Linear-sequence
    /// marker for integer equality comparison. Target of `tla.eq` lowering
    /// when both operands are integer-typed.
    IntEq,
    /// Graduated lowering of [`crate::verif::VerifBoolAnd`]. Linear-sequence
    /// marker for boolean conjunction. Target of `tla.and` lowering.
    BoolAnd,
    /// Graduated lowering of [`crate::verif::VerifBoolOr`]. Linear-sequence
    /// marker for boolean disjunction. Target of `tla.or` lowering.
    BoolOr,
    /// Graduated lowering of [`crate::verif::VerifBoolNot`]. Linear-sequence
    /// marker for boolean negation. Target of `tla.not` lowering.
    BoolNot,
}

/// The result of lowering a single `DialectOp`.
#[derive(Debug)]
pub enum Lowered {
    /// The op decomposes into a sequence of next-dialect ops.
    Ops(Vec<Box<dyn DialectOp>>),
    /// The op is at the terminal boundary and produces a concrete leaf.
    Leaf(LlvmLeaf),
}

// -----------------------------------------------------------------------------
// Core traits
// -----------------------------------------------------------------------------

/// Common interface for every op in every dialect.
///
/// The trait is deliberately small. We resist MLIR-completeness — this is a
/// pragmatic skeleton, not a general-purpose compiler IR toolkit.
pub trait DialectOp: std::fmt::Debug + Send + Sync {
    /// The dialect this op belongs to. Matches [`Dialect::name`].
    fn dialect(&self) -> &'static str;

    /// The op's mnemonic, e.g. `"tla.init"`, `"verif.bfs_step"`.
    fn op_name(&self) -> &'static str;

    /// Coarse category. Used by pass routers.
    fn kind(&self) -> OpKind;

    /// Structural verification. Checks invariants that must hold for the op to
    /// be well-formed *in isolation*. Cross-op or cross-module checks belong
    /// in dialect-level passes, not here.
    fn verify(&self) -> Result<(), DialectError>;

    /// Lower to zero or more ops in the next dialect down the tower.
    fn lower(&self) -> Result<Lowered, DialectError>;
}

/// A registered dialect. Provides the name and list of op mnemonics, with an
/// optional fold hook for per-dialect rewriting during passes.
pub trait Dialect {
    /// The dialect name. Must match `DialectOp::dialect()` for every op in
    /// this dialect.
    fn name(&self) -> &'static str;

    /// List of op mnemonics owned by this dialect. Used for registration and
    /// documentation.
    fn op_names(&self) -> &'static [&'static str];

    /// Optional fold hook. Returns `Some(replacement)` to rewrite the op
    /// in-place during pass execution, or `None` to leave it unchanged.
    fn fold(&self, op: &dyn DialectOp) -> Option<Box<dyn DialectOp>> {
        let _ = op;
        None
    }
}

// -----------------------------------------------------------------------------
// Tests: trait contract
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_kind_is_hashable_and_copy() {
        let a = OpKind::Expression;
        let b = a;
        assert_eq!(a, b);

        // Use in a HashMap to confirm Hash derive works.
        use std::collections::HashSet;
        let mut s = HashSet::new();
        s.insert(OpKind::Invariant);
        s.insert(OpKind::Invariant);
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn dialect_error_display_mentions_dialect_and_op() {
        let e = DialectError::VerifyFailed {
            dialect: "tla",
            op: "tla.init",
            message: "state_vars empty".into(),
        };
        let msg = format!("{e}");
        assert!(msg.contains("tla"));
        assert!(msg.contains("tla.init"));
        assert!(msg.contains("state_vars empty"));
    }

    #[test]
    fn lowered_leaf_variant_round_trips() {
        // Wave 14 TL3h: all Wave 12 expression ops (int_add, int_sub,
        // int_mul, int_div, int_mod, int_lt/le/gt/ge/eq, bool_and/or/not)
        // are now graduated to structured `LlvmLeaf` unit variants — no
        // production path lowers to `LlvmLeaf::Todo(...)` anymore. The
        // `Todo` variant is kept as an escape hatch for future
        // placeholder-only ops; this test exercises it as a pure
        // round-trip check on the enum itself.
        let lowered = Lowered::Leaf(LlvmLeaf::Todo("placeholder_sentinel"));
        match lowered {
            Lowered::Leaf(LlvmLeaf::Todo(tag)) => assert_eq!(tag, "placeholder_sentinel"),
            _ => panic!("expected leaf"),
        }
    }

    #[test]
    fn wave14_tl3g_graduated_leaves_carry_structured_fields() {
        // Canonical round-trip smoke test for all TL3g graduated leaves —
        // each one exposes its full field set via pattern match (no Todo
        // placeholder).
        let bfs = LlvmLeaf::BfsStep {
            kind: 1,
            action_id: 7,
            worker_id: 2,
            frontier_size: 128,
            depth: 3,
        };
        match bfs {
            LlvmLeaf::BfsStep {
                kind,
                action_id,
                worker_id,
                frontier_size,
                depth,
            } => {
                assert_eq!(kind, 1);
                assert_eq!(action_id, 7);
                assert_eq!(worker_id, 2);
                assert_eq!(frontier_size, 128);
                assert_eq!(depth, 3);
            }
            _ => panic!("expected BfsStep leaf"),
        }
        match (LlvmLeaf::ScalarInt { value: -42 }) {
            LlvmLeaf::ScalarInt { value } => assert_eq!(value, -42),
            _ => panic!("expected ScalarInt leaf"),
        }
        match (LlvmLeaf::ScalarBool { value: true }) {
            LlvmLeaf::ScalarBool { value } => assert!(value),
            _ => panic!("expected ScalarBool leaf"),
        }
        match (LlvmLeaf::StateSuccessors {
            action_id: 1,
            source_slot: 9,
            count: 4,
            target_depth: 2,
            worker_id: 0,
        }) {
            LlvmLeaf::StateSuccessors {
                action_id,
                source_slot,
                count,
                target_depth,
                worker_id,
            } => {
                assert_eq!(action_id, 1);
                assert_eq!(source_slot, 9);
                assert_eq!(count, 4);
                assert_eq!(target_depth, 2);
                assert_eq!(worker_id, 0);
            }
            _ => panic!("expected StateSuccessors leaf"),
        }
    }
}
