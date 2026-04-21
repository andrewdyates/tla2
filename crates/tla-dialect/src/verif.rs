// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `verif::` dialect — verification primitives.
//!
//! Ops at this level express verification concepts independent of TLA+
//! surface syntax: a BFS step, a fingerprint computation, an invariant
//! check. They form the boundary between "what TLA+ means" (the `tla::`
//! dialect above) and "what the backend emits" (LLVM IR / GPU shader /
//! WASM below).
//!
//! # Skeleton contents
//!
//! - [`VerifBfsStep`] — concrete, lowers to a terminal [`LlvmLeaf`].
//! - Wave 12 expression ops — graduated Wave 14 TL3h to structured
//!   [`LlvmLeaf`] variants (no `Todo` placeholders remain in production
//!   lowering):
//!   - [`VerifScalarInt`], [`VerifScalarBool`] — literal expressions
//!     (graduated Wave 14 TL3g with value fields).
//!   - [`VerifIntAdd`], [`VerifIntSub`], [`VerifIntMul`], [`VerifIntDiv`],
//!     [`VerifIntMod`] — integer arithmetic (unit-variant leaves
//!     [`LlvmLeaf::IntAdd`], [`LlvmLeaf::IntSub`], etc.).
//!   - [`VerifIntLt`], [`VerifIntLe`], [`VerifIntGt`], [`VerifIntGe`],
//!     [`VerifIntEq`] — integer comparison (unit-variant leaves).
//!   - [`VerifBoolAnd`], [`VerifBoolOr`], [`VerifBoolNot`] — boolean ops
//!     (unit-variant leaves [`LlvmLeaf::BoolAnd`], [`LlvmLeaf::BoolOr`],
//!     [`LlvmLeaf::BoolNot`]).
//! - Wave 13 verification primitives (graduated — each lowers to its own
//!   structured [`LlvmLeaf`] variant carrying real fields, not a `Todo`
//!   placeholder):
//!   - [`VerifStateFingerprint`] — compute a 64-bit state fingerprint
//!     (target of `tla.fingerprint` lowering). Graduated Wave 14 TL3d
//!     with a BFS `depth` field to
//!     [`LlvmLeaf::StateFingerprint`](crate::LlvmLeaf::StateFingerprint).
//!   - [`VerifInvariantCheck`] — assert an invariant over the current state
//!     (target of `tla.invariant` lowering). Graduated Wave 14 TL3d with
//!     `state_slot` + `depth` fields to
//!     [`LlvmLeaf::InvariantCheck`](crate::LlvmLeaf::InvariantCheck).
//!   - [`VerifFrontierDrain`] — pull up to `max` states from the BFS frontier
//!     (the unit of work for a BFS worker thread). Pins the namespace asked
//!     for in mail LLVM2#4268. Graduated Wave 14 TL3 to
//!     [`LlvmLeaf::FrontierDrain`](crate::LlvmLeaf::FrontierDrain).
//!   - [`VerifFingerprintBatch`] — batched fingerprint computation over a
//!     slab of states. Pins the namespace asked for in mail LLVM2#4268.
//!     Graduated Wave 14 TL3 to
//!     [`LlvmLeaf::FingerprintBatch`](crate::LlvmLeaf::FingerprintBatch).
//!
//! # Wave 12 op shape (linear-sequence convention)
//!
//! The Wave 12 binary/unary expression ops ([`VerifIntAdd`], etc.) are
//! *markers* in the flat `Lowered::Ops` sequence — they do not carry their
//! operand fields as structured children. The sequence itself is the source
//! of truth: an `Lowered::Ops(vec![L1, ..., Ln, R1, ..., Rm, VerifIntAdd])`
//! means "compute the left subtree, compute the right subtree, take the sum".
//! This matches the linear-bytecode shape that real `verif::` → LLVM lowering
//! will produce. Per-op operand fields stay at the `tla::` level, where
//! they're structurally useful for verify().
//!
//! Migration of the real `tla-llvm2` emit paths into these ops is follow-up
//! work under epic #4251.

use crate::{
    interface::{Capabilities, Divergence, DivergenceClass, HasCapabilities, HasParallelism, Pure},
    Dialect, DialectError, DialectOp, LlvmLeaf, Lowered, OpKind,
};

/// The name of this dialect.
pub const DIALECT_NAME: &str = "verif";

/// The op mnemonics owned by this dialect.
pub const OP_NAMES: &[&str] = &[
    "verif.bfs_step",
    "verif.state_fingerprint",
    "verif.invariant_check",
    "verif.frontier_drain",
    "verif.fingerprint_batch",
    "verif.action_eval",
    "verif.enabled_check",
    "verif.state_successors",
    "verif.scalar_int",
    "verif.scalar_bool",
    "verif.int_add",
    "verif.int_sub",
    "verif.int_mul",
    "verif.int_div",
    "verif.int_mod",
    "verif.int_lt",
    "verif.int_le",
    "verif.int_gt",
    "verif.int_ge",
    "verif.int_eq",
    "verif.bool_and",
    "verif.bool_or",
    "verif.bool_not",
];

/// Registration struct for the `verif::` dialect.
#[derive(Debug, Default, Clone, Copy)]
pub struct VerifDialect;

impl Dialect for VerifDialect {
    fn name(&self) -> &'static str {
        "verif"
    }
    fn op_names(&self) -> &'static [&'static str] {
        OP_NAMES
    }
}

// -----------------------------------------------------------------------------
// BfsKind
// -----------------------------------------------------------------------------

/// Discriminator for `VerifBfsStep`. The skeleton distinguishes the initial
/// seed step (from `Init`) from the expansion step (from `Next`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BfsKind {
    /// Seed an initial state — produced from `tla::TlaInit` lowering.
    Seed,
    /// Expand a frontier state along one action — produced from
    /// `tla::TlaAction` lowering (not wired in the skeleton).
    Expand,
}

// -----------------------------------------------------------------------------
// Concrete: VerifBfsStep (Wave 14 graduation)
// -----------------------------------------------------------------------------

/// A single BFS step at the `verif::` level.
///
/// # Fields
///
/// - `kind`: [`BfsKind::Seed`] (an Init-produced initial state) vs
///   [`BfsKind::Expand`] (a Next-produced successor state).
/// - `action_id`: stable id of the TLA+ action that produced the successor.
///   For [`BfsKind::Seed`], `action_id` must be `0` (Init has no action
///   dispatch); for [`BfsKind::Expand`], any value is allowed.
/// - `worker_id`: zero-based worker lane id. Single-threaded BFS uses `0`;
///   parallel BFS uses the crossbeam-deque worker index.
/// - `frontier_size`: size of the BFS frontier at the moment this step was
///   emitted. Used by backend schedulers for load balancing; `0` is a valid
///   hint meaning "frontier size unknown / not tracked".
/// - `depth`: BFS depth (TLC level) of the state being processed. Depth is
///   bounded by the spec's reachable state graph diameter; `0` is the Init
///   level.
///
/// # Verification rules
///
/// - [`BfsKind::Seed`] requires `action_id == 0` (Init has no action dispatch).
/// - [`BfsKind::Seed`] requires `depth == 0` (seeds are the BFS root level).
///
/// # Graduation history
///
/// - **Wave 11**: stub — only `kind` and `action_id`.
/// - **Wave 14**: added `worker_id`, `frontier_size`, `depth`; added
///   [`VerifBfsStep::new_seed`] + [`VerifBfsStep::new_expand`] constructors;
///   tightened `verify()` with a seed-depth check; wired into `tla-check`
///   BFS worker loop via the [`crate`] `TLA2_DIALECT_TRACE=1` env hook.
#[derive(Debug, Clone, Copy)]
pub struct VerifBfsStep {
    /// Seed (Init-produced) vs Expand (Next-produced) discriminator.
    pub kind: BfsKind,
    /// Stable id of the action that produced this step. `0` for seeds.
    pub action_id: u32,
    /// Worker lane id (0 for single-threaded; parallel BFS worker index).
    pub worker_id: u32,
    /// Frontier size at the moment this step was emitted (`0` = unknown).
    pub frontier_size: u32,
    /// BFS depth (TLC level) of the state being processed (`0` for seeds).
    pub depth: u32,
}

impl Default for VerifBfsStep {
    /// Default is a seed step on worker 0 with unknown frontier size at
    /// depth 0. Useful for tests that only care about the op's trait
    /// metadata and want the remaining fields via `..Default::default()`
    /// struct-update syntax.
    fn default() -> Self {
        Self {
            kind: BfsKind::Seed,
            action_id: 0,
            worker_id: 0,
            frontier_size: 0,
            depth: 0,
        }
    }
}

impl VerifBfsStep {
    /// Build a [`BfsKind::Seed`] step. `action_id` and `depth` are implicitly
    /// `0`; `worker_id` and `frontier_size` are caller-supplied.
    #[must_use]
    pub fn new_seed(worker_id: u32, frontier_size: u32) -> Self {
        Self {
            kind: BfsKind::Seed,
            action_id: 0,
            worker_id,
            frontier_size,
            depth: 0,
        }
    }

    /// Build a [`BfsKind::Expand`] step for the given action at the given
    /// worker/frontier/depth.
    #[must_use]
    pub fn new_expand(action_id: u32, worker_id: u32, frontier_size: u32, depth: u32) -> Self {
        Self {
            kind: BfsKind::Expand,
            action_id,
            worker_id,
            frontier_size,
            depth,
        }
    }
}

impl DialectOp for VerifBfsStep {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.bfs_step"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if matches!(self.kind, BfsKind::Seed) {
            if self.action_id != 0 {
                return Err(DialectError::VerifyFailed {
                    dialect: "verif",
                    op: "verif.bfs_step",
                    message: format!("Seed step must have action_id == 0, got {}", self.action_id),
                });
            }
            if self.depth != 0 {
                return Err(DialectError::VerifyFailed {
                    dialect: "verif",
                    op: "verif.bfs_step",
                    message: format!("Seed step must have depth == 0, got {}", self.depth),
                });
            }
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        // Wave 14 TL3g (#4286): graduated to structured leaf carrying every
        // field. `kind` is encoded as a u8 (0 = Seed, 1 = Expand) so the
        // leaf is serializable without the `BfsKind` enum dependency. The
        // encoding matches `BfsKind`'s declaration order — changing the
        // enum without updating this match is a compile error (fully
        // covered by the match exhaustiveness check).
        let kind = match self.kind {
            BfsKind::Seed => 0u8,
            BfsKind::Expand => 1u8,
        };
        Ok(Lowered::Leaf(LlvmLeaf::BfsStep {
            kind,
            action_id: self.action_id,
            worker_id: self.worker_id,
            frontier_size: self.frontier_size,
            depth: self.depth,
        }))
    }
}

// Op interface capabilities (TL25 Wave 14 — Part of #4253).
//
// `VerifBfsStep` is the worker-loop boundary record — it ORDERS the BFS
// pipeline (seed vs expand, worker lane assignment, depth bookkeeping). It
// is NOT `Pure` (records scheduling side effects) and NOT
// `HasParallelism` (each step is serial within its worker lane). Divergence
// is `High` because seed/expand branching per worker is arbitrary. Result:
// NOT GPU-eligible — stays on the scalar scheduler path.
impl DivergenceClass for VerifBfsStep {
    fn divergence(&self) -> Divergence {
        Divergence::High
    }
}
impl HasCapabilities for VerifBfsStep {
    fn capabilities(&self) -> Capabilities {
        Capabilities::none().with_divergence(self.divergence())
    }
}

// -----------------------------------------------------------------------------
// Wave 12: scalar literal expression ops.
// -----------------------------------------------------------------------------

/// Integer literal expression — the Wave 12 target of an integer-typed
/// [`crate::tla::TlaVarRef`] lowering. The surface name of the variable is
/// not preserved in the literal (Wave 12 is a kickoff — a future wave will
/// add `VerifVarLoad { slot }` or similar for real variable slots).
///
/// # Verification rules
///
/// No structural invariants — every i64 is a valid literal.
#[derive(Debug, Clone, Copy)]
pub struct VerifScalarInt {
    pub value: i64,
}

impl VerifScalarInt {
    /// Construct a new integer-literal op.
    #[must_use]
    pub fn new(value: i64) -> Self {
        Self { value }
    }
}

impl DialectOp for VerifScalarInt {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.scalar_int"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        // Wave 14 TL3g (#4286): graduated to structured leaf carrying the
        // literal value. Replaces `LlvmLeaf::Todo("scalar_int")` — the
        // backend now receives the i64 constant directly without re-parsing
        // a debug tag.
        Ok(Lowered::Leaf(LlvmLeaf::ScalarInt { value: self.value }))
    }
}

/// Boolean literal expression — `TRUE` / `FALSE`.
///
/// # Verification rules
///
/// No structural invariants — both boolean values are valid.
#[derive(Debug, Clone, Copy)]
pub struct VerifScalarBool {
    pub value: bool,
}

impl VerifScalarBool {
    /// Construct a new boolean-literal op.
    #[must_use]
    pub fn new(value: bool) -> Self {
        Self { value }
    }
}

impl DialectOp for VerifScalarBool {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.scalar_bool"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        // Wave 14 TL3g (#4286): graduated to structured leaf carrying the
        // literal value. Replaces `LlvmLeaf::Todo("scalar_bool")` — the
        // backend now receives the bool constant directly without re-parsing
        // a debug tag.
        Ok(Lowered::Leaf(LlvmLeaf::ScalarBool { value: self.value }))
    }
}

// -----------------------------------------------------------------------------
// Wave 12: binary `verif::` expression ops — arithmetic + comparison + boolean.
// -----------------------------------------------------------------------------

/// Generates a Wave 12 binary `verif::` expression op as a linear-sequence
/// *marker* — no operand fields. The flat `Lowered::Ops` sequence produced
/// by `tla::` lowering is the source of truth: `[...left_ops, ...right_ops,
/// VerifIntAdd]` means "top two values on the evaluation stack are the
/// operands". See module docs for the linear-sequence convention.
///
/// Wave 14 TL3h (#4286): the macro's `$leaf_variant` parameter names a
/// structured `LlvmLeaf` unit variant (e.g. `IntAdd`, `BoolAnd`) rather
/// than a `Todo("...")` string tag. The backend receives a dispatch-ready
/// enum variant, not a debug string.
macro_rules! binary_verif_op {
    (
        $(#[$outer:meta])*
        $name:ident,
        $mnemonic:literal,
        $leaf_variant:ident
    ) => {
        $(#[$outer])*
        #[derive(Debug, Clone, Copy, Default)]
        pub struct $name;

        impl DialectOp for $name {
            fn dialect(&self) -> &'static str {
                "verif"
            }
            fn op_name(&self) -> &'static str {
                $mnemonic
            }
            fn kind(&self) -> OpKind {
                OpKind::Expression
            }
            fn verify(&self) -> Result<(), DialectError> {
                // No structural fields — always well-formed in isolation. The
                // enclosing pass validates the flat sequence's operand shape.
                Ok(())
            }
            fn lower(&self) -> Result<Lowered, DialectError> {
                // Wave 14 TL3h (#4286): graduated to a structured unit-variant
                // leaf. Replaces `LlvmLeaf::Todo("<tag>")` — the backend now
                // dispatches on an exhaustive enum rather than pattern-matching
                // a debug string.
                Ok(Lowered::Leaf(LlvmLeaf::$leaf_variant))
            }
        }
    };
}

binary_verif_op!(
    /// Integer addition at the `verif::` level. Target of `tla.add` lowering.
    VerifIntAdd,
    "verif.int_add",
    IntAdd
);

binary_verif_op!(
    /// Integer subtraction at the `verif::` level. Target of `tla.sub` lowering.
    VerifIntSub,
    "verif.int_sub",
    IntSub
);

binary_verif_op!(
    /// Integer multiplication at the `verif::` level. Target of `tla.mul` lowering.
    VerifIntMul,
    "verif.int_mul",
    IntMul
);

binary_verif_op!(
    /// Euclidean integer division at the `verif::` level. Target of `tla.div` lowering.
    VerifIntDiv,
    "verif.int_div",
    IntDiv
);

binary_verif_op!(
    /// Euclidean integer modulus at the `verif::` level. Target of `tla.mod` lowering.
    VerifIntMod,
    "verif.int_mod",
    IntMod
);

binary_verif_op!(
    /// Integer less-than comparison at the `verif::` level. Target of `tla.lt` lowering.
    VerifIntLt,
    "verif.int_lt",
    IntLt
);

binary_verif_op!(
    /// Integer less-or-equal comparison at the `verif::` level. Target of `tla.le` lowering.
    VerifIntLe,
    "verif.int_le",
    IntLe
);

binary_verif_op!(
    /// Integer greater-than comparison at the `verif::` level. Target of `tla.gt` lowering.
    VerifIntGt,
    "verif.int_gt",
    IntGt
);

binary_verif_op!(
    /// Integer greater-or-equal comparison at the `verif::` level. Target of `tla.ge` lowering.
    VerifIntGe,
    "verif.int_ge",
    IntGe
);

binary_verif_op!(
    /// Integer equality comparison at the `verif::` level. Target of `tla.eq`
    /// lowering when both operands are integer-typed.
    VerifIntEq,
    "verif.int_eq",
    IntEq
);

binary_verif_op!(
    /// Boolean conjunction at the `verif::` level. Target of `tla.and` lowering.
    VerifBoolAnd,
    "verif.bool_and",
    BoolAnd
);

binary_verif_op!(
    /// Boolean disjunction at the `verif::` level. Target of `tla.or` lowering.
    VerifBoolOr,
    "verif.bool_or",
    BoolOr
);

// -----------------------------------------------------------------------------
// Wave 12: unary `verif::` expression op — `verif.bool_not`.
// -----------------------------------------------------------------------------

/// Boolean negation at the `verif::` level — linear-sequence marker (no
/// operand field). Target of `tla.not` lowering.
#[derive(Debug, Clone, Copy, Default)]
pub struct VerifBoolNot;

impl DialectOp for VerifBoolNot {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.bool_not"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        // Wave 14 TL3h (#4286): graduated to a structured unit-variant
        // leaf. Replaces `LlvmLeaf::Todo("bool_not")` — the backend now
        // dispatches on the exhaustive enum.
        Ok(Lowered::Leaf(LlvmLeaf::BoolNot))
    }
}

// -----------------------------------------------------------------------------
// Wave 13: concrete verification primitives — fingerprint + invariant check +
// frontier drain + fingerprint batch.
// -----------------------------------------------------------------------------

/// Compute a 64-bit fingerprint of the current state. Target of
/// `tla::TlaFingerprint` lowering. The `state_slot` identifies which state
/// slab (by index) to fingerprint; real backends resolve it to a base
/// address + stride at emit time.
///
/// # Fields
///
/// - `state_slot`: slot index of the state slab to fingerprint (any `u32`).
/// - `depth`: BFS depth (TLC level) at which the fingerprint was computed.
///   `0` = Init-produced seed level. Carrying depth at the dialect level lets
///   backends tag fingerprint records with their graph depth without a
///   side-channel lookup — the scalar per-state counterpart of
///   [`VerifFingerprintBatch`]'s `depth` field.
///
/// # Verification rules
///
/// No structural invariants today — every `u32` combination is well-formed.
///
/// # Graduation history (#4286)
///
/// - **Wave 13**: stub — only `state_slot`; lowered to
///   `LlvmLeaf::Todo("state_fingerprint")`.
/// - **Wave 14 TL3d**: added `depth`; added
///   [`VerifStateFingerprint::new_at_depth`] constructor; graduated the
///   lowering to a structured [`LlvmLeaf::StateFingerprint`] leaf carrying
///   both fields; wired into the BFS worker loop `TLA2_DIALECT_TRACE=1` path
///   via `DialectTracer::emit_state_fingerprint`.
#[derive(Debug, Clone, Copy)]
pub struct VerifStateFingerprint {
    /// Slot index of the state slab to fingerprint.
    pub state_slot: u32,
    /// BFS depth (TLC level) at which the fingerprint was computed.
    pub depth: u32,
}

impl VerifStateFingerprint {
    /// Construct a new state-fingerprint op at BFS depth `0` (the Init level).
    /// Equivalent to [`VerifStateFingerprint::new_at_depth`] with `depth = 0`.
    #[must_use]
    pub fn new(state_slot: u32) -> Self {
        Self {
            state_slot,
            depth: 0,
        }
    }

    /// Construct a new state-fingerprint op tagged with the producing BFS
    /// `depth`. Both fields accept any `u32`.
    #[must_use]
    pub fn new_at_depth(state_slot: u32, depth: u32) -> Self {
        Self { state_slot, depth }
    }
}

impl DialectOp for VerifStateFingerprint {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.state_fingerprint"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        // state_slot and depth are u32, so non-negativity is type-enforced.
        // No other structural invariants today.
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        Ok(Lowered::Leaf(LlvmLeaf::StateFingerprint {
            state_slot: self.state_slot,
            depth: self.depth,
        }))
    }
}

/// Assert an invariant holds over the current state. Target of
/// `tla::TlaInvariant` lowering. The `invariant_id` identifies which
/// named invariant; real backends resolve it to the compiled predicate.
///
/// # Fields
///
/// - `invariant_id`: stable id of the invariant being checked (any `u32`).
/// - `state_slot`: slot index of the state slab to check against the
///   invariant. Real backends resolve it to a base address + stride at
///   emit time.
/// - `depth`: BFS depth (TLC level) at which the check was run. `0` =
///   Init-produced seed level. Carrying depth at the dialect level lets
///   backends attribute a violation to its BFS level without a side-channel
///   lookup.
///
/// # Verification rules
///
/// No structural invariants today — every `u32` combination is well-formed.
/// Future waves may require a registered `invariant_id` (cross-module
/// check, not an isolated-op check).
///
/// # Graduation history (#4286)
///
/// - **Wave 13**: stub — only `invariant_id`; lowered to
///   `LlvmLeaf::Todo("invariant_check")`.
/// - **Wave 14 TL3d**: added `state_slot` + `depth`; added
///   [`VerifInvariantCheck::new_on_state`] and
///   [`VerifInvariantCheck::new_at_depth`] constructors; graduated the
///   lowering to a structured [`LlvmLeaf::InvariantCheck`] leaf carrying
///   every field; wired into the BFS worker loop `TLA2_DIALECT_TRACE=1`
///   path via `DialectTracer::emit_invariant_check`.
#[derive(Debug, Clone, Copy)]
pub struct VerifInvariantCheck {
    /// Stable id of the invariant being checked.
    pub invariant_id: u32,
    /// Slot index of the state slab to check against the invariant.
    pub state_slot: u32,
    /// BFS depth (TLC level) at which the check was run.
    pub depth: u32,
}

impl VerifInvariantCheck {
    /// Construct a new invariant-check op on state slot `0` at BFS depth `0`.
    /// Equivalent to [`VerifInvariantCheck::new_at_depth`] with
    /// `state_slot = 0` and `depth = 0`.
    #[must_use]
    pub fn new(invariant_id: u32) -> Self {
        Self {
            invariant_id,
            state_slot: 0,
            depth: 0,
        }
    }

    /// Construct a new invariant-check op against a specific state slot at
    /// BFS depth `0`. Equivalent to [`VerifInvariantCheck::new_at_depth`]
    /// with `depth = 0`.
    #[must_use]
    pub fn new_on_state(invariant_id: u32, state_slot: u32) -> Self {
        Self {
            invariant_id,
            state_slot,
            depth: 0,
        }
    }

    /// Construct a new invariant-check op with every field explicit. All
    /// three fields accept any `u32`.
    #[must_use]
    pub fn new_at_depth(invariant_id: u32, state_slot: u32, depth: u32) -> Self {
        Self {
            invariant_id,
            state_slot,
            depth,
        }
    }
}

impl DialectOp for VerifInvariantCheck {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.invariant_check"
    }
    fn kind(&self) -> OpKind {
        OpKind::Invariant
    }
    fn verify(&self) -> Result<(), DialectError> {
        // invariant_id, state_slot, and depth are u32 — non-negativity is
        // type-enforced. No other structural invariants today.
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        Ok(Lowered::Leaf(LlvmLeaf::InvariantCheck {
            invariant_id: self.invariant_id,
            state_slot: self.state_slot,
            depth: self.depth,
        }))
    }
}

/// Drain up to `max` states from the BFS frontier on worker lane
/// `worker_id`. The unit of work for a BFS worker thread at the `verif::`
/// level. Real backends lower this to a work-stealing dequeue pop loop
/// bounded by `max`.
///
/// # Fields
///
/// - `max`: upper bound on dequeues per drain. Must be >= 1 — a zero-max
///   drain is a no-op that indicates a miswiring of the frontier pipeline.
/// - `worker_id`: zero-based BFS worker lane id. Single-threaded BFS uses
///   `0`; parallel BFS uses the crossbeam-deque worker index. Has no upper
///   bound today (the backend clamps to its actual worker count at emit
///   time).
///
/// # Verification rules
///
/// - `max` must be non-zero.
///
/// # Graduation history (#4286)
///
/// - **Wave 13**: stub — only `max`, lowered to `LlvmLeaf::Todo("frontier_drain")`.
/// - **Wave 14 TL3**: added `worker_id`; added [`VerifFrontierDrain::new_on_worker`]
///   constructor; graduated the lowering to carry both fields on a structured
///   [`LlvmLeaf::FrontierDrain`] leaf; wired into the BFS worker loop
///   `TLA2_DIALECT_TRACE=1` path via `DialectTracer::emit_frontier_drain`.
#[derive(Debug, Clone, Copy)]
pub struct VerifFrontierDrain {
    /// Maximum number of states to drain from the frontier in one op.
    pub max: u32,
    /// Zero-based BFS worker lane id (`0` for single-threaded BFS).
    pub worker_id: u32,
}

impl VerifFrontierDrain {
    /// Construct a frontier-drain op for the default (single-threaded) worker
    /// lane. Equivalent to [`VerifFrontierDrain::new_on_worker`] with
    /// `worker_id = 0`.
    #[must_use]
    pub fn new(max: u32) -> Self {
        Self { max, worker_id: 0 }
    }

    /// Construct a frontier-drain op bound to a specific parallel-BFS worker
    /// lane. `max` still must be >= 1; `worker_id` accepts any `u32`.
    #[must_use]
    pub fn new_on_worker(max: u32, worker_id: u32) -> Self {
        Self { max, worker_id }
    }
}

impl DialectOp for VerifFrontierDrain {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.frontier_drain"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.max == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "verif",
                op: "verif.frontier_drain",
                message: "max must be > 0; zero-max drain is a no-op miswiring".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        Ok(Lowered::Leaf(LlvmLeaf::FrontierDrain {
            max: self.max,
            worker_id: self.worker_id,
        }))
    }
}

// Op interface capabilities (TL25 Wave 14 — Part of #4253).
//
// `VerifFrontierDrain` mutates shared worker frontier state (it *removes*
// states from a queue), so it is NOT `Pure`. It can be sharded across
// workers but each shard is serial within itself, so we do NOT claim
// `HasParallelism` at the op level (shard scheduling is a higher-level
// concern). Divergence is `Low` — the drain loop is straight-line with a
// bounded `max`.
impl DivergenceClass for VerifFrontierDrain {
    fn divergence(&self) -> Divergence {
        Divergence::Low
    }
}
impl HasCapabilities for VerifFrontierDrain {
    fn capabilities(&self) -> Capabilities {
        Capabilities::none().with_divergence(self.divergence())
    }
}

/// Batched fingerprint computation over a contiguous slab of `count` states
/// starting at `state_base`, produced at BFS `depth`. Real backends lower this
/// to a vectorized / SIMD-unrolled fingerprint kernel. Pins the namespace
/// asked for in mail LLVM2#4268.
///
/// # Fields
///
/// - `state_base`: inclusive base index of the state slab.
/// - `count`: number of states in the batch. Must be >= 1 — a zero-count
///   batch is a no-op.
/// - `depth`: BFS depth (TLC level) at which the batch was produced. `0` =
///   Init-produced seed level. Carrying depth at the dialect level lets
///   backends tag fingerprint records with their graph depth without a
///   side-channel lookup.
///
/// # Verification rules
///
/// - `count` must be non-zero.
///
/// # Graduation history (#4286)
///
/// - **Wave 13**: stub — only `state_base`, `count`; lowered to
///   `LlvmLeaf::Todo("fingerprint_batch")`.
/// - **Wave 14 TL3**: added `depth`; added
///   [`VerifFingerprintBatch::new_at_depth`] constructor; graduated the
///   lowering to carry every field on a structured
///   [`LlvmLeaf::FingerprintBatch`] leaf; wired into the BFS worker loop
///   `TLA2_DIALECT_TRACE=1` path via `DialectTracer::emit_fingerprint_batch`.
#[derive(Debug, Clone, Copy)]
pub struct VerifFingerprintBatch {
    /// Base state slot (inclusive).
    pub state_base: u32,
    /// Number of states to fingerprint in the batch.
    pub count: u32,
    /// BFS depth (TLC level) at which the batch was produced.
    pub depth: u32,
}

impl VerifFingerprintBatch {
    /// Construct a fingerprint-batch op at BFS depth `0` (the Init level).
    /// Equivalent to [`VerifFingerprintBatch::new_at_depth`] with `depth = 0`.
    #[must_use]
    pub fn new(state_base: u32, count: u32) -> Self {
        Self {
            state_base,
            count,
            depth: 0,
        }
    }

    /// Construct a fingerprint-batch op tagged with the producing BFS
    /// `depth`. `count` still must be >= 1; `state_base` and `depth` accept
    /// any `u32`.
    #[must_use]
    pub fn new_at_depth(state_base: u32, count: u32, depth: u32) -> Self {
        Self {
            state_base,
            count,
            depth,
        }
    }
}

impl DialectOp for VerifFingerprintBatch {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.fingerprint_batch"
    }
    fn kind(&self) -> OpKind {
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.count == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "verif",
                op: "verif.fingerprint_batch",
                message: "count must be > 0; zero-count batch is a no-op".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        Ok(Lowered::Leaf(LlvmLeaf::FingerprintBatch {
            state_base: self.state_base,
            count: self.count,
            depth: self.depth,
        }))
    }
}

// Op interface capabilities (TL25 Wave 14 — Part of #4253).
//
// `VerifFingerprintBatch` is the canonical GPU-eligible verif op:
// - `Pure` — fingerprinting a state is a pure hash of the state bytes, no
//   side effects. The output slab is write-once by the producing lane.
// - `HasParallelism` — fingerprinting `count` independent states is
//   embarrassingly data-parallel (SIMD lane, GPU warp, thread pool task).
// - `DivergenceClass = Uniform` — every lane runs the identical fingerprint
//   kernel over its own state; there is no lane-local branching.
//
// Therefore `is_gpu_eligible(caps) == true` — a KernelExtract-style pass
// will promote this op to a GPU kernel automatically, without a hand-coded
// op-kind allowlist. This is the acceptance criterion from issue #4253:
// "a new verif.* op implementing Pure+HasParallelism+DivergenceClass(≤Low)
// becomes GPU-eligible without modifying KernelExtract".
impl Pure for VerifFingerprintBatch {}
impl HasParallelism for VerifFingerprintBatch {}
impl DivergenceClass for VerifFingerprintBatch {
    fn divergence(&self) -> Divergence {
        Divergence::Uniform
    }
}
impl HasCapabilities for VerifFingerprintBatch {
    fn capabilities(&self) -> Capabilities {
        Capabilities::none()
            .with_pure()
            .with_parallelism()
            .with_divergence(self.divergence())
    }
}

// -----------------------------------------------------------------------------
// Wave 14 TL3f (#4286): VerifActionEval — per-action successor expansion.
// -----------------------------------------------------------------------------

/// Evaluate a TLA+ action against a source state, producing zero or more
/// successor states. The per-state unit of BFS successor expansion at the
/// `verif::` level. Real backends lower this to a call against the compiled
/// action evaluator (TIR / bytecode / JIT), resolving `action_id` to the
/// predicate function and `source_slot` to the source state address.
///
/// # Fields
///
/// - `action_id`: stable id of the action being evaluated. `0` is reserved
///   for Init (seed-level) evaluation; Next-level actions use ids `>= 1`.
/// - `source_slot`: slot index of the source state slab that drives the
///   evaluator.
/// - `depth`: BFS depth (TLC level) at which the evaluator ran. `0` =
///   Init-produced seed level.
/// - `worker_id`: zero-based BFS worker lane id. Single-threaded BFS uses
///   `0`; parallel BFS routes the crossbeam-deque worker index.
///
/// # Verification rules
///
/// - `action_id` must be non-zero. `0` is reserved for Init; a Next-level
///   `verif.action_eval` with `action_id == 0` is a miswiring — callers
///   evaluating Init should route through `tla.init` / `verif.bfs_step`
///   (seed kind), not through `verif.action_eval`.
///
/// # Graduation history (#4286)
///
/// - **Wave 14 TL3f**: graduated from the `tla::TlaActionEval` surface op
///   to a structured lowering producing [`LlvmLeaf::ActionEval`]. Four
///   canonical fields carry every piece of information the backend needs
///   to emit a concrete successor-expansion call: which action, over which
///   source state, at which BFS depth, on which worker lane.
#[derive(Debug, Clone, Copy)]
pub struct VerifActionEval {
    /// Stable id of the action being evaluated (`0` reserved for Init).
    pub action_id: u32,
    /// Slot index of the source state driving evaluation.
    pub source_slot: u32,
    /// BFS depth (TLC level) at which the evaluator ran.
    pub depth: u32,
    /// Zero-based BFS worker lane id.
    pub worker_id: u32,
}

impl VerifActionEval {
    /// Construct an action-eval op on source slot `source_slot`, at BFS
    /// depth `0` and worker lane `0`. Equivalent to
    /// [`VerifActionEval::new_at_depth`] with `depth = 0` and
    /// `worker_id = 0`.
    #[must_use]
    pub fn new(action_id: u32, source_slot: u32) -> Self {
        Self {
            action_id,
            source_slot,
            depth: 0,
            worker_id: 0,
        }
    }

    /// Construct an action-eval op tagged with the producing BFS `depth`
    /// and `worker_id`. `action_id` must be `>= 1`; the other three
    /// fields accept any `u32`.
    #[must_use]
    pub fn new_at_depth(action_id: u32, source_slot: u32, depth: u32, worker_id: u32) -> Self {
        Self {
            action_id,
            source_slot,
            depth,
            worker_id,
        }
    }
}

impl DialectOp for VerifActionEval {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.action_eval"
    }
    fn kind(&self) -> OpKind {
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.action_id == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "verif",
                op: "verif.action_eval",
                message: "action_id must be >= 1; 0 is reserved for Init (use verif.bfs_step seed)"
                    .into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        Ok(Lowered::Leaf(LlvmLeaf::ActionEval {
            action_id: self.action_id,
            source_slot: self.source_slot,
            depth: self.depth,
            worker_id: self.worker_id,
        }))
    }
}

// -----------------------------------------------------------------------------
// Wave 14 TL3f (#4286): VerifEnabledCheck — ENABLED A predicate.
// -----------------------------------------------------------------------------

/// Evaluate the TLA+ `ENABLED A` predicate against a state — returns `TRUE`
/// iff action `A` has at least one successor from that state. Unlike
/// [`VerifInvariantCheck`] (which aborts on failure), `verif.enabled_check`
/// is a pure predicate that produces a boolean value — it is typically used
/// inside invariants or fairness conditions.
///
/// # Fields
///
/// - `action_id`: stable id of the action whose enabledness is being
///   queried. `0` is forbidden — `ENABLED Init` is nonsensical (Init is
///   not a Next-level action, and seed-level evaluation always fires).
/// - `state_slot`: slot index of the state slab to check against.
/// - `depth`: BFS depth (TLC level) at which the check was run. `0` =
///   Init-produced seed level.
///
/// # Verification rules
///
/// - `action_id` must be non-zero. `ENABLED Init` is a miswiring.
///
/// # Graduation history (#4286)
///
/// - **Wave 14 TL3f**: graduated from the `tla::TlaEnabled` surface op to
///   a structured lowering producing [`LlvmLeaf::EnabledCheck`]. Three
///   canonical fields (`action_id`, `state_slot`, `depth`) give the
///   backend everything needed to emit a concrete predicate call.
#[derive(Debug, Clone, Copy)]
pub struct VerifEnabledCheck {
    /// Stable id of the action whose enabledness is queried (>= 1).
    pub action_id: u32,
    /// Slot index of the state slab to check.
    pub state_slot: u32,
    /// BFS depth (TLC level) at which the check was run.
    pub depth: u32,
}

impl VerifEnabledCheck {
    /// Construct an enabled-check op on state slot `0` at BFS depth `0`.
    /// Equivalent to [`VerifEnabledCheck::new_at_depth`] with
    /// `state_slot = 0` and `depth = 0`.
    #[must_use]
    pub fn new(action_id: u32) -> Self {
        Self {
            action_id,
            state_slot: 0,
            depth: 0,
        }
    }

    /// Construct an enabled-check op against a specific state slot at BFS
    /// depth `0`. Equivalent to [`VerifEnabledCheck::new_at_depth`] with
    /// `depth = 0`.
    #[must_use]
    pub fn new_on_state(action_id: u32, state_slot: u32) -> Self {
        Self {
            action_id,
            state_slot,
            depth: 0,
        }
    }

    /// Construct an enabled-check op with every field explicit. `action_id`
    /// must be `>= 1`; `state_slot` and `depth` accept any `u32`.
    #[must_use]
    pub fn new_at_depth(action_id: u32, state_slot: u32, depth: u32) -> Self {
        Self {
            action_id,
            state_slot,
            depth,
        }
    }
}

impl DialectOp for VerifEnabledCheck {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.enabled_check"
    }
    fn kind(&self) -> OpKind {
        // ENABLED is a pure predicate — it produces a Bool value. Unlike
        // verif.invariant_check (which aborts on failure and is OpKind::Invariant),
        // verif.enabled_check is an expression.
        OpKind::Expression
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.action_id == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "verif",
                op: "verif.enabled_check",
                message: "action_id must be >= 1; ENABLED Init is nonsensical".into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        Ok(Lowered::Leaf(LlvmLeaf::EnabledCheck {
            action_id: self.action_id,
            state_slot: self.state_slot,
            depth: self.depth,
        }))
    }
}

// -----------------------------------------------------------------------------
// Wave 14 TL3g (#4286): VerifStateSuccessors — action expansion output.
// -----------------------------------------------------------------------------

/// Describes the *output* of evaluating a TLA+ action on a source state:
/// a batch of `count` successor states enqueued at BFS `target_depth` on
/// worker lane `worker_id`. The natural companion to [`VerifActionEval`]:
/// where `VerifActionEval` says "call action `A` on source slot `S`",
/// `VerifStateSuccessors` describes "that call produced `N` successors and
/// enqueued them onto worker `W` at depth `D`".
///
/// Real backends use this record to drive the successor-admission pipeline:
/// - Dedup + seen-set insertion runs against exactly `count` states.
/// - Work-stealing / frontier partitioning sees `count` items landing on
///   `worker_id`.
/// - BFS depth bookkeeping advances from `target_depth - 1` (the source's
///   depth) to `target_depth`.
///
/// # Fields
///
/// - `action_id`: stable id of the action that produced the successors.
///   `0` is reserved for Init (seed-level enqueue); Next-level expansions
///   use ids `>= 1`.
/// - `source_slot`: slot index of the source state that was expanded.
/// - `count`: number of successors produced. Must be `>= 1` — a zero-count
///   expansion is a disabled-action signal and belongs on the separate
///   [`VerifEnabledCheck`] path.
/// - `target_depth`: BFS depth at which the successors are enqueued.
///   Must be `>= 1` — enqueuing at depth `0` would mean "replay the Init
///   level", which is a miswiring.
/// - `worker_id`: zero-based BFS worker lane id enqueuing the batch.
///
/// # Verification rules
///
/// - `action_id` must be non-zero. `0` is reserved for Init; Init does not
///   expand a source state, it produces seeds (handled by `verif.bfs_step`
///   seed kind).
/// - `count` must be non-zero. Use [`VerifEnabledCheck`] instead when the
///   evaluator signals "disabled" (zero successors).
/// - `target_depth` must be non-zero. Successors are always enqueued one
///   level below the source, and the source's depth is `>= 0`.
///
/// # Graduation history (#4286)
///
/// - **Wave 14 TL3g**: new op — introduced as a graduated op, not as a
///   stub-then-graduated pair. Lowers to a structured
///   [`LlvmLeaf::StateSuccessors`] leaf carrying every field. Covers the
///   "action expansion output" semantics that neither `verif.action_eval`
///   (which is the call) nor `verif.fingerprint_batch` (which is the
///   fingerprint kernel) expresses.
#[derive(Debug, Clone, Copy)]
pub struct VerifStateSuccessors {
    /// Stable id of the action that produced the successors (`>= 1`).
    pub action_id: u32,
    /// Slot index of the source state that was expanded.
    pub source_slot: u32,
    /// Number of successors produced (`>= 1`).
    pub count: u32,
    /// BFS depth at which the successors are enqueued (`>= 1`).
    pub target_depth: u32,
    /// Zero-based BFS worker lane id enqueuing the batch.
    pub worker_id: u32,
}

impl VerifStateSuccessors {
    /// Construct a new state-successors op on source slot `source_slot` at
    /// `target_depth == 1` and worker lane `0`. Equivalent to
    /// [`VerifStateSuccessors::new_full`] with `target_depth = 1` and
    /// `worker_id = 0`.
    #[must_use]
    pub fn new(action_id: u32, source_slot: u32, count: u32) -> Self {
        Self {
            action_id,
            source_slot,
            count,
            target_depth: 1,
            worker_id: 0,
        }
    }

    /// Construct a new state-successors op with every field explicit.
    /// `action_id` and `count` and `target_depth` must all be `>= 1`.
    #[must_use]
    pub fn new_full(
        action_id: u32,
        source_slot: u32,
        count: u32,
        target_depth: u32,
        worker_id: u32,
    ) -> Self {
        Self {
            action_id,
            source_slot,
            count,
            target_depth,
            worker_id,
        }
    }
}

impl DialectOp for VerifStateSuccessors {
    fn dialect(&self) -> &'static str {
        "verif"
    }
    fn op_name(&self) -> &'static str {
        "verif.state_successors"
    }
    fn kind(&self) -> OpKind {
        // A state-successors record describes an enqueue into the BFS
        // frontier — it is a state-pipeline event, not an expression value.
        OpKind::StateTransform
    }
    fn verify(&self) -> Result<(), DialectError> {
        if self.action_id == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "verif",
                op: "verif.state_successors",
                message: "action_id must be >= 1; 0 is reserved for Init (use verif.bfs_step seed)"
                    .into(),
            });
        }
        if self.count == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "verif",
                op: "verif.state_successors",
                message: "count must be >= 1; zero successors is a disabled-action signal \
                          — use verif.enabled_check instead"
                    .into(),
            });
        }
        if self.target_depth == 0 {
            return Err(DialectError::VerifyFailed {
                dialect: "verif",
                op: "verif.state_successors",
                message: "target_depth must be >= 1; successors enqueue one level below source"
                    .into(),
            });
        }
        Ok(())
    }
    fn lower(&self) -> Result<Lowered, DialectError> {
        self.verify()?;
        Ok(Lowered::Leaf(LlvmLeaf::StateSuccessors {
            action_id: self.action_id,
            source_slot: self.source_slot,
            count: self.count,
            target_depth: self.target_depth,
            worker_id: self.worker_id,
        }))
    }
}

// -----------------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -------------------------------------------------------------------------
    // Pre-existing tests (Wave 5).
    // -------------------------------------------------------------------------

    #[test]
    fn verif_dialect_registration_exposes_op_names() {
        let d = VerifDialect;
        assert_eq!(d.name(), "verif");
        assert!(d.op_names().contains(&"verif.bfs_step"));
        assert!(d.op_names().contains(&"verif.invariant_check"));
    }

    #[test]
    fn bfs_step_seed_accepts_action_id_zero() {
        let op = VerifBfsStep {
            kind: BfsKind::Seed,
            action_id: 0,
            ..Default::default()
        };
        op.verify().unwrap();
    }

    #[test]
    fn bfs_step_seed_rejects_nonzero_action_id() {
        let op = VerifBfsStep {
            kind: BfsKind::Seed,
            action_id: 3,
            ..Default::default()
        };
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.bfs_step");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn bfs_step_expand_allows_any_action_id() {
        let op = VerifBfsStep {
            kind: BfsKind::Expand,
            action_id: 99,
            ..Default::default()
        };
        op.verify().unwrap();
    }

    #[test]
    fn bfs_step_lowers_to_leaf() {
        // Wave 14 TL3g: bfs_step lowers to a structured leaf (not Todo).
        let op = VerifBfsStep {
            kind: BfsKind::Expand,
            action_id: 0,
            ..Default::default()
        };
        let lowered = op.lower().unwrap();
        assert!(matches!(
            lowered,
            Lowered::Leaf(LlvmLeaf::BfsStep { kind: 1, .. })
        ));
    }

    #[test]
    fn op_names_constant_is_exported() {
        // Public API reachability test — see tla::tests::op_names_constant_is_exported.
        // Wave 13: 18 Wave 12 ops + 2 new (frontier_drain, fingerprint_batch) = 20.
        // Wave 14 TL3f: +2 (action_eval, enabled_check) = 22.
        // Wave 14 TL3g: +1 (state_successors) = 23.
        assert_eq!(OP_NAMES.len(), 23);
        assert!(!DIALECT_NAME.is_empty());
    }

    // -------------------------------------------------------------------------
    // Wave 14 tests — VerifBfsStep graduated with worker_id + frontier_size +
    // depth fields and new_seed / new_expand constructors.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_new_seed_sets_canonical_fields() {
        let step = VerifBfsStep::new_seed(2, 128);
        assert!(matches!(step.kind, BfsKind::Seed));
        assert_eq!(step.action_id, 0);
        assert_eq!(step.worker_id, 2);
        assert_eq!(step.frontier_size, 128);
        assert_eq!(step.depth, 0);
        step.verify()
            .expect("seed with worker/frontier fields must verify");
    }

    #[test]
    fn wave14_new_expand_preserves_all_caller_fields() {
        let step = VerifBfsStep::new_expand(9, 4, 1024, 7);
        assert!(matches!(step.kind, BfsKind::Expand));
        assert_eq!(step.action_id, 9);
        assert_eq!(step.worker_id, 4);
        assert_eq!(step.frontier_size, 1024);
        assert_eq!(step.depth, 7);
        step.verify()
            .expect("expand step with all fields must verify");
    }

    #[test]
    fn wave14_seed_rejects_nonzero_depth() {
        let step = VerifBfsStep {
            kind: BfsKind::Seed,
            action_id: 0,
            worker_id: 0,
            frontier_size: 0,
            depth: 1,
        };
        let err = step.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.bfs_step");
                assert!(message.contains("depth"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_default_is_canonical_seed() {
        let step = VerifBfsStep::default();
        assert!(matches!(step.kind, BfsKind::Seed));
        assert_eq!(step.action_id, 0);
        assert_eq!(step.worker_id, 0);
        assert_eq!(step.frontier_size, 0);
        assert_eq!(step.depth, 0);
        step.verify().expect("default seed must verify");
    }

    #[test]
    fn wave14_expand_with_large_worker_and_frontier_still_verifies() {
        // No upper bounds today — the verify contract accepts u32::MAX for
        // worker_id, frontier_size, and depth. Future waves may tighten this.
        let step = VerifBfsStep::new_expand(u32::MAX, u32::MAX, u32::MAX, u32::MAX);
        step.verify()
            .expect("expand with u32::MAX fields must verify");
    }

    // -------------------------------------------------------------------------
    // Wave 12 tests — scalar literal ops.
    // -------------------------------------------------------------------------

    #[test]
    fn wave12_scalar_int_reports_dialect_and_mnemonic() {
        let op = VerifScalarInt::new(42);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.scalar_int");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.value, 42);
    }

    #[test]
    fn wave12_scalar_int_accepts_any_value() {
        for v in [i64::MIN, -1, 0, 1, i64::MAX] {
            let op = VerifScalarInt::new(v);
            op.verify().expect("scalar_int must accept any i64");
        }
    }

    #[test]
    fn wave12_scalar_int_lowers_to_leaf() {
        // Wave 14 TL3g: scalar_int lowers to a structured leaf carrying the
        // literal value (not a Todo placeholder).
        let op = VerifScalarInt::new(7);
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::ScalarInt { value }) => assert_eq!(value, 7),
            other => panic!("expected ScalarInt leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave12_scalar_bool_reports_dialect_and_mnemonic() {
        let op = VerifScalarBool::new(true);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.scalar_bool");
        assert_eq!(op.kind(), OpKind::Expression);
        assert!(op.value);
    }

    #[test]
    fn wave12_scalar_bool_lowers_to_leaf() {
        // Wave 14 TL3g: scalar_bool lowers to a structured leaf carrying the
        // literal value (not a Todo placeholder).
        let op = VerifScalarBool::new(false);
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::ScalarBool { value }) => assert!(!value),
            other => panic!("expected ScalarBool leaf, got {other:?}"),
        }
    }

    // -------------------------------------------------------------------------
    // Wave 12 tests — binary verif expression ops.
    // -------------------------------------------------------------------------

    #[test]
    fn wave12_binary_ops_report_expected_mnemonic_and_kind() {
        // One per-mnemonic sanity assertion that covers every new binary op.
        assert_eq!(VerifIntAdd.op_name(), "verif.int_add");
        assert_eq!(VerifIntAdd.dialect(), "verif");
        assert_eq!(VerifIntAdd.kind(), OpKind::Expression);

        assert_eq!(VerifIntSub.op_name(), "verif.int_sub");
        assert_eq!(VerifIntMul.op_name(), "verif.int_mul");
        assert_eq!(VerifIntDiv.op_name(), "verif.int_div");
        assert_eq!(VerifIntMod.op_name(), "verif.int_mod");

        assert_eq!(VerifIntLt.op_name(), "verif.int_lt");
        assert_eq!(VerifIntLe.op_name(), "verif.int_le");
        assert_eq!(VerifIntGt.op_name(), "verif.int_gt");
        assert_eq!(VerifIntGe.op_name(), "verif.int_ge");
        assert_eq!(VerifIntEq.op_name(), "verif.int_eq");

        assert_eq!(VerifBoolAnd.op_name(), "verif.bool_and");
        assert_eq!(VerifBoolOr.op_name(), "verif.bool_or");
    }

    #[test]
    fn wave12_binary_verify_is_trivially_ok() {
        // Linear-sequence markers have no operand fields, so verify() is
        // always Ok. The enclosing pass is responsible for sequence-level
        // operand validation.
        VerifIntAdd.verify().unwrap();
        VerifIntSub.verify().unwrap();
        VerifIntMul.verify().unwrap();
        VerifIntDiv.verify().unwrap();
        VerifIntMod.verify().unwrap();
        VerifIntLt.verify().unwrap();
        VerifIntLe.verify().unwrap();
        VerifIntGt.verify().unwrap();
        VerifIntGe.verify().unwrap();
        VerifIntEq.verify().unwrap();
        VerifBoolAnd.verify().unwrap();
        VerifBoolOr.verify().unwrap();
    }

    #[test]
    fn wave12_int_arith_ops_lower_to_matching_leaves() {
        // Wave 14 TL3h (#4286): graduated to structured unit-variant leaves.
        assert!(matches!(
            VerifIntAdd.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntAdd)
        ));
        assert!(matches!(
            VerifIntSub.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntSub)
        ));
        assert!(matches!(
            VerifIntMul.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntMul)
        ));
        assert!(matches!(
            VerifIntDiv.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntDiv)
        ));
        assert!(matches!(
            VerifIntMod.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntMod)
        ));
    }

    #[test]
    fn wave12_int_cmp_ops_lower_to_matching_leaves() {
        // Wave 14 TL3h (#4286): graduated to structured unit-variant leaves.
        assert!(matches!(
            VerifIntLt.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntLt)
        ));
        assert!(matches!(
            VerifIntLe.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntLe)
        ));
        assert!(matches!(
            VerifIntGt.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntGt)
        ));
        assert!(matches!(
            VerifIntGe.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntGe)
        ));
        assert!(matches!(
            VerifIntEq.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::IntEq)
        ));
    }

    #[test]
    fn wave12_bool_and_or_lower_to_matching_leaves() {
        // Wave 14 TL3h (#4286): graduated to structured unit-variant leaves.
        assert!(matches!(
            VerifBoolAnd.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::BoolAnd)
        ));
        assert!(matches!(
            VerifBoolOr.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::BoolOr)
        ));
    }

    // -------------------------------------------------------------------------
    // Wave 12 tests — unary verif.bool_not.
    // -------------------------------------------------------------------------

    #[test]
    fn wave12_bool_not_reports_dialect_and_mnemonic() {
        assert_eq!(VerifBoolNot.dialect(), "verif");
        assert_eq!(VerifBoolNot.op_name(), "verif.bool_not");
        assert_eq!(VerifBoolNot.kind(), OpKind::Expression);
    }

    #[test]
    fn wave12_bool_not_verify_is_trivially_ok() {
        VerifBoolNot.verify().unwrap();
    }

    #[test]
    fn wave12_bool_not_lowers_to_bool_not_leaf() {
        // Graduated Wave 14 TL3h: was `Todo("bool_not")`, now structured.
        assert!(matches!(
            VerifBoolNot.lower().unwrap(),
            Lowered::Leaf(LlvmLeaf::BoolNot)
        ));
    }

    // -------------------------------------------------------------------------
    // Wave 12 tests — dialect registration covers new ops.
    // -------------------------------------------------------------------------

    #[test]
    fn wave12_dialect_op_names_contains_every_new_wave12_op() {
        let d = VerifDialect;
        let names = d.op_names();
        for expected in &[
            "verif.scalar_int",
            "verif.scalar_bool",
            "verif.int_add",
            "verif.int_sub",
            "verif.int_mul",
            "verif.int_div",
            "verif.int_mod",
            "verif.int_lt",
            "verif.int_le",
            "verif.int_gt",
            "verif.int_ge",
            "verif.int_eq",
            "verif.bool_and",
            "verif.bool_or",
            "verif.bool_not",
        ] {
            assert!(
                names.contains(expected),
                "verif dialect must expose {expected}"
            );
        }
    }

    #[test]
    fn wave12_all_new_ops_are_send_and_sync() {
        // DialectOp requires Send + Sync; confirm trait objects are usable
        // across threads via a trivial type-level check.
        fn assert_send_sync<T: Send + Sync + ?Sized>() {}
        assert_send_sync::<dyn DialectOp>();

        // Every Wave 12 op as a trait object must also fit the bound.
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifScalarInt::new(0));
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifScalarBool::new(true));
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntAdd);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntSub);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntMul);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntDiv);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntMod);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntLt);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntLe);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntGt);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntGe);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifIntEq);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifBoolAnd);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifBoolOr);
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifBoolNot);
    }

    // -------------------------------------------------------------------------
    // Wave 13 tests — verification primitives: fingerprint, invariant check,
    // frontier drain, fingerprint batch.
    // -------------------------------------------------------------------------

    #[test]
    fn wave13_state_fingerprint_reports_dialect_and_mnemonic() {
        let op = VerifStateFingerprint::new(7);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.state_fingerprint");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.state_slot, 7);
    }

    #[test]
    fn wave13_state_fingerprint_verify_always_ok() {
        VerifStateFingerprint::new(0).verify().unwrap();
        VerifStateFingerprint::new(u32::MAX).verify().unwrap();
    }

    #[test]
    fn wave13_state_fingerprint_lowers_to_leaf() {
        // Graduated Wave 14 TL3d (#4286): `verif.state_fingerprint` now lowers
        // to a structured `LlvmLeaf::StateFingerprint` carrying `state_slot`
        // and `depth` — no more `Todo` placeholder. `new(slot)` defaults
        // `depth == 0`.
        let lowered = VerifStateFingerprint::new(0).lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::StateFingerprint { state_slot, depth }) => {
                assert_eq!(state_slot, 0);
                assert_eq!(depth, 0);
            }
            other => panic!("expected StateFingerprint leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave13_invariant_check_reports_dialect_and_mnemonic() {
        let op = VerifInvariantCheck::new(3);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.invariant_check");
        assert_eq!(op.kind(), OpKind::Invariant);
        assert_eq!(op.invariant_id, 3);
    }

    #[test]
    fn wave13_invariant_check_lowers_to_leaf() {
        // Graduated Wave 14 TL3d (#4286): `verif.invariant_check` now lowers
        // to a structured `LlvmLeaf::InvariantCheck` carrying `invariant_id`,
        // `state_slot`, and `depth` — no more `Todo` placeholder. `new(id)`
        // defaults both `state_slot == 0` and `depth == 0`.
        let lowered = VerifInvariantCheck::new(0).lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::InvariantCheck {
                invariant_id,
                state_slot,
                depth,
            }) => {
                assert_eq!(invariant_id, 0);
                assert_eq!(state_slot, 0);
                assert_eq!(depth, 0);
            }
            other => panic!("expected InvariantCheck leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave13_frontier_drain_reports_dialect_and_mnemonic() {
        let op = VerifFrontierDrain::new(128);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.frontier_drain");
        assert_eq!(op.kind(), OpKind::StateTransform);
        assert_eq!(op.max, 128);
    }

    #[test]
    fn wave13_frontier_drain_rejects_zero_max() {
        let err = VerifFrontierDrain::new(0).verify().unwrap_err();
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.frontier_drain");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave13_frontier_drain_lower_propagates_verify_error() {
        // verify() is embedded in lower() — a zero-max drain must fail early.
        let err = VerifFrontierDrain::new(0).lower().unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn wave13_frontier_drain_lowers_to_structured_leaf_for_nonzero_max() {
        // Graduated lowering (#4286): `verif.frontier_drain` now lowers to a
        // structured `LlvmLeaf::FrontierDrain` carrying `max` and `worker_id`
        // directly — no more `Todo` placeholder.
        let lowered = VerifFrontierDrain::new(1).lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::FrontierDrain { max, worker_id }) => {
                assert_eq!(max, 1);
                assert_eq!(worker_id, 0);
            }
            other => panic!("expected FrontierDrain leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave13_fingerprint_batch_reports_dialect_and_mnemonic() {
        let op = VerifFingerprintBatch::new(100, 32);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.fingerprint_batch");
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.state_base, 100);
        assert_eq!(op.count, 32);
    }

    #[test]
    fn wave13_fingerprint_batch_rejects_zero_count() {
        let err = VerifFingerprintBatch::new(0, 0).verify().unwrap_err();
        match err {
            DialectError::VerifyFailed { dialect, op, .. } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.fingerprint_batch");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave13_fingerprint_batch_lowers_to_structured_leaf_for_nonzero_count() {
        // Graduated lowering (#4286): `verif.fingerprint_batch` now lowers to
        // a structured `LlvmLeaf::FingerprintBatch` carrying `state_base`,
        // `count`, and `depth` — no more `Todo` placeholder.
        let lowered = VerifFingerprintBatch::new(0, 1).lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::FingerprintBatch {
                state_base,
                count,
                depth,
            }) => {
                assert_eq!(state_base, 0);
                assert_eq!(count, 1);
                assert_eq!(depth, 0);
            }
            other => panic!("expected FingerprintBatch leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave13_dialect_op_names_contains_every_new_wave13_op() {
        let d = VerifDialect;
        let names = d.op_names();
        for expected in &["verif.frontier_drain", "verif.fingerprint_batch"] {
            assert!(
                names.contains(expected),
                "verif dialect must expose {expected}"
            );
        }
    }

    #[test]
    fn wave13_all_new_ops_are_send_and_sync() {
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifStateFingerprint::new(0));
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifInvariantCheck::new(0));
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifFrontierDrain::new(1));
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifFingerprintBatch::new(0, 1));
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3 tests — VerifFrontierDrain + VerifFingerprintBatch graduated
    // with real structured lowering and multi-field constructors (#4286).
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3_frontier_drain_default_worker_is_zero() {
        // `new(max)` keeps the Wave 13 ergonomics — single-threaded BFS uses
        // worker_id 0 implicitly.
        let drain = VerifFrontierDrain::new(256);
        assert_eq!(drain.max, 256);
        assert_eq!(drain.worker_id, 0);
        drain.verify().expect("default-worker drain must verify");
    }

    #[test]
    fn wave14_tl3_frontier_drain_new_on_worker_preserves_fields() {
        let drain = VerifFrontierDrain::new_on_worker(64, 7);
        assert_eq!(drain.max, 64);
        assert_eq!(drain.worker_id, 7);
        drain.verify().expect("worker-bound drain must verify");
    }

    #[test]
    fn wave14_tl3_frontier_drain_lowers_to_structured_leaf_with_all_fields() {
        let drain = VerifFrontierDrain::new_on_worker(1024, 3);
        let lowered = drain.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::FrontierDrain { max, worker_id }) => {
                assert_eq!(max, 1024);
                assert_eq!(worker_id, 3);
            }
            other => panic!("expected FrontierDrain leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3_frontier_drain_worker_id_u32_max_verifies() {
        // No upper bound on worker_id — the backend clamps at emit time.
        let drain = VerifFrontierDrain::new_on_worker(1, u32::MAX);
        drain.verify().expect("u32::MAX worker id must verify");
        let lowered = drain.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::FrontierDrain { worker_id, .. }) => {
                assert_eq!(worker_id, u32::MAX);
            }
            other => panic!("expected FrontierDrain leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3_frontier_drain_zero_max_still_rejected_by_lower() {
        // The graduated lowering must still propagate the verify() error —
        // a zero-max drain must fail before a leaf is produced.
        let err = VerifFrontierDrain::new_on_worker(0, 9).lower().unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn wave14_tl3_fingerprint_batch_default_depth_is_zero() {
        // `new(state_base, count)` defaults `depth == 0` (Init level) for
        // Wave 13 callers that didn't track BFS depth.
        let batch = VerifFingerprintBatch::new(10, 32);
        assert_eq!(batch.state_base, 10);
        assert_eq!(batch.count, 32);
        assert_eq!(batch.depth, 0);
        batch.verify().expect("default-depth batch must verify");
    }

    #[test]
    fn wave14_tl3_fingerprint_batch_new_at_depth_preserves_fields() {
        let batch = VerifFingerprintBatch::new_at_depth(100, 64, 5);
        assert_eq!(batch.state_base, 100);
        assert_eq!(batch.count, 64);
        assert_eq!(batch.depth, 5);
        batch.verify().expect("depth-tagged batch must verify");
    }

    #[test]
    fn wave14_tl3_fingerprint_batch_lowers_to_structured_leaf_with_all_fields() {
        let batch = VerifFingerprintBatch::new_at_depth(200, 16, 9);
        let lowered = batch.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::FingerprintBatch {
                state_base,
                count,
                depth,
            }) => {
                assert_eq!(state_base, 200);
                assert_eq!(count, 16);
                assert_eq!(depth, 9);
            }
            other => panic!("expected FingerprintBatch leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3_fingerprint_batch_u32_max_depth_verifies() {
        // Graph diameter is bounded by u32::MAX in the dialect — far beyond
        // any realistic BFS depth. Verify it roundtrips through lower().
        let batch = VerifFingerprintBatch::new_at_depth(0, 1, u32::MAX);
        batch.verify().expect("u32::MAX depth must verify");
        let lowered = batch.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::FingerprintBatch { depth, .. }) => {
                assert_eq!(depth, u32::MAX);
            }
            other => panic!("expected FingerprintBatch leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3_fingerprint_batch_zero_count_still_rejected_by_lower() {
        // The graduated lowering must still propagate the verify() error —
        // a zero-count batch must fail before a leaf is produced, regardless
        // of depth.
        let err = VerifFingerprintBatch::new_at_depth(0, 0, 42)
            .lower()
            .unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn wave14_tl3_frontier_drain_and_fingerprint_batch_fields_are_public_and_copy() {
        // Sanity: struct-update syntax works on both graduated ops, so tests
        // and callers can build minor variants without re-typing every field.
        let d = VerifFrontierDrain::new_on_worker(16, 1);
        let d2 = VerifFrontierDrain { worker_id: 2, ..d };
        assert_eq!(d2.max, 16);
        assert_eq!(d2.worker_id, 2);
        let b = VerifFingerprintBatch::new_at_depth(0, 4, 1);
        let b2 = VerifFingerprintBatch { depth: 2, ..b };
        assert_eq!(b2.count, 4);
        assert_eq!(b2.depth, 2);
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3d tests (#4286) — VerifStateFingerprint + VerifInvariantCheck
    // graduated with real structured lowering and multi-field constructors.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3d_state_fingerprint_default_depth_is_zero() {
        // `new(state_slot)` keeps the Wave 13 ergonomics — the default depth
        // is `0` (Init-produced seed level).
        let fp = VerifStateFingerprint::new(42);
        assert_eq!(fp.state_slot, 42);
        assert_eq!(fp.depth, 0);
        fp.verify().expect("default-depth fingerprint must verify");
    }

    #[test]
    fn wave14_tl3d_state_fingerprint_new_at_depth_preserves_fields() {
        let fp = VerifStateFingerprint::new_at_depth(100, 7);
        assert_eq!(fp.state_slot, 100);
        assert_eq!(fp.depth, 7);
        fp.verify().expect("depth-tagged fingerprint must verify");
    }

    #[test]
    fn wave14_tl3d_state_fingerprint_lowers_to_structured_leaf_with_all_fields() {
        let fp = VerifStateFingerprint::new_at_depth(256, 3);
        let lowered = fp.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::StateFingerprint { state_slot, depth }) => {
                assert_eq!(state_slot, 256);
                assert_eq!(depth, 3);
            }
            other => panic!("expected StateFingerprint leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3d_state_fingerprint_u32_max_depth_verifies() {
        // No upper bound on depth — graph diameter is bounded by u32::MAX.
        let fp = VerifStateFingerprint::new_at_depth(0, u32::MAX);
        fp.verify().expect("u32::MAX depth must verify");
        let lowered = fp.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::StateFingerprint { depth, .. }) => {
                assert_eq!(depth, u32::MAX);
            }
            other => panic!("expected StateFingerprint leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3d_invariant_check_default_state_and_depth_are_zero() {
        // `new(invariant_id)` keeps the Wave 13 ergonomics — both state_slot
        // and depth default to `0`.
        let check = VerifInvariantCheck::new(9);
        assert_eq!(check.invariant_id, 9);
        assert_eq!(check.state_slot, 0);
        assert_eq!(check.depth, 0);
        check.verify().expect("default-state check must verify");
    }

    #[test]
    fn wave14_tl3d_invariant_check_new_on_state_preserves_fields() {
        let check = VerifInvariantCheck::new_on_state(3, 42);
        assert_eq!(check.invariant_id, 3);
        assert_eq!(check.state_slot, 42);
        assert_eq!(check.depth, 0);
        check.verify().expect("state-bound check must verify");
    }

    #[test]
    fn wave14_tl3d_invariant_check_new_at_depth_preserves_fields() {
        let check = VerifInvariantCheck::new_at_depth(3, 42, 5);
        assert_eq!(check.invariant_id, 3);
        assert_eq!(check.state_slot, 42);
        assert_eq!(check.depth, 5);
        check.verify().expect("depth-tagged check must verify");
    }

    #[test]
    fn wave14_tl3d_invariant_check_lowers_to_structured_leaf_with_all_fields() {
        let check = VerifInvariantCheck::new_at_depth(7, 88, 2);
        let lowered = check.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::InvariantCheck {
                invariant_id,
                state_slot,
                depth,
            }) => {
                assert_eq!(invariant_id, 7);
                assert_eq!(state_slot, 88);
                assert_eq!(depth, 2);
            }
            other => panic!("expected InvariantCheck leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3d_invariant_check_u32_max_fields_verify() {
        // No upper bounds on any field — all three accept u32::MAX.
        let check = VerifInvariantCheck::new_at_depth(u32::MAX, u32::MAX, u32::MAX);
        check.verify().expect("u32::MAX fields must verify");
        let lowered = check.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::InvariantCheck {
                invariant_id,
                state_slot,
                depth,
            }) => {
                assert_eq!(invariant_id, u32::MAX);
                assert_eq!(state_slot, u32::MAX);
                assert_eq!(depth, u32::MAX);
            }
            other => panic!("expected InvariantCheck leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3d_state_fingerprint_and_invariant_check_fields_are_public_and_copy() {
        // Sanity: struct-update syntax works on both graduated ops.
        let f = VerifStateFingerprint::new_at_depth(10, 1);
        let f2 = VerifStateFingerprint { depth: 3, ..f };
        assert_eq!(f2.state_slot, 10);
        assert_eq!(f2.depth, 3);
        let c = VerifInvariantCheck::new_at_depth(1, 2, 3);
        let c2 = VerifInvariantCheck {
            state_slot: 99,
            ..c
        };
        assert_eq!(c2.invariant_id, 1);
        assert_eq!(c2.state_slot, 99);
        assert_eq!(c2.depth, 3);
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3f tests (#4286) — VerifActionEval + VerifEnabledCheck
    // graduated with real structured lowering and multi-field constructors.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3f_action_eval_reports_dialect_and_mnemonic() {
        let op = VerifActionEval::new(3, 42);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.action_eval");
        assert_eq!(op.kind(), OpKind::StateTransform);
        assert_eq!(op.action_id, 3);
        assert_eq!(op.source_slot, 42);
        assert_eq!(op.depth, 0);
        assert_eq!(op.worker_id, 0);
    }

    #[test]
    fn wave14_tl3f_action_eval_rejects_zero_action_id() {
        // action_id == 0 is reserved for Init; verif.action_eval is Next-level
        // only. Zero is a miswiring.
        let err = VerifActionEval::new(0, 0).verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.action_eval");
                assert!(message.contains("action_id"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_action_eval_lower_propagates_verify_error() {
        // verify() is embedded in lower() — a zero-action_id eval must fail
        // before a leaf is produced.
        let err = VerifActionEval::new(0, 10).lower().unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn wave14_tl3f_action_eval_new_defaults_depth_and_worker() {
        let op = VerifActionEval::new(7, 99);
        assert_eq!(op.depth, 0);
        assert_eq!(op.worker_id, 0);
        op.verify().expect("non-zero action_id must verify");
    }

    #[test]
    fn wave14_tl3f_action_eval_new_at_depth_preserves_fields() {
        let op = VerifActionEval::new_at_depth(5, 88, 3, 2);
        assert_eq!(op.action_id, 5);
        assert_eq!(op.source_slot, 88);
        assert_eq!(op.depth, 3);
        assert_eq!(op.worker_id, 2);
        op.verify()
            .expect("fully-specified action_eval must verify");
    }

    #[test]
    fn wave14_tl3f_action_eval_lowers_to_structured_leaf_with_all_fields() {
        let op = VerifActionEval::new_at_depth(9, 256, 4, 1);
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::ActionEval {
                action_id,
                source_slot,
                depth,
                worker_id,
            }) => {
                assert_eq!(action_id, 9);
                assert_eq!(source_slot, 256);
                assert_eq!(depth, 4);
                assert_eq!(worker_id, 1);
            }
            other => panic!("expected ActionEval leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_action_eval_u32_max_non_action_id_fields_verify() {
        // No upper bounds on source_slot, depth, or worker_id — only
        // action_id has the >= 1 constraint.
        let op = VerifActionEval::new_at_depth(1, u32::MAX, u32::MAX, u32::MAX);
        op.verify()
            .expect("u32::MAX source/depth/worker must verify");
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::ActionEval {
                source_slot,
                depth,
                worker_id,
                ..
            }) => {
                assert_eq!(source_slot, u32::MAX);
                assert_eq!(depth, u32::MAX);
                assert_eq!(worker_id, u32::MAX);
            }
            other => panic!("expected ActionEval leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_enabled_check_reports_dialect_and_mnemonic() {
        let op = VerifEnabledCheck::new(3);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.enabled_check");
        // ENABLED is a pure predicate — Expression kind, not Invariant.
        assert_eq!(op.kind(), OpKind::Expression);
        assert_eq!(op.action_id, 3);
        assert_eq!(op.state_slot, 0);
        assert_eq!(op.depth, 0);
    }

    #[test]
    fn wave14_tl3f_enabled_check_rejects_zero_action_id() {
        // ENABLED Init is nonsensical: Init is always "fire-able" at the seed
        // level and never occurs as a Next-level action subject to ENABLED.
        let err = VerifEnabledCheck::new(0).verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.enabled_check");
                assert!(message.contains("action_id"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_enabled_check_lower_propagates_verify_error() {
        let err = VerifEnabledCheck::new(0).lower().unwrap_err();
        assert!(matches!(err, DialectError::VerifyFailed { .. }));
    }

    #[test]
    fn wave14_tl3f_enabled_check_new_on_state_preserves_fields() {
        let op = VerifEnabledCheck::new_on_state(7, 42);
        assert_eq!(op.action_id, 7);
        assert_eq!(op.state_slot, 42);
        assert_eq!(op.depth, 0);
        op.verify().expect("state-bound enabled_check must verify");
    }

    #[test]
    fn wave14_tl3f_enabled_check_new_at_depth_preserves_fields() {
        let op = VerifEnabledCheck::new_at_depth(7, 42, 5);
        assert_eq!(op.action_id, 7);
        assert_eq!(op.state_slot, 42);
        assert_eq!(op.depth, 5);
        op.verify().expect("depth-tagged enabled_check must verify");
    }

    #[test]
    fn wave14_tl3f_enabled_check_lowers_to_structured_leaf_with_all_fields() {
        let op = VerifEnabledCheck::new_at_depth(4, 88, 2);
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::EnabledCheck {
                action_id,
                state_slot,
                depth,
            }) => {
                assert_eq!(action_id, 4);
                assert_eq!(state_slot, 88);
                assert_eq!(depth, 2);
            }
            other => panic!("expected EnabledCheck leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_enabled_check_u32_max_non_action_id_fields_verify() {
        let op = VerifEnabledCheck::new_at_depth(1, u32::MAX, u32::MAX);
        op.verify().expect("u32::MAX state/depth must verify");
        let lowered = op.lower().unwrap();
        match lowered {
            Lowered::Leaf(LlvmLeaf::EnabledCheck {
                state_slot, depth, ..
            }) => {
                assert_eq!(state_slot, u32::MAX);
                assert_eq!(depth, u32::MAX);
            }
            other => panic!("expected EnabledCheck leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3f_action_eval_and_enabled_check_fields_are_public_and_copy() {
        // Struct-update syntax works on both graduated TL3f ops.
        let a = VerifActionEval::new_at_depth(1, 2, 3, 4);
        let a2 = VerifActionEval { worker_id: 9, ..a };
        assert_eq!(a2.action_id, 1);
        assert_eq!(a2.source_slot, 2);
        assert_eq!(a2.depth, 3);
        assert_eq!(a2.worker_id, 9);
        let e = VerifEnabledCheck::new_at_depth(5, 6, 7);
        let e2 = VerifEnabledCheck { depth: 99, ..e };
        assert_eq!(e2.action_id, 5);
        assert_eq!(e2.state_slot, 6);
        assert_eq!(e2.depth, 99);
    }

    #[test]
    fn wave14_tl3f_dialect_op_names_contains_every_new_tl3f_op() {
        let d = VerifDialect;
        let names = d.op_names();
        for expected in &["verif.action_eval", "verif.enabled_check"] {
            assert!(
                names.contains(expected),
                "verif dialect must expose {expected}"
            );
        }
    }

    #[test]
    fn wave14_tl3f_all_new_ops_are_send_and_sync() {
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifActionEval::new(1, 0));
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifEnabledCheck::new(1));
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3g tests (#4286) — graduated bfs_step + scalar_int + scalar_bool
    // to structured leaves; new state_successors op.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3g_bfs_step_seed_lowers_to_structured_leaf() {
        // Seed steps carry kind=0 and implicit action_id=0, depth=0. Every
        // other field must reach the leaf unchanged.
        let step = VerifBfsStep::new_seed(3, 256);
        match step.lower().expect("seed must lower") {
            Lowered::Leaf(LlvmLeaf::BfsStep {
                kind,
                action_id,
                worker_id,
                frontier_size,
                depth,
            }) => {
                assert_eq!(kind, 0, "Seed encodes as kind=0");
                assert_eq!(action_id, 0);
                assert_eq!(worker_id, 3);
                assert_eq!(frontier_size, 256);
                assert_eq!(depth, 0);
            }
            other => panic!("expected BfsStep leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3g_bfs_step_expand_lowers_to_structured_leaf() {
        // Expand steps carry kind=1 and propagate every field.
        let step = VerifBfsStep::new_expand(7, 2, 1024, 5);
        match step.lower().expect("expand must lower") {
            Lowered::Leaf(LlvmLeaf::BfsStep {
                kind,
                action_id,
                worker_id,
                frontier_size,
                depth,
            }) => {
                assert_eq!(kind, 1, "Expand encodes as kind=1");
                assert_eq!(action_id, 7);
                assert_eq!(worker_id, 2);
                assert_eq!(frontier_size, 1024);
                assert_eq!(depth, 5);
            }
            other => panic!("expected BfsStep leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3g_scalar_int_leaf_carries_value() {
        for v in [i64::MIN, -7, 0, 1, i64::MAX] {
            let op = VerifScalarInt::new(v);
            match op.lower().expect("scalar_int must lower") {
                Lowered::Leaf(LlvmLeaf::ScalarInt { value }) => assert_eq!(value, v),
                other => panic!("expected ScalarInt leaf for {v}, got {other:?}"),
            }
        }
    }

    #[test]
    fn wave14_tl3g_scalar_bool_leaf_carries_value() {
        for v in [true, false] {
            let op = VerifScalarBool::new(v);
            match op.lower().expect("scalar_bool must lower") {
                Lowered::Leaf(LlvmLeaf::ScalarBool { value }) => assert_eq!(value, v),
                other => panic!("expected ScalarBool leaf for {v}, got {other:?}"),
            }
        }
    }

    #[test]
    fn wave14_tl3g_state_successors_reports_dialect_and_mnemonic() {
        let op = VerifStateSuccessors::new(1, 0, 3);
        assert_eq!(op.dialect(), "verif");
        assert_eq!(op.op_name(), "verif.state_successors");
        assert_eq!(op.kind(), OpKind::StateTransform);
        assert_eq!(op.action_id, 1);
        assert_eq!(op.source_slot, 0);
        assert_eq!(op.count, 3);
        assert_eq!(op.target_depth, 1);
        assert_eq!(op.worker_id, 0);
    }

    #[test]
    fn wave14_tl3g_state_successors_rejects_action_id_zero() {
        let op = VerifStateSuccessors {
            action_id: 0,
            source_slot: 0,
            count: 1,
            target_depth: 1,
            worker_id: 0,
        };
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.state_successors");
                assert!(message.contains("action_id"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3g_state_successors_rejects_zero_count() {
        let op = VerifStateSuccessors {
            action_id: 1,
            source_slot: 0,
            count: 0,
            target_depth: 1,
            worker_id: 0,
        };
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.state_successors");
                assert!(message.contains("count"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3g_state_successors_rejects_zero_target_depth() {
        let op = VerifStateSuccessors {
            action_id: 1,
            source_slot: 0,
            count: 3,
            target_depth: 0,
            worker_id: 0,
        };
        let err = op.verify().unwrap_err();
        match err {
            DialectError::VerifyFailed {
                dialect,
                op,
                message,
            } => {
                assert_eq!(dialect, "verif");
                assert_eq!(op, "verif.state_successors");
                assert!(message.contains("target_depth"), "message: {message}");
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3g_state_successors_lowers_to_structured_leaf() {
        let op = VerifStateSuccessors::new_full(5, 12, 4, 7, 2);
        match op.lower().expect("state_successors must lower") {
            Lowered::Leaf(LlvmLeaf::StateSuccessors {
                action_id,
                source_slot,
                count,
                target_depth,
                worker_id,
            }) => {
                assert_eq!(action_id, 5);
                assert_eq!(source_slot, 12);
                assert_eq!(count, 4);
                assert_eq!(target_depth, 7);
                assert_eq!(worker_id, 2);
            }
            other => panic!("expected StateSuccessors leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3g_state_successors_new_defaults_are_canonical() {
        // `new` sets target_depth=1 and worker_id=0 — the minimal-depth,
        // single-threaded-worker case.
        let op = VerifStateSuccessors::new(3, 8, 2);
        assert_eq!(op.action_id, 3);
        assert_eq!(op.source_slot, 8);
        assert_eq!(op.count, 2);
        assert_eq!(op.target_depth, 1);
        assert_eq!(op.worker_id, 0);
        op.verify().expect("canonical new() must verify");
    }

    #[test]
    fn wave14_tl3g_state_successors_is_send_and_sync() {
        let _: Box<dyn DialectOp + Send + Sync> = Box::new(VerifStateSuccessors::new(1, 0, 1));
    }

    #[test]
    fn wave14_tl3g_dialect_op_names_contains_state_successors() {
        let d = VerifDialect;
        assert!(
            d.op_names().contains(&"verif.state_successors"),
            "verif dialect must expose verif.state_successors"
        );
    }

    // -------------------------------------------------------------------------
    // Wave 14 TL3h tests — Wave 12 expression ops graduated to structured
    // `LlvmLeaf` unit variants. Every op covered below was lowering to
    // `LlvmLeaf::Todo("<tag>")` before this wave; the tests here pin the new
    // exhaustive-enum shape against regressions.
    // -------------------------------------------------------------------------

    #[test]
    fn wave14_tl3h_int_arith_ops_graduated_to_unit_variants() {
        // Per-op smoke test: every integer-arith marker lowers to its
        // dedicated unit variant and `verify()` is trivially Ok.
        let cases: [(Box<dyn DialectOp>, LlvmLeaf); 5] = [
            (Box::new(VerifIntAdd), LlvmLeaf::IntAdd),
            (Box::new(VerifIntSub), LlvmLeaf::IntSub),
            (Box::new(VerifIntMul), LlvmLeaf::IntMul),
            (Box::new(VerifIntDiv), LlvmLeaf::IntDiv),
            (Box::new(VerifIntMod), LlvmLeaf::IntMod),
        ];
        for (op, expected) in cases {
            op.verify().expect("graduated op must verify");
            match op.lower().expect("graduated op must lower") {
                Lowered::Leaf(leaf) => assert_eq!(leaf, expected),
                other => panic!("expected structured leaf, got {other:?}"),
            }
        }
    }

    #[test]
    fn wave14_tl3h_int_cmp_ops_graduated_to_unit_variants() {
        // Comparison markers lower to their dedicated unit variants.
        let cases: [(Box<dyn DialectOp>, LlvmLeaf); 5] = [
            (Box::new(VerifIntLt), LlvmLeaf::IntLt),
            (Box::new(VerifIntLe), LlvmLeaf::IntLe),
            (Box::new(VerifIntGt), LlvmLeaf::IntGt),
            (Box::new(VerifIntGe), LlvmLeaf::IntGe),
            (Box::new(VerifIntEq), LlvmLeaf::IntEq),
        ];
        for (op, expected) in cases {
            op.verify().expect("graduated op must verify");
            match op.lower().expect("graduated op must lower") {
                Lowered::Leaf(leaf) => assert_eq!(leaf, expected),
                other => panic!("expected structured leaf, got {other:?}"),
            }
        }
    }

    #[test]
    fn wave14_tl3h_bool_ops_graduated_to_unit_variants() {
        // Binary + unary bool ops lower to dedicated unit variants.
        // `Lowered` is not PartialEq, so match the inner leaf directly.
        match VerifBoolAnd.lower().expect("must lower") {
            Lowered::Leaf(leaf) => assert_eq!(leaf, LlvmLeaf::BoolAnd),
            other => panic!("expected leaf, got {other:?}"),
        }
        match VerifBoolOr.lower().expect("must lower") {
            Lowered::Leaf(leaf) => assert_eq!(leaf, LlvmLeaf::BoolOr),
            other => panic!("expected leaf, got {other:?}"),
        }
        match VerifBoolNot.lower().expect("must lower") {
            Lowered::Leaf(leaf) => assert_eq!(leaf, LlvmLeaf::BoolNot),
            other => panic!("expected leaf, got {other:?}"),
        }
    }

    #[test]
    fn wave14_tl3h_graduated_leaves_are_pairwise_distinct() {
        // All 13 graduated variants are distinct — the exhaustive-enum
        // dispatch depends on this. Uniqueness is checked via pairwise
        // `PartialEq` comparison (LlvmLeaf is Eq but not Hash).
        let leaves = [
            LlvmLeaf::IntAdd,
            LlvmLeaf::IntSub,
            LlvmLeaf::IntMul,
            LlvmLeaf::IntDiv,
            LlvmLeaf::IntMod,
            LlvmLeaf::IntLt,
            LlvmLeaf::IntLe,
            LlvmLeaf::IntGt,
            LlvmLeaf::IntGe,
            LlvmLeaf::IntEq,
            LlvmLeaf::BoolAnd,
            LlvmLeaf::BoolOr,
            LlvmLeaf::BoolNot,
        ];
        for (i, a) in leaves.iter().enumerate() {
            for (j, b) in leaves.iter().enumerate() {
                if i == j {
                    assert_eq!(a, b, "self-equality must hold for TL3h leaf {i}");
                } else {
                    assert_ne!(
                        a, b,
                        "distinct TL3h leaves at indices {i} and {j} compared equal"
                    );
                }
            }
        }
    }

    #[test]
    fn wave14_tl3h_no_expression_op_lowers_to_todo() {
        // Regression guard: no Wave 12 expression op may regress to a
        // `Todo(...)` placeholder. All 13 graduated ops in one table.
        let ops: [Box<dyn DialectOp>; 13] = [
            Box::new(VerifIntAdd),
            Box::new(VerifIntSub),
            Box::new(VerifIntMul),
            Box::new(VerifIntDiv),
            Box::new(VerifIntMod),
            Box::new(VerifIntLt),
            Box::new(VerifIntLe),
            Box::new(VerifIntGt),
            Box::new(VerifIntGe),
            Box::new(VerifIntEq),
            Box::new(VerifBoolAnd),
            Box::new(VerifBoolOr),
            Box::new(VerifBoolNot),
        ];
        for op in &ops {
            match op.lower().expect("must lower") {
                Lowered::Leaf(LlvmLeaf::Todo(tag)) => panic!(
                    "op {} regressed to LlvmLeaf::Todo({:?}) — must be a structured unit variant",
                    op.op_name(),
                    tag
                ),
                Lowered::Leaf(_) => {}
                other => panic!("op {} lowered to non-leaf: {other:?}", op.op_name()),
            }
        }
    }

    #[test]
    fn wave14_tl3h_graduated_leaves_are_clone_and_eq() {
        // Unit-variant leaves must be Clone + Eq to be usable as dispatch
        // records downstream. (LlvmLeaf is not Copy because sibling
        // struct-variants carry multi-field state records; Clone on unit
        // variants is trivial.) Exercise Clone + Eq explicitly.
        fn assert_clone_eq<T: Clone + Eq>(_: &T) {}
        let a = LlvmLeaf::IntAdd;
        assert_clone_eq(&a);
        let b = a.clone();
        assert_eq!(a, b);
        assert_ne!(LlvmLeaf::IntAdd, LlvmLeaf::IntSub);
        assert_ne!(LlvmLeaf::BoolAnd, LlvmLeaf::BoolOr);
    }

    // -------------------------------------------------------------------------
    // TL25 (Part of #4253): op interface capability integration tests.
    // -------------------------------------------------------------------------

    #[test]
    fn tl25_fingerprint_batch_is_gpu_eligible_via_interfaces() {
        // This is the issue #4253 acceptance-criterion test: the op is
        // GPU-eligible because it implements Pure + HasParallelism +
        // DivergenceClass(Uniform ≤ Low). The KernelExtract-style
        // predicate `op_is_gpu_eligible` queries capabilities, not op kind.
        let op = VerifFingerprintBatch::new(0, 64);
        let caps = op.capabilities();
        assert!(caps.pure_, "FingerprintBatch must be Pure");
        assert!(caps.parallel, "FingerprintBatch must be HasParallelism");
        assert_eq!(caps.divergence, Some(Divergence::Uniform));
        assert!(
            crate::op_is_gpu_eligible(&op),
            "FingerprintBatch must be GPU-eligible per capability triple"
        );
    }

    #[test]
    fn tl25_bfs_step_is_not_gpu_eligible() {
        // BfsStep records scheduling side effects and has High divergence.
        // Capabilities-based routing correctly excludes it from the GPU
        // lane without a hand-coded op-kind allowlist.
        let op = VerifBfsStep::new_seed(0, 0);
        let caps = op.capabilities();
        assert!(!caps.pure_, "BfsStep must not be Pure");
        assert!(!caps.parallel, "BfsStep must not be HasParallelism");
        assert_eq!(caps.divergence, Some(Divergence::High));
        assert!(
            !crate::op_is_gpu_eligible(&op),
            "BfsStep must not be GPU-eligible (High divergence)"
        );
    }

    #[test]
    fn tl25_frontier_drain_low_divergence_not_gpu_eligible_without_pure() {
        // FrontierDrain is Low divergence but NOT pure (it mutates the
        // frontier queue). It exercises the boundary case: Low divergence
        // alone is insufficient — the full Pure+Parallel+Divergence triple
        // is required.
        let op = VerifFrontierDrain::new(128);
        let caps = op.capabilities();
        assert!(
            !caps.pure_,
            "FrontierDrain must not be Pure (mutates queue)"
        );
        assert!(
            !caps.parallel,
            "FrontierDrain is not data-parallel at the op level"
        );
        assert_eq!(caps.divergence, Some(Divergence::Low));
        assert!(
            !crate::op_is_gpu_eligible(&op),
            "FrontierDrain must not be GPU-eligible — missing Pure + Parallel"
        );
    }

    #[test]
    fn tl25_kernel_extract_partitions_op_batch_by_capabilities() {
        // Acceptance test for issue #4253: a KernelExtract-style pass
        // partitions a heterogeneous op batch into GPU-eligible vs
        // scalar *solely* by capabilities query. Adding a new op that
        // satisfies Pure+Parallel+Uniform here lands in the GPU bucket
        // automatically — no pass edit required.
        let fingerprint = VerifFingerprintBatch::new(0, 16);
        let drain = VerifFrontierDrain::new(32);
        let bfs = VerifBfsStep::new_seed(0, 0);

        let caps = [
            fingerprint.capabilities(),
            drain.capabilities(),
            bfs.capabilities(),
        ];
        let gpu_count = caps.iter().filter(|c| crate::is_gpu_eligible(c)).count();
        let scalar_count = caps.len() - gpu_count;
        assert_eq!(gpu_count, 1, "only FingerprintBatch is GPU-eligible");
        assert_eq!(
            scalar_count, 2,
            "BfsStep + FrontierDrain stay on scalar path"
        );
    }
}
