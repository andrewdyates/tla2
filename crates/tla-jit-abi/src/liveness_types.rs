// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Backend-agnostic liveness predicate descriptors.
//!
//! These types describe liveness (fairness) predicates in a form that can be
//! consumed by either the Cranelift (`tla-jit`) or LLVM2 (`tla-llvm2`) backend
//! without creating a cargo cycle. They are pure data structures — no compiler
//! dependencies — which is why they belong in the `tla-jit-abi` leaf crate.
//!
//! Part of #4267 (Stage 2d of epic #4251): consolidated the previously
//! duplicated definitions in `tla-jit::compiled_liveness` and
//! `tla-llvm2::runtime_abi::liveness_types` so the migration to LLVM2 can
//! delete `tla-jit` without orphaning these descriptors.
//!
//! # Overview
//!
//! Liveness predicates are evaluated every BFS transition to determine which
//! fairness constraints (WF/SF, state predicates, action predicates) hold.
//! The compiled batch functions take a flat `[i64]` state buffer and return
//! a `u64` bitmask — bit `tag` is set when the predicate with that tag is
//! true.
//!
//! # Function pointer types
//!
//! - [`CompiledStatePredBatchFn`] — evaluates state-level predicates on a
//!   single flat state.
//! - [`CompiledActionPredBatchFn`] — evaluates action-level predicates on a
//!   (current, next) transition.
//! - [`CompiledAcceptanceCheckFn`] — evaluates SCC acceptance against a set
//!   of precomputed acceptance masks.

/// Function pointer type for a compiled batch of state-level liveness predicates.
///
/// Takes a pointer to the current state as a flat i64 array and the number of
/// state variables. Returns a u64 bitmask where bit `tag` is set if predicate
/// with that tag evaluates to true.
///
/// # Safety
///
/// `state` must point to a valid `[i64; state_len]` array. The function reads
/// exactly `state_len` elements.
pub type CompiledStatePredBatchFn = unsafe extern "C" fn(state: *const i64, state_len: u32) -> u64;

/// Function pointer type for a compiled batch of action-level liveness predicates.
///
/// Takes pointers to the current and next state as flat i64 arrays and the
/// number of state variables. Returns a u64 bitmask where bit `tag` is set
/// if predicate with that tag evaluates to true for the transition.
///
/// # Safety
///
/// Both `current` and `next` must point to valid `[i64; state_len]` arrays.
pub type CompiledActionPredBatchFn =
    unsafe extern "C" fn(current: *const i64, next: *const i64, state_len: u32) -> u64;

/// Function pointer type for compiled SCC acceptance checking.
///
/// Takes a node/SCC bitmask plus a pointer to acceptance masks. Returns 1 if
/// every acceptance mask has at least one overlapping bit in
/// `node_state_bitmask`, otherwise returns 0.
///
/// # Safety
///
/// `acceptance_masks_ptr` must point to `num_masks` valid `u64` values unless
/// `num_masks == 0`.
pub type CompiledAcceptanceCheckFn = unsafe extern "C" fn(
    node_state_bitmask: u64,
    acceptance_masks_ptr: *const u64,
    num_masks: u32,
) -> u32;

/// Statistics from liveness predicate compilation.
#[derive(Debug, Clone, Default)]
pub struct LivenessCompileStats {
    /// Number of state predicates eligible for compilation.
    pub state_eligible: usize,
    /// Number of state predicates successfully compiled.
    pub state_compiled: usize,
    /// Number of action predicates eligible for compilation.
    pub action_eligible: usize,
    /// Number of action predicates successfully compiled.
    pub action_compiled: usize,
    /// Number of predicates skipped (Enabled, StateChanged, compound types).
    pub skipped_ineligible: usize,
    /// Compilation time in microseconds.
    pub compile_time_us: u64,
}

/// Information about a single liveness predicate to be compiled.
///
/// This is the interface between the model checker (which knows about
/// `LiveExpr`) and the compilation backend. The checker extracts predicate
/// metadata and passes it through this descriptor so the backend never sees
/// `LiveExpr` directly.
#[derive(Debug, Clone)]
pub struct LivenessPredInfo {
    /// Unique tag for this predicate (bit position in the bitmask).
    pub tag: u32,
    /// Whether this is a state predicate (true) or action predicate (false).
    pub is_state_pred: bool,
    /// Indices of the variables being compared, if this is a simple variable
    /// equality/comparison predicate. Used for direct register access in
    /// the compiled code.
    pub var_indices: Vec<u16>,
    /// The kind of predicate for compilation dispatch.
    pub kind: LivenessPredKind,
}

/// Kind of liveness predicate for compilation.
///
/// Not marked `#[non_exhaustive]` because every backend exhaustively pattern-
/// matches on this enum (Cranelift IR lowering, LLVM2 IR lowering, interpreter
/// fallback). Adding a new variant is intentionally source-breaking for all
/// consumers.
#[derive(Debug, Clone)]
pub enum LivenessPredKind {
    /// A scalar comparison: `state[var_idx] <op> constant_value`.
    /// This is the most common and most efficiently compiled case.
    ScalarComparison {
        /// Index of the state variable to read.
        var_idx: u16,
        /// The comparison operation.
        op: ScalarCompOp,
        /// The constant value to compare against.
        constant: i64,
    },
    /// A variable-to-variable comparison: `state[lhs] <op> state[rhs]`.
    VarComparison {
        /// Index of the left-hand state variable.
        lhs_var_idx: u16,
        /// Index of the right-hand state variable.
        rhs_var_idx: u16,
        /// The comparison operation.
        op: ScalarCompOp,
    },
    /// State change check: `current[var_idx] != next[var_idx]`.
    /// Only valid for action predicates.
    StateChangeCheck {
        /// Indices of variables to check for changes.
        var_indices: Vec<u16>,
    },
    /// A predicate that is not eligible for direct compilation.
    /// The tag is recorded so the caller knows to use interpreter fallback.
    NotEligible,
}

/// Scalar comparison operations supported in compiled predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarCompOp {
    /// Equal (=).
    Eq,
    /// Not equal (/=).
    Ne,
    /// Less than (<).
    Lt,
    /// Less than or equal (<=).
    Le,
    /// Greater than (>).
    Gt,
    /// Greater than or equal (>=).
    Ge,
}
