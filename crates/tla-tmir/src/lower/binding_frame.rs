// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed binding frame used by every bounded quantifier (`\A`, `\E`,
//! `CHOOSE`, `[x \in S |-> ...]`).
//!
//! # What this abstracts
//!
//! A TLA+ quantifier body runs once per element of a domain set `S`. At
//! the tMIR level, each iteration must
//!
//! 1. load `S`'s length from its aggregate header,
//! 2. keep a monotonic loop-iteration index on the stack,
//! 3. bounds-check `i < |S|` at the header,
//! 4. load `S[i + 1]` into the body's binding register, and
//! 5. branch into the body with that register visible.
//!
//! Every existing quantifier implementation (`lower_forall_begin`,
//! `lower_exists_begin`, `lower_choose_begin`, `lower_func_def_begin`)
//! repeats this CFG verbatim. The shape is identical; only the element
//! type, the aggregate layout, and the per-iteration post-actions
//! differ.
//!
//! `BindingFrame` captures that shared structure so callers can opt in
//! to a single, typed representation of the binding instead of copying
//! alloca/load/branch boilerplate. The struct names every intermediate
//! ValueId and block index so the body emitters (`*_next`) can reach
//! the right slots without reaching back into private context state.
//!
//! # Types
//!
//! Bindings are currently i64-valued (TLA+ values are fingerprints at
//! the JIT ABI level). The `elem_ty` field records that explicitly so
//! the tMIR optimizer and future widening passes can see the type
//! associated with the binding register without re-deriving it.
//!
//! The struct is a plain value type; it does NOT own any lowering
//! state. Lifetime is a single `*Begin` → `*Next` lowering call pair.

use tmir::ty::Ty;
use tmir::value::ValueId;

/// All ValueIds and block indices produced by `emit_binding_frame_prelude`.
///
/// A `BindingFrame` represents the allocated loop index, the domain
/// pointer/length pair, and the full header/load/body/exit CFG wiring
/// for one quantifier's binding. It is consumed by the paired `*Next`
/// opcode to (a) advance the index, and (b) resolve the short-circuit
/// target block.
///
/// All fields are `pub(super)` so both `quantifiers.rs` and
/// `functions.rs` in the same `lower/` module can construct and
/// inspect frames directly. Outside `lower/`, this type is internal.
#[derive(Debug, Clone)]
pub(super) struct BindingFrame {
    /// Alloca holding the current iteration index (i64).
    pub(super) idx_alloca: ValueId,
    /// ValueId for the domain aggregate pointer (loaded from `r_domain`).
    #[allow(dead_code)]
    pub(super) domain_ptr: ValueId,
    /// ValueId for the domain length (loaded from slot 0).
    #[allow(dead_code)]
    pub(super) domain_len: ValueId,
    /// Bytecode register holding the element type's logical binding.
    /// Stored for diagnostics / future type-refinement passes.
    #[allow(dead_code)]
    pub(super) binding_reg: u8,
    /// Static element type (currently Ty::I64 for all TLA+ bindings).
    #[allow(dead_code)]
    pub(super) elem_ty: Ty,
    /// tMIR block index for the loop header (bounds check + CondBr).
    pub(super) header_block: usize,
    /// tMIR block index for the exit point (after the loop).
    pub(super) exit_block: usize,
}
