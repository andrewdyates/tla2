// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla_*` runtime ABI — handle-based FFI for LLVM2-compiled aggregate ops.
//!
//! This module hosts the "Option B" runtime surface chosen by R27
//! (`designs/2026-04-20-llvm2-runtime-abi-scope.md`). `tir_lower.rs` emits
//! `call i64 @tla_<op>(...)` for every Phase 3/5 aggregate opcode; the
//! helpers live here. Every helper:
//!
//! 1. Accepts operand handles as raw `i64` (SSA register values).
//! 2. Unboxes via [`handle::handle_to_value`] so interpreter semantics
//!    apply verbatim.
//! 3. Calls into `tla_value::Value` APIs — no op logic is re-implemented.
//! 4. Reboxes results via [`handle::handle_from_value`].
//!
//! # Submodules (Option B roadmap)
//!
//! | Submodule | Symbols | LOC budget | Status |
//! |-----------|---------|------------|--------|
//! | [`handle`] | `TlaHandle`, arena, round trip | 150 | **done** |
//! | [`set`]    | 10 `tla_set_*` helpers + N=0..8 monomorphs | 250 | **done** |
//! | [`seq`]    | 8 `tla_seq_*` helpers + N=0..8 monomorphs | 220 | **done (this agent)** |
//! | [`tuple`]  | 2 `tla_tuple_*` helpers + N=0..8 monomorphs | 150 | **done (this agent)** |
//! | [`record_func`] | 3 helpers | 120 | **done (this agent)** |
//! | [`const_builtin`] | 4 helpers | 80 | **done (this agent)** |
//! | [`quantifier`] | 4 helpers | 200 | **done (this agent)** |
//!
//! Part of #4318.

pub mod const_builtin;
pub mod handle;
pub mod quantifier;
pub mod record_func;
pub mod seq;
pub mod set;
pub mod tuple;

// ============================================================================
// FFI-safe abort helper (shared across tla_* helpers)
// ============================================================================

/// Abort the process with a diagnostic message. **Never returns.**
///
/// Use this in place of `panic!`/`unwrap`/`expect` inside any code path
/// reachable from an `extern "C" fn tla_*` helper. Unwinding a Rust panic
/// across the `extern "C"` boundary is **undefined behaviour** (Rust
/// reference: <https://doc.rust-lang.org/reference/items/functions.html#extern-function-qualifier>).
///
/// `std::process::abort` is well-defined in every ABI — it terminates the
/// process with `SIGABRT` without running destructors. We emit a short
/// diagnostic to stderr first so aborts are not silent in development.
///
/// # When to use
///
/// Only on "compiler bug" paths that should be unreachable in practice
/// (malformed handles, arena overflow past i61 bounds, unknown handle
/// tags). Soft failures — non-enumerable operands, out-of-domain arguments,
/// empty sequences passed to `Head`/`Tail` — must return `NIL_HANDLE`
/// instead so `tir_lower` can fall back to the interpreter.
///
/// # Pattern established by `quantifier::tla_quantifier_runtime_error`
///
/// ```ignore
/// if unreachable_invariant_violated {
///     ait_ffi_abort("tla_my_helper: invariant X violated");
/// }
/// ```
///
/// Part of #4333.
#[cold]
#[inline(never)]
pub(crate) fn ait_ffi_abort(msg: &str) -> ! {
    eprintln!("tla_ops ffi abort: {msg}");
    std::process::abort();
}

pub use const_builtin::{
    clear_tla_constant_pool, set_tla_constant_pool, tla_cardinality, tla_is_finite_set,
    tla_load_const, tla_tostring,
};
pub use handle::{
    clear_tla_arena, handle_from_state_slot, handle_from_value, handle_tag, handle_to_value,
    tla_handle_nil, TlaHandle, H_TAG_ARENA, H_TAG_BOOL, H_TAG_INT, H_TAG_NIL, H_TAG_STRING,
    HANDLE_TAG_BITS, HANDLE_TAG_MASK, NIL_HANDLE,
};
pub use quantifier::{
    clear_tla_iter_arena, tla_quantifier_iter_done, tla_quantifier_iter_new,
    tla_quantifier_iter_next, tla_quantifier_runtime_error,
};
pub use record_func::{tla_domain, tla_func_apply, tla_record_get};
pub use seq::{
    tla_seq_append, tla_seq_concat, tla_seq_head, tla_seq_len, tla_seq_new_0, tla_seq_new_1,
    tla_seq_new_2, tla_seq_new_3, tla_seq_new_4, tla_seq_new_5, tla_seq_new_6, tla_seq_new_7,
    tla_seq_new_8, tla_seq_set, tla_seq_subseq, tla_seq_tail,
};
pub use set::{
    tla_set_big_union, tla_set_diff, tla_set_enum_0, tla_set_enum_1, tla_set_enum_2,
    tla_set_enum_3, tla_set_enum_4, tla_set_enum_5, tla_set_enum_6, tla_set_enum_7,
    tla_set_enum_8, tla_set_in, tla_set_intersect, tla_set_ksubset, tla_set_powerset,
    tla_set_range, tla_set_subseteq, tla_set_union,
};
pub use tuple::{
    tla_tuple_get, tla_tuple_new_0, tla_tuple_new_1, tla_tuple_new_2, tla_tuple_new_3,
    tla_tuple_new_4, tla_tuple_new_5, tla_tuple_new_6, tla_tuple_new_7, tla_tuple_new_8,
};
