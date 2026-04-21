// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `TlaHandle` — value-register ABI for the Phase 3/5 `tla_*` runtime surface.
//!
//! # Why this exists
//!
//! `tir_lower.rs` emits `call i64 @tla_<op>(...)` declarations for every TIR
//! aggregate opcode. Operands flow through the SSA register file as raw `i64`
//! values and may be (a) state-variable slots in the flat state buffer, or
//! (b) intermediate compound values produced by earlier opcodes
//! (`SetEnum`/`SeqNew`/`FuncApply`). The `jit_*` helper family operates on
//! serialized flat-state slot pointers and cannot service intermediate
//! handles. R27 (`designs/2026-04-20-llvm2-runtime-abi-scope.md` §4) picked
//! **Option B — a handle-based ABI** as the architecturally correct bridge.
//!
//! # Encoding
//!
//! A `TlaHandle` is an `i64` whose low 3 bits are a **handle tag** and whose
//! upper 61 bits are the payload. Encoding is chosen so (a) the common-case
//! `Int`/`Bool` scalars never touch the arena, and (b) compound values are
//! boxed as indices into a per-worker-thread `Vec<Value>` that is cleared at
//! action boundaries.
//!
//! | Tag (low 3 bits) | Name              | Payload semantics                    |
//! |------------------|-------------------|--------------------------------------|
//! | `0b001` = 1      | `H_TAG_INT`       | Sign-extended 61-bit integer value   |
//! | `0b010` = 2      | `H_TAG_BOOL`      | 0 = FALSE, 1 = TRUE                  |
//! | `0b011` = 3      | `H_TAG_STRING`    | [`NameId`] (`u32`) padded into i61   |
//! | `0b100` = 4      | `H_TAG_ARENA`     | Index into per-worker arena `Vec`    |
//! | `0b101` = 5      | `H_TAG_NIL`       | Sentinel (nothing); payload == 0     |
//!
//! Tags `0`, `6`, `7` are reserved for future extensions (e.g., inline tuple
//! handles, state-slot fast-path, error sentinels). Zero payload + zero tag
//! is the "zero handle" and is treated as NIL by [`handle_to_value`] —
//! callers emit an explicit [`tla_handle_nil`] rather than relying on
//! all-zero i64 registers.
//!
//! The 61-bit sign-extended int range is `[-2^60, 2^60 - 1]`. Values outside
//! this range are boxed via `H_TAG_ARENA`. This matches the range available
//! to TIR constant-folding which runs in i64 already.
//!
//! # Arena
//!
//! The arena is a per-worker-thread `RefCell<Vec<Value>>`. Arena indices are
//! stable for the lifetime of one action evaluation; the caller MUST invoke
//! [`clear_tla_arena`] at action boundaries, mirroring the
//! `compound_scratch` pattern in `runtime_abi::abi`.
//!
//! # Soundness contract
//!
//! Every helper in `runtime_abi::tla_ops::*` MUST:
//! 1. Unbox input handles via [`handle_to_value`] (interpreter-parity read).
//! 2. Execute its op through `tla_value::Value` APIs (no re-implementation).
//! 3. Rebox results via [`handle_from_value`] (interpreter-parity write).
//!
//! This makes the `tla_*` surface a thin FFI layer; semantic parity with
//! the tree-walking interpreter is inherited for free.
//!
//! Part of #4318. R27 design doc: `designs/2026-04-20-llvm2-runtime-abi-scope.md`.

use std::cell::RefCell;

use num_bigint::BigInt;
use tla_core::{intern_name, resolve_name_id, NameId};
use tla_value::value::Value;

// ============================================================================
// Handle tag layout
// ============================================================================

/// Number of low bits reserved for the handle tag. The payload occupies the
/// remaining `64 - HANDLE_TAG_BITS = 61` bits.
pub const HANDLE_TAG_BITS: u32 = 3;

/// Mask over the handle tag bits (`0b0000_0111`).
pub const HANDLE_TAG_MASK: i64 = (1 << HANDLE_TAG_BITS) - 1;

/// Handle tag: inline sign-extended integer (i61).
pub const H_TAG_INT: i64 = 0b001;
/// Handle tag: inline boolean (0 = FALSE, 1 = TRUE).
pub const H_TAG_BOOL: i64 = 0b010;
/// Handle tag: inline [`NameId`] string reference.
pub const H_TAG_STRING: i64 = 0b011;
/// Handle tag: index into the per-worker arena.
pub const H_TAG_ARENA: i64 = 0b100;
/// Handle tag: explicit NIL sentinel (payload must be 0).
pub const H_TAG_NIL: i64 = 0b101;

/// Minimum integer value representable inline as `H_TAG_INT` (i61 range).
pub const HANDLE_INT_MIN: i64 = -(1 << 60);
/// Maximum integer value representable inline as `H_TAG_INT` (i61 range).
pub const HANDLE_INT_MAX: i64 = (1 << 60) - 1;

/// Opaque handle type exchanged across the `tla_*` FFI boundary.
///
/// Kept as `i64` so it travels through LLVM registers without conversion.
pub type TlaHandle = i64;

/// Canonical NIL handle. Callers that need a "no value" sentinel should use
/// this constant rather than relying on zero-initialised memory.
pub const NIL_HANDLE: TlaHandle = H_TAG_NIL;

// ============================================================================
// Arena (per-worker, interior-mutable)
// ============================================================================

thread_local! {
    /// Per-worker arena backing `H_TAG_ARENA` handles. Holds owned `Value`s;
    /// arena indices are stable for the lifetime of one action evaluation.
    ///
    /// Reset via [`clear_tla_arena`] at action boundaries. This mirrors the
    /// `compound_scratch` lifecycle used by the existing `jit_*` helpers.
    static TLA_ARENA: RefCell<Vec<Value>> = const { RefCell::new(Vec::new()) };
}

/// Clear the per-worker arena.
///
/// Must be invoked at action boundaries to prevent unbounded growth. After
/// calling, all outstanding `H_TAG_ARENA` handles are invalidated. The
/// compiled BFS driver is responsible for placing this call between
/// successive invariant / next-state evaluations.
#[no_mangle]
pub extern "C" fn clear_tla_arena() {
    TLA_ARENA.with(|arena| arena.borrow_mut().clear());
}

/// Number of live entries currently in the arena. Debug-only helper for
/// tests; production code must not rely on this value.
#[cfg(test)]
pub(crate) fn arena_len() -> usize {
    TLA_ARENA.with(|arena| arena.borrow().len())
}

/// Intern a [`Value`] into the arena and return its `H_TAG_ARENA` handle.
///
/// # Aborts (not panics)
///
/// Aborts the process (via [`super::ait_ffi_abort`]) if the arena index
/// exceeds `HANDLE_INT_MAX` (i.e. more than ~2^60 allocations within a
/// single action). This is a theoretical bound — real workloads clear the
/// arena per action. Aborting rather than panicking keeps this helper safe
/// to call from any `extern "C"` path (see #4333).
fn arena_push(value: Value) -> TlaHandle {
    TLA_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let idx = arena.len();
        arena.push(value);
        let idx_i64 = match i64::try_from(idx) {
            Ok(n) => n,
            Err(_) => {
                // Drop the value we just pushed so arena length stays
                // consistent with what we report, then abort.
                let _ = arena.pop();
                super::ait_ffi_abort(
                    "handle::arena_push: arena index exceeds i64 — clear_tla_arena not called?",
                );
            }
        };
        if idx_i64 > HANDLE_INT_MAX {
            let _ = arena.pop();
            super::ait_ffi_abort(
                "handle::arena_push: arena index overflows i61 payload — clear_tla_arena not called?",
            );
        }
        (idx_i64 << HANDLE_TAG_BITS) | H_TAG_ARENA
    })
}

/// Fetch an arena-boxed value by its handle. Returns `None` if the handle
/// tag is not `H_TAG_ARENA` or if the index is out of range.
fn arena_get(handle: TlaHandle) -> Option<Value> {
    if (handle & HANDLE_TAG_MASK) != H_TAG_ARENA {
        return None;
    }
    let idx = (handle >> HANDLE_TAG_BITS) as usize;
    TLA_ARENA.with(|arena| arena.borrow().get(idx).cloned())
}

// ============================================================================
// Value <-> Handle bridges (public API for FFI helpers)
// ============================================================================

/// Encode a [`Value`] as a [`TlaHandle`].
///
/// Inline scalars (`Value::SmallInt` within i61, `Value::Bool`,
/// `Value::String` on interned names) skip the arena. Everything else boxes.
///
/// This is the slow-path constructor used by helpers when an input is
/// produced by the interpreter. Hot paths should prefer
/// [`handle_from_state_slot`] when reading from the flat state buffer.
#[must_use]
pub fn handle_from_value(value: &Value) -> TlaHandle {
    match value {
        Value::Bool(b) => ((*b as i64) << HANDLE_TAG_BITS) | H_TAG_BOOL,
        Value::SmallInt(n) => encode_int(*n),
        Value::Int(n) => {
            // BigInt → try i64 → try i61 inline → fall through to arena.
            if let Ok(small) = i64::try_from(n.as_ref()) {
                encode_int(small)
            } else {
                arena_push(value.clone())
            }
        }
        Value::String(s) => {
            // Intern on demand. `intern_name` returns the existing id if the
            // string was already interned (parse-time path) or allocates a
            // new id otherwise (test-constructed strings). Either way we
            // stay inline, which is a big win for EWD998-style specs that
            // carry small string-tag values through aggregate ops.
            encode_string(intern_name(s))
        }
        _ => arena_push(value.clone()),
    }
}

/// Decode a [`TlaHandle`] back into a [`Value`].
///
/// This is the interpreter-parity contract: every FFI helper ultimately
/// delegates to `tla_value::Value` methods, so every handle produced by
/// [`handle_from_value`] must round-trip exactly.
///
/// Returns a fresh owned `Value`. Callers may clone cheaply because compound
/// `Value` variants are `Arc`-wrapped.
///
/// # Aborts (not panics)
///
/// Aborts the process (via [`super::ait_ffi_abort`]) on a malformed handle
/// (unknown tag, or `H_TAG_ARENA` pointing to a stale index). Malformed
/// handles are always a compiler bug — `tir_lower` is the sole producer;
/// there is no user-facing path that can generate one. This helper is
/// called from every `extern "C" fn tla_*`, so panicking here would be UB
/// (#4333).
#[must_use]
pub fn handle_to_value(handle: TlaHandle) -> Value {
    let tag = handle & HANDLE_TAG_MASK;
    let payload = handle >> HANDLE_TAG_BITS;
    match tag {
        H_TAG_INT => Value::SmallInt(payload),
        H_TAG_BOOL => Value::Bool(payload != 0),
        H_TAG_STRING => {
            // Reconstruct the NameId. Payload was a u32 cast to i64.
            // Masking to 32 bits preserves the original id even after the
            // arithmetic shift (sign extension) above, because NameId fits
            // in the low 32 bits.
            let name_id = NameId((payload & 0xFFFF_FFFF) as u32);
            let s = resolve_name_id(name_id);
            Value::String(s)
        }
        H_TAG_ARENA => match arena_get(handle) {
            Some(v) => v,
            None => super::ait_ffi_abort(&format!(
                "handle::handle_to_value: H_TAG_ARENA handle {handle:#x} has no arena entry — \
                 clear_tla_arena called between construction and use?"
            )),
        },
        H_TAG_NIL => {
            // NIL decodes to SmallInt(0) by convention; downstream helpers
            // that care about NIL should branch on the tag before decoding.
            // This keeps `handle_to_value` total.
            Value::SmallInt(0)
        }
        _ => super::ait_ffi_abort(&format!(
            "handle::handle_to_value: unknown handle tag {tag} in handle {handle:#x}"
        )),
    }
}

/// Fast-path handle constructor for values that already live in the flat
/// state buffer at slot `slot` of `state_ptr`.
///
/// This deserialises the slot via the existing `compound_layout` logic and
/// then reboxes into a handle. The indirection is unavoidable for compound
/// values: the flat-state encoding is TAG-prefixed bytes, not a handle.
///
/// For scalar slots the result is `H_TAG_INT` / `H_TAG_BOOL` / `H_TAG_STRING`
/// without touching the arena.
///
/// # Safety
///
/// The caller must ensure `state_ptr` is valid for reads of at least
/// `slot + N` i64s where `N` is the serialized length of the variable at
/// `slot` (determined by its TAG). This is upheld by `tir_lower`'s emit
/// sequence — `LoadVar` only materialises slots that exist in the state
/// layout.
#[must_use]
pub unsafe fn handle_from_state_slot(state_ptr: *const i64, slot: i64) -> TlaHandle {
    use super::super::compound_layout::{
        deserialize_value, TAG_BOOL, TAG_INT, TAG_STRING,
    };
    debug_assert!(!state_ptr.is_null(), "handle_from_state_slot: null state_ptr");
    let slot_usize = slot as usize;
    // Fast path: scalar tags encode the value in exactly 2 slots, and we
    // can bypass the full deserializer for cache friendliness.
    let tag = *state_ptr.add(slot_usize);
    match tag {
        TAG_INT => encode_int(*state_ptr.add(slot_usize + 1)),
        TAG_BOOL => {
            let payload = *state_ptr.add(slot_usize + 1);
            ((payload & 1) << HANDLE_TAG_BITS) | H_TAG_BOOL
        }
        TAG_STRING => {
            let payload = *state_ptr.add(slot_usize + 1);
            encode_string(NameId(payload as u32))
        }
        _ => {
            // Compound tag — fall through to the shared deserializer and
            // arena-box. The deserializer's invariants match
            // `compound_layout::serialize_value`.
            //
            // `deserialize_value` walks the slot stream until its terminator;
            // if it fails we surface a NIL handle so the caller can fall
            // back to the interpreter (panicking inside FFI is unsafe).
            //
            // NOTE: `deserialize_value` takes a slice starting at the
            // compound's TAG; we build one spanning `slot..` of the buffer.
            // The caller must guarantee the buffer has at least one slot
            // past the compound, which is a `tir_lower` invariant (it
            // appends a terminator word).
            let slice = std::slice::from_raw_parts(
                state_ptr.add(slot_usize),
                // Over-approximate length: deserialize_value reads only as
                // many slots as the compound claims in its length header.
                // We pass usize::MAX - slot to sidestep the slice's own
                // bounds check; the real bounds are enforced by the layout.
                usize::MAX - slot_usize,
            );
            match deserialize_value(slice, 0) {
                Ok((v, _consumed)) => handle_from_value(&v),
                Err(_) => NIL_HANDLE,
            }
        }
    }
}

// ============================================================================
// Inline scalar encoders (internal)
// ============================================================================

fn encode_int(n: i64) -> TlaHandle {
    if (HANDLE_INT_MIN..=HANDLE_INT_MAX).contains(&n) {
        (n << HANDLE_TAG_BITS) | H_TAG_INT
    } else {
        // Overflow of i61 range → box as BigInt in the arena so the round
        // trip is lossless.
        arena_push(Value::Int(std::sync::Arc::new(BigInt::from(n))))
    }
}

fn encode_string(name_id: NameId) -> TlaHandle {
    // NameId is a u32; widen to i64 then shift. The zero-extended high bits
    // decode cleanly via the mask in `handle_to_value`.
    ((name_id.0 as i64) << HANDLE_TAG_BITS) | H_TAG_STRING
}

// ============================================================================
// Convenience FFI helpers
// ============================================================================

/// Construct a NIL handle. Used by codegen for the `EmptySet` / no-value
/// terminator paths.
#[no_mangle]
pub extern "C" fn tla_handle_nil() -> TlaHandle {
    NIL_HANDLE
}

/// Extract the handle tag. Test helper exposed to exercise the encoding
/// from outside this module.
#[must_use]
pub fn handle_tag(handle: TlaHandle) -> i64 {
    handle & HANDLE_TAG_MASK
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use tla_value::value::{SortedSet, Value};

    fn clear() {
        clear_tla_arena();
    }

    #[test]
    fn round_trip_small_int_inline() {
        clear();
        let h = handle_from_value(&Value::SmallInt(42));
        assert_eq!(handle_tag(h), H_TAG_INT);
        assert_eq!(handle_to_value(h), Value::SmallInt(42));
        // Inline encoding must not touch the arena.
        assert_eq!(arena_len(), 0);
    }

    #[test]
    fn round_trip_negative_int_inline() {
        clear();
        let h = handle_from_value(&Value::SmallInt(-7));
        assert_eq!(handle_tag(h), H_TAG_INT);
        assert_eq!(handle_to_value(h), Value::SmallInt(-7));
        assert_eq!(arena_len(), 0);
    }

    #[test]
    fn round_trip_int_boundaries() {
        clear();
        for n in [HANDLE_INT_MIN, -1, 0, 1, HANDLE_INT_MAX] {
            let h = handle_from_value(&Value::SmallInt(n));
            assert_eq!(handle_tag(h), H_TAG_INT, "tag for {n}");
            assert_eq!(handle_to_value(h), Value::SmallInt(n));
        }
        assert_eq!(arena_len(), 0);
    }

    #[test]
    fn large_int_boxes_to_arena() {
        clear();
        let big = BigInt::from(1i64 << 62);
        let h = handle_from_value(&Value::Int(std::sync::Arc::new(big.clone())));
        assert_eq!(handle_tag(h), H_TAG_ARENA);
        let Value::Int(ref decoded) = handle_to_value(h) else {
            panic!("expected Value::Int");
        };
        assert_eq!(**decoded, big);
        assert_eq!(arena_len(), 1);
    }

    #[test]
    fn round_trip_bool_inline() {
        clear();
        let h_true = handle_from_value(&Value::Bool(true));
        let h_false = handle_from_value(&Value::Bool(false));
        assert_eq!(handle_tag(h_true), H_TAG_BOOL);
        assert_eq!(handle_tag(h_false), H_TAG_BOOL);
        assert_eq!(handle_to_value(h_true), Value::Bool(true));
        assert_eq!(handle_to_value(h_false), Value::Bool(false));
        assert_eq!(arena_len(), 0);
    }

    #[test]
    fn round_trip_boxed_set() {
        clear();
        let set = Value::Set(std::sync::Arc::new(SortedSet::from_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ])));
        let h = handle_from_value(&set);
        assert_eq!(handle_tag(h), H_TAG_ARENA);
        let decoded = handle_to_value(h);
        assert_eq!(decoded, set);
        assert_eq!(arena_len(), 1);
    }

    #[test]
    fn round_trip_boxed_seq() {
        clear();
        use tla_value::value::SeqValue;
        let seq = Value::Seq(std::sync::Arc::new(SeqValue::from_vec(vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
        ])));
        let h = handle_from_value(&seq);
        assert_eq!(handle_tag(h), H_TAG_ARENA);
        assert_eq!(handle_to_value(h), seq);
    }

    #[test]
    fn round_trip_boxed_record() {
        clear();
        use std::sync::Arc;
        use tla_value::value::RecordValue;
        let rec = Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::SmallInt(1)),
            (Arc::from("b"), Value::Bool(true)),
        ]));
        let h = handle_from_value(&rec);
        assert_eq!(handle_tag(h), H_TAG_ARENA);
        assert_eq!(handle_to_value(h), rec);
    }

    #[test]
    fn nil_handle_decodes_to_zero() {
        clear();
        let h = tla_handle_nil();
        assert_eq!(handle_tag(h), H_TAG_NIL);
        assert_eq!(handle_to_value(h), Value::SmallInt(0));
    }

    #[test]
    fn clear_tla_arena_empties_storage() {
        clear();
        let _ = handle_from_value(&Value::Set(std::sync::Arc::new(SortedSet::from_vec(
            vec![Value::SmallInt(1)],
        ))));
        assert_eq!(arena_len(), 1);
        clear_tla_arena();
        assert_eq!(arena_len(), 0);
    }

    #[test]
    fn round_trip_string_inline() {
        clear();
        // `intern_name` returns the existing id if already interned, or
        // interns on demand.
        let s = "hello";
        let name = intern_name(s);
        let h = encode_string(name);
        assert_eq!(handle_tag(h), H_TAG_STRING);
        let Value::String(ref decoded) = handle_to_value(h) else {
            panic!("expected Value::String");
        };
        assert_eq!(decoded.as_ref(), s);
        assert_eq!(arena_len(), 0);
    }
}
