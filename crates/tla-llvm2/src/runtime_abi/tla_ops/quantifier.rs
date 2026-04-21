// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla_quantifier_*` runtime helpers — handle-based FFI for Phase 5
//! quantifier (Forall/Exists/Choose) iteration.
//!
//! `tir_lower::lower_quantifier_begin` / `lower_quantifier_next`
//! (`tmir_lower.rs:1813-2145`) emit a three-step loop skeleton around a
//! set-domain iterator:
//!
//! 1. `tla_quantifier_iter_new(domain_handle) -> iter_handle` once per
//!    quantifier, to materialize the iteration state.
//! 2. `tla_quantifier_iter_done(iter_handle) -> i64 (0 or 1)` before each
//!    yield — 1 means the iterator has no more elements.
//! 3. `tla_quantifier_iter_next(iter_handle) -> elem_handle` to fetch the
//!    current element and advance past it.
//!
//! A fourth helper, `tla_quantifier_runtime_error()`, is called for CHOOSE
//! on empty / exhausted domains. It must not return.
//!
//! # Iteration order — soundness contract (design §7.1 R2)
//!
//! For witness parity with the interpreter, the order returned by
//! [`tla_quantifier_iter_next`] MUST match the interpreter's canonical
//! set iteration order (`tla_value::Value::iter_set`, which delegates to
//! [`tla_value::value::SortedSet::iter`] for `Value::Set` and to
//! `LazySet::set_iter_owned` for lazy compound sets).
//!
//! We achieve parity by materialising the domain via
//! [`Value::to_sorted_set`] and then iterating its normalized slice in
//! index order. `SortedSet::iter` returns `normalized_slice().iter()` —
//! the same sorted order the interpreter uses — so the two paths agree
//! by construction.
//!
//! # Iterator state — arena lifetime
//!
//! The [`IteratorState`] holds the materialised `Vec<Value>` snapshot and
//! a position cursor. It is boxed into a per-worker-thread arena
//! (`TLA_ITER_ARENA`) and referenced via an arena-tagged handle. Like the
//! value arena ([`handle::clear_tla_arena`]), the iterator arena is
//! cleared at action boundaries through [`clear_tla_iter_arena`]; all
//! live iterator handles are invalidated on clear.
//!
//! # Soundness contract
//!
//! - Every helper unboxes input handles via
//!   [`super::handle::handle_to_value`] and reboxes results via
//!   [`super::handle::handle_from_value`] / [`NIL_HANDLE`]. No semantic
//!   logic is re-implemented.
//! - A non-set domain falls back to an empty iterator whose handle
//!   reports `done() == 1` immediately, so tir_lower's empty-domain
//!   branches (vacuous `\A`, false `\E`, CHOOSE runtime error) take the
//!   correct path. An alternative would be returning [`NIL_HANDLE`] from
//!   `iter_new`, but subsequent `iter_done(NIL)` would have to decide a
//!   value for NIL — empty-iter is the less error-prone contract.
//! - `tla_quantifier_runtime_error()` aborts the process via
//!   `std::process::abort()`. Panicking across the FFI boundary is
//!   undefined behaviour, and the IR emitter places an `unreachable`
//!   after the call — so not returning is the only sound option.
//!
//! Part of #4318 (R27 Option B). Design doc:
//! `designs/2026-04-20-llvm2-runtime-abi-scope.md` §2.6, §7.1 R2.

use std::cell::RefCell;

use tla_value::value::Value;

use super::handle::{handle_from_value, handle_to_value, TlaHandle, HANDLE_INT_MAX};

// ============================================================================
// Iterator state + arena
// ============================================================================

/// Materialised iterator snapshot over a set domain.
///
/// The snapshot is owned outright so subsequent mutation of the source
/// value (re-using arena slots at the next action boundary, for example)
/// cannot disturb an in-flight loop.
pub(crate) struct IteratorState {
    /// Fully materialised sequence of elements in interpreter-parity
    /// sorted order.
    values: Vec<Value>,
    /// Index of the next element to return. `pos == values.len()` means
    /// exhausted.
    pos: usize,
}

impl IteratorState {
    fn new(values: Vec<Value>) -> Self {
        Self { values, pos: 0 }
    }

    #[inline]
    fn done(&self) -> bool {
        self.pos >= self.values.len()
    }

    /// Return the element at the current cursor and advance. Returns
    /// `None` if the iterator is already exhausted.
    fn advance(&mut self) -> Option<Value> {
        if self.done() {
            return None;
        }
        let out = self.values[self.pos].clone();
        self.pos += 1;
        Some(out)
    }
}

thread_local! {
    /// Per-worker arena of iterator states. Mirrors the [`TLA_ARENA`]
    /// discipline in [`handle`](super::handle): cleared at action
    /// boundaries; entries are owned and indices are stable for the
    /// lifetime of one action.
    static TLA_ITER_ARENA: RefCell<Vec<IteratorState>> = const { RefCell::new(Vec::new()) };
}

/// Clear the per-worker iterator arena. Must be called at action
/// boundaries alongside [`handle::clear_tla_arena`](super::handle::clear_tla_arena).
///
/// This is a separate entry point so tests can exercise the iterator
/// arena in isolation; production callers typically invoke both in
/// sequence.
#[no_mangle]
pub extern "C" fn clear_tla_iter_arena() {
    TLA_ITER_ARENA.with(|arena| arena.borrow_mut().clear());
}

/// Number of live iterators in the arena — debug/test helper.
#[cfg(test)]
pub(crate) fn iter_arena_len() -> usize {
    TLA_ITER_ARENA.with(|arena| arena.borrow().len())
}

// ============================================================================
// Handle encoding
// ============================================================================
//
// Iterator handles are **raw i64 arena indices**, not `TlaHandle`
// tag-encoded values. The IR emitter treats the iterator handle as an
// opaque `i64` carried through `%qiter_N_ptr` allocas and never runs it
// through `handle_to_value` (it only passes it back to the quantifier
// helpers). Keeping the encoding raw avoids paying for tag/untag on the
// hot loop and keeps the value arena disjoint from the iterator arena.
//
// A sentinel of `-1` denotes "no iterator" — used when the domain was
// not a set. Any `iter_done(-1)` returns 1 immediately, and
// `iter_next(-1)` returns NIL — this matches tir_lower's empty-domain
// fast path.

/// Sentinel handle: iteration over a non-set domain. `iter_done` returns
/// 1 and `iter_next` returns [`NIL_HANDLE`](super::handle::NIL_HANDLE).
const EMPTY_ITER_HANDLE: i64 = -1;

/// Arena-push an iterator state and return its raw-index handle.
fn iter_arena_push(state: IteratorState) -> i64 {
    TLA_ITER_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let idx = arena.len();
        arena.push(state);
        // Bound-check against i61 range so we cannot alias EMPTY_ITER_HANDLE
        // (-1) or overflow downstream consumers. The bound is shared with
        // the value arena — one action's worth of iterators should never
        // come close.
        match i64::try_from(idx) {
            Ok(n) if n <= HANDLE_INT_MAX => n,
            _ => {
                // Arena overflow is a programmer bug: clear_tla_iter_arena
                // was not invoked at the previous action boundary. Abort
                // rather than panic — `iter_arena_push` is called
                // transitively from `extern "C" fn tla_quantifier_iter_new`,
                // so unwinding here would be undefined behaviour (#4333).
                //
                // Drop the entry we just pushed so the arena length does
                // not diverge from its reported capacity.
                let _ = arena.pop();
                super::ait_ffi_abort(
                    "quantifier::iter_arena_push: iterator arena overflowed i61 bound — \
                     clear_tla_iter_arena not called?",
                );
            }
        }
    })
}

// ============================================================================
// Extern "C" helpers
// ============================================================================

/// Construct an iterator over the set `domain`.
///
/// Returns a raw-index handle into the per-worker iterator arena. A
/// non-set (or otherwise non-enumerable) domain yields the
/// [`EMPTY_ITER_HANDLE`] sentinel, which behaves as an empty iterator
/// for the subsequent `done` / `next` calls — matching tir_lower's
/// empty-domain fast paths.
///
/// Iteration order matches the interpreter's canonical set order via
/// [`Value::to_sorted_set`] → [`SortedSet::iter`] (design §7.1 R2).
#[no_mangle]
pub extern "C" fn tla_quantifier_iter_new(domain: TlaHandle) -> i64 {
    let v = handle_to_value(domain);
    let Some(sorted) = v.to_sorted_set() else {
        return EMPTY_ITER_HANDLE;
    };
    // `SortedSet::iter` walks the normalized, sorted slice — the same
    // order `Value::iter_set` exposes to the interpreter. We collect into
    // a Vec so the iterator state is self-contained (independent of the
    // source `SortedSet` Arc's lifetime) and the arena entry is freely
    // movable.
    let values: Vec<Value> = sorted.iter().cloned().collect();
    iter_arena_push(IteratorState::new(values))
}

/// Return 1 if the iterator has no more elements, 0 otherwise.
///
/// The [`EMPTY_ITER_HANDLE`] sentinel (`-1`) always reports done.
/// Out-of-range handles also report done defensively — they can only
/// arise from a compiler bug and short-circuiting the loop is the least
/// unsafe recovery.
#[no_mangle]
pub extern "C" fn tla_quantifier_iter_done(iter: i64) -> i64 {
    if iter == EMPTY_ITER_HANDLE {
        return 1;
    }
    TLA_ITER_ARENA.with(|arena| {
        let arena = arena.borrow();
        let idx = iter as usize;
        match arena.get(idx) {
            Some(state) => i64::from(state.done()),
            None => 1,
        }
    })
}

/// Advance the iterator and return the current element as a
/// [`TlaHandle`]. Returns [`super::handle::NIL_HANDLE`] when exhausted
/// or when called with the empty-iter sentinel — tir_lower's emitted
/// loop skeleton always brackets `iter_next` with an `iter_done` check
/// so this path should only trigger on the empty-domain fast path where
/// the returned NIL is discarded.
#[no_mangle]
pub extern "C" fn tla_quantifier_iter_next(iter: i64) -> TlaHandle {
    if iter == EMPTY_ITER_HANDLE {
        return super::handle::NIL_HANDLE;
    }
    TLA_ITER_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let idx = iter as usize;
        match arena.get_mut(idx) {
            Some(state) => match state.advance() {
                Some(v) => handle_from_value(&v),
                None => super::handle::NIL_HANDLE,
            },
            None => super::handle::NIL_HANDLE,
        }
    })
}

/// Runtime-error marker for CHOOSE on an empty or exhausted domain.
///
/// Never returns — the emitted IR places an `unreachable` instruction
/// immediately after the call (`tmir_lower.rs:1889-1892,2129-2132`).
/// We call [`std::process::abort`] because:
///
/// 1. Panicking across an `extern "C"` boundary is undefined behaviour
///    on most platforms; the unwinder cannot safely traverse the JIT's
///    register-only frames.
/// 2. A runtime-error CHOOSE indicates a spec bug that the tree-walking
///    interpreter would report as `EvalError::NoChooseMatch`. Surfacing
///    it as an abort keeps compiled execution at least as loud as the
///    interpreter, and avoids a soundness hole where the wrong result
///    is returned.
///
/// A future follow-up may replace the abort with a controlled unwind
/// once the JIT grows catch-frames; for now, abort is the only
/// FFI-safe option.
#[no_mangle]
pub extern "C" fn tla_quantifier_runtime_error() -> ! {
    // Emit a short diagnostic so the abort is not totally silent in
    // development. Production error reporting goes through the
    // interpreter fallback path.
    eprintln!(
        "tla_quantifier_runtime_error: CHOOSE predicate unsatisfied on \
         compiled path (aborting)"
    );
    std::process::abort();
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::super::handle::{clear_tla_arena, handle_to_value, NIL_HANDLE};
    use super::*;
    use tla_value::value::{SortedSet, Value};

    fn fresh() {
        clear_tla_arena();
        clear_tla_iter_arena();
    }

    fn small_int_set(xs: &[i64]) -> Value {
        Value::set(xs.iter().copied().map(Value::SmallInt).collect::<Vec<_>>())
    }

    #[test]
    fn iter_new_on_empty_set_is_done_immediately() {
        fresh();
        let empty = super::super::handle::handle_from_value(&Value::empty_set());
        let iter = tla_quantifier_iter_new(empty);
        assert_eq!(tla_quantifier_iter_done(iter), 1);
    }

    #[test]
    fn iter_new_on_non_set_returns_empty_iter_sentinel() {
        fresh();
        // A scalar handle is not a set — iter_new should fall back to
        // the empty-iter sentinel so tir_lower's vacuous/false/CHOOSE
        // branches take the empty-domain path.
        let scalar = super::super::handle::handle_from_value(&Value::SmallInt(7));
        let iter = tla_quantifier_iter_new(scalar);
        assert_eq!(iter, EMPTY_ITER_HANDLE);
        assert_eq!(tla_quantifier_iter_done(iter), 1);
        assert_eq!(tla_quantifier_iter_next(iter), NIL_HANDLE);
    }

    #[test]
    fn iter_yields_elements_in_sorted_order_small() {
        fresh();
        let set_h = super::super::handle::handle_from_value(&small_int_set(&[7, 3, 5, 1]));
        let iter = tla_quantifier_iter_new(set_h);
        let mut yielded = Vec::new();
        for _ in 0..8 {
            if tla_quantifier_iter_done(iter) != 0 {
                break;
            }
            let h = tla_quantifier_iter_next(iter);
            yielded.push(handle_to_value(h));
        }
        let expected = vec![
            Value::SmallInt(1),
            Value::SmallInt(3),
            Value::SmallInt(5),
            Value::SmallInt(7),
        ];
        assert_eq!(yielded, expected);
        // After draining, done must be 1 and next returns NIL.
        assert_eq!(tla_quantifier_iter_done(iter), 1);
        assert_eq!(tla_quantifier_iter_next(iter), NIL_HANDLE);
    }

    #[test]
    fn iter_order_matches_interpreter_1357() {
        // Explicit parity test for the {1, 3, 5, 7} case called out in
        // the task spec: the runtime helper must yield the same sequence
        // as `Value::iter_set` for the same input.
        fresh();
        let interp: Vec<Value> = small_int_set(&[1, 3, 5, 7])
            .iter_set()
            .expect("set is enumerable")
            .collect();

        let set_h = super::super::handle::handle_from_value(&small_int_set(&[1, 3, 5, 7]));
        let iter = tla_quantifier_iter_new(set_h);
        let mut compiled = Vec::new();
        while tla_quantifier_iter_done(iter) == 0 {
            let h = tla_quantifier_iter_next(iter);
            compiled.push(handle_to_value(h));
        }
        assert_eq!(compiled, interp);
    }

    #[test]
    fn iter_done_matches_position_each_step() {
        fresh();
        let set_h = super::super::handle::handle_from_value(&small_int_set(&[10, 20, 30]));
        let iter = tla_quantifier_iter_new(set_h);
        // Step through and check done between each advance.
        assert_eq!(tla_quantifier_iter_done(iter), 0);
        let _ = tla_quantifier_iter_next(iter);
        assert_eq!(tla_quantifier_iter_done(iter), 0);
        let _ = tla_quantifier_iter_next(iter);
        assert_eq!(tla_quantifier_iter_done(iter), 0);
        let _ = tla_quantifier_iter_next(iter);
        assert_eq!(tla_quantifier_iter_done(iter), 1);
    }

    #[test]
    fn iter_over_lazy_set_materialises_sorted_order() {
        // Intervals are LazySet values. `to_sorted_set()` must produce
        // the same order as `Value::iter_set` does for them.
        fresh();
        use num_bigint::BigInt;
        use tla_value::value::range_set;
        let lazy = range_set(&BigInt::from(3), &BigInt::from(6));
        let set_h = super::super::handle::handle_from_value(&lazy);
        let iter = tla_quantifier_iter_new(set_h);
        let mut yielded: Vec<i64> = Vec::new();
        while tla_quantifier_iter_done(iter) == 0 {
            let h = tla_quantifier_iter_next(iter);
            yielded.push(handle_to_value(h).as_i64().expect("int"));
        }
        assert_eq!(yielded, vec![3, 4, 5, 6]);
    }

    #[test]
    fn multiple_iters_coexist_independently() {
        fresh();
        let a = super::super::handle::handle_from_value(&small_int_set(&[1, 2]));
        let b = super::super::handle::handle_from_value(&small_int_set(&[10, 20]));
        let ia = tla_quantifier_iter_new(a);
        let ib = tla_quantifier_iter_new(b);
        assert_ne!(ia, ib, "independent iterators must have distinct handles");
        // Fully drain A then B and confirm B is unaffected.
        while tla_quantifier_iter_done(ia) == 0 {
            let _ = tla_quantifier_iter_next(ia);
        }
        let mut b_vals: Vec<i64> = Vec::new();
        while tla_quantifier_iter_done(ib) == 0 {
            let h = tla_quantifier_iter_next(ib);
            b_vals.push(handle_to_value(h).as_i64().expect("int"));
        }
        assert_eq!(b_vals, vec![10, 20]);
    }

    #[test]
    fn clear_tla_iter_arena_empties_storage() {
        fresh();
        let s = super::super::handle::handle_from_value(&small_int_set(&[1, 2, 3]));
        let _ = tla_quantifier_iter_new(s);
        assert_eq!(iter_arena_len(), 1);
        clear_tla_iter_arena();
        assert_eq!(iter_arena_len(), 0);
    }

    #[test]
    fn iter_over_boxed_sorted_set_value() {
        // Direct `Value::Set(Arc<SortedSet>)` input — the most common
        // shape produced by `tla_set_enum_N` helpers. Ensures the Set
        // match arm in `to_sorted_set` yields the same order as the
        // SortedSet's own `iter()`.
        fresh();
        let ss = SortedSet::from_vec(vec![
            Value::SmallInt(30),
            Value::SmallInt(10),
            Value::SmallInt(20),
        ]);
        let expected: Vec<Value> = ss.iter().cloned().collect();
        let boxed = Value::Set(std::sync::Arc::new(ss));
        let set_h = super::super::handle::handle_from_value(&boxed);
        let iter = tla_quantifier_iter_new(set_h);
        let mut yielded = Vec::new();
        while tla_quantifier_iter_done(iter) == 0 {
            yielded.push(handle_to_value(tla_quantifier_iter_next(iter)));
        }
        assert_eq!(yielded, expected);
    }

    // `tla_quantifier_runtime_error` is intentionally NOT unit-tested —
    // calling it terminates the test process via `std::process::abort`.
    // Coverage is limited to the symbol-map smoke test, which confirms
    // the pointer is registered and non-null.
}
