// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Iterative (non-recursive) `Drop` for `Value`.
//!
//! The compiler-generated `Drop` for `Value` recursively descends through
//! compound types (Set, Func, Record, Seq, Tuple, lazy sets, etc.), each
//! containing inner `Value`s that trigger further recursive drops. Profiling
//! shows ~4.5% of CPU time in `Value::drop` across multiple monomorphizations.
//!
//! This module replaces the recursive descent with an iterative loop using a
//! thread-local work stack. When a compound Value is dropped:
//!
//! 1. The Value is placed on the work stack (via `std::mem::replace`)
//! 2. The outer loop pops Values and drops their shells, catching inner Values
//!    via the re-entrant Drop path which pushes them back to the stack
//! 3. This continues until the stack is empty
//!
//! The key benefit is converting recursive drops (which can overflow the call
//! stack for deeply nested structures like sets of sets of sets...) into an
//! iterative loop with a heap-allocated stack.
//!
//! ## Re-entrant Drop Safety
//!
//! When a Value is dropped inside the iterative loop, its fields' drops trigger
//! our custom `Drop::drop`. Since `IN_ITERATIVE_DROP` is set, these re-entrant
//! drops push compound children to the stack for later processing, converting
//! depth into breadth.
//!
//! ## Aliasing Safety
//!
//! The thread-local drop stack uses `UnsafeCell<Vec<Value>>`. The critical
//! invariant: a `&mut Vec` borrow is NEVER held while any Value is dropped.
//! Each stack operation acquires and releases the borrow within its own scope.
//!
//! Part of #3805: Reduce Value::drop overhead from ~4.5% CPU.
#![allow(unsafe_code)]

use super::Value;
use std::cell::Cell;
use std::mem::ManuallyDrop;
use std::sync::Arc;

thread_local! {
    static DROP_STACK: std::cell::UnsafeCell<Vec<Value>> =
        const { std::cell::UnsafeCell::new(Vec::new()) };
}

thread_local! {
    static IN_ITERATIVE_DROP: Cell<bool> = const { Cell::new(false) };
}

impl Drop for Value {
    fn drop(&mut self) {
        // Fast path: leaf values have no inner Values to drop.
        if !is_compound(self) {
            return;
        }

        // Fast path: shared Arc-wrapped values only decrement the refcount.
        // No inner Value drops fire, so the iterative machinery is pure overhead.
        // After our Drop::drop returns, the compiler-generated field drops run,
        // performing the atomic decrement. This is the common case in BFS model
        // checking where Values are shared across fingerprint tables and caches.
        if is_shared_arc(self) {
            return;
        }

        // During thread shutdown, thread-locals may already be destroyed.
        // Fall back to natural (recursive) drop in that case.
        let Ok(in_iterative) = IN_ITERATIVE_DROP.try_with(|c| c.get()) else {
            return;
        };

        // Re-entrant path: push this value for the outer loop to process.
        if in_iterative {
            if let Ok(()) = DROP_STACK.try_with(|cell| {
                let stack = unsafe { &mut *cell.get() };
                let owned = std::mem::replace(self, Value::Bool(false));
                stack.push(owned);
            }) {
                return;
            }
            // DROP_STACK destroyed during thread shutdown — fall through to
            // natural recursive drop.
            return;
        }

        // Outermost compound drop: start the iterative loop.
        let _ = IN_ITERATIVE_DROP.try_with(|c| c.set(true));

        let owned = std::mem::replace(self, Value::Bool(false));
        drop_iterative(owned);

        // Drain the stack iteratively.
        loop {
            let next = DROP_STACK.try_with(|cell| {
                let stack = unsafe { &mut *cell.get() };
                stack.pop()
            });
            match next {
                Ok(Some(v)) => {
                    if !is_compound(&v) {
                        continue;
                    }
                    drop_iterative(v);
                }
                _ => break,
            }
        }

        let _ = IN_ITERATIVE_DROP.try_with(|c| c.set(false));
    }
}

/// Check whether a Value variant is compound (contains inner Values).
#[inline(always)]
fn is_compound(val: &Value) -> bool {
    !matches!(
        val,
        Value::Bool(_)
            | Value::SmallInt(_)
            | Value::Int(_)
            | Value::String(_)
            | Value::ModelValue(_)
            | Value::Interval(_)
            | Value::StringSet
            | Value::AnySet
    )
}

/// Check whether a compound Value's drop would be trivial (just an Arc refcount
/// decrement). When an Arc-wrapped value has refcount > 1, dropping it never
/// touches the inner data — it just decrements the atomic counter. The iterative
/// drop machinery (TLS access, mem::replace, ManuallyDrop) is pure overhead
/// in this common case.
///
/// Returns `true` if the value is a shared Arc-wrapped type where the iterative
/// drop can be skipped. Returns `false` for all other cases (non-Arc types,
/// sole-owner Arcs, inline Box types).
#[inline(always)]
fn is_shared_arc(val: &Value) -> bool {
    match val {
        Value::Set(a) => Arc::strong_count(a) > 1,
        Value::Func(a) => Arc::strong_count(a) > 1,
        Value::IntFunc(a) => Arc::strong_count(a) > 1,
        Value::Seq(a) => Arc::strong_count(a) > 1,
        Value::Tuple(a) => Arc::strong_count(a) > 1,
        Value::Closure(a) => Arc::strong_count(a) > 1,
        Value::LazyFunc(a) => Arc::strong_count(a) > 1,
        Value::RecordSet(a) => Arc::strong_count(a) > 1,
        Value::TupleSet(a) => Arc::strong_count(a) > 1,
        _ => false,
    }
}

#[inline]
fn drop_stack_push(val: Value) {
    // Use try_with instead of with to handle thread shutdown gracefully.
    // During thread destruction, DROP_STACK TLS may already be destroyed.
    // If so, the closure is never called and its captures (including `val`)
    // are dropped when the closure itself is dropped. That re-enters
    // Value::Drop::drop, which also uses try_with and falls through to
    // natural recursive drop on TLS destruction.
    let _ = DROP_STACK.try_with(|cell| {
        // SAFETY: No Value drops happen while this &mut is held.
        // The borrow is released before any Value is dropped.
        let stack = unsafe { &mut *cell.get() };
        stack.push(val);
    });
}


/// Read an owned `T` out of a reference without running drop on the source.
///
/// # Safety
/// - `src` must point to a valid, initialized `T`
/// - The caller must ensure the source location is never used or dropped again
///   (e.g., it lives inside a `ManuallyDrop`)
#[inline]
unsafe fn take<T>(src: &T) -> T {
    std::ptr::read(src as *const T)
}

/// Drop a compound Value iteratively by extracting its payload with ManuallyDrop
/// and letting the payload drop naturally. Inner Values are caught by the
/// re-entrant Drop path and pushed to the stack.
///
/// For inline types (Subset, FuncSet, etc.) with Box<Value> children, we extract
/// the child Values directly to the stack, avoiding one recursion level per child.
/// For Arc-wrapped types, we take the Arc out of ManuallyDrop and let it drop
/// naturally. When the Arc's refcount reaches zero, the inner Values trigger
/// re-entrant drops that push to the stack.
fn drop_iterative(owned: Value) {
    // Wrap in ManuallyDrop to prevent our custom Drop from firing.
    let md = ManuallyDrop::new(owned);

    // Match on a shared reference to determine the variant.
    // We use take() (ptr::read) to move data out of the ManuallyDrop.
    //
    // SAFETY for all take() calls:
    // - md is ManuallyDrop, so its Drop (our custom impl) won't fire
    // - We read each field exactly once, taking full ownership
    // - After the match arm executes, md goes out of scope without dropping
    // - The remaining enum shell (discriminant + non-heap fields) leaks harmlessly
    match &*md {
        // --- Inline Box<Value> types: extract children directly to stack ---
        Value::Subset(subset) => {
            let base: Box<Value> = unsafe { take(&subset.base) };
            drop_stack_push(*base);
        }
        Value::FuncSet(funcset) => {
            let domain: Box<Value> = unsafe { take(&funcset.domain) };
            let codomain: Box<Value> = unsafe { take(&funcset.codomain) };
            drop_stack_push(*domain);
            drop_stack_push(*codomain);
        }
        Value::SetCup(cup) => {
            let set1: Box<Value> = unsafe { take(&cup.set1) };
            let set2: Box<Value> = unsafe { take(&cup.set2) };
            drop_stack_push(*set1);
            drop_stack_push(*set2);
        }
        Value::SetCap(cap) => {
            let set1: Box<Value> = unsafe { take(&cap.set1) };
            let set2: Box<Value> = unsafe { take(&cap.set2) };
            drop_stack_push(*set1);
            drop_stack_push(*set2);
        }
        Value::SetDiff(diff) => {
            let set1: Box<Value> = unsafe { take(&diff.set1) };
            let set2: Box<Value> = unsafe { take(&diff.set2) };
            drop_stack_push(*set1);
            drop_stack_push(*set2);
        }
        Value::KSubset(ksub) => {
            let base: Box<Value> = unsafe { take(&ksub.base) };
            drop_stack_push(*base);
        }
        Value::BigUnion(union_val) => {
            let set: Box<Value> = unsafe { take(&union_val.set) };
            drop_stack_push(*set);
        }
        Value::SeqSet(seqset) => {
            let base: Box<Value> = unsafe { take(&seqset.base) };
            drop_stack_push(*base);
        }

        // --- Arc-wrapped types: take the Arc out and let it drop naturally.
        // Inner Value drops are caught by the re-entrant path. ---
        Value::Set(arc_ref) => {
            let _arc: Arc<super::SortedSet> = unsafe { take(arc_ref) };
        }
        Value::Func(arc_ref) => {
            let _arc: Arc<super::FuncValue> = unsafe { take(arc_ref) };
        }
        Value::IntFunc(arc_ref) => {
            let _arc: Arc<super::IntIntervalFunc> = unsafe { take(arc_ref) };
        }
        Value::Seq(arc_ref) => {
            let _arc: Arc<super::SeqValue> = unsafe { take(arc_ref) };
        }
        Value::Tuple(arc_ref) => {
            let _arc: Arc<[Value]> = unsafe { take(arc_ref) };
        }
        Value::Closure(arc_ref) => {
            let _arc: Arc<super::ClosureValue> = unsafe { take(arc_ref) };
        }
        Value::LazyFunc(arc_ref) => {
            let _arc: Arc<super::LazyFuncValue> = unsafe { take(arc_ref) };
        }
        Value::RecordSet(arc_ref) => {
            let _arc: Arc<super::RecordSetValue> = unsafe { take(arc_ref) };
        }
        Value::TupleSet(arc_ref) => {
            let _arc: Arc<super::TupleSetValue> = unsafe { take(arc_ref) };
        }

        // Record is inline (not behind Arc) -- take its entries Arc
        Value::Record(rec) => {
            let _entries: Arc<Vec<(tla_core::NameId, Value)>> = unsafe { take(&rec.entries) };
        }

        // SetPred is Box-wrapped
        Value::SetPred(pred) => {
            let _pred: Box<super::SetPredValue> = unsafe { take(pred) };
        }

        // Leaf values should not reach here (guarded by is_compound).
        // If they do, the ManuallyDrop leaks harmlessly.
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use std::sync::Arc;

    /// Dropping deeply nested Values must not overflow the stack.
    #[test]
    fn test_deep_nested_set_drop() {
        let mut v = Value::int(42);
        for _ in 0..10_000 {
            v = Value::set([v]);
        }
        drop(v);
    }

    /// Shared values (Arc refcount > 1) are handled correctly.
    #[test]
    fn test_shared_arc_drop() {
        let set = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
        let clone1 = set.clone();
        let clone2 = set.clone();
        drop(set);
        assert_eq!(clone1, clone2);
        drop(clone1);
        drop(clone2);
    }

    /// All compound types drop correctly through the iterative path.
    #[test]
    fn test_compound_type_drops() {
        let rec = Value::Record(RecordValue::from_sorted_entries(vec![
            (tla_core::intern_name("a"), Value::int(1)),
            (tla_core::intern_name("b"), Value::int(2)),
        ]));
        drop(rec);

        let tup = Value::Tuple(Arc::from(vec![Value::int(1), Value::int(2)]));
        drop(tup);

        let seq = Value::seq([Value::int(1), Value::int(2)]);
        drop(seq);

        let nested = Value::set([
            Value::set([Value::int(1), Value::int(2)]),
            Value::set([Value::int(3), Value::int(4)]),
        ]);
        drop(nested);

        let set_of_rec = Value::set([Value::Record(RecordValue::from_sorted_entries(vec![
            (tla_core::intern_name("x"), Value::int(99)),
        ]))]);
        drop(set_of_rec);
    }

    /// Leaf values have minimal overhead from the custom Drop.
    #[test]
    fn test_leaf_value_drops() {
        drop(Value::Bool(true));
        drop(Value::SmallInt(42));
        drop(Value::string("hello"));
        drop(Value::StringSet);
        drop(Value::AnySet);
    }
}
