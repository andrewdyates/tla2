// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC-normalized iteration APIs and thread-local sort cache.
//!
//! Provides `iter_set_tlc_normalized` and `tlc_first_element` for bounded
//! `CHOOSE` parity with TLC. The thread-local cache avoids O(n²) re-sorting
//! when the same set is iterated multiple times per state evaluation.
//! Extracted from `tlc_cmp.rs` as part of #3309.

use super::{FuncSetIterator, KSubsetIterator, SubsetIterator, Value};
use crate::error::{EvalError, EvalResult};
use std::cmp::Ordering;
use std::sync::Arc;

// Part of #3073, #3063: Thread-local cache for TLC-normalized set element orders.
//
// When the evaluator iterates a set of non-safe types (Records, Tuples, etc.)
// via iter_set_tlc_normalized, TLC's insertion sort must reorder the elements.
// In MultiPaxos, the `msgs` set (up to 500 records) is iterated ~9 times per
// state via \E quantifiers. Without caching, each iteration re-sorts O(n²).
//
// This cache maps the `Arc<[Value]>` data pointer (stable across SortedSet
// clones) to the TLC-sorted element vector. Thread-local avoids synchronization
// overhead; the model checker uses sequential mode for MultiPaxos.
//
// The cache holds at most one entry — the most recently sorted set. This is
// optimal for the common pattern where the same large set (msgs) is iterated
// multiple times consecutively during one state's evaluation.
//
// Safety: The cache stores the original Arc<[Value]> alongside the sorted result.
// This prevents deallocation of the backing array, ensuring the Arc pointer
// identity check cannot match a stale (reused) allocation.
// Part of #3073: Store sorted result as Arc<[Value]> instead of Vec<Value>.
// On cache hit, Arc::clone is O(1) (atomic increment) vs Vec::clone which is
// O(n) Value clones. For EXISTS short-circuit, elements are cloned on demand
// — only K clones instead of N when short-circuiting at position K.
type TlcNormCacheEntry = Option<(Arc<[Value]>, Arc<[Value]>)>;
thread_local! {
    static TLC_NORM_CACHE: std::cell::RefCell<TlcNormCacheEntry> =
        const { std::cell::RefCell::new(None) };
}

/// Clear the thread-local TLC normalization cache.
/// Call between model checking runs to free memory.
pub(crate) fn clear_tlc_norm_cache() {
    TLC_NORM_CACHE.with(|cache| {
        *cache.borrow_mut() = None;
    });
}

/// Stack-allocated iterator for TLC-normalized set iteration.
///
/// Part of #3364: Eliminates `Box<dyn Iterator>` heap allocation on the quantifier
/// hot path. For the common case (homogeneous safe `Value::Set`), the iterator is
/// a zero-alloc `Cloned<slice::Iter>`. All other cases fall back to a boxed iterator.
pub enum TlcSetIterInline<'a> {
    /// Homogeneous safe set — stored order IS TLC order. Zero heap allocation.
    SliceCloned(std::iter::Cloned<std::slice::Iter<'a, Value>>),
    /// Fallback for non-safe sets, intervals, materialized sets, etc.
    Boxed(Box<dyn Iterator<Item = Value> + 'a>),
}

impl Iterator for TlcSetIterInline<'_> {
    type Item = Value;

    #[inline]
    fn next(&mut self) -> Option<Value> {
        match self {
            TlcSetIterInline::SliceCloned(it) => it.next(),
            TlcSetIterInline::Boxed(it) => it.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            TlcSetIterInline::SliceCloned(it) => it.size_hint(),
            TlcSetIterInline::Boxed(it) => it.size_hint(),
        }
    }
}

impl Value {
    /// Iterate over this set-like value in TLC's "normalized order" (used by bounded `CHOOSE`).
    ///
    /// This is parity-critical: TLC evaluates bounded `CHOOSE` by normalizing the domain and
    /// then iterating in `Enumerable.Ordering.NORMALIZED`, which is defined by TLC's per-type
    /// `compareTo` rules (including their error behavior for incomparable values).
    pub fn iter_set_tlc_normalized(&self) -> EvalResult<Box<dyn Iterator<Item = Value> + '_>> {
        if !self.is_set() {
            return Err(EvalError::type_error("Set", self, None));
        }

        match self {
            Value::Interval(iv) => Ok(Box::new(iv.iter_values())),
            // Part of #2955: SortedSet elements are pre-sorted by Value::cmp.
            // For HOMOGENEOUS sets of safe types (Bool, Int, String), Value::cmp
            // agrees with tlc_cmp, so the stored order IS TLC-normalized order.
            // Mixed-type sets (e.g., {Bool, Int}) or unsafe types (Tuple, Set,
            // ModelValue, Record, Func) must fall through to tlc_sort_nodup.
            // Check both first and last: SortedSet groups by discriminant, so if
            // first and last share a type class, all elements do.
            Value::Set(ss) => {
                // Fast path: homogeneous safe types — stored order IS TLC order.
                let homogeneous_safe = match (ss.first(), ss.last()) {
                    (Some(f), Some(l)) => {
                        Self::tlc_cmp_agrees_with_ord(f)
                            && Self::tlc_cmp_type_class(f) == Self::tlc_cmp_type_class(l)
                    }
                    _ => true, // empty sets are trivially safe
                };
                if homogeneous_safe {
                    return Ok(Box::new(ss.iter().cloned()));
                }
                // Part of #3073, #3063: Thread-local cache for non-safe sets.
                // The cache stores the Arc<[Value]> itself (not just a raw pointer)
                // to prevent deallocation and ensure identity checks are safe.
                // Arc::ptr_eq compares data pointers — stable across SortedSet
                // clones (all share the same Arc). This avoids O(n²) re-sorting
                // when the same set is iterated multiple times per state
                // (e.g., MultiPaxos `msgs` iterated ~9 times via \E quantifiers).
                let arc = ss.to_arc_slice();
                let cached = TLC_NORM_CACHE.with(|cache| {
                    let borrow = cache.borrow();
                    if let Some((ref cached_arc, ref sorted)) = *borrow {
                        if Arc::ptr_eq(cached_arc, &arc) {
                            return Some(Arc::clone(sorted));
                        }
                    }
                    None
                });
                if let Some(sorted_arc) = cached {
                    // Part of #3073: lazy clone — only clone elements consumed
                    // by the caller. EXISTS short-circuit clones K instead of N.
                    let len = sorted_arc.len();
                    return Ok(Box::new((0..len).map(move |i| sorted_arc[i].clone())));
                }
                // Cache miss: sort, convert to Arc, and store
                let sorted_arc: Arc<[Value]> =
                    Self::tlc_sort_nodup(ss.iter().cloned().collect())?.into();
                TLC_NORM_CACHE.with(|cache| {
                    *cache.borrow_mut() = Some((arc, Arc::clone(&sorted_arc)));
                });
                let len = sorted_arc.len();
                Ok(Box::new((0..len).map(move |i| sorted_arc[i].clone())))
            }
            Value::Subset(sv) => {
                let base_elems: Vec<Value> = sv.base.as_ref().iter_set_tlc_normalized()?.collect();
                Ok(Box::new(SubsetIterator::from_elements(base_elems)))
            }
            Value::KSubset(ksv) => {
                let base_elems: Vec<Value> = ksv.base.as_ref().iter_set_tlc_normalized()?.collect();
                Ok(Box::new(KSubsetIterator::from_elements(base_elems, ksv.k)))
            }
            Value::FuncSet(fs) => {
                // Fix #2364: Lazy odometer iteration for [S -> T] in TLC-normalized order.
                //
                // The generic fallback below materializes ALL |T|^|S| functions and sorts
                // them, which is O(|T|^|S| * log(|T|^|S|)) — catastrophic for large sets.
                // For [Node -> Node] with 5 nodes, that's 3125 functions sorted.
                //
                // Instead, get domain/range elements in TLC-normalized order and use the
                // odometer iterator directly. The odometer's enumeration order (last domain
                // element changes fastest) matches TLC's SetOfFcnsValue.elements() order
                // when domain/range elements are in canonical order.
                let domain_elems: Vec<Value> = fs.domain.iter_set_tlc_normalized()?.collect();
                let codomain_elems: Vec<Value> = fs.codomain.iter_set_tlc_normalized()?.collect();
                Ok(Box::new(FuncSetIterator::from_elems(
                    domain_elems,
                    codomain_elems,
                )))
            }
            _ => {
                let iter = self
                    .iter_set()
                    .ok_or(EvalError::SetTooLarge { span: None })?;
                let elems = Self::tlc_sort_nodup(iter.collect())?;
                Ok(Box::new(elems.into_iter()))
            }
        }
    }

    /// Stack-allocated variant of `iter_set_tlc_normalized` for hot paths.
    ///
    /// Part of #3364: Avoids `Box<dyn Iterator>` for the most common case:
    /// - `Value::Set` with homogeneous safe types → `SliceCloned` (zero heap alloc)
    ///
    /// All other cases fall back to `Boxed` via the existing `iter_set_tlc_normalized`.
    pub fn iter_set_tlc_normalized_inline(&self) -> EvalResult<TlcSetIterInline<'_>> {
        match self {
            Value::Set(ss) => {
                let homogeneous_safe = match (ss.first(), ss.last()) {
                    (Some(f), Some(l)) => {
                        Self::tlc_cmp_agrees_with_ord(f)
                            && Self::tlc_cmp_type_class(f) == Self::tlc_cmp_type_class(l)
                    }
                    _ => true,
                };
                if homogeneous_safe {
                    Ok(TlcSetIterInline::SliceCloned(ss.iter().cloned()))
                } else {
                    // Non-safe types: delegate to boxed path (sort cache, etc.)
                    Ok(TlcSetIterInline::Boxed(self.iter_set_tlc_normalized()?))
                }
            }
            _ => Ok(TlcSetIterInline::Boxed(self.iter_set_tlc_normalized()?)),
        }
    }

    /// Return the minimum element of a set in TLC comparison order without fully sorting.
    ///
    /// Part of #2955: O(n) scan instead of O(n log n) sort for `CHOOSE x \in S : TRUE`.
    /// Returns the same element that `iter_set_tlc_normalized().next()` would return,
    /// but avoids allocating and sorting the full element vector.
    pub fn tlc_first_element(&self) -> EvalResult<Option<Value>> {
        if !self.is_set() {
            return Err(EvalError::type_error("Set", self, None));
        }
        match self {
            Value::Interval(iv) => {
                if iv.is_empty() {
                    Ok(None)
                } else {
                    // Interval elements are already in ascending order
                    Ok(iv.iter_values().next())
                }
            }
            // Part of #2955: O(1) for SortedSet when ALL elements are the same
            // safe type class. Must check both first and last: SortedSet groups
            // by discriminant, so same type class at endpoints means homogeneous.
            // Mixed-type sets (e.g., {ModelValue, Int}) fall through to O(n) scan.
            Value::Set(ss) => {
                let homogeneous_safe = match (ss.first(), ss.last()) {
                    (Some(f), Some(l)) => {
                        Self::tlc_cmp_agrees_with_ord(f)
                            && Self::tlc_cmp_type_class(f) == Self::tlc_cmp_type_class(l)
                    }
                    _ => false,
                };
                if homogeneous_safe {
                    Ok(ss.first().cloned())
                } else if ss.is_empty() {
                    Ok(None)
                } else {
                    // Part of #2955: O(1) for same-length tuples of safe types.
                    // TLC's tuple comparison is length-first, then element-wise.
                    // Value::cmp is element-wise (lexicographic). These agree when
                    // all tuples have the same length, reducing to element-wise
                    // comparison in both orderings. Verify: (1) all elements are
                    // tuples of the same length, (2) first tuple's elements are
                    // safe types (well-typed TLA+ guarantees all tuples in the set
                    // share element types).
                    if let Some(Value::Tuple(first_t)) = ss.first() {
                        let expected_len = first_t.len();
                        if expected_len > 0
                            && first_t.iter().all(Self::tlc_cmp_agrees_with_ord)
                            && ss
                                .iter()
                                .all(|v| matches!(v, Value::Tuple(t) if t.len() == expected_len))
                        {
                            return Ok(ss.first().cloned());
                        }
                    }
                    self.tlc_first_element_scan()
                }
            }
            _ => self.tlc_first_element_scan(),
        }
    }

    /// O(n) scan fallback for tlc_first_element — finds minimum by tlc_cmp.
    fn tlc_first_element_scan(&self) -> EvalResult<Option<Value>> {
        let iter = self
            .iter_set()
            .ok_or(EvalError::SetTooLarge { span: None })?;
        let mut min: Option<Value> = None;
        for elem in iter {
            min = Some(match min {
                None => elem,
                Some(current_min) => {
                    match Self::tlc_cmp(&elem, &current_min) {
                        Ok(Ordering::Less) => elem,
                        Ok(_) => current_min,
                        Err(_) => {
                            // Incomparable elements — fall through to full sort
                            // which will produce the correct error
                            return self.iter_set_tlc_normalized().map(|mut it| it.next());
                        }
                    }
                }
            });
        }
        Ok(min)
    }
}
