// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `impl Value` set-like predicates and enumerable-set adapters.

use super::super::*;

impl Value {
    pub fn is_set(&self) -> bool {
        match self {
            Value::Set(_)
            | Value::Interval(_)
            | Value::Subset(_)
            | Value::FuncSet(_)
            | Value::RecordSet(_)
            | Value::TupleSet(_)
            | Value::SetCup(_)
            | Value::SetCap(_)
            | Value::SetDiff(_)
            | Value::SetPred(_)
            | Value::KSubset(_)
            | Value::BigUnion(_)
            | Value::StringSet
            | Value::AnySet
            | Value::SeqSet(_) => true,
            // ModelValue for infinite sets (Nat, Int, Real)
            Value::ModelValue(name) => matches!(name.as_ref(), "Nat" | "Int" | "Real"),
            _ => false,
        }
    }

    /// Check if this value is a finite set.
    ///
    /// Returns `true` for sets with finitely many elements, `false` for infinite
    /// sets (Nat, Int, Real, STRING, Seq(S), AnySet) and non-set values.
    /// Recurses on composite set types matching TLC's `isFinite()` semantics.
    ///
    /// Part of #1508: IsFiniteSet must check semantic finiteness, not just `is_set()`.
    pub fn is_finite_set(&self) -> bool {
        match self {
            // Materialized sets are always finite
            Value::Set(_) | Value::Interval(_) => true,
            // Composite sets: finite iff components are finite
            Value::Subset(sv) => sv.base.is_finite_set(),
            Value::FuncSet(fsv) => fsv.domain.is_finite_set() && fsv.codomain.is_finite_set(),
            Value::RecordSet(rsv) => rsv.fields.values().all(|v| v.is_finite_set()),
            Value::TupleSet(tsv) => tsv.components.iter().all(|c| c.is_finite_set()),
            Value::SetCup(scv) => scv.set1.is_finite_set() && scv.set2.is_finite_set(),
            Value::SetCap(scv) => scv.set1.is_finite_set() || scv.set2.is_finite_set(),
            Value::SetDiff(sdv) => sdv.set1.is_finite_set(),
            Value::SetPred(spv) => spv.source.is_finite_set(),
            Value::KSubset(ksv) => ksv.base.is_finite_set(),
            Value::BigUnion(_) => {
                // Conservative: we cannot recurse into elements without eval context.
                // TLC enumerates elements and checks each — we approximate by checking
                // if the outer set itself is finite (which it must be to enumerate).
                // A finite union of finite sets is finite, but we can't check inner
                // finiteness without evaluation. Return true for now — this matches
                // practical TLC behavior where UNION is only applied to enumerable sets.
                true
            }
            // Known infinite sets
            Value::StringSet | Value::AnySet | Value::SeqSet(_) => false,
            // Nat/Int/Real are infinite sets → false.
            // User model values (symmetry elements) are atoms, not sets → false.
            // TLC: ModelValue is not Enumerable, so isFinite() returns false.
            Value::ModelValue(_) => false,
            // Non-set values
            _ => false,
        }
    }

    /// Check if this value is an empty set.
    /// Returns Some(true) for empty, Some(false) for non-empty, None for non-sets.
    /// Part of #343: Optimization for S /= {} patterns.
    pub fn is_empty_set(&self) -> Option<bool> {
        match self {
            Value::Set(s) => Some(s.is_empty()),
            Value::Interval(iv) => Some(iv.low > iv.high), // Empty if low > high
            // For other set types (SetPred, etc), check if first element exists.
            // Critical: use next().is_none() NOT count() == 0 to avoid iterating all elements!
            _ if self.is_set() => self.iter_set().map(|mut it| it.next().is_none()),
            _ => None, // Not a set
        }
    }

    pub fn as_set(&self) -> Option<&SortedSet> {
        match self {
            Value::Set(s) => Some(s),
            _ => None,
        }
    }

    /// Return a trait object for this value's lazy set implementation, if applicable.
    ///
    /// Covers: Interval, Subset, FuncSet, RecordSet, TupleSet, SetCup, SetCap,
    /// SetDiff, KSubset, BigUnion, SeqSet. Does NOT cover: Set (eager), SetPred
    /// (needs eval context), StringSet, AnySet, ModelValue (special cases).
    pub(crate) fn as_lazy_set(&self) -> Option<&dyn LazySet> {
        match self {
            Value::Interval(v) => Some(v.as_ref()),
            Value::Subset(v) => Some(v),
            Value::FuncSet(v) => Some(v),
            Value::RecordSet(v) => Some(v.as_ref()),
            Value::TupleSet(v) => Some(v.as_ref()),
            Value::SetCup(v) => Some(v),
            Value::SetCap(v) => Some(v),
            Value::SetDiff(v) => Some(v),
            Value::KSubset(v) => Some(v),
            Value::BigUnion(v) => Some(v),
            Value::SeqSet(v) => Some(v),
            _ => None,
        }
    }

    /// Check if this value (as a set) contains another value
    /// Works for Set, Interval, Subset, FuncSet, RecordSet, TupleSet, SetCup, SetCap, SetDiff, KSubset, BigUnion, SeqSet types
    pub fn set_contains(&self, v: &Value) -> Option<bool> {
        match self {
            Value::Set(s) => Some(s.contains(v)),
            Value::SetPred(_) => None, // Needs eval context
            // StringSet contains all strings
            Value::StringSet => Some(matches!(v, Value::String(_))),
            // AnySet contains all values
            Value::AnySet => Some(true),
            // ModelValue for infinite sets (Nat, Int, Real)
            Value::ModelValue(name) => match name.as_ref() {
                "Nat" => Some(match v {
                    Value::SmallInt(n) => *n >= 0,
                    Value::Int(n) => **n >= BigInt::zero(),
                    _ => false,
                }),
                "Int" => Some(matches!(v, Value::SmallInt(_) | Value::Int(_))),
                "Real" => Some(matches!(v, Value::SmallInt(_) | Value::Int(_))), // Int ⊆ Real
                _ => None, // Other model values are not sets
            },
            _ => self.as_lazy_set()?.set_contains(v),
        }
    }

    /// Convert this set-like value to a SortedSet
    /// Works for Set, Interval, Subset, FuncSet, RecordSet, TupleSet, SetCup, SetCap, SetDiff, KSubset, BigUnion types
    pub fn to_sorted_set(&self) -> Option<SortedSet> {
        match self {
            Value::Set(s) => Some((**s).clone()),
            _ => self.as_lazy_set()?.to_sorted_set(),
        }
    }

    /// O(1) check: is this set-like value equal to {1, 2, ..., n}?
    ///
    /// For `Interval` values, this is a direct comparison without materializing
    /// the entire set. Falls back to `to_sorted_set()` for other set types.
    pub fn is_sequence_domain(&self, n: usize) -> bool {
        match self {
            Value::Interval(iv) => {
                let expected_high = match i64::try_from(n) {
                    Ok(h) => h,
                    Err(_) => return false,
                };
                iv.low == BigInt::one() && iv.high == BigInt::from(expected_high)
            }
            Value::Set(s) => s.equals_sequence_domain(n),
            _ => self
                .to_sorted_set()
                .is_some_and(|s| s.equals_sequence_domain(n)),
        }
    }

    /// O(1) check: is this set-like value equal to the integer interval {min, min+1, ..., max}?
    ///
    /// For `Interval` values, this is a direct comparison without materializing
    /// the entire set. Falls back to `to_sorted_set()` for other set types.
    pub fn is_integer_interval(&self, min: i64, max: i64) -> bool {
        match self {
            Value::Interval(iv) => iv.low == BigInt::from(min) && iv.high == BigInt::from(max),
            Value::Set(s) => s.equals_integer_interval(min, max),
            _ => self
                .to_sorted_set()
                .is_some_and(|s| s.equals_integer_interval(min, max)),
        }
    }

    /// Get the number of elements in this set-like value
    pub fn set_len(&self) -> Option<BigInt> {
        match self {
            Value::Set(s) => Some(BigInt::from(s.len())),
            _ => self.as_lazy_set()?.set_len(),
        }
    }

    /// Iterate over this set-like value.
    ///
    /// Returns boxed iterator for Set, Interval, Subset, FuncSet, RecordSet, TupleSet, SetCup,
    /// SetCap, SetDiff, KSubset, BigUnion, and (in the degenerate case) SeqSet types when
    /// enumerable.
    pub fn iter_set(&self) -> Option<Box<dyn Iterator<Item = Value> + '_>> {
        match self {
            Value::Set(s) => Some(Box::new(s.iter().cloned())),
            _ => self.as_lazy_set()?.set_iter(),
        }
    }

    /// Iterate over this set-like value, returning a fully owned iterator.
    ///
    /// Part of #3978: Unlike `iter_set()` which returns an iterator borrowing `self`,
    /// this returns a `'static` iterator that owns its data. This enables streaming
    /// iteration in `SetPredStreamIter` where the source iterator must outlive the
    /// source value reference.
    ///
    /// For types with native owned iterators (FuncSet's odometer, Interval, Subset,
    /// KSubset), delegates to `LazySet::set_iter_owned()` which returns a truly lazy
    /// iterator without collecting. For other types, falls back to collecting through
    /// `iter_set()`.
    pub fn iter_set_owned(&self) -> Option<Box<dyn Iterator<Item = Value>>> {
        match self {
            Value::Set(s) => {
                let elements: Vec<Value> = s.iter().cloned().collect();
                Some(Box::new(elements.into_iter()))
            }
            _ => self.as_lazy_set()?.set_iter_owned(),
        }
    }
}
