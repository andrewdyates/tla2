// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interval value types for lazy integer ranges.
//!
//! `IntervalValue` represents a contiguous integer range `[low, high]` without
//! materializing all elements. Used for TLA+ integer interval expressions like
//! `1..N`.

use super::Value;
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::sync::Arc;

use super::SortedSet;

/// A lazy interval value representing a..b without allocating all elements
///
/// This is a performance optimization for large integer ranges.
/// The interval is inclusive: [low, high].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntervalValue {
    /// Lower bound (inclusive)
    pub(crate) low: BigInt,
    /// Upper bound (inclusive)
    pub(crate) high: BigInt,
}

impl IntervalValue {
    /// Create a new interval [low, high]
    pub fn new(low: BigInt, high: BigInt) -> Self {
        IntervalValue { low, high }
    }

    pub fn low(&self) -> &BigInt {
        &self.low
    }

    pub fn high(&self) -> &BigInt {
        &self.high
    }

    /// Check if the interval is empty (low > high)
    pub fn is_empty(&self) -> bool {
        self.low > self.high
    }

    /// Get the number of elements in the interval
    pub fn len(&self) -> BigInt {
        if self.is_empty() {
            BigInt::zero()
        } else {
            &self.high - &self.low + BigInt::one()
        }
    }

    /// Check if a value is contained in this interval
    pub fn contains(&self, v: &Value) -> bool {
        match v {
            Value::SmallInt(n) => {
                // Fast path: avoid BigInt allocation when bounds fit in i64.
                if let (Some(low), Some(high)) = (self.low.to_i64(), self.high.to_i64()) {
                    return *n >= low && *n <= high;
                }
                let n = BigInt::from(*n);
                n >= self.low && n <= self.high
            }
            Value::Int(n) => {
                // Fast path: compare in i64 space when possible.
                if let (Some(low), Some(high), Some(v)) =
                    (self.low.to_i64(), self.high.to_i64(), n.to_i64())
                {
                    return v >= low && v <= high;
                }
                **n >= self.low && **n <= self.high
            }
            _ => false,
        }
    }

    /// Iterate over all elements in the interval
    pub fn iter(&self) -> impl Iterator<Item = BigInt> {
        IntervalIterator {
            current: self.low.clone(),
            high: self.high.clone(),
        }
    }

    /// Iterate over all elements in the interval as `Value`.
    ///
    /// Uses an i64-backed iterator when bounds fit, avoiding per-element BigInt work.
    pub fn iter_values(&self) -> impl Iterator<Item = Value> {
        match (self.low.to_i64(), self.high.to_i64()) {
            (Some(low), Some(high)) => IntervalValueIter::I64(low..=high),
            _ => IntervalValueIter::BigInt(IntervalIterator {
                current: self.low.clone(),
                high: self.high.clone(),
            }),
        }
    }

    /// Convert to an eager SortedSet (use sparingly for large intervals)
    pub fn to_sorted_set(&self) -> SortedSet {
        // Interval elements are already sorted (low to high), so skip sort
        let vec: Vec<Value> = self.iter_values().collect();
        SortedSet::from_sorted_vec(vec)
    }
}

/// Iterator over interval elements
pub(crate) struct IntervalIterator {
    current: BigInt,
    high: BigInt,
}

impl Iterator for IntervalIterator {
    type Item = BigInt;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current > self.high {
            None
        } else {
            let result = self.current.clone();
            self.current += 1;
            Some(result)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.current > self.high {
            (0, Some(0))
        } else {
            let len = (&self.high - &self.current + BigInt::one())
                .to_usize()
                .unwrap_or(usize::MAX);
            (len, Some(len))
        }
    }
}

/// Iterator over interval elements as `Value`.
///
/// For small ranges (bounds fit in i64), this avoids BigInt allocation and arithmetic.
pub(crate) enum IntervalValueIter {
    I64(std::ops::RangeInclusive<i64>),
    BigInt(IntervalIterator),
}

impl Iterator for IntervalValueIter {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IntervalValueIter::I64(r) => r.next().map(Value::SmallInt),
            IntervalValueIter::BigInt(it) => it.next().map(|n| Value::Int(Arc::new(n))),
        }
    }
}

impl Ord for IntervalValue {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.low.cmp(&other.low) {
            Ordering::Equal => self.high.cmp(&other.high),
            ord => ord,
        }
    }
}

impl PartialOrd for IntervalValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
