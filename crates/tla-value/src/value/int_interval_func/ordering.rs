// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ordering, equality, and conversion impls for `IntIntervalFunc`.
//!
//! Split from `int_interval_func.rs` as part of #3443.

use super::IntIntervalFunc;
use crate::value::{FuncValue, Value};
use std::cmp::Ordering;

impl IntIntervalFunc {
    /// Convert to FuncValue (for compatibility with code expecting FuncValue)
    /// Phase 1A (#3073): builds sorted entries directly — integer range is
    /// already sorted, so from_sorted_entries avoids OrdSet/OrdMap overhead.
    pub(crate) fn to_func_value(&self) -> FuncValue {
        let entries: Vec<(Value, Value)> = (self.min..=self.max)
            .zip(self.values.iter().cloned())
            .map(|(k, v)| (Value::SmallInt(k), v))
            .collect();
        FuncValue::from_sorted_entries(entries)
    }
}

impl Ord for IntIntervalFunc {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare by domain bounds first
        match self.min.cmp(&other.min) {
            Ordering::Equal => {}
            ord => return ord,
        }
        match self.max.cmp(&other.max) {
            Ordering::Equal => {}
            ord => return ord,
        }
        // Then compare values element-wise
        self.values.iter().cmp(other.values.iter())
    }
}

impl PartialOrd for IntIntervalFunc {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for IntIntervalFunc {
    fn eq(&self, other: &Self) -> bool {
        self.min == other.min && self.max == other.max && self.values == other.values
    }
}

impl Eq for IntIntervalFunc {}
