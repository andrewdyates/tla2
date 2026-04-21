// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `LazySet` implementations for binary lazy-set wrappers (cup, cap, diff).

use super::trait_api::LazySet;
use crate::value::sorted_set::SortedSet;
use crate::value::{SetCapValue, SetCupValue, SetDiffValue, Value};

// ==========================================================================
// Tier 1 (materializing): SetCupValue — Phase 1A (#3073): direct to_sorted_set
// to_sorted_set delegates to own optimized method
// ==========================================================================

impl LazySet for SetCupValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        SetCupValue::to_sorted_set(self)
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn is_enumerable(&self) -> bool {
        SetCupValue::is_enumerable(self)
    }
}

// ==========================================================================
// Tier 1 (materializing): SetCapValue — Phase 1A (#3073): direct to_sorted_set
// to_sorted_set delegates to own optimized method
// ==========================================================================

impl LazySet for SetCapValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        SetCapValue::to_sorted_set(self)
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn is_enumerable(&self) -> bool {
        SetCapValue::is_enumerable(self)
    }
}

// ==========================================================================
// Tier 1 (materializing): SetDiffValue — Phase 1A (#3073): direct to_sorted_set
// to_sorted_set delegates to own optimized method
// ==========================================================================

impl LazySet for SetDiffValue {
    fn set_contains(&self, value: &Value) -> Option<bool> {
        self.contains(value)
    }

    fn to_sorted_set(&self) -> Option<SortedSet> {
        SetDiffValue::to_sorted_set(self)
    }

    fn set_is_empty(&self) -> bool {
        self.is_empty()
    }

    fn is_enumerable(&self) -> bool {
        SetDiffValue::is_enumerable(self)
    }
}
