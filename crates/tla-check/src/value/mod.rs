// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA+ Value types — re-exported from tla-value.
//!
//! The Value enum, value operations, and supporting types have moved to
//! the `tla-value` crate. This module re-exports the types used by
//! tla-check for backward compatibility. Items not used by tla-check
//! (e.g., `boolean_set`, `val_true`) are intentionally omitted.
//!
//! Part of #1269 Phase 4: value extraction to tla-value.

// Interning primitives — crate- (Part of #2957)
// These are implementation details for state management and should not
// be part of the crate's public semver surface.
pub(crate) use tla_value::{
    clear_int_func_intern_table, clear_model_value_registry, clear_set_intern_table,
    clear_string_intern_table, intern_string,
};

// Test-only interning helpers (no production callers).
#[cfg(test)]
pub(crate) use tla_value::value::{model_value_count, tlc_string_token};

// Value types — public API surface.
pub use tla_value::value::{
    // Set constructors
    range_set,
    // String utilities
    tlc_string_len,
    // Closure / lazy function types
    ClosureValue,
    FuncBuilder,
    FuncSetValue,
    // Function types
    FuncValue,
    IntIntervalFunc,
    // Interval types
    IntervalValue,
    KSubsetValue,
    LazyDomain,
    LazyFuncCaptures,
    LazyFuncValue,
    // Symmetry
    MVPerm,
    RecordBuilder,
    RecordSetValue,
    // Record types
    RecordValue,
    SeqSetValue,
    // Sequence types
    SeqValue,
    SetBuilder,
    SetCapValue,
    SetCupValue,
    SetDiffValue,
    SetPredIdentity,
    SetPredIdentityVisitor,
    SetPredValue,
    // Set types — materialized and lazy
    SortedSet,
    SubsetValue,
    // Tuple types
    TupleSetValue,
    UnionValue,
    // Core value type
    Value,
};

// Re-export submodules that external code accesses by path
#[cfg(feature = "memory-stats")]
pub mod memory_stats {
    pub use tla_value::value::memory_stats::*;
}
