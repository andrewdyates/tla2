// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// Allow unsafe in the compact module only (tagged pointer representation).
// All other modules remain safe.
#![deny(unsafe_code)]

//! TLA+ value representation.
//!
//! This crate holds the runtime value model for TLA+ specifications:
//! sets, functions, records, sequences, tuples, model values, and their
//! associated operations (equality, hashing, ordering, fingerprinting).
//!
//! ## Modules
//!
//! - `value`: The `Value` enum and all value operations
//! - `error`: `EvalError` and `EvalResult` types
//! - `dedup_fingerprint`: State-deduplication fingerprints for model checking
//! - `fingerprint`: TLC-compatible FP64 polynomial rolling hash

// debug_flag! macro must be defined before modules that use it
#[macro_use]
pub(crate) mod debug_env;

pub mod dedup_fingerprint;
pub mod error;
pub mod fingerprint;
pub mod itf;
pub mod value;

// Re-export error types at crate root
pub use error::{EvalError, EvalResult};

// Re-export ITF serialization at crate root
pub use itf::value_to_itf;

// Re-export value types at crate root with explicit API surface (Part of #1582)
// Re-export CompactValue (8-byte tagged pointer representation)
pub use value::compact::CompactValue;

pub use value::{
    // Set builders
    big_union,
    boolean_set,
    cartesian_product,
    // Utilities
    checked_interval_len,
    // Value constructors and interning
    clear_int_func_intern_table,
    clear_model_value_registry,
    clear_set_intern_table,
    clear_string_intern_table,
    clear_tlc_string_tokens,
    // Model values
    get_or_assign_model_value_index,
    intern_string,
    interned_model_value,
    lookup_model_value_index,
    model_value_count,
    powerset,
    range_set,
    set_skip_int_func_interning,
    set_skip_set_interning,
    tlc_string_len,
    tlc_string_subseq_utf16_offsets,
    tlc_string_token,
    val_false,
    val_int,
    val_true,
    CapturedChain,
    // Core value types
    ClosureValue,
    ComponentDomain,
    FuncBuilder,
    FuncSetValue,
    FuncTakeSource,
    FuncValue,
    IntIntervalFunc,
    IntervalValue,
    KSubsetValue,
    LazyDomain,
    LazyFuncCaptures,
    LazyFuncValue,
    MVPerm,
    RecordBuilder,
    RecordSetValue,
    RecordValue,
    SeqSetValue,
    SeqValue,
    SetBuilder,
    SetCapValue,
    SetCupValue,
    SetDiffValue,
    SetPredCaptures,
    SetPredIdentity,
    SetPredIdentityVisitor,
    SetPredValue,
    SortedSet,
    SubsetValue,
    TirBody,
    TlcSetIterInline,
    TupleSetValue,
    UnionValue,
    Value,
};

// Re-export value_fingerprint at crate root for extraction (#1269)
pub use fingerprint::value_fingerprint;

// Re-export fingerprint error types at crate root (Part of #3203)
pub use value::value_fingerprint::{FingerprintError, FingerprintResult};

/// Clear thread-local TLC normalization cache between model-checking runs.
pub fn clear_tlc_norm_cache() {
    value::clear_tlc_norm_cache();
}

// Part of #3285, Part of #3334: Re-export parallel interning API for use by tla-check.
// Raw lifecycle toggles (freeze/unfreeze/enable/disable) are now crate-internal;
// external callers use ParallelValueInternRunGuard instead.
pub use value::parallel_intern::{
    parallel_readonly_value_caches_active, read_intern_attribution_counters,
    InternAttributionCounters, ParallelValueInternRunGuard, SharedValueCacheMode,
    WorkerInternGuard,
};
