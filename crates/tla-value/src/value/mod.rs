// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLA+ Value types
//!
//! This module defines the runtime values used during TLA+ expression evaluation.
//! Values are designed to be:
//! - Immutable: All values are immutable (functional style)
//! - Hashable: All values can be used as set elements or function domain elements
//! - Comparable: Total ordering for deterministic iteration
//!
//! # Value Types
//!
//! | TLA+ Type | Rust Type | Notes |
//! |-----------|-----------|-------|
//! | BOOLEAN   | `Value::Bool(bool)` | |
//! | Int       | `Value::SmallInt(i64)` | Fast path for common integers |
//! | Int       | `Value::Int(Arc::new(BigInt))` | Arbitrary-precision fallback |
//! | STRING    | `Value::String(Arc<str>)` | |
//! | Set       | `Value::set(...)`, `Value::from_sorted_set(...)` | Canonical sorted view; Arc-backed (#3445) |
//! | Set       | `Value::Interval`, `Subset`, `FuncSet`, `Value::record_set(...)`, `Value::tuple_set(...)`, ... | Lazy set variants |
//! | Function  | `Value::Func(Arc::new(FuncValue))` | Split domain/value arrays with COW EXCEPT |
//! | Function  | `Value::IntFunc(Arc::new(IntIntervalFunc))` | Array backed (int domains) |
//! | Function  | `Value::LazyFunc(Arc<LazyFuncValue>)` | Non-enumerable domains, Arc-backed |
//! | Sequence  | `Value::Seq(Arc::new(SeqValue))` | Arc-backed, O(1) clone |
//! | Record    | `Value::Record(RecordValue)` | Array-backed fields |
//! | Tuple     | `Value::Tuple(Arc<[Value]>)` | Arc-backed, O(1) clone |
//! | Model     | `Value::ModelValue(Arc<str>)` | Symmetry sets |
//! | Closure   | `Value::Closure(Arc::new(ClosureValue))` | LAMBDA expressions |
//!
//! Submodules: `closure`, `cmp_helpers`, `extensional_budget`, `formatting`,
//! `functions`, `hashing`, `int_interval_func`, `intern_tables`, `interval`,
//! `lazy_func`, `lazy_set`, `model_values`, `ordering`, `permute`, `record`,
//! `seq`, `set_builders`, `sorted_set`, `strings`, `test_support`, `tlc_cmp`,
//! `value_fingerprint`.

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tla_core::ast::{BoundVar, Expr};
use tla_core::kani_types::HashMap;
use tla_core::Spanned;

// ============================================================================
// Extracted helper modules (Part of #3332)
// ============================================================================

#[cfg(test)]
mod test_support;
#[cfg(test)]
pub(crate) use test_support::lock_intern_state;

mod extensional_budget;
pub(crate) use extensional_budget::should_materialize_extensionally;

mod interval;
pub use interval::IntervalValue;

// ============================================================================
// Memory Statistics (compile with --features memory-stats)
// ============================================================================

#[cfg(feature = "memory-stats")]
pub mod memory_stats;

// ============================================================================
// Module declarations
// ============================================================================

mod closure;
mod cmp_helpers;
pub mod compact;
mod error_constructors;
mod formatting;
mod functions;
mod hashing;
mod int_interval_func;
mod intern_tables;
mod lazy_func;
mod lazy_set;
mod model_values;
mod ordering;
pub(crate) mod parallel_intern;
mod permute;
mod record;
mod record_impls;
mod seq;
mod set_builders;
mod set_ops;
mod sorted_set;
mod strings;
mod tlc_cmp;
mod tlc_iter;
mod tlc_sort;
pub(crate) use tlc_iter::clear_tlc_norm_cache;
pub use tlc_iter::TlcSetIterInline;
pub mod value_fingerprint;
mod value_impl;
pub(crate) mod value_pool;

// ============================================================================
// Re-exports
// ============================================================================

pub use set_ops::{
    SeqSetValue, SetCapValue, SetCupValue, SetDiffValue, SetPredCaptures, SetPredIdentity,
    SetPredIdentityVisitor, SetPredValue, UnionValue,
};

pub use intern_tables::{
    clear_int_func_intern_table, clear_set_intern_table, set_skip_int_func_interning,
    set_skip_set_interning,
};
pub(crate) use lazy_set::LazySet;
pub use model_values::{
    clear_model_value_registry, get_or_assign_model_value_index, interned_model_value,
    lookup_model_value_index, model_value_count, MVPerm,
};
pub use seq::SeqValue;
pub use set_builders::{big_union, boolean_set, cartesian_product, powerset, range_set};
pub use sorted_set::{val_false, val_int, val_true, SetBuilder, SortedSet};
pub use strings::tlc_string_token;
pub use strings::{clear_string_intern_table, intern_string};
pub use strings::{clear_tlc_string_tokens, tlc_string_len, tlc_string_subseq_utf16_offsets};

pub use closure::{ClosureValue, TirBody};
pub use functions::{checked_interval_len, FuncBuilder, FuncTakeSource, FuncValue};
pub use int_interval_func::IntIntervalFunc;
pub use lazy_func::{CapturedChain, ComponentDomain, LazyDomain, LazyFuncCaptures, LazyFuncValue};
pub use record::RecordValue;
pub use record_impls::RecordBuilder;

// ============================================================================
use intern_tables::{intern_int_func_array, try_get_interned_modified, MAX_INTERN_INT_FUNC_SIZE};

// ============================================================================
// Value enum
// ============================================================================

/// A TLA+ runtime value
#[derive(Clone)]
#[non_exhaustive]
pub enum Value {
    /// Boolean: TRUE or FALSE
    Bool(bool),
    /// Small integer (fits in i64) - fast path for common case
    SmallInt(i64),
    /// Arbitrary-precision integer (BigInt) - slow path for large numbers
    /// Arc-wrapped to reduce Value enum size from ~96 to ~32 bytes.
    Int(Arc<BigInt>),
    /// String value
    String(Arc<str>),
    /// Set of values (sorted array for performance)
    /// Arc-wrapped to reduce Value enum size from 56B to 24B (#3445).
    Set(Arc<SortedSet>),
    /// Lazy integer interval (a..b) without allocating all elements
    /// Arc-wrapped to reduce Value enum size.
    Interval(Arc<IntervalValue>),
    /// Lazy powerset (SUBSET S) without allocating all 2^|S| elements
    Subset(SubsetValue),
    /// Lazy function set ([S -> T]) without allocating all |T|^|S| functions
    FuncSet(FuncSetValue),
    /// Lazy record set ([a: S, b: T]) without allocating all |S|*|T| records
    /// Arc-wrapped to reduce Value enum size from 56B to 24B (#3445).
    RecordSet(Arc<RecordSetValue>),
    /// Lazy tuple set (S1 \X S2 \X ...) without allocating all |S1|*|S2|*... tuples
    /// Arc-wrapped to reduce Value enum size from 56B to 24B (#3445).
    TupleSet(Arc<TupleSetValue>),
    /// Lazy set union (S1 \cup S2) without eager enumeration
    SetCup(SetCupValue),
    /// Lazy set intersection (S1 \cap S2) without eager enumeration
    SetCap(SetCapValue),
    /// Lazy set difference (S1 \ S2) without eager enumeration
    SetDiff(SetDiffValue),
    /// Lazy set filter ({x \in S : P(x)}) without eager enumeration
    /// Membership requires evaluation context, so set_contains returns None
    /// Boxed to reduce Value enum size — SetPredValue contains cached identity
    /// signatures (#2788) that would otherwise inflate the enum by 48 bytes.
    SetPred(Box<SetPredValue>),
    /// Lazy k-subset set (Ksubsets(S, k)) without allocating all C(n,k) subsets
    KSubset(KSubsetValue),
    /// Lazy big union (UNION S) without allocating all elements
    BigUnion(UnionValue),
    /// Function (mapping from domain to range)
    /// Arc-wrapped to reduce Value enum size.
    Func(Arc<FuncValue>),
    /// Array-backed function for small integer interval domains
    /// Much faster than Func for EXCEPT operations on int-indexed functions
    /// Arc-wrapped to reduce Value enum size.
    IntFunc(Arc<IntIntervalFunc>),
    /// Lazy function for non-enumerable domains (e.g., Nat, Int)
    /// Arc-wrapped for O(1) clone: recursive self-reference push (8.4M times on
    /// GameOfLife) and function argument passing now cost 1 refcount bump instead
    /// of a deep clone with Box allocation. Part of #2955.
    LazyFunc(Arc<LazyFuncValue>),
    /// Sequence (1-indexed) - uses Arc<[Value]> for O(1) clone
    /// Arc-wrapped to reduce Value enum size.
    Seq(Arc<SeqValue>),
    /// Record with named fields
    /// Uses array-backed RecordValue for better cache locality and iteration performance
    Record(RecordValue),
    /// Tuple (heterogeneous, 1-indexed) - uses Arc<[Value]> for O(1) clone
    Tuple(Arc<[Value]>),
    /// Model value (for symmetry sets and state graph)
    ModelValue(Arc<str>),
    /// Closure for higher-order operator arguments (LAMBDA expressions)
    /// Stores the lambda parameters, body, and captured environment
    /// Arc-wrapped to reduce Value enum size.
    Closure(Arc<ClosureValue>),
    /// The set of all strings (infinite, lazy)
    /// Used by the Strings module STRING constant
    StringSet,
    /// The set of all values (infinite, lazy)
    /// Used by TLC's AnySet module and TLC!Any operator
    AnySet,
    /// Lazy sequence set (Seq(S)) without allocating all finite sequences over S
    SeqSet(SeqSetValue),
}

mod drop;
mod compound_sets;
#[cfg(test)]
use compound_sets::binomial;
pub(crate) use compound_sets::{
    FuncSetIterator, KSubsetIterator, RecordSetOwnedIterator, SubsetIterator,
    TupleSetOwnedIterator,
};
pub use compound_sets::{FuncSetValue, KSubsetValue, RecordSetValue, SubsetValue, TupleSetValue};

// impl Value constructors, type predicates, and extractors extracted to value_impl.rs

// FuncBuilder, FuncValue impls in functions/mod.rs
// IntIntervalFunc impls in int_interval_func/
// Set builder utility functions extracted to set_builders.rs

#[cfg(test)]
mod tests;
