// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extensional materialization budget for lazy set comparison.
//!
//! Determines whether a set-like value is small enough to materialize
//! for extensional comparison (Hash, Ord). Shared between `hashing.rs`
//! and `ordering.rs` — consolidated per #2037.

use super::Value;
use num_traits::ToPrimitive;

/// Hard cap for set materialization in `Hash`/`Ord` hot paths.
///
/// Above this threshold we keep lazy values structural to avoid exponential blowups
/// (for example `SUBSET(S)` and `[S -> T]`). Shared between `hashing.rs` and
/// `ordering.rs` per #2037.
const MAX_SET_MATERIALIZE: u64 = 10_000;

/// Check whether a set-like value is small enough to materialize for
/// extensional comparison (Hash, Ord). Used by both `hashing.rs` and
/// `ordering.rs` — consolidated per #2037.
pub(crate) fn should_materialize_extensionally(value: &Value) -> bool {
    match value {
        Value::Set(set) => set.len() <= MAX_SET_MATERIALIZE as usize,
        Value::Interval(iv) => iv.len().to_u64().is_some_and(|n| n <= MAX_SET_MATERIALIZE),
        Value::Subset(sv) => sv
            .len()
            .and_then(|n| n.to_u64())
            .is_some_and(|n| n <= MAX_SET_MATERIALIZE),
        Value::FuncSet(fsv) => fsv
            .len()
            .and_then(|n| n.to_u64())
            .is_some_and(|n| n <= MAX_SET_MATERIALIZE),
        Value::RecordSet(rsv) => rsv
            .len()
            .and_then(|n| n.to_u64())
            .is_some_and(|n| n <= MAX_SET_MATERIALIZE),
        Value::TupleSet(tsv) => tsv
            .len()
            .and_then(|n| n.to_u64())
            .is_some_and(|n| n <= MAX_SET_MATERIALIZE),
        Value::SetCup(cup) => match (cup.set1().set_len(), cup.set2().set_len()) {
            // Use an additive upper bound. If the bound is within budget we can
            // safely materialize extensionally for Hash/Ord without violating
            // the budget gate on overlapping operands.
            (Some(left), Some(right)) => (left + right)
                .to_u64()
                .is_some_and(|n| n <= MAX_SET_MATERIALIZE),
            _ => false,
        },
        Value::KSubset(ksv) => ksv
            .len()
            .and_then(|n| n.to_u64())
            .is_some_and(|n| n <= MAX_SET_MATERIALIZE),
        // These variants do not have a cheap safe cardinality bound.
        Value::SetCap(_)
        | Value::SetDiff(_)
        | Value::BigUnion(_)
        | Value::SetPred(_)
        | Value::SeqSet(_)
        | Value::StringSet
        | Value::AnySet => false,
        _ => false,
    }
}
