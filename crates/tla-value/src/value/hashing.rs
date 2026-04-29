// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{should_materialize_extensionally, Value};
use num_traits::ToPrimitive;
use std::hash::{Hash, Hasher};

/// Hash an i64 value in a way that produces the same result as BigInt::from(n).to_bytes_le()
/// This avoids allocating a BigInt for small integers (the common case).
#[inline]
fn hash_i64_as_bigint<H: Hasher>(n: i64, state: &mut H) {
    use num_bigint::Sign;

    if n == 0 {
        Sign::NoSign.hash(state);
        // Empty slice for zero - same as BigInt::from(0).to_bytes_le().1
        let empty: [u8; 0] = [];
        empty.hash(state);
    } else if n > 0 {
        Sign::Plus.hash(state);
        // Compute minimal little-endian bytes (same as BigInt)
        let unsigned = n as u64;
        let byte_len = (64 - unsigned.leading_zeros()).div_ceil(8) as usize;
        unsigned.to_le_bytes()[..byte_len].hash(state);
    } else {
        Sign::Minus.hash(state);
        // Handle negative: compute absolute value
        // Special case: i64::MIN cannot be negated directly
        let abs_val = if n == i64::MIN {
            (i64::MAX as u64) + 1
        } else {
            (-n) as u64
        };
        let byte_len = (64 - abs_val.leading_zeros()).div_ceil(8) as usize;
        abs_val.to_le_bytes()[..byte_len].hash(state);
    }
}

#[inline]
fn hash_set_extensional_if_budgeted<H: Hasher>(value: &Value, state: &mut H) -> bool {
    if !should_materialize_extensionally(value) {
        return false;
    }
    if let Some(set) = value.to_sorted_set() {
        for v in &set {
            v.hash(state);
        }
        return true;
    }
    false
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Use a common discriminant for all set types so they hash the same
        // when they represent the same set extensionally.
        // Similarly, Tuple/Seq/Record/Func all use the same discriminant (6)
        // since they are all functions in TLA+ (tuples/seqs have domain 1..n,
        // records have string domain).
        match self {
            Value::Bool(_) => 0u8.hash(state),
            Value::SmallInt(_) | Value::Int(_) => 1u8.hash(state),
            Value::String(_) => 2u8.hash(state),
            Value::ModelValue(_) => 3u8.hash(state),
            // All function-like types (Tuple, Seq, Record, Func, IntFunc) use same discriminant
            // since they are semantically functions and should hash equally when equal
            Value::Tuple(_)
            | Value::Seq(_)
            | Value::Record(_)
            | Value::Func(_)
            | Value::IntFunc(_) => 6u8.hash(state),
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
            | Value::SeqSet(_) => 7u8.hash(state),
            Value::LazyFunc(_) => 9u8.hash(state),
            Value::Closure(_) => 10u8.hash(state),
        }
        match self {
            Value::Bool(b) => b.hash(state),
            // SmallInt and Int must hash the same for equal values
            Value::SmallInt(n) => {
                // Hash i64 directly, producing same result as BigInt::from(n).to_bytes_le()
                hash_i64_as_bigint(*n, state);
            }
            Value::Int(n) => {
                // Fast path: if fits in i64, use direct hashing
                if let Some(small) = n.to_i64() {
                    hash_i64_as_bigint(small, state);
                } else {
                    // Slow path: large integers need byte conversion
                    let (sign, bytes) = n.to_bytes_le();
                    sign.hash(state);
                    bytes.hash(state);
                }
            }
            Value::String(s) => s.hash(state),
            Value::ModelValue(s) => s.hash(state),
            // Tuple/Seq: function with domain 1..n
            // Hash domain (integers 1..n) then mapping (index -> value)
            Value::Tuple(t) => {
                // Hash domain: 1, 2, ..., n (using direct i64 hashing to avoid BigInt allocation)
                for i in 1..=t.len() {
                    1u8.hash(state); // Discriminant for integers
                    hash_i64_as_bigint(i as i64, state);
                }
                // Hash mapping: (1, v1), (2, v2), ..., (n, vn)
                for (i, v) in t.iter().enumerate() {
                    1u8.hash(state); // Discriminant for integers
                    hash_i64_as_bigint((i + 1) as i64, state);
                    v.hash(state);
                }
            }
            Value::Seq(s) => {
                // Hash domain: 1, 2, ..., n (using direct i64 hashing to avoid BigInt allocation)
                for i in 1..=s.len() {
                    1u8.hash(state); // Discriminant for integers
                    hash_i64_as_bigint(i as i64, state);
                }
                // Hash mapping: (1, v1), (2, v2), ..., (n, vn)
                for (i, v) in s.iter().enumerate() {
                    1u8.hash(state); // Discriminant for integers
                    hash_i64_as_bigint((i + 1) as i64, state);
                    v.hash(state);
                }
            }
            // Record: function with string domain
            // Hash domain (strings) then mapping (string -> value)
            // MUST hash in alphabetical string order to maintain hash/eq contract
            // with FuncValue (which iterates in Value::cmp order = alphabetical for strings).
            // Part of #3063 Phase I2: NameId sorting is for comparison performance;
            // Hash resolves back to strings for cross-type consistency.
            Value::Record(r) => {
                let mut pairs: Vec<(std::sync::Arc<str>, &Value)> = r.iter_str().collect();
                pairs.sort_by(|(a, _), (b, _)| a.cmp(b));
                // Hash domain (keys in alphabetical order)
                for (k, _) in &pairs {
                    2u8.hash(state); // String discriminant
                    k.hash(state);
                }
                // Hash mapping (key-value pairs in alphabetical order)
                for (k, v) in &pairs {
                    2u8.hash(state); // String discriminant
                    k.hash(state);
                    v.hash(state);
                }
            }
            Value::Set(s) => {
                for v in s.as_ref() {
                    v.hash(state);
                }
            }
            // Interval is hashed by iterating elements (extensional)
            Value::Interval(iv) => {
                for v in iv.iter_values() {
                    v.hash(state);
                }
            }
            // Subset is hashed by iterating elements (extensional)
            Value::Subset(sv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    // Large/unknown cardinality: keep lazy structure to avoid
                    // exponential materialization.
                    sv.hash(state);
                }
            }
            // FuncSet is hashed extensionally only within the materialization budget.
            Value::FuncSet(fsv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    fsv.hash(state);
                }
            }
            // RecordSet is hashed extensionally only within the materialization budget.
            Value::RecordSet(rsv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    rsv.hash(state);
                }
            }
            // TupleSet is hashed extensionally only within the materialization budget.
            Value::TupleSet(tsv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    tsv.hash(state);
                }
            }
            // Set operators default to structural hashing to avoid expensive expansion.
            Value::SetCup(scv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    scv.hash(state);
                }
            }
            // Set operators default to structural hashing to avoid expensive expansion.
            Value::SetCap(scv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    scv.hash(state);
                }
            }
            // Set operators default to structural hashing to avoid expensive expansion.
            Value::SetDiff(sdv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    sdv.hash(state);
                }
            }
            // SetPred hash is structural and deterministic (runtime ID excluded).
            Value::SetPred(spv) => spv.hash(state),
            // KSubset is hashed extensionally only within the materialization budget.
            Value::KSubset(ksv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    ksv.hash(state);
                }
            }
            // BigUnion defaults to structural hashing to avoid large flattening.
            Value::BigUnion(uv) => {
                if !hash_set_extensional_if_budgeted(self, state) {
                    uv.hash(state);
                }
            }
            Value::Func(f) => {
                // Hash domain first (sorted iteration order matches Record's OrdMap keys)
                for k in f.domain_iter() {
                    k.hash(state);
                }
                // Hash all (key, value) pairs - entries are sorted so order is deterministic
                for (k, v) in f.mapping_iter() {
                    k.hash(state);
                    v.hash(state);
                }
            }
            Value::IntFunc(f) => {
                // Hash domain (min..max as integers)
                for i in f.min..=f.max {
                    1u8.hash(state); // Integer discriminant
                    hash_i64_as_bigint(i, state);
                }
                // Hash mapping (key, value pairs)
                for (i, v) in f.values.iter().enumerate() {
                    1u8.hash(state); // Integer discriminant
                    hash_i64_as_bigint(f.min + i as i64, state);
                    v.hash(state);
                }
            }
            // Lazy functions are hashed by their unique ID (not extensionally)
            Value::LazyFunc(f) => f.id().hash(state),
            // Closures are hashed by their unique ID
            Value::Closure(c) => c.id().hash(state),
            // StringSet is a singleton, hash it as a constant
            Value::StringSet => "STRING".hash(state),
            // AnySet is a singleton, hash it as a constant
            Value::AnySet => "ANY".hash(state),
            // SeqSet is hashed by its base set
            Value::SeqSet(ssv) => {
                // Maintain Hash/Eq consistency with the special-case equality:
                // Seq({}) == {<<>>}. When base is the empty set, hash exactly like the
                // singleton set containing the empty sequence.
                if ssv.base.is_empty_set() == Some(true) {
                    Value::seq(Vec::<Value>::new()).hash(state);
                } else {
                    "SEQSET".hash(state);
                    ssv.base.hash(state);
                }
            }
        }
    }
}
