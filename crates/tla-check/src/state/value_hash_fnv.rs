// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FNV-1a recursive value hashing for TLC-compatible fingerprinting.
//!
//! Contains `hash_value()`, the recursive FNV-1a hash function used for all
//! `Value` variants. Also contains optimized helpers `hash_smallint()` and
//! `hash_string()` for common types.
//!
//! Extracted from `value_hash.rs` as part of #3338.

use crate::value::{IntIntervalFunc, SortedSet};
use crate::Value;
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};
use tla_core::FNV_PRIME;

/// Hash a small integer directly into the running FNV-1a hash
/// This is an optimization to avoid creating temporary Value::SmallInt wrappers
#[inline(always)]
pub(super) fn hash_smallint(mut hash: u64, n: i64) -> u64 {
    // Type tag for integers (same as SmallInt/Int)
    hash ^= 1u64;
    hash = hash.wrapping_mul(FNV_PRIME);

    // Hash using the same two's-complement byte representation as BigInt
    let bytes = n.to_le_bytes();
    let mut len = bytes.len();
    if n >= 0 {
        while len > 1 && bytes[len - 1] == 0x00 && (bytes[len - 2] & 0x80) == 0 {
            len -= 1;
        }
    } else {
        while len > 1 && bytes[len - 1] == 0xFF && (bytes[len - 2] & 0x80) != 0 {
            len -= 1;
        }
    }
    for &byte in &bytes[..len] {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// Hash a string directly into the running FNV-1a hash
/// This is an optimization to avoid creating temporary Value::String wrappers
#[inline(always)]
pub(super) fn hash_string(mut hash: u64, s: &str) -> u64 {
    // Type tag for strings (tag 2)
    hash ^= 2u64;
    hash = hash.wrapping_mul(FNV_PRIME);

    // Hash the string bytes
    for byte in s.bytes() {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// Hash elements from a sorted set into the running hash.
///
/// Shared enumerable path: XOR in the element count, then hash each element.
/// Used by set-like variants that support `to_sorted_set()`.
/// Part of #3260: extracted from 7 duplicated match arms in `hash_value`.
#[inline]
fn hash_sorted_elements(mut hash: u64, set: &SortedSet) -> u64 {
    hash ^= set.len() as u64;
    hash = hash.wrapping_mul(FNV_PRIME);
    for elem in set.iter() {
        hash = hash_value(hash, elem);
    }
    hash
}

/// Hash a set-like value: enumerate via `to_sorted_set()` if possible,
/// otherwise hash structural components.
///
/// Part of #3260: deduplicates the to_sorted_set() → hash-or-structure pattern
/// shared by FuncSet, SetCup, SetCap, SetDiff, and BigUnion.
#[inline]
fn hash_enumerable_set(
    hash: u64,
    sorted: Option<SortedSet>,
    structural_components: &[&Value],
) -> u64 {
    if let Some(ref set) = sorted {
        hash_sorted_elements(hash, set)
    } else {
        let mut h = hash;
        for component in structural_components {
            h = hash_value(h, component);
        }
        h
    }
}

/// Hash a value into the running FNV-1a hash
pub(crate) fn hash_value(mut hash: u64, value: &Value) -> u64 {
    // Type tag (Interval, Subset, FuncSet, RecordSet, TupleSet use same tag as Set for consistency)
    // Tuple, Seq, Record, Func all use the same tag (4) since they are all functions in TLA+
    // (tuples/seqs have domain 1..n, records have string domain)
    let tag = match value {
        Value::Bool(_) => 0u8,
        Value::SmallInt(_) | Value::Int(_) => 1,
        Value::String(_) => 2,
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
        | Value::SeqSet(_) => 3,
        // All function-like types use same tag for equivalence
        Value::Func(_) | Value::IntFunc(_) | Value::Seq(_) | Value::Record(_) | Value::Tuple(_) => {
            4
        }
        Value::ModelValue(_) => 8,
        Value::Closure(_) => 9,
        Value::LazyFunc(_) => 10,
        _ => unreachable!("unhandled Value variant in hash tag"),
    };
    hash ^= tag as u64;
    hash = hash.wrapping_mul(FNV_PRIME);

    match value {
        Value::Bool(b) => {
            hash ^= *b as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        Value::SmallInt(n) => {
            // Hash SmallInt using the same two's-complement byte representation
            // as BigInt::to_signed_bytes_le(), but without allocating a BigInt/Vec.
            let bytes = n.to_le_bytes();
            let mut len = bytes.len();
            if *n >= 0 {
                while len > 1 && bytes[len - 1] == 0x00 && (bytes[len - 2] & 0x80) == 0 {
                    len -= 1;
                }
            } else {
                while len > 1 && bytes[len - 1] == 0xFF && (bytes[len - 2] & 0x80) != 0 {
                    len -= 1;
                }
            }
            for &byte in &bytes[..len] {
                hash ^= byte as u64;
                hash = hash.wrapping_mul(FNV_PRIME);
            }
        }
        Value::Int(n) => {
            // Hash the bytes of the integer
            for byte in n.to_signed_bytes_le() {
                hash ^= byte as u64;
                hash = hash.wrapping_mul(FNV_PRIME);
            }
        }
        Value::String(s) | Value::ModelValue(s) => {
            for byte in s.bytes() {
                hash ^= byte as u64;
                hash = hash.wrapping_mul(FNV_PRIME);
            }
        }
        Value::Set(set) => {
            // Hash set cardinality first (helps with collision resistance)
            hash ^= set.len() as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
            // Hash elements in sorted order (OrdSet guarantees this)
            for elem in set.as_ref() {
                hash = hash_value(hash, elem);
            }
        }
        Value::Interval(iv) => {
            // Hash interval elements (same as Set for correctness)
            // For efficiency, we iterate through the interval values
            // Fast path: avoid BigInt allocation when bounds fit in i64
            match (iv.low().to_i64(), iv.high().to_i64()) {
                (Some(low), Some(high)) => {
                    hash ^= (high - low + 1) as u64;
                    hash = hash.wrapping_mul(FNV_PRIME);
                }
                _ => {
                    let len = iv.high() - iv.low() + BigInt::one();
                    match len.to_u64() {
                        Some(l) => {
                            hash ^= l;
                            hash = hash.wrapping_mul(FNV_PRIME);
                        }
                        None => {
                            // Length exceeds u64 — hash the BigInt bytes
                            // directly instead of silently truncating to 0
                            // (which would produce identical hashes for
                            // distinct out-of-range intervals). Part of #1890.
                            for byte in len.to_signed_bytes_le() {
                                hash ^= byte as u64;
                                hash = hash.wrapping_mul(FNV_PRIME);
                            }
                        }
                    }
                }
            }
            for v in iv.iter_values() {
                hash = hash_value(hash, &v);
            }
        }
        Value::Subset(sv) => {
            // Hash subset elements (same as Set for correctness)
            // This eagerly iterates - could be expensive for large powersets
            if let Some(iter) = sv.iter() {
                let elements: Vec<_> = iter.collect();
                hash ^= elements.len() as u64;
                hash = hash.wrapping_mul(FNV_PRIME);
                for elem in elements {
                    hash = hash_value(hash, &elem);
                }
            } else {
                // Non-enumerable - hash by structure (base set)
                hash = hash_value(hash, sv.base());
            }
        }
        Value::FuncSet(fsv) => {
            hash = hash_enumerable_set(hash, fsv.to_sorted_set(), &[fsv.domain(), fsv.codomain()]);
        }
        Value::RecordSet(rsv) => {
            if let Some(set) = rsv.to_sorted_set() {
                hash = hash_sorted_elements(hash, &set);
            } else {
                // Non-enumerable - hash by structure (field names + domain sets)
                for (name, domain) in rsv.fields_iter() {
                    hash = hash_string(hash, name.as_ref());
                    hash = hash_value(hash, domain);
                }
            }
        }
        Value::TupleSet(tsv) => {
            if let Some(set) = tsv.to_sorted_set() {
                hash = hash_sorted_elements(hash, &set);
            } else {
                // Non-enumerable - hash by structure (component domains)
                for component in tsv.components_iter() {
                    hash = hash_value(hash, component);
                }
            }
        }
        Value::SetCup(scv) => {
            hash = hash_enumerable_set(hash, scv.to_sorted_set(), &[scv.set1(), scv.set2()]);
        }
        Value::SetCap(scv) => {
            hash = hash_enumerable_set(hash, scv.to_sorted_set(), &[scv.set1(), scv.set2()]);
        }
        Value::SetDiff(sdv) => {
            hash = hash_enumerable_set(hash, sdv.to_sorted_set(), &[sdv.set1(), sdv.set2()]);
        }
        Value::Func(func) => {
            // Hash domain size then key-value pairs
            // Note: Domain elements are NOT hashed separately because they're
            // identical to the mapping keys (domain = set of keys). Hashing
            // both would be redundant. The mapping iteration produces the same
            // semantic fingerprint since it covers all keys.
            hash ^= func.domain_len() as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
            // Hash mapping (key-value pairs) - keys are implicitly the domain
            for (k, v) in func.mapping_iter() {
                hash = hash_value(hash, k);
                hash = hash_value(hash, v);
            }
        }
        Value::IntFunc(func) => {
            // Array-backed function for integer interval domains
            // Hash domain size (length), then key-value pairs (key = index)
            hash ^= func.len() as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
            // Hash mapping: (min, v0), (min+1, v1), ..., (max, vn)
            for (i, v) in func.values().iter().enumerate() {
                hash = hash_smallint(hash, IntIntervalFunc::min(func) + i as i64);
                hash = hash_value(hash, v);
            }
        }
        // Lazy functions are hashed by their unique ID (not extensionally)
        Value::LazyFunc(func) => {
            hash ^= func.id();
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        Value::Seq(seq) => {
            // Seq is a function with domain 1..n
            // Hash like Func: domain size, then mapping (no separate domain)
            hash ^= seq.len() as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
            // Hash mapping: (1, v1), (2, v2), ..., (n, vn)
            for (i, v) in seq.iter().enumerate() {
                hash = hash_smallint(hash, (i + 1) as i64);
                hash = hash_value(hash, v);
            }
        }
        Value::Tuple(tup) => {
            // Tuple is a function with domain 1..n
            // Hash like Func: domain size, then mapping (no separate domain)
            hash ^= tup.len() as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
            // Hash mapping: (1, v1), (2, v2), ..., (n, vn)
            for (i, v) in tup.iter().enumerate() {
                hash = hash_smallint(hash, (i + 1) as i64);
                hash = hash_value(hash, v);
            }
        }
        Value::Record(rec) => {
            // Record is a function with string domain
            // Hash like Func: domain size, then mapping (no separate domain)
            hash ^= rec.len() as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
            // Hash mapping (key-value pairs)
            // Domain elements (field names) are NOT hashed separately because
            // they're identical to the mapping keys. This matches the Func
            // and Tuple/Seq optimizations above.
            // Uses hash_string to avoid creating temporary Value::String wrappers.
            for (name_id, val) in rec {
                let name = tla_core::resolve_name_id(name_id);
                hash = hash_string(hash, &name);
                hash = hash_value(hash, val);
            }
        }
        // Closures are hashed by their unique ID
        Value::Closure(c) => {
            hash ^= c.id();
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        // SetPred uses deterministic structural hashing (runtime ID excluded).
        Value::SetPred(spv) => {
            struct FnvSetPredVisitor {
                hash: u64,
            }

            impl FnvSetPredVisitor {
                fn hash_optional_state(&mut self, values: Option<&[Value]>) {
                    match values {
                        Some(values) => {
                            self.hash ^= 1;
                            self.hash = self.hash.wrapping_mul(FNV_PRIME);
                            self.hash ^= values.len() as u64;
                            self.hash = self.hash.wrapping_mul(FNV_PRIME);
                            for value in values {
                                self.hash = hash_value(self.hash, value);
                            }
                        }
                        None => {
                            self.hash ^= 0;
                            self.hash = self.hash.wrapping_mul(FNV_PRIME);
                        }
                    }
                }
            }

            impl crate::value::SetPredIdentityVisitor for FnvSetPredVisitor {
                fn visit_source(&mut self, source: &Value) {
                    self.hash = hash_value(self.hash, source);
                }

                fn visit_bound_sig(&mut self, bound_sig: u64) {
                    self.hash ^= bound_sig;
                    self.hash = self.hash.wrapping_mul(FNV_PRIME);
                }

                fn visit_pred_sig(&mut self, pred_sig: u64) {
                    self.hash ^= pred_sig;
                    self.hash = self.hash.wrapping_mul(FNV_PRIME);
                }

                fn visit_env_len(&mut self, len: usize) {
                    self.hash ^= len as u64;
                    self.hash = self.hash.wrapping_mul(FNV_PRIME);
                }

                fn visit_env_entry(&mut self, name: &str, value: &Value) {
                    self.hash = hash_string(self.hash, name);
                    self.hash = hash_value(self.hash, value);
                }

                fn visit_captured_state(&mut self, captured_state: Option<&[Value]>) {
                    self.hash_optional_state(captured_state);
                }

                fn visit_captured_next_state(&mut self, captured_next_state: Option<&[Value]>) {
                    self.hash_optional_state(captured_next_state);
                }
            }

            let mut visitor = FnvSetPredVisitor { hash };
            spv.visit_identity_fields(&mut visitor);
            hash = visitor.hash;
        }
        // KSubset is hashed by iterating elements if enumerable
        Value::KSubset(ksv) => {
            if let Some(iter) = ksv.iter() {
                let elements: Vec<_> = iter.collect();
                hash ^= elements.len() as u64;
                hash = hash.wrapping_mul(FNV_PRIME);
                for elem in elements {
                    hash = hash_value(hash, &elem);
                }
            } else {
                // Non-enumerable - hash by structure
                hash ^= ksv.k() as u64;
                hash = hash.wrapping_mul(FNV_PRIME);
                hash = hash_value(hash, ksv.base());
            }
        }
        Value::BigUnion(uv) => {
            hash = hash_enumerable_set(hash, uv.to_sorted_set(), &[uv.set()]);
        }
        // StringSet is infinite - hash it as a special constant
        Value::StringSet => {
            // Use a constant marker for STRING (infinite set)
            hash ^= 0x5354_5249_4E47_5345; // "STRINGSE" in hex
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        // AnySet is infinite - hash it as a special constant
        Value::AnySet => {
            hash ^= 0x414E_5953_4554_5F5F; // "ANYSET__" in hex
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        // SeqSet is infinite - hash it by the base set
        Value::SeqSet(ssv) => {
            hash ^= 0x5345_5153_4554_5F5F; // "SEQSET__" in hex
            hash = hash.wrapping_mul(FNV_PRIME);
            hash = hash_value(hash, ssv.base());
        }
        _ => unreachable!("unhandled Value variant in hash body"),
    }

    hash
}
