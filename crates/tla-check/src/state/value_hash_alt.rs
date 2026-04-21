// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alternative hash algorithm implementations for benchmarking.
//!
//! These produce DIFFERENT fingerprints than the primary FNV-1a implementation
//! exposed through `value_hash` and implemented in `value_hash_fnv.rs`.
//! They exist for performance comparison and are not used in production
//! model checking.

use tla_core::FNV_OFFSET;

use crate::value::IntIntervalFunc;
use crate::Value;

use super::value_hash::hash_value;

// ============================================================================
// XXH3-based fingerprinting (for benchmarking/comparison)
// ============================================================================

/// Compute fingerprint using xxh3 (faster than FNV-1a for larger values)
///
/// This is an alternative fingerprint implementation for benchmarking.
/// Note: This produces DIFFERENT fingerprints than `value_fingerprint`.
pub fn value_fingerprint_xxh3(value: &Value) -> u64 {
    use xxhash_rust::xxh3::xxh3_64;

    // Pre-allocate buffer for serialization
    let mut buffer = Vec::with_capacity(256);
    serialize_value_for_hash(&mut buffer, value);
    xxh3_64(&buffer)
}

/// Serialize a value into bytes for hashing
/// This produces a deterministic byte representation
fn serialize_value_for_hash(buffer: &mut Vec<u8>, value: &Value) {
    match value {
        Value::Bool(b) => {
            buffer.push(0); // type tag
            buffer.push(*b as u8);
        }
        Value::SmallInt(n) => {
            buffer.push(1); // type tag
            buffer.extend_from_slice(&n.to_le_bytes());
        }
        Value::Int(n) => {
            buffer.push(1); // type tag (same as SmallInt)
            buffer.extend_from_slice(&n.to_signed_bytes_le());
        }
        Value::String(s) | Value::ModelValue(s) => {
            buffer.push(if matches!(value, Value::String(_)) {
                2
            } else {
                8
            }); // type tag
            buffer.extend_from_slice(&(s.len() as u32).to_le_bytes());
            buffer.extend_from_slice(s.as_bytes());
        }
        Value::Set(set) => {
            buffer.push(3); // type tag
            buffer.extend_from_slice(&(set.len() as u32).to_le_bytes());
            for elem in set.as_ref() {
                serialize_value_for_hash(buffer, elem);
            }
        }
        Value::Func(func) => {
            buffer.push(4); // type tag
            buffer.extend_from_slice(&(func.domain_len() as u32).to_le_bytes());
            for (k, v) in func.mapping_iter() {
                serialize_value_for_hash(buffer, k);
                serialize_value_for_hash(buffer, v);
            }
        }
        Value::Tuple(t) => {
            buffer.push(4); // type tag (same as Func)
            buffer.extend_from_slice(&(t.len() as u32).to_le_bytes());
            for (i, v) in t.iter().enumerate() {
                // Key is 1-based index
                buffer.push(1); // SmallInt tag
                buffer.extend_from_slice(&((i + 1) as i64).to_le_bytes());
                serialize_value_for_hash(buffer, v);
            }
        }
        Value::Seq(s) => {
            buffer.push(4); // type tag (same as Func)
            buffer.extend_from_slice(&(s.len() as u32).to_le_bytes());
            for (i, v) in s.iter().enumerate() {
                buffer.push(1); // SmallInt tag
                buffer.extend_from_slice(&((i + 1) as i64).to_le_bytes());
                serialize_value_for_hash(buffer, v);
            }
        }
        Value::Record(r) => {
            buffer.push(4); // type tag (same as Func)
            buffer.extend_from_slice(&(r.len() as u32).to_le_bytes());
            for (k_id, v) in r.iter() {
                let k = tla_core::resolve_name_id(k_id);
                buffer.push(2); // String tag
                buffer.extend_from_slice(&(k.len() as u32).to_le_bytes());
                buffer.extend_from_slice(k.as_bytes());
                serialize_value_for_hash(buffer, v);
            }
        }
        Value::IntFunc(func) => {
            buffer.push(4); // type tag (same as Func)
            buffer.extend_from_slice(&(func.values().len() as u32).to_le_bytes());
            for (i, v) in func.values().iter().enumerate() {
                let key = IntIntervalFunc::min(func) + i as i64;
                buffer.push(1); // SmallInt tag
                buffer.extend_from_slice(&key.to_le_bytes());
                serialize_value_for_hash(buffer, v);
            }
        }
        // For complex lazy types, fall back to FNV fingerprint
        Value::Interval(_)
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
        | Value::SeqSet(_)
        | Value::Closure(_)
        | Value::LazyFunc(_) => {
            // Fall back to FNV for complex types
            let fp = hash_value(FNV_OFFSET, value);
            buffer.push(255); // special tag for FNV fallback
            buffer.extend_from_slice(&fp.to_le_bytes());
        }
        _ => unreachable!("unhandled Value variant in serialize_value_for_hash"),
    }
}

// ============================================================================
// ahash-based fingerprinting (streaming, no buffer allocation)
// ============================================================================

/// Compute fingerprint using ahash streaming API (AES-NI accelerated)
///
/// This avoids buffer allocation by using ahash's streaming interface.
/// Expected to be faster than XXH3 (which requires serialization) and FNV-1a
/// (which is inherently slow) for most value sizes.
///
/// Note: This produces DIFFERENT fingerprints than `value_fingerprint` or `value_fingerprint_xxh3`.
pub fn value_fingerprint_ahash(value: &Value) -> u64 {
    use ahash::AHasher;
    use std::hash::Hasher;

    let mut hasher = AHasher::default();
    hash_value_ahash(&mut hasher, value);
    hasher.finish()
}

/// Hash a value using ahash streaming API
fn hash_value_ahash(hasher: &mut ahash::AHasher, value: &Value) {
    use std::hash::Hasher;

    // Type tag (same scheme as FNV-1a for consistency)
    let tag: u8 = match value {
        Value::Bool(_) => 0,
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
        Value::Func(_) | Value::IntFunc(_) | Value::Seq(_) | Value::Record(_) | Value::Tuple(_) => {
            4
        }
        Value::ModelValue(_) => 8,
        Value::Closure(_) => 9,
        Value::LazyFunc(_) => 10,
        _ => unreachable!("unhandled Value variant in ahash tag"),
    };
    hasher.write_u8(tag);

    match value {
        Value::Bool(b) => {
            hasher.write_u8(*b as u8);
        }
        Value::SmallInt(n) => {
            hasher.write_i64(*n);
        }
        Value::Int(n) => {
            // Hash as signed bytes (same canonical form as FNV)
            let bytes = n.to_signed_bytes_le();
            hasher.write(&bytes);
        }
        Value::String(s) | Value::ModelValue(s) => {
            hasher.write(s.as_bytes());
        }
        Value::Set(set) => {
            hasher.write_usize(set.len());
            for elem in set.as_ref() {
                hash_value_ahash(hasher, elem);
            }
        }
        Value::Func(func) => {
            hasher.write_usize(func.domain_len());
            for (k, v) in func.mapping_iter() {
                hash_value_ahash(hasher, k);
                hash_value_ahash(hasher, v);
            }
        }
        Value::IntFunc(func) => {
            hasher.write_usize(func.values().len());
            for (i, v) in func.values().iter().enumerate() {
                let key = IntIntervalFunc::min(func) + i as i64;
                hasher.write_i64(key);
                hash_value_ahash(hasher, v);
            }
        }
        Value::Tuple(t) => {
            hasher.write_usize(t.len());
            for (i, v) in t.iter().enumerate() {
                hasher.write_i64((i + 1) as i64); // 1-based index
                hash_value_ahash(hasher, v);
            }
        }
        Value::Seq(s) => {
            hasher.write_usize(s.len());
            for (i, v) in s.iter().enumerate() {
                hasher.write_i64((i + 1) as i64);
                hash_value_ahash(hasher, v);
            }
        }
        Value::Record(r) => {
            hasher.write_usize(r.len());
            for (k_id, v) in r.iter() {
                let k = tla_core::resolve_name_id(k_id);
                hasher.write(k.as_bytes());
                hash_value_ahash(hasher, v);
            }
        }
        Value::Interval(iv) => {
            // Hash interval as its bounds
            use num_traits::ToPrimitive;
            if let (Some(low), Some(high)) = (iv.low().to_i64(), iv.high().to_i64()) {
                hasher.write_i64(low);
                hasher.write_i64(high);
            } else {
                hasher.write(&iv.low().to_signed_bytes_le());
                hasher.write(&iv.high().to_signed_bytes_le());
            }
        }
        // For lazy types, hash by structure (not evaluated)
        Value::Subset(s) => {
            hasher.write_usize(42); // marker for subset
            hash_value_ahash(hasher, s.base());
        }
        Value::FuncSet(fs) => {
            hasher.write_usize(43);
            hash_value_ahash(hasher, fs.domain());
            hash_value_ahash(hasher, fs.codomain());
        }
        Value::RecordSet(rs) => {
            hasher.write_usize(44);
            hasher.write_usize(rs.fields_len());
            for (name, domain) in rs.fields_iter() {
                hasher.write(name.as_bytes());
                hash_value_ahash(hasher, domain);
            }
        }
        Value::TupleSet(ts) => {
            hasher.write_usize(45);
            hasher.write_usize(ts.components_len());
            for domain in ts.components_iter() {
                hash_value_ahash(hasher, domain);
            }
        }
        Value::SetCup(sc) => {
            hasher.write_usize(46);
            hash_value_ahash(hasher, sc.set1());
            hash_value_ahash(hasher, sc.set2());
        }
        Value::SetCap(sc) => {
            hasher.write_usize(47);
            hash_value_ahash(hasher, sc.set1());
            hash_value_ahash(hasher, sc.set2());
        }
        Value::SetDiff(sd) => {
            hasher.write_usize(48);
            hash_value_ahash(hasher, sd.set1());
            hash_value_ahash(hasher, sd.set2());
        }
        Value::SetPred(_) => {
            // SetPred contains closures which are complex; use fallback
            hasher.write_u64(hash_value(FNV_OFFSET, value));
        }
        Value::KSubset(ks) => {
            hasher.write_usize(50);
            hasher.write_usize(ks.k());
            hash_value_ahash(hasher, ks.base());
        }
        Value::BigUnion(bu) => {
            hasher.write_usize(51);
            hash_value_ahash(hasher, bu.set());
        }
        Value::StringSet => {
            hasher.write_usize(52);
        }
        Value::AnySet => {
            hasher.write_usize(53);
        }
        Value::SeqSet(ss) => {
            hasher.write_usize(54);
            hash_value_ahash(hasher, ss.base());
        }
        Value::Closure(_) | Value::LazyFunc(_) => {
            // Fall back to FNV for closures/lazy functions
            hasher.write_u64(hash_value(FNV_OFFSET, value));
        }
        _ => unreachable!("unhandled Value variant in ahash body"),
    }
}
