// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Additive (commutative) fingerprinting for compound value types.
//!
//! Part of #3168: Uses wrapping addition of SplitMix64-mixed per-entry hashes.
//! Unlike FP64 (sequential rolling hash), this is COMMUTATIVE:
//! - Unchanged nested values use their cached fingerprint (O(1) lookup)
//! - Order-independent, so no TLC normalization needed
//! - O(entries) but with O(1) cached lookups for unchanged nested values
//!
//! Extracted from `value_hash.rs` as part of #3338.

use crate::value::{IntervalValue, SortedSet};
use crate::Value;
use num_traits::ToPrimitive;
use tla_core::{FNV_OFFSET, FNV_PRIME};

use super::value_hash::value_fingerprint;

/// Compute the FP64 fingerprint for a small integer without constructing a Value.
/// Used by seq/tuple/intfunc fingerprinting to avoid allocating a Value::SmallInt
/// on the stack (~96 bytes) for each element index.
///
/// Part of #3805: Uses the precomputed lookup table for values in [-256, 1023],
/// which covers all 1-indexed sequence/tuple keys (up to length 1023) and common
/// counter values. This eliminates 12 byte-at-a-time hash operations per element
/// in the typical case, replacing them with a single array lookup.
#[inline(always)]
fn smallint_fp(n: i64) -> u64 {
    if let Some(fp) = crate::fingerprint::fp64_smallint_lookup(n) {
        return fp;
    }
    use crate::fingerprint::value_tags::INTVALUE;
    use crate::fingerprint::{fp64_extend_i32, fp64_extend_i64, FP64_INIT};
    let fp = fp64_extend_i64(FP64_INIT, INTVALUE);
    if i32::try_from(n).is_ok() {
        fp64_extend_i32(fp, n as i32)
    } else {
        fp64_extend_i64(fp, n)
    }
}

/// SplitMix64 bit mixer for distributing per-entry hashes.
///
/// Part of #3168: used by the additive fingerprint to mix entry hashes
/// before summing, reducing collision risk from structured data patterns.
#[inline(always)]
pub(crate) fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E3779B97F4A7C15);
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB);
    x ^ (x >> 31)
}

/// Seed for function-type additive fingerprints.
pub(crate) const ADDITIVE_FUNC_SEED: u64 = 0x517cc1b727220a95;

/// Seed for set additive fingerprints (distinct from FUNC_SEED).
pub(super) const ADDITIVE_SET_SEED: u64 = 0x6a09e667f3bcc908;

/// Compute per-entry hash for additive fingerprinting.
///
/// Combines key and value fingerprints asymmetrically so (k, v) and (v, k)
/// produce different hashes, then applies SplitMix64 mixing.
#[inline]
pub(crate) fn additive_entry_hash(key_fp: u64, val_fp: u64) -> u64 {
    splitmix64(key_fp.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(val_fp))
}

/// Compute additive fingerprint for a FuncValue.
///
/// Part of #3168: Uses wrapping addition of mixed per-entry hashes.
/// Unlike FP64 (sequential rolling hash), this is COMMUTATIVE:
/// - Unchanged nested values use their cached fingerprint (O(1) lookup)
/// - Order-independent, so no TLC normalization needed
/// - O(entries) but with O(1) cached lookups for unchanged nested values
///   vs FP64's O(total_entries_all_levels) due to sequential dependency
pub(super) fn compute_func_additive_fp(func: &crate::value::FuncValue) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(func.domain_len() as u64));
    for (key, val) in func.mapping_iter() {
        let kfp = value_fingerprint(key);
        let vfp = value_fingerprint(val);
        fp = fp.wrapping_add(additive_entry_hash(kfp, vfp));
    }
    fp
}

/// Compute additive fingerprint for an IntIntervalFunc.
///
/// Part of #3168: Same commutative approach as FuncValue.
/// Part of #3285: Uses `value_fingerprint(&Value::SmallInt(key))` for integer
/// keys to match FuncValue's `value_fingerprint(key)` — without this,
/// `Func({1->a})` and `IntFunc(1,1,[a])` produce different fingerprints.
pub(super) fn compute_int_func_additive_fp(func: &crate::value::IntIntervalFunc) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(func.len() as u64));
    for (i, val) in func.values().iter().enumerate() {
        let key_int = crate::value::IntIntervalFunc::min(func) + i as i64;
        let key_fp = smallint_fp(key_int);
        let vfp = value_fingerprint(val);
        fp = fp.wrapping_add(additive_entry_hash(key_fp, vfp));
    }
    fp
}

/// Compute additive fingerprint for a SeqValue.
///
/// Part of #3168: Seq is semantically IntFunc({1..n → values}), so it must
/// produce the same additive fingerprint as IntFunc(min=1). Without this,
/// a state variable that appears as Seq in one state and IntFunc in another
/// would produce different state fingerprints for the same mathematical
/// value, causing false non-deduplication.
/// Part of #3285: Integer keys use `value_fingerprint` to match FuncValue.
pub(super) fn compute_seq_additive_fp(seq: &crate::value::SeqValue) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(seq.len() as u64));
    for (i, val) in seq.iter().enumerate() {
        let key_int = (i as i64) + 1; // 1-indexed, same as IntFunc(min=1)
        let key_fp = smallint_fp(key_int);
        let vfp = value_fingerprint(val);
        fp = fp.wrapping_add(additive_entry_hash(key_fp, vfp));
    }
    fp
}

/// Compute additive fingerprint for a RecordValue.
///
/// Part of #3281: Record uses the same additive scheme as function-like values.
/// Reads the cached standalone FP64 fingerprint for each NameId key so records
/// and equivalent FuncValues with string keys produce identical state
/// fingerprints without rehashing field names on the hot path.
/// Must match the tla-value crate's compute_record_additive_fp exactly.
pub(super) fn compute_record_additive_fp(rec: &crate::value::RecordValue) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(rec.len() as u64));
    for (field_id, val) in rec.iter() {
        let key_fp = tla_core::resolve_name_id_string_fp64(field_id);
        let vfp = value_fingerprint(val);
        fp = fp.wrapping_add(additive_entry_hash(key_fp, vfp));
    }
    fp
}

/// Compute additive fingerprint for a SortedSet.
///
/// Part of #3246: Uses commutative wrapping addition of splitmix64-mixed element
/// fingerprints. Must match the tla-value crate's compute_set_additive_fp exactly.
pub(super) fn compute_set_additive_fp(set: &SortedSet) -> u64 {
    let mut fp = ADDITIVE_SET_SEED;
    fp = fp.wrapping_add(splitmix64(set.len() as u64));
    for elem in set.iter() {
        fp = fp.wrapping_add(splitmix64(value_fingerprint(elem)));
    }
    fp
}

/// Compute additive fingerprint for an IntervalValue.
///
/// Part of #3278: Interval is semantically the same set as its materialized
/// SortedSet, so state dedup must not distinguish `1..3` from `{1, 2, 3}`.
/// Iterate the interval directly to avoid materializing a temporary set.
pub(super) fn compute_interval_additive_fp(interval: &IntervalValue) -> u64 {
    let mut fp = ADDITIVE_SET_SEED;
    let len = interval.len();
    let len_fp = len.to_u64().map(splitmix64).unwrap_or_else(|| {
        let mut hash = FNV_OFFSET;
        for byte in len.to_signed_bytes_le() {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        splitmix64(hash)
    });
    fp = fp.wrapping_add(len_fp);
    for elem in interval.iter_values() {
        fp = fp.wrapping_add(splitmix64(value_fingerprint(&elem)));
    }
    fp
}

/// Compute additive fingerprint for a Tuple (boxed slice of Values).
///
/// Part of #3191: Tuple is semantically IntFunc({1..n → values}), same as Seq.
/// TLC treats tuples and sequences as the same type (FcnRcdValue). Before #3168,
/// both used FP64 so they matched. After #3168 switched Seq to additive, Tuple
/// must also use additive to maintain Tuple/Seq fingerprint equivalence.
/// Part of #3285: Integer keys use `value_fingerprint` to match FuncValue.
pub(super) fn compute_tuple_additive_fp(elems: &[Value]) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(elems.len() as u64));
    for (i, val) in elems.iter().enumerate() {
        let key_int = (i as i64) + 1; // 1-indexed, same as IntFunc(min=1)
        let key_fp = smallint_fp(key_int);
        let vfp = value_fingerprint(val);
        fp = fp.wrapping_add(additive_entry_hash(key_fp, vfp));
    }
    fp
}
