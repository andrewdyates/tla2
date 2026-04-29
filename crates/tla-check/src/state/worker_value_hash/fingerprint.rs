// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Worker-local fingerprint computation using a HashMap memo instead of
//! embedded `AtomicU64` caches. Eliminates cross-thread cache-line bouncing.
//!
//! Part of #3337.

use rustc_hash::FxHashMap;
use std::sync::Arc;

use crate::value::{FuncValue, IntIntervalFunc, RecordValue, SeqValue, SortedSet};
use crate::Value;

use tla_core::FNV_PRIME;

// Re-derive additive fingerprint constants (must match value_hash.rs exactly).
const ADDITIVE_FUNC_SEED: u64 = 0x517cc1b727220a95;
const ADDITIVE_SET_SEED: u64 = 0x6a09e667f3bcc908;

#[inline(always)]
fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E3779B97F4A7C15);
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB);
    x ^ (x >> 31)
}

#[inline]
fn additive_entry_hash(key_fp: u64, val_fp: u64) -> u64 {
    splitmix64(key_fp.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(val_fp))
}

// ============================================================================
// WorkerFpMemo
// ============================================================================

/// Worker-local fingerprint memo.
///
/// Caches value fingerprints keyed by Arc pointer identity for compound types.
/// Primitive types (Bool, SmallInt) are computed inline without caching.
///
/// Replaces the embedded `AtomicU64` caches in `FuncValue`, `SortedSet`, etc.
/// for the worker-local lane, eliminating cross-thread contention.
pub(crate) struct WorkerFpMemo {
    cache: FxHashMap<usize, u64>,
}

impl WorkerFpMemo {
    pub(crate) fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
        }
    }

    pub(crate) fn with_capacity(cap: usize) -> Self {
        Self {
            cache: FxHashMap::with_capacity_and_hasher(cap, Default::default()),
        }
    }

    /// Clear the memo for reuse across states.
    pub(crate) fn clear(&mut self) {
        self.cache.clear();
    }

    /// Compute a value fingerprint using the worker-local memo.
    pub(crate) fn value_fingerprint(&mut self, value: &Value) -> u64 {
        worker_value_fingerprint(value, &mut self.cache)
    }
}

// ============================================================================
// Worker-local fingerprint computation
// ============================================================================

/// Compute the fingerprint of a single value using a worker-local memo.
///
/// Mirrors `value_hash::value_fingerprint` but uses a HashMap memo instead
/// of embedded `AtomicU64` caches. For compound types, results are cached
/// by Arc pointer identity so repeated accesses to the same value are O(1).
///
/// Part of #3805: SmallInt and Bool use precomputed lookup tables to eliminate
/// byte-at-a-time FP64 computation on the worker hot path.

/// Compute the FP64 fingerprint for a small integer without constructing a Value.
/// Used by seq/tuple fingerprinting to avoid allocating a Value::SmallInt on the
/// stack (~96 bytes) for each element index. Falls back to byte-at-a-time for
/// values outside the precomputed table range.
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

pub(super) fn worker_value_fingerprint(value: &Value, memo: &mut FxHashMap<usize, u64>) -> u64 {
    use crate::fingerprint::FP64_INIT;

    // Part of #3805: Fast path for primitives using precomputed lookup tables.
    // SmallInt and Bool are the most common leaf types — skip all compound checks.
    match value {
        Value::Bool(b) => return crate::fingerprint::fp64_bool_lookup(*b),
        Value::SmallInt(n) => return smallint_fp(*n),
        _ => {}
    }

    if let Value::Func(func) = value {
        let key = Arc::as_ptr(func) as usize;
        if let Some(&cached) = memo.get(&key) {
            return cached;
        }
        let fp = worker_compute_func_additive_fp(func, memo);
        memo.insert(key, fp);
        return fp;
    }

    if let Value::IntFunc(func) = value {
        let key = Arc::as_ptr(func) as usize;
        if let Some(&cached) = memo.get(&key) {
            return cached;
        }
        let fp = worker_compute_int_func_additive_fp(func, memo);
        memo.insert(key, fp);
        return fp;
    }

    if let Value::Set(set) = value {
        let key = set.storage_ptr_identity();
        if let Some(&cached) = memo.get(&key) {
            return cached;
        }
        let fp = worker_compute_set_additive_fp(set, memo);
        memo.insert(key, fp);
        return fp;
    }

    if let Value::Interval(interval) = value {
        return worker_compute_interval_additive_fp(interval, memo);
    }

    if let Value::Record(rec) = value {
        let key = rec.storage_ptr_identity();
        if let Some(&cached) = memo.get(&key) {
            return cached;
        }
        let fp = worker_compute_record_additive_fp(rec, memo);
        memo.insert(key, fp);
        return fp;
    }

    if let Value::Seq(seq) = value {
        let key = Arc::as_ptr(seq) as usize;
        if let Some(&cached) = memo.get(&key) {
            return cached;
        }
        let fp = worker_compute_seq_additive_fp(seq, memo);
        memo.insert(key, fp);
        return fp;
    }

    if let Value::Tuple(elems) = value {
        // Arc<[Value]> pointer identity
        let key = Arc::as_ptr(elems).cast::<Value>() as usize;
        if let Some(&cached) = memo.get(&key) {
            return cached;
        }
        let fp = worker_compute_tuple_additive_fp(elems, memo);
        memo.insert(key, fp);
        return fp;
    }

    // All other types: FP64 directly (cheap for primitives)
    value
        .fingerprint_extend(FP64_INIT)
        .expect("worker state dedup: value fingerprint within TLC-compatible limits")
}

fn worker_compute_func_additive_fp(func: &FuncValue, memo: &mut FxHashMap<usize, u64>) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(func.domain_len() as u64));
    for (key, val) in func.mapping_iter() {
        let kfp = worker_value_fingerprint(key, memo);
        let vfp = worker_value_fingerprint(val, memo);
        fp = fp.wrapping_add(additive_entry_hash(kfp, vfp));
    }
    fp
}

fn worker_compute_int_func_additive_fp(
    func: &IntIntervalFunc,
    memo: &mut FxHashMap<usize, u64>,
) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(func.len() as u64));
    for (i, val) in func.values().iter().enumerate() {
        let key_int = IntIntervalFunc::min(func) + i as i64;
        let key_fp = smallint_fp(key_int);
        let vfp = worker_value_fingerprint(val, memo);
        fp = fp.wrapping_add(additive_entry_hash(key_fp, vfp));
    }
    fp
}

fn worker_compute_set_additive_fp(set: &SortedSet, memo: &mut FxHashMap<usize, u64>) -> u64 {
    let mut fp = ADDITIVE_SET_SEED;
    fp = fp.wrapping_add(splitmix64(set.len() as u64));
    for elem in set.iter() {
        fp = fp.wrapping_add(splitmix64(worker_value_fingerprint(elem, memo)));
    }
    fp
}

fn worker_compute_interval_additive_fp(
    interval: &crate::value::IntervalValue,
    memo: &mut FxHashMap<usize, u64>,
) -> u64 {
    use num_traits::ToPrimitive;

    let mut fp = ADDITIVE_SET_SEED;
    let len = interval.len();
    let len_fp = len.to_u64().map(splitmix64).unwrap_or_else(|| {
        let mut hash = tla_core::FNV_OFFSET;
        for byte in len.to_signed_bytes_le() {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        splitmix64(hash)
    });
    fp = fp.wrapping_add(len_fp);
    for elem in interval.iter_values() {
        fp = fp.wrapping_add(splitmix64(worker_value_fingerprint(&elem, memo)));
    }
    fp
}

fn worker_compute_record_additive_fp(rec: &RecordValue, memo: &mut FxHashMap<usize, u64>) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(rec.len() as u64));
    for (field_id, val) in rec.iter() {
        let key_fp = tla_core::resolve_name_id_string_fp64(field_id);
        let vfp = worker_value_fingerprint(val, memo);
        fp = fp.wrapping_add(additive_entry_hash(key_fp, vfp));
    }
    fp
}

fn worker_compute_seq_additive_fp(seq: &SeqValue, memo: &mut FxHashMap<usize, u64>) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(seq.len() as u64));
    for (i, val) in seq.iter().enumerate() {
        let key_fp = smallint_fp((i as i64) + 1);
        let vfp = worker_value_fingerprint(val, memo);
        fp = fp.wrapping_add(additive_entry_hash(key_fp, vfp));
    }
    fp
}

fn worker_compute_tuple_additive_fp(elems: &[Value], memo: &mut FxHashMap<usize, u64>) -> u64 {
    let mut fp = ADDITIVE_FUNC_SEED;
    fp = fp.wrapping_add(splitmix64(elems.len() as u64));
    for (i, val) in elems.iter().enumerate() {
        let key_fp = smallint_fp((i as i64) + 1);
        let vfp = worker_value_fingerprint(val, memo);
        fp = fp.wrapping_add(additive_entry_hash(key_fp, vfp));
    }
    fp
}
