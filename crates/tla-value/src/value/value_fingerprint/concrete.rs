// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC-compatible FP64 fingerprinting for concrete value types.
//!
//! Handles: Bool, SmallInt, Int, String, Set, Interval, Func, IntFunc,
//! Tuple, Seq, Record, ModelValue.

use super::super::tlc_sort::TlcFuncOrder;
use super::super::{FuncValue, Value};
use super::error::{FingerprintError, FingerprintResult};
use super::helpers::{fp_bigint_len_to_i32, fp_usize_to_i32};
use crate::fingerprint::{
    fp64_extend_bigint, fp64_extend_i32, fp64_extend_i64, fp64_extend_str, value_tags::*,
};

fn ordered_key<'a>(func: &'a FuncValue, order: &TlcFuncOrder<'_>, pos: usize) -> &'a Value {
    match order {
        TlcFuncOrder::Stored => func.key_at(pos),
        TlcFuncOrder::Permuted(indices) => func.key_at(indices[pos]),
    }
}

fn ordered_value<'a>(func: &'a FuncValue, order: &TlcFuncOrder<'_>, pos: usize) -> &'a Value {
    match order {
        TlcFuncOrder::Stored => func.value_at(pos),
        TlcFuncOrder::Permuted(indices) => func.value_at(indices[pos]),
    }
}

pub(super) fn fingerprint_extend_concrete(value: &Value, fp: u64) -> FingerprintResult<u64> {
    match value {
        Value::Bool(b) => {
            // TLC: fp = FP64.Extend(fp, BOOLVALUE); fp = FP64.Extend(fp, (val) ? 't' : 'f');
            let fp = fp64_extend_i64(fp, BOOLVALUE);
            // TLC uses 't' or 'f' as char, which is extended as a single byte
            let c = if *b { b't' } else { b'f' };
            Ok(crate::fingerprint::fp64_extend_byte(fp, c))
        }
        Value::SmallInt(n) => {
            // TLC: fp = FP64.Extend(FP64.Extend(fp, INTVALUE), this.val);
            let fp = fp64_extend_i64(fp, INTVALUE);
            // TLC's IntValue uses int (32-bit), but we may have larger values
            if i32::try_from(*n).is_ok() {
                Ok(fp64_extend_i32(fp, *n as i32))
            } else {
                Ok(fp64_extend_i64(fp, *n))
            }
        }
        Value::Int(n) => {
            let fp = fp64_extend_i64(fp, INTVALUE);
            Ok(fp64_extend_bigint(fp, n))
        }
        Value::String(s) => {
            // TLC: fp = FP64.Extend(fp, STRINGVALUE); fp = FP64.Extend(fp, len); fp = FP64.Extend(fp, str);
            let fp = fp64_extend_i64(fp, STRINGVALUE);
            let fp = fp64_extend_i32(fp, fp_usize_to_i32(s.len(), "string length")?);
            Ok(fp64_extend_str(fp, s))
        }
        Value::Set(set) => {
            // TLC SetEnumValue: fp = FP64.Extend(fp, SETENUMVALUE); fp = FP64.Extend(fp, sz);
            // then normalize() (sort by compareTo), then fingerprint each elem.
            // Fix #3006: iterate in TLC's compareTo order, not Value::Ord order.
            let mut fp = fp64_extend_i64(fp, SETENUMVALUE);
            fp = fp64_extend_i32(fp, fp_usize_to_i32(set.len(), "set cardinality")?);
            // Fast path: for homogeneous safe types (Bool, Int),
            // Value::Ord agrees with tlc_cmp — use stored order (zero allocation).
            let homogeneous_safe = match (set.first(), set.last()) {
                (Some(f), Some(l)) => {
                    Value::tlc_cmp_agrees_with_ord(f)
                        && Value::tlc_cmp_type_class(f) == Value::tlc_cmp_type_class(l)
                }
                _ => true, // empty set — trivially correct
            };
            if homogeneous_safe {
                for elem in set.as_ref() {
                    fp = elem.fingerprint_extend(fp)?;
                }
            } else {
                // Slow path: re-sort by tlc_cmp for sets with complex element types
                // (tuples, sets, records, functions, model values).
                // Optimization: sort borrowed references to avoid cloning all elements.
                // This preserves TLC's insertion-sort/error behavior while shifting only
                // `&Value` handles instead of allocating and cloning full elements.
                let refs = Value::tlc_sort_refs_nodup(set.iter().collect())
                    .map_err(|e| FingerprintError::TlcNormalization(e.to_string()))?;
                for elem in refs {
                    fp = elem.fingerprint_extend(fp)?;
                }
            }
            Ok(fp)
        }
        Value::Interval(intv) => {
            // TLC IntervalValue fingerprints as SETENUMVALUE (a set)
            // Each element is fingerprinted as INTVALUE
            let mut fp = fp64_extend_i64(fp, SETENUMVALUE);
            let len = &intv.high - &intv.low + num_bigint::BigInt::from(1);
            let len_i32 = fp_bigint_len_to_i32(&len, "interval length")?;
            fp = fp64_extend_i32(fp, len_i32);
            for val in intv.iter_values() {
                fp = val.fingerprint_extend(fp)?;
            }
            Ok(fp)
        }
        Value::Func(func) => {
            // TLC FcnRcdValue: normalize() then fingerprint entries in compareTo order.
            // Fix #3006: use TLC compareTo order via func_tlc_order(), not stored
            // Value::Ord order. Homogeneous-safe domains (Bool/Int) use the stored
            // order directly; non-safe domains use a cached domain-index permutation.
            let mut fp = fp64_extend_i64(fp, FCNRCDVALUE);
            let order = Value::func_tlc_order(func)
                .map_err(|e| FingerprintError::TlcNormalization(e.to_string()))?;
            fp = fp64_extend_i32(
                fp,
                fp_usize_to_i32(func.domain_len(), "function domain size")?,
            );
            for pos in 0..func.domain_len() {
                let key = ordered_key(func, &order, pos);
                let val = ordered_value(func, &order, pos);
                fp = key.fingerprint_extend(fp)?;
                fp = val.fingerprint_extend(fp)?;
            }
            Ok(fp)
        }
        Value::IntFunc(func) => {
            // IntFunc is semantically a function, fingerprint as FCNRCDVALUE
            // Domain is min..max (integers)
            let mut fp = fp64_extend_i64(fp, FCNRCDVALUE);
            let len = func.values.len();
            fp = fp64_extend_i32(fp, fp_usize_to_i32(len, "interval function length")?);
            // For IntIntervalFunc, domain is min..max
            for (i, val) in func.values.iter().enumerate() {
                // Domain key: min + i (checked to prevent silent wrapping in release mode)
                let key =
                    func.min
                        .checked_add(i as i64)
                        .ok_or(FingerprintError::I64DomainOverflow {
                            min: func.min,
                            offset: i,
                        })?;
                let fp_tmp = fp64_extend_i64(fp, INTVALUE);
                let fp_tmp = if i32::try_from(key).is_ok() {
                    fp64_extend_i32(fp_tmp, key as i32)
                } else {
                    fp64_extend_i64(fp_tmp, key)
                };
                fp = val.fingerprint_extend(fp_tmp)?;
            }
            Ok(fp)
        }
        Value::Tuple(elems) => {
            // TLC TupleValue: fingerprinted as FCNRCDVALUE with integer domain 1..n
            // fp = FP64.Extend(fp, FCNRCDVALUE); fp = FP64.Extend(fp, len);
            // for i in 1..len: fp = FP64.Extend(fp, INTVALUE); fp = FP64.Extend(fp, i); fp = elems[i].fingerPrint(fp);
            let mut fp = fp64_extend_i64(fp, FCNRCDVALUE);
            fp = fp64_extend_i32(fp, fp_usize_to_i32(elems.len(), "tuple length")?);
            for (i, elem) in elems.iter().enumerate() {
                // Domain key: 1-indexed
                fp = fp64_extend_i64(fp, INTVALUE);
                fp = fp64_extend_i32(fp, fp_usize_to_i32(i + 1, "tuple index")?);
                fp = elem.fingerprint_extend(fp)?;
            }
            Ok(fp)
        }
        Value::Seq(seq) => {
            // Sequences are like tuples: functions from 1..n
            let mut fp = fp64_extend_i64(fp, FCNRCDVALUE);
            fp = fp64_extend_i32(fp, fp_usize_to_i32(seq.len(), "sequence length")?);
            for (i, elem) in seq.iter().enumerate() {
                fp = fp64_extend_i64(fp, INTVALUE);
                fp = fp64_extend_i32(fp, fp_usize_to_i32(i + 1, "sequence index")?);
                fp = elem.fingerprint_extend(fp)?;
            }
            Ok(fp)
        }
        Value::Record(rec) => {
            // TLC RecordValue: fingerprinted as FCNRCDVALUE
            // Keys are strings resolved from NameId for content-based FP64
            let mut fp = fp64_extend_i64(fp, FCNRCDVALUE);
            fp = fp64_extend_i32(fp, fp_usize_to_i32(rec.len(), "record field count")?);
            for (key_id, val) in rec.iter() {
                // Resolve NameId to string for content-based fingerprinting
                let key = tla_core::resolve_name_id(key_id);
                let fp_tmp = fp64_extend_i64(fp, STRINGVALUE);
                let fp_tmp =
                    fp64_extend_i32(fp_tmp, fp_usize_to_i32(key.len(), "record key length")?);
                let fp_tmp = fp64_extend_str(fp_tmp, &key);
                fp = val.fingerprint_extend(fp_tmp)?;
            }
            Ok(fp)
        }
        Value::ModelValue(name) => {
            // TLC ModelValue: MODELVALUE tag + name string
            let fp = fp64_extend_i64(fp, MODELVALUE);
            Ok(fp64_extend_str(fp, name))
        }
        _ => unreachable!("fingerprint_extend_concrete called with non-concrete value"),
    }
}
