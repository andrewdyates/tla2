// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC-compatible FP64 fingerprinting for lazy/derived value types.
//!
//! Handles: Subset, FuncSet, RecordSet, TupleSet, SetCup, SetCap, SetDiff,
//! SetPred, KSubset, BigUnion, StringSet, AnySet, SeqSet, LazyFunc, Closure.

use super::super::Value;
use super::error::FingerprintResult;
use super::helpers::fp_usize_to_i32;
use crate::fingerprint::{fp64_extend_i32, fp64_extend_i64, fp64_extend_str, value_tags::*};

/// Fingerprint a lazy set as a concrete Set when enumerable, otherwise use a
/// caller-provided structural fallback.
#[inline]
fn fingerprint_lazy_set_or_structural<F>(
    value: &Value,
    fp: u64,
    structural: F,
) -> FingerprintResult<u64>
where
    F: FnOnce(u64) -> FingerprintResult<u64>,
{
    if let Some(set) = value
        .as_lazy_set()
        .and_then(super::super::lazy_set::LazySet::to_sorted_set)
    {
        Value::from_sorted_set(set).fingerprint_extend(fp)
    } else {
        structural(fp)
    }
}

pub(super) fn fingerprint_extend_lazy(value: &Value, fp: u64) -> FingerprintResult<u64> {
    match value {
        Value::LazyFunc(lazy) => {
            // Lazy functions cannot be enumerated without evaluation context.
            // They are identified by their unique ID for fingerprinting purposes.
            // This is a rare case - most functions become Func or IntFunc during evaluation.
            let fp = fp64_extend_i64(fp, FCNLAMBDAVALUE);
            Ok(fp64_extend_i64(fp, lazy.id() as i64))
        }
        // Lazy set types - convert to concrete representation for fingerprinting
        Value::Subset(subset) => fingerprint_lazy_set_or_structural(value, fp, |fp| {
            // If we can't enumerate, use a fallback
            let fp = fp64_extend_i64(fp, SUBSETVALUE);
            subset.base.fingerprint_extend(fp)
        }),
        Value::FuncSet(funcset) => {
            let fp = fp64_extend_i64(fp, SETOFFCNSVALUE);
            let fp = funcset.domain.fingerprint_extend(fp)?;
            funcset.codomain.fingerprint_extend(fp)
        }
        Value::RecordSet(recset) => {
            let mut fp = fp64_extend_i64(fp, SETOFRCDSVALUE);
            fp = fp64_extend_i32(
                fp,
                fp_usize_to_i32(recset.fields.len(), "record-set field count")?,
            );
            for (name, vals) in &recset.fields {
                let fp_tmp = fp64_extend_str(fp, name);
                fp = vals.fingerprint_extend(fp_tmp)?;
            }
            Ok(fp)
        }
        Value::TupleSet(tupset) => {
            let mut fp = fp64_extend_i64(fp, SETOFTUPLESVALUE);
            fp = fp64_extend_i32(
                fp,
                fp_usize_to_i32(tupset.components.len(), "tuple-set component count")?,
            );
            for comp in &tupset.components {
                fp = comp.fingerprint_extend(fp)?;
            }
            Ok(fp)
        }
        Value::SetCup(cup) => fingerprint_lazy_set_or_structural(value, fp, |fp| {
            // Union of two sets - try to enumerate, otherwise use structural fp
            let fp = fp64_extend_i64(fp, SETCUPVALUE);
            let fp = cup.set1.fingerprint_extend(fp)?;
            cup.set2.fingerprint_extend(fp)
        }),
        Value::SetCap(cap) => fingerprint_lazy_set_or_structural(value, fp, |fp| {
            let fp = fp64_extend_i64(fp, SETCAPVALUE);
            let fp = cap.set1.fingerprint_extend(fp)?;
            cap.set2.fingerprint_extend(fp)
        }),
        Value::SetDiff(diff) => fingerprint_lazy_set_or_structural(value, fp, |fp| {
            let fp = fp64_extend_i64(fp, SETDIFFVALUE);
            let fp = diff.set1.fingerprint_extend(fp)?;
            diff.set2.fingerprint_extend(fp)
        }),
        Value::SetPred(pred) => {
            // SetPred can't always be enumerated without eval context.
            // Use deterministic structural fingerprinting and avoid runtime IDs.
            let fp = fp64_extend_i64(fp, SETPREDVALUE);
            pred.structural_fingerprint_extend(fp)
        }
        Value::KSubset(ksubset) => fingerprint_lazy_set_or_structural(value, fp, |fp| {
            // Fallback: structural fingerprint
            let fp = fp64_extend_i64(fp, SUBSETVALUE);
            let fp = ksubset.base.fingerprint_extend(fp)?;
            Ok(fp64_extend_i32(
                fp,
                fp_usize_to_i32(ksubset.k, "k-subset size")?,
            ))
        }),
        Value::BigUnion(union) => fingerprint_lazy_set_or_structural(value, fp, |fp| {
            let fp = fp64_extend_i64(fp, UNIONVALUE);
            union.set.fingerprint_extend(fp)
        }),
        Value::StringSet => {
            // Infinite set - use a unique tag
            Ok(fp64_extend_i64(fp, STRINGVALUE + 100)) // Arbitrary unique value
        }
        Value::AnySet => {
            // Infinite set
            Ok(fp64_extend_i64(fp, USERVALUE + 100))
        }
        Value::SeqSet(seqset) => {
            // Seq(S) - fingerprint based on base set
            let fp = fp64_extend_i64(fp, SETENUMVALUE + 100);
            seqset.base.fingerprint_extend(fp)
        }
        Value::Closure(c) => {
            // FIX #1859: include unique closure ID to distinguish distinct closures.
            // Without this, all closures produce the same fingerprint, causing
            // false state deduplication when closures appear in state variables.
            let fp = fp64_extend_i64(fp, OPLAMBDAVALUE);
            Ok(fp64_extend_i64(fp, c.id() as i64))
        }
        _ => unreachable!("fingerprint_extend_lazy called with non-lazy value"),
    }
}
