// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC structured-value comparison rules (tuple, seq, record).

use super::super::{FuncValue, Value};
use crate::error::EvalResult;
use std::cmp::Ordering;
use std::sync::Arc;

/// Compare tuple/seq values per TLC rules.
///
/// Handles fast path for Tuple-Tuple comparison (Part of #2955) and fallback
/// through `tlc_to_tuple` / function coercion.
pub(super) fn cmp_tuple_seq(a: &Value, b: &Value) -> EvalResult<Ordering> {
    // Part of #2955: Fast path for Tuple-Tuple comparison — compare
    // elements in place without allocating temporary Vecs.
    // GameOfLife's CHOOSE on tuple sets calls tlc_cmp ~67M times.
    if let (Value::Tuple(at), Some(b_slice)) = (a, Value::tlc_as_tuple_slice(b)) {
        let a_slice = at.as_ref();
        let len_cmp = a_slice.len().cmp(&b_slice.len());
        if len_cmp != Ordering::Equal {
            return Ok(len_cmp);
        }
        for (av, bv) in a_slice.iter().zip(b_slice.iter()) {
            let cmp = Value::tlc_cmp(av, bv)?;
            if cmp != Ordering::Equal {
                return Ok(cmp);
            }
        }
        return Ok(Ordering::Equal);
    }

    // General path for Seq, Func, or mixed Tuple/Func comparison.
    let a_elems: Vec<Value> = match a {
        Value::Tuple(t) => t.as_ref().to_vec(),
        Value::Seq(s) => s.to_vec(),
        _ => unreachable!(),
    };
    if let Some(b_elems) = Value::tlc_to_tuple(b)? {
        let len_cmp = a_elems.len().cmp(&b_elems.len());
        if len_cmp != Ordering::Equal {
            return Ok(len_cmp);
        }
        for (av, bv) in a_elems.iter().zip(b_elems.iter()) {
            let cmp = Value::tlc_cmp(av, bv)?;
            if cmp != Ordering::Equal {
                return Ok(cmp);
            }
        }
        return Ok(Ordering::Equal);
    }

    // Fallback: compare as functions.
    let entries: Vec<(Value, Value)> = a_elems
        .iter()
        .enumerate()
        .map(|(i, v)| (Value::SmallInt((i + 1) as i64), v.clone()))
        .collect();
    Value::tlc_cmp(
        &Value::Func(Arc::new(FuncValue::from_sorted_entries(entries))),
        b,
    )
}

/// Compare record values per TLC rules.
pub(super) fn cmp_record(a: &Value, b: &Value) -> EvalResult<Ordering> {
    let Value::Record(r) = a else {
        unreachable!("cmp_record called on non-record");
    };
    let Some(br) = Value::tlc_to_record(b)? else {
        return Err(Value::tlc_cmp_err(format!(
            "Attempted to compare record {a:?} with non-record {b:?}"
        )));
    };
    // Compare by length, then domain (field names), then values.
    let len_cmp = r.len().cmp(&br.len());
    if len_cmp != Ordering::Equal {
        return Ok(len_cmp);
    }
    for ((ak, _), (bk, _)) in r.iter_str().zip(br.iter()) {
        let key_cmp = ak.cmp(bk);
        if key_cmp != Ordering::Equal {
            return Ok(key_cmp);
        }
    }
    for ((_, av), (_, bv)) in r.iter_str().zip(br.iter()) {
        let cmp = Value::tlc_cmp(av, bv)?;
        if cmp != Ordering::Equal {
            return Ok(cmp);
        }
    }
    Ok(Ordering::Equal)
}
