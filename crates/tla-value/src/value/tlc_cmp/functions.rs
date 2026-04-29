// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC function/int-function comparison rules.
//!
//! Part of #1434: Zero-allocation fast paths for function comparison.
//! TLC normalizes functions once (isNorm flag) then compares in-place.

use super::super::tlc_sort::TlcFuncOrder;
use super::super::{FuncValue, Value};
use crate::error::EvalResult;
use std::cmp::Ordering;

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

/// Compare function values per TLC rules.
///
/// Handles IntFunc-IntFunc fast path, Func-Func cached normalization,
/// and cross-type fallback through `tlc_function_dom_vals`.
pub(super) fn cmp_functions(a: &Value, b: &Value) -> EvalResult<Ordering> {
    // IntFunc-IntFunc: integer domains are always in ascending order,
    // which agrees with tlc_cmp. Compare domain bounds + values in-place.
    if let (Value::IntFunc(af), Value::IntFunc(bf)) = (a, b) {
        let alen = (af.max - af.min + 1).max(0) as usize;
        let blen = (bf.max - bf.min + 1).max(0) as usize;
        let len_cmp = alen.cmp(&blen);
        if len_cmp != Ordering::Equal {
            return Ok(len_cmp);
        }
        // Same length → domain keys are SmallInts in sequence.
        // Compare starting points (identical length + same start = same domain).
        let dom_cmp = af.min.cmp(&bf.min);
        if dom_cmp != Ordering::Equal {
            return Ok(dom_cmp);
        }
        for (av, bv) in af.values.iter().zip(bf.values.iter()) {
            let cmp = Value::tlc_cmp(av, bv)?;
            if cmp != Ordering::Equal {
                return Ok(cmp);
            }
        }
        return Ok(Ordering::Equal);
    }

    // Func-Func: use TLC-normalized domain order with OnceLock caching.
    // Homogeneous-safe domains (Bool/Int) stay on the stored order.
    // Non-safe domains (String, ModelValue, Tuple, etc.) cache a domain-index
    // permutation so repeated comparisons avoid re-sorting or rebuilding pairs.
    if let (Value::Func(af), Value::Func(bf)) = (a, b) {
        let a_order = Value::func_tlc_order(af)?;
        let b_order = Value::func_tlc_order(bf)?;
        let len_cmp = af.domain_len().cmp(&bf.domain_len());
        if len_cmp != Ordering::Equal {
            return Ok(len_cmp);
        }
        for pos in 0..af.domain_len() {
            let cmp = Value::tlc_cmp(
                ordered_key(af, &a_order, pos),
                ordered_key(bf, &b_order, pos),
            )?;
            if cmp != Ordering::Equal {
                return Ok(cmp);
            }
        }
        for pos in 0..af.domain_len() {
            let cmp = Value::tlc_cmp(
                ordered_value(af, &a_order, pos),
                ordered_value(bf, &b_order, pos),
            )?;
            if cmp != Ordering::Equal {
                return Ok(cmp);
            }
        }
        return Ok(Ordering::Equal);
    }

    // General path: cross-type comparison (Func vs IntFunc, etc.).
    // Extracts domain/values via tlc_function_dom_vals (allocates).
    let Some((ad, av)) = Value::tlc_function_dom_vals(a)? else {
        return Err(Value::tlc_cmp_err(format!(
            "Attempted to compare function with non-function: {a:?}"
        )));
    };
    let Some((bd, bv)) = Value::tlc_function_dom_vals(b)? else {
        return Err(Value::tlc_cmp_err(format!(
            "Attempted to compare function {a:?} with non-function: {b:?}"
        )));
    };
    let len_cmp = av.len().cmp(&bv.len());
    if len_cmp != Ordering::Equal {
        return Ok(len_cmp);
    }
    for (x, y) in ad.iter().zip(bd.iter()) {
        let cmp = Value::tlc_cmp(x, y)?;
        if cmp != Ordering::Equal {
            return Ok(cmp);
        }
    }
    for (x, y) in av.iter().zip(bv.iter()) {
        let cmp = Value::tlc_cmp(x, y)?;
        if cmp != Ordering::Equal {
            return Ok(cmp);
        }
    }
    Ok(Ordering::Equal)
}
