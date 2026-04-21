// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC-compatible sort, conversion, and classification helpers for `Value`.
//!
//! These functions support both the TLC-normalized iteration APIs (`tlc_iter`)
//! and the core directional comparison (`tlc_cmp`). Extracted from `tlc_cmp.rs`
//! as part of #3309.

use super::{FuncValue, Value};
use crate::error::{EvalError, EvalResult};
use std::cmp::Ordering;
use std::sync::Arc;

pub(crate) enum TlcFuncOrder<'a> {
    Stored,
    Permuted(&'a [usize]),
}

impl Value {
    /// Returns true if `Value::cmp` agrees with `tlc_cmp` for elements of this type.
    ///
    /// Safe types: Bool (bool::cmp), SmallInt/Int (numeric).
    /// Unsafe: Tuple/Seq (tlc: length-first), Set/Interval/Subset/KSubset/FuncSet
    /// (tlc: cardinality-first), Record/Func/IntFunc (tlc: length-first),
    /// ModelValue (tlc: registration-order indices),
    /// String (tlc: intern-token order, not lexical; Part of #3193).
    pub(super) fn tlc_cmp_agrees_with_ord(v: &Value) -> bool {
        // Part of #3193: String removed — TLC sorts strings by intern-token order
        // (first-seen/parse order), not lexical order. Value::cmp uses lexical.
        matches!(v, Value::Bool(_) | Value::SmallInt(_) | Value::Int(_))
    }

    /// Returns a type class identifier for tlc_cmp-compatible types.
    ///
    /// Elements within the same type class can be compared by both Value::cmp and tlc_cmp
    /// with identical ordering. Different type classes are incomparable in tlc_cmp (error)
    /// but have a defined discriminant order in Value::cmp — so mixed-class sets must NOT
    /// use the O(1) shortcut.
    ///
    /// Classes: 0=Bool, 1=Int/SmallInt, u8::MAX=unsafe/incompatible.
    /// Part of #3193: String moved to u8::MAX (unsafe) since tlc_cmp uses token order.
    pub(super) fn tlc_cmp_type_class(v: &Value) -> u8 {
        match v {
            Value::Bool(_) => 0,
            Value::SmallInt(_) | Value::Int(_) => 1,
            _ => u8::MAX,
        }
    }

    /// Returns true if all domain keys in a FuncValue are homogeneous-safe
    /// types (Bool or Int of the same class), meaning Value::cmp and tlc_cmp
    /// agree on their ordering. When true, the stored sort order (by Value::cmp)
    /// is already the TLC-normalized order, enabling zero-allocation comparison.
    ///
    /// Part of #1434: TLC caches normalization via `isNorm` flag. This check enables
    /// the equivalent optimization for tla2's immutable FuncValue.
    pub(super) fn func_domain_is_tlc_safe(func: &FuncValue) -> bool {
        match (func.domain_iter().next(), func.domain_iter().last()) {
            (Some(first), Some(last)) => {
                Self::tlc_cmp_agrees_with_ord(first)
                    && Self::tlc_cmp_type_class(first) == Self::tlc_cmp_type_class(last)
            }
            _ => true, // empty function is trivially safe
        }
    }

    fn tlc_sort_func_domain_indices(func: &FuncValue) -> EvalResult<Vec<usize>> {
        let mut sorted: Vec<usize> = Vec::with_capacity(func.domain_len());
        for idx in 0..func.domain_len() {
            let mut lo = 0usize;
            let mut hi = sorted.len();
            while lo < hi {
                let mid = (lo + hi) / 2;
                match Self::tlc_cmp(func.key_at(idx), func.key_at(sorted[mid]))? {
                    Ordering::Less => hi = mid,
                    Ordering::Greater => lo = mid + 1,
                    Ordering::Equal => {
                        return Err(Self::tlc_cmp_err(format!(
                            "The value {:?} occurs multiple times in function domain.",
                            func.key_at(idx)
                        )));
                    }
                }
            }
            sorted.insert(lo, idx);
        }
        Ok(sorted)
    }

    /// Get TLC-normalized domain order for a FuncValue, computing and caching if needed.
    ///
    /// For homogeneous-safe domains (Bool/Int), the stored order already matches
    /// TLC order, so returns [`TlcFuncOrder::Stored`] without populating the cache.
    /// For non-safe domains (String, ModelValue, Tuple, etc.), computes the TLC
    /// sort on first call and caches the domain-index permutation via OnceLock.
    ///
    /// Part of #1434: TLC's `FcnRcdValue.normalize()` equivalent for tla2.
    /// Eliminates per-comparison allocation for non-safe function domains.
    pub(crate) fn func_tlc_order(func: &FuncValue) -> EvalResult<TlcFuncOrder<'_>> {
        if Self::func_domain_is_tlc_safe(func) {
            return Ok(TlcFuncOrder::Stored);
        }

        if let Some(cached) = func.tlc_normalized_order() {
            return Ok(TlcFuncOrder::Permuted(cached));
        }

        let arc: Arc<[usize]> = Self::tlc_sort_func_domain_indices(func)?.into();
        Ok(TlcFuncOrder::Permuted(func.cache_tlc_normalized_order(arc)))
    }

    pub(super) fn tlc_model_value_type(name: &Arc<str>) -> Option<char> {
        // TLC: typed model values have the form "<type>_<rest>" with length > 2.
        // See ~/tlaplus/.../tlc2/value/impl/ModelValue.java.
        let s = name.as_ref();
        let mut chars = s.chars();
        let t0 = chars.next()?;
        let t1 = chars.next()?;
        if t1 == '_' && chars.next().is_some() {
            Some(t0)
        } else {
            None
        }
    }

    pub(super) fn tlc_is_special_model_set(name: &Arc<str>) -> bool {
        matches!(name.as_ref(), "Nat" | "Int" | "Real")
    }

    pub(super) fn tlc_cmp_err(message: impl Into<String>) -> EvalError {
        EvalError::Internal {
            message: message.into(),
            span: None,
        }
    }

    /// TLC's `ValueVec.sort(true)`: insertion-sort with binary-search + shifting insert, plus
    /// dedup.
    ///
    /// Parity-critical details:
    /// - Comparisons are directional: TLC calls `elem.compareTo(existing)` where `elem` is the
    ///   element being inserted into the sorted prefix.
    /// - Dedup is by `compareTo == 0`: when equal, the current `elem` is *not inserted* (the
    ///   earlier element is kept).
    /// - We intentionally avoid `Vec::sort_by(...)` (and friends) here: TLC `compareTo` is
    ///   direction-observable (e.g. `toTuple`/`toRcd`/`toFcnRcd` probes) and not guaranteed to
    ///   behave like a strict total order across all values, but standard sorts are free to call
    ///   the comparator in patterns TLC never does.
    ///
    /// Primary use: TLC-normalized set iteration (bounded `CHOOSE` parity).
    ///
    /// Reference: `~/tlaplus/tlatools/org.lamport.tlatools/src/tlc2/value/impl/ValueVec.java:167-194`.
    pub(super) fn tlc_sort_nodup(mut elems: Vec<Value>) -> EvalResult<Vec<Value>> {
        let mut sorted: Vec<Value> = Vec::with_capacity(elems.len());
        for elem in elems.drain(..) {
            let mut lo = 0usize;
            let mut hi = sorted.len();
            let mut dup = false;
            while lo < hi {
                let mid = (lo + hi) / 2;
                match Self::tlc_cmp(&elem, &sorted[mid])? {
                    Ordering::Less => hi = mid,
                    Ordering::Greater => lo = mid + 1,
                    Ordering::Equal => {
                        dup = true;
                        break;
                    }
                }
            }
            if !dup {
                sorted.insert(lo, elem);
            }
        }
        Ok(sorted)
    }

    /// TLC-style insertion sort for borrowed set elements.
    ///
    /// This preserves TLC's directional `compareTo` call pattern and error
    /// propagation while still avoiding cloning the underlying `Value`s.
    /// The sort remains O(n²) in pointer moves, but only shifts `&Value`
    /// handles instead of allocating and cloning full elements.
    ///
    /// Part of #3063, #3169: fingerprinting large sets should stay zero-clone
    /// without masking TLC compare failures as equality.
    pub(super) fn tlc_sort_refs_nodup<'a>(mut refs: Vec<&'a Value>) -> EvalResult<Vec<&'a Value>> {
        let mut sorted: Vec<&'a Value> = Vec::with_capacity(refs.len());
        for elem in refs.drain(..) {
            let mut lo = 0usize;
            let mut hi = sorted.len();
            let mut dup = false;
            while lo < hi {
                let mid = (lo + hi) / 2;
                match Self::tlc_cmp(elem, sorted[mid])? {
                    Ordering::Less => hi = mid,
                    Ordering::Greater => lo = mid + 1,
                    Ordering::Equal => {
                        dup = true;
                        break;
                    }
                }
            }
            if !dup {
                sorted.insert(lo, elem);
            }
        }
        Ok(sorted)
    }

    /// TLC-style insertion sort for function/record domains where duplicates are an error.
    ///
    /// TLC `FcnRcdValue.normalize()` fails if a domain element compares equal (`compareTo == 0`)
    /// to another element in the domain.
    pub(super) fn tlc_sort_unique(
        mut elems: Vec<Value>,
        context: &'static str,
    ) -> EvalResult<Vec<Value>> {
        let mut sorted: Vec<Value> = Vec::with_capacity(elems.len());
        for elem in elems.drain(..) {
            let mut lo = 0usize;
            let mut hi = sorted.len();
            while lo < hi {
                let mid = (lo + hi) / 2;
                match Self::tlc_cmp(&elem, &sorted[mid])? {
                    Ordering::Less => hi = mid,
                    Ordering::Greater => lo = mid + 1,
                    Ordering::Equal => {
                        return Err(Self::tlc_cmp_err(format!(
                            "The value {elem:?} occurs multiple times in {context}."
                        )));
                    }
                }
            }
            sorted.insert(lo, elem);
        }
        Ok(sorted)
    }

    /// Part of #2955: Zero-allocation tuple element access for the common case
    /// where both sides are Value::Tuple. Returns None for Seq, Func, etc.
    /// (those fall back to the allocating path via tlc_to_tuple).
    pub(super) fn tlc_as_tuple_slice(v: &Value) -> Option<&[Value]> {
        match v {
            Value::Tuple(t) => Some(t.as_ref()),
            _ => None,
        }
    }

    pub(super) fn tlc_to_tuple(v: &Value) -> EvalResult<Option<Vec<Value>>> {
        match v {
            Value::Tuple(t) => Ok(Some(t.as_ref().to_vec())),
            Value::Seq(s) => Ok(Some(s.to_vec())),
            Value::Func(_) | Value::IntFunc(_) => {
                let Some((dom, vals)) = Self::tlc_function_dom_vals(v)? else {
                    return Ok(None);
                };
                let n = vals.len();
                if dom.len() != n {
                    return Ok(None);
                }
                for (i, k) in dom.iter().enumerate() {
                    let expected = (i + 1) as i64;
                    if k.as_i64() != Some(expected) {
                        return Ok(None);
                    }
                }
                Ok(Some(vals))
            }
            _ => Ok(None),
        }
    }

    #[allow(clippy::type_complexity)]
    pub(super) fn tlc_to_record(v: &Value) -> EvalResult<Option<Vec<(Arc<str>, Value)>>> {
        match v {
            Value::Record(r) => Ok(Some(r.iter_str().map(|(k, vv)| (k, vv.clone())).collect())),
            Value::Func(f) => {
                let mut entries: Vec<(Arc<str>, Value)> = Vec::with_capacity(f.domain_len());
                for (k, vv) in f.mapping_iter() {
                    match k {
                        Value::String(s) => entries.push((Arc::clone(s), vv.clone())),
                        _ => return Ok(None),
                    }
                }
                entries.sort_by(|(a, _), (b, _)| a.cmp(b));
                Ok(Some(entries))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn tlc_function_dom_vals(v: &Value) -> EvalResult<Option<(Vec<Value>, Vec<Value>)>> {
        match v {
            Value::Tuple(t) => {
                let n = t.len();
                let domain: Vec<Value> = (1..=n as i64).map(Value::SmallInt).collect();
                Ok(Some((domain, t.as_ref().to_vec())))
            }
            Value::Seq(s) => {
                let n = s.len();
                let domain: Vec<Value> = (1..=n as i64).map(Value::SmallInt).collect();
                Ok(Some((domain, s.to_vec())))
            }
            Value::Record(r) => {
                let mut domain: Vec<Value> = Vec::with_capacity(r.len());
                let mut values: Vec<Value> = Vec::with_capacity(r.len());
                for (k, vv) in r.iter() {
                    domain.push(Value::string(tla_core::resolve_name_id(k)));
                    values.push(vv.clone());
                }
                domain = Self::tlc_sort_unique(domain, "record domain")?;
                let mut ordered_values: Vec<Value> = Vec::with_capacity(domain.len());
                for key in &domain {
                    let Value::String(field) = key else {
                        return Err(Self::tlc_cmp_err(
                            "Record domain normalization produced non-string key",
                        ));
                    };
                    let val = r
                        .get(field.as_ref())
                        .ok_or_else(|| Self::tlc_cmp_err("Record domain/mapping mismatch"))?;
                    ordered_values.push(val.clone());
                }
                Ok(Some((domain, ordered_values)))
            }
            Value::IntFunc(f) => {
                let domain: Vec<Value> = (f.min..=f.max).map(Value::SmallInt).collect();
                Ok(Some((domain, f.values.as_ref().clone())))
            }
            Value::Func(f) => {
                let mut domain: Vec<Value> = Vec::with_capacity(f.domain_len());
                let mut values: Vec<Value> = Vec::with_capacity(f.domain_len());
                match Self::func_tlc_order(f)? {
                    TlcFuncOrder::Stored => {
                        for (key, value) in f.iter() {
                            domain.push(key.clone());
                            values.push(value.clone());
                        }
                    }
                    TlcFuncOrder::Permuted(order) => {
                        for &idx in order {
                            domain.push(f.key_at(idx).clone());
                            values.push(f.value_at(idx).clone());
                        }
                    }
                }
                Ok(Some((domain, values)))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn tlc_set_elems(v: &Value) -> EvalResult<Option<Vec<Value>>> {
        if !v.is_set() {
            return Ok(None);
        }
        let iter = v.iter_set().ok_or(EvalError::SetTooLarge { span: None })?;
        Ok(Some(Self::tlc_sort_nodup(iter.collect())?))
    }
}
