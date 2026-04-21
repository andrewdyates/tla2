// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `impl Value` tuple/sequence/function coercions.

use super::super::*;

impl Value {
    /// Extract elements from a Seq or Tuple.
    /// Both Seq and Tuple are indexed collections in TLA+.
    /// Returns Cow::Borrowed for Tuple (which uses Arc<[Value]>)
    /// and Cow::Owned for Seq (which uses im::Vector).
    #[inline]
    pub fn as_seq_or_tuple_elements(&self) -> Option<Cow<'_, [Value]>> {
        match self {
            Value::Seq(s) => Some(Cow::Owned(s.to_vec())),
            Value::Tuple(t) => Some(Cow::Borrowed(t.as_ref())),
            _ => None,
        }
    }

    /// Extract elements from a tuple-like value for tuple-pattern destructuring.
    ///
    /// TLC-parity: TLC's `toTuple()` converts sequence-like functions (domain 1..n)
    /// into tuples. This method implements the same coercion for:
    /// - `Value::Tuple` - direct extraction
    /// - `Value::Seq` - convert to slice
    /// - `Value::IntFunc` with min=1 - sequence-like function
    /// - `Value::Func` with keys exactly 1..n - sequence-like function
    ///
    /// Used by tuple-pattern binding in eval.rs and liveness/ast_to_live.rs.
    /// See `designs/2026-01-31-tuple-pattern-binding-toTuple-coercions.md`.
    pub fn to_tuple_like_elements(&self) -> Option<Cow<'_, [Value]>> {
        match self {
            Value::Tuple(t) => Some(Cow::Borrowed(t.as_ref())),
            Value::Seq(s) => Some(Cow::Owned(s.to_vec())),
            Value::IntFunc(f) if f.min == 1 => {
                // IntFunc with domain 1..n is sequence-like
                Some(Cow::Owned(f.values.to_vec()))
            }
            Value::Func(f) => {
                if f.domain_is_empty() {
                    return Some(Cow::Owned(vec![]));
                }
                if !f.domain_is_sequence() {
                    return None;
                }
                Some(Cow::Owned(f.mapping_values().cloned().collect()))
            }
            _ => None,
        }
    }

    /// Extract the SeqValue from a Seq
    #[inline]
    pub fn as_seq_value(&self) -> Option<&SeqValue> {
        match self {
            Value::Seq(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_func(&self) -> Option<&FuncValue> {
        match self {
            Value::Func(f) => Some(f),
            _ => None,
        }
    }

    /// Coerce function-like values (Func, Tuple, Seq, IntFunc, Record) to FuncValue.
    /// This is used for operations that accept any function-like type (e.g., Bags).
    /// Returns None for non-function-like types.
    pub fn to_func_coerced(&self) -> Option<FuncValue> {
        match self {
            Value::Func(f) => Some((**f).clone()),
            Value::IntFunc(f) => Some(f.to_func_value()),
            Value::Tuple(elems) => {
                // Convert to function with domain 1..n
                let entries: Vec<(Value, Value)> = elems
                    .iter()
                    .enumerate()
                    .map(|(i, v)| (Value::SmallInt((i + 1) as i64), v.clone()))
                    .collect();
                Some(FuncValue::from_sorted_entries(entries))
            }
            Value::Seq(seq) => {
                // Convert to function with domain 1..n
                let entries: Vec<(Value, Value)> = seq
                    .iter()
                    .enumerate()
                    .map(|(i, v)| (Value::SmallInt((i + 1) as i64), v.clone()))
                    .collect();
                Some(FuncValue::from_sorted_entries(entries))
            }
            Value::Record(rec) => {
                // Convert to function with string domain (resolve NameId to string)
                let mut entries: Vec<(Value, Value)> = rec
                    .iter()
                    .map(|(k, v)| (Value::string(tla_core::resolve_name_id(k)), v.clone()))
                    .collect();
                entries.sort_by(|a, b| a.0.cmp(&b.0));
                Some(FuncValue::from_sorted_entries(entries))
            }
            _ => None,
        }
    }

    pub fn as_seq(&self) -> Option<Cow<'_, [Value]>> {
        // In TLA+, sequences and tuples share the same <<...>> syntax
        // and sequence operations work on both.
        // Also accept Func/IntFunc — the SET_INTERN_TABLE can substitute
        // semantically-equal variants (e.g., Seq([]) ↔ Func([])) (#1713)
        self.as_seq_or_tuple_elements()
            .or_else(|| self.to_tuple_like_elements())
    }

    pub fn as_record(&self) -> Option<&RecordValue> {
        match self {
            Value::Record(r) => Some(r),
            _ => None,
        }
    }

    pub fn as_tuple(&self) -> Option<&Arc<[Value]>> {
        match self {
            Value::Tuple(t) => Some(t),
            _ => None,
        }
    }
}
