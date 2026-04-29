// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla_record_get` / `tla_func_apply` / `tla_domain` — handle-based FFI for
//! record field access, function application, and `DOMAIN`.
//!
//! These three helpers extend the R27 Option B runtime surface to cover the
//! record/function family of aggregate opcodes. Each helper takes operand
//! handles as raw `i64`, unboxes via [`handle_to_value`], dispatches to
//! `tla_value::Value` accessors, and reboxes the result via
//! [`handle_from_value`].
//!
//! | Helper | Signature | Semantics |
//! |--------|-----------|-----------|
//! | `tla_record_get` | `i64 (i64 rec, i64 field_idx)` | `rec.field` — `field_idx` is a raw [`NameId`] scalar, not a handle |
//! | `tla_func_apply` | `i64 (i64 f, i64 arg)` | `f[arg]` — `arg` is a handle |
//! | `tla_domain`     | `i64 (i64 f)` | `DOMAIN f` |
//!
//! # Soundness contract
//!
//! Following the [`super::set`] module convention, helpers that cannot
//! compute their result (non-record field access, `f[arg]` on a non-callable
//! operand, `DOMAIN` of a non-function value, or out-of-domain arguments)
//! return [`NIL_HANDLE`]. `tir_lower` must emit a guard that falls back to
//! the interpreter on NIL so the FFI surface stays panic-free without
//! silently returning incorrect results.
//!
//! # Why `field_idx` is a raw scalar
//!
//! TIR lowers `rec.field` with the field's interned [`NameId`] baked in at
//! compile time. Passing the id as a raw i64 (same treatment as `lo`/`hi`
//! in `tla_set_range`) avoids a round-trip through the arena for a value
//! that is already a constant at the emit site. The upper 32 bits of the
//! i64 are ignored; callers pass the u32 NameId zero-extended.
//!
//! Part of #4318. R27 design doc:
//! `designs/2026-04-20-llvm2-runtime-abi-scope.md` §2.4.

use num_bigint::BigInt;
use num_traits::One;
use tla_core::NameId;
use tla_value::value::{range_set, ComponentDomain, IntIntervalFunc, LazyDomain, SortedSet, Value};

use super::handle::{handle_from_value, handle_to_value, TlaHandle, NIL_HANDLE};

// ============================================================================
// tla_record_get — rec.field (NameId fast path)
// ============================================================================

/// `rec.field` — look up a field by interned [`NameId`].
///
/// `field_idx` is a raw `i64` whose low 32 bits decode to a [`NameId`]. The
/// upper bits are ignored; `tir_lower` must zero-extend the u32 name id it
/// holds at the emit site.
///
/// Returns a handle to the field value, or [`NIL_HANDLE`] if:
/// - `rec` is not a [`Value::Record`].
/// - The field name is not present in the record.
///
/// tir_lower falls back to the interpreter on NIL.
#[no_mangle]
pub extern "C" fn tla_record_get(rec: TlaHandle, field_idx: i64) -> TlaHandle {
    let rec_v = handle_to_value(rec);
    let Value::Record(r) = &rec_v else {
        return NIL_HANDLE;
    };
    // Truncate to u32 — NameId wraps a u32 so masking matches the encoding
    // used by `handle_from_state_slot` / `handle::encode_string`.
    let id = NameId((field_idx & 0xFFFF_FFFF) as u32);
    match r.get_by_id(id) {
        Some(v) => handle_from_value(v),
        None => NIL_HANDLE,
    }
}

// ============================================================================
// tla_func_apply — f[arg]
// ============================================================================

/// `f[arg]` — apply a function-like value to an argument handle.
///
/// Supports every eager function-like variant the interpreter applies in
/// `helpers::function_values::apply::try_apply_func_value_eager_*`:
/// [`Value::Func`], [`Value::IntFunc`], [`Value::Seq`], [`Value::Tuple`],
/// and [`Value::Record`] (records are functions keyed by field name).
///
/// Returns [`NIL_HANDLE`] on:
/// - Non-function operand (e.g. an `Int`).
/// - [`Value::LazyFunc`] — lazy application needs an evaluation context,
///   so tir_lower must fall back to the interpreter.
/// - Argument out of domain / out of bounds / missing field / wrong type
///   (e.g. a non-integer arg to a sequence).
#[no_mangle]
pub extern "C" fn tla_func_apply(f: TlaHandle, arg: TlaHandle) -> TlaHandle {
    let fv = handle_to_value(f);
    let arg_v = handle_to_value(arg);
    match value_apply(&fv, &arg_v) {
        Some(v) => handle_from_value(&v),
        None => NIL_HANDLE,
    }
}

/// Apply a function-like value to an argument. Mirrors the eager dispatch
/// in `tla-eval::helpers::function_values::apply::try_apply_func_value_eager_owned`.
///
/// Returns `None` if the value is not applicable in the eager path (e.g.
/// `LazyFunc`) or the application is not well-defined (out-of-domain,
/// out-of-bounds, wrong argument type).
fn value_apply(fv: &Value, arg: &Value) -> Option<Value> {
    match fv {
        Value::Func(f) => f.apply(arg).cloned(),
        Value::IntFunc(f) => f.apply(arg).cloned(),
        Value::Seq(s) => {
            let idx = arg.as_i64()?;
            if idx < 1 || (idx as usize) > s.len() {
                return None;
            }
            s.get((idx - 1) as usize).cloned()
        }
        Value::Tuple(t) => {
            let idx = arg.as_i64()?;
            if idx < 1 || (idx as usize) > t.len() {
                return None;
            }
            t.get((idx - 1) as usize).cloned()
        }
        Value::Record(r) => {
            let field = arg.as_string()?;
            r.get(field).cloned()
        }
        _ => None,
    }
}

// ============================================================================
// tla_domain — DOMAIN f
// ============================================================================

/// `DOMAIN f` — return the domain of a function-like value.
///
/// Mirrors `tla-eval::eval_constructors::eval_domain_value`:
/// - [`Value::Func`] → the sorted set of domain keys.
/// - [`Value::IntFunc`] → the integer interval `min..max`.
/// - [`Value::Seq`] / [`Value::Tuple`] → `1..len` (empty set if empty).
/// - [`Value::Record`] → set of field names (as `Value::String`s).
/// - [`Value::LazyFunc`] → the set-representation of the stored
///   [`LazyDomain`].
///
/// Returns [`NIL_HANDLE`] for any other variant — tir_lower falls back to
/// the interpreter when the FFI cannot compute the domain purely from the
/// value (e.g. `DOMAIN` of a non-function or of an exotic lazy domain that
/// the FFI does not yet model).
#[no_mangle]
pub extern "C" fn tla_domain(f: TlaHandle) -> TlaHandle {
    let fv = handle_to_value(f);
    match value_domain(&fv) {
        Some(v) => handle_from_value(&v),
        None => NIL_HANDLE,
    }
}

/// Compute `DOMAIN fv`. Returns `None` on unsupported variants so the FFI
/// can fall through to a NIL sentinel.
fn value_domain(fv: &Value) -> Option<Value> {
    match fv {
        Value::Func(f) => {
            let keys: Vec<Value> = f.domain_iter().cloned().collect();
            Some(Value::from_sorted_set(SortedSet::from_sorted_vec(keys)))
        }
        Value::IntFunc(f) => {
            let lo = BigInt::from(IntIntervalFunc::min(f));
            let hi = BigInt::from(IntIntervalFunc::max(f));
            Some(range_set(&lo, &hi))
        }
        Value::Seq(s) => {
            if s.is_empty() {
                Some(Value::empty_set())
            } else {
                Some(range_set(&BigInt::one(), &BigInt::from(s.len())))
            }
        }
        Value::Tuple(t) => {
            if t.is_empty() {
                Some(Value::empty_set())
            } else {
                Some(range_set(&BigInt::one(), &BigInt::from(t.len())))
            }
        }
        Value::Record(r) => {
            let names: SortedSet = r.key_strings().map(Value::String).collect();
            Some(Value::from_sorted_set(names))
        }
        Value::LazyFunc(lf) => lazy_domain_as_value(lf.domain()),
        _ => None,
    }
}

/// Convert a [`LazyDomain`] into a concrete `Value` set representation.
/// Returns `None` for domains the FFI does not materialise (currently
/// always `Some` — kept fallible so future variants can bail to NIL).
fn lazy_domain_as_value(d: &LazyDomain) -> Option<Value> {
    match d {
        LazyDomain::Nat => Some(Value::ModelValue(std::sync::Arc::from("Nat"))),
        LazyDomain::Int => Some(Value::ModelValue(std::sync::Arc::from("Int"))),
        LazyDomain::Real => Some(Value::ModelValue(std::sync::Arc::from("Real"))),
        LazyDomain::String => Some(Value::StringSet),
        LazyDomain::Product(components) => {
            let sets: Vec<Value> = components.iter().map(component_domain_as_value).collect();
            Some(Value::tuple_set(sets))
        }
        LazyDomain::General(v) => Some(v.as_ref().clone()),
    }
}

fn component_domain_as_value(c: &ComponentDomain) -> Value {
    match c {
        ComponentDomain::Nat => Value::ModelValue(std::sync::Arc::from("Nat")),
        ComponentDomain::Int => Value::ModelValue(std::sync::Arc::from("Int")),
        ComponentDomain::Real => Value::ModelValue(std::sync::Arc::from("Real")),
        ComponentDomain::String => Value::StringSet,
        ComponentDomain::Finite(s) => Value::from_sorted_set(s.clone()),
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::super::handle::clear_tla_arena;
    use super::*;
    use std::sync::Arc;
    use tla_core::intern_name;
    use tla_value::value::{FuncBuilder, RecordValue, SeqValue};

    fn small_int_set(xs: &[i64]) -> Value {
        Value::set(xs.iter().copied().map(Value::SmallInt).collect::<Vec<_>>())
    }

    fn func_from_pairs(pairs: Vec<(Value, Value)>) -> Value {
        let mut b = FuncBuilder::new();
        for (k, v) in pairs {
            b.insert(k, v);
        }
        Value::Func(Arc::new(b.build()))
    }

    fn record_ab() -> Value {
        Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::SmallInt(1)),
            (Arc::from("b"), Value::Bool(true)),
        ]))
    }

    #[test]
    fn record_get_existing_field_matches_interpreter() {
        clear_tla_arena();
        let h = handle_from_value(&record_ab());
        let a_id = intern_name("a").0 as i64;
        let b_id = intern_name("b").0 as i64;
        assert_eq!(handle_to_value(tla_record_get(h, a_id)), Value::SmallInt(1));
        assert_eq!(handle_to_value(tla_record_get(h, b_id)), Value::Bool(true));
    }

    #[test]
    fn record_get_missing_field_returns_nil() {
        clear_tla_arena();
        let h = handle_from_value(&record_ab());
        let missing = intern_name("not_a_field").0 as i64;
        assert_eq!(tla_record_get(h, missing), NIL_HANDLE);
    }

    #[test]
    fn record_get_on_non_record_returns_nil() {
        clear_tla_arena();
        let not_a_record = handle_from_value(&Value::SmallInt(42));
        let id = intern_name("a").0 as i64;
        assert_eq!(tla_record_get(not_a_record, id), NIL_HANDLE);
    }

    #[test]
    fn func_apply_on_func_matches_interpreter() {
        clear_tla_arena();
        let f = func_from_pairs(vec![
            (Value::SmallInt(1), Value::SmallInt(10)),
            (Value::SmallInt(2), Value::SmallInt(20)),
            (Value::SmallInt(3), Value::SmallInt(30)),
        ]);
        let fh = handle_from_value(&f);
        for (k, want) in [(1, 10), (2, 20), (3, 30)] {
            let arg = handle_from_value(&Value::SmallInt(k));
            let r = tla_func_apply(fh, arg);
            assert_eq!(handle_to_value(r), Value::SmallInt(want));
        }
    }

    #[test]
    fn func_apply_out_of_domain_returns_nil() {
        clear_tla_arena();
        let f = func_from_pairs(vec![(Value::SmallInt(1), Value::SmallInt(10))]);
        let fh = handle_from_value(&f);
        let arg = handle_from_value(&Value::SmallInt(99));
        assert_eq!(tla_func_apply(fh, arg), NIL_HANDLE);
    }

    #[test]
    fn func_apply_on_seq_uses_one_based_indexing() {
        clear_tla_arena();
        let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![
            Value::SmallInt(100),
            Value::SmallInt(200),
            Value::SmallInt(300),
        ])));
        let sh = handle_from_value(&seq);
        for (idx, want) in [(1, 100), (2, 200), (3, 300)] {
            let arg = handle_from_value(&Value::SmallInt(idx));
            let r = tla_func_apply(sh, arg);
            assert_eq!(handle_to_value(r), Value::SmallInt(want));
        }
        // Out of bounds
        let zero = handle_from_value(&Value::SmallInt(0));
        assert_eq!(tla_func_apply(sh, zero), NIL_HANDLE);
        let past = handle_from_value(&Value::SmallInt(4));
        assert_eq!(tla_func_apply(sh, past), NIL_HANDLE);
    }

    #[test]
    fn func_apply_on_tuple_uses_one_based_indexing() {
        clear_tla_arena();
        let tup: Arc<[Value]> = Arc::from(vec![Value::SmallInt(7), Value::SmallInt(8)]);
        let th = handle_from_value(&Value::Tuple(tup));
        let one = handle_from_value(&Value::SmallInt(1));
        assert_eq!(handle_to_value(tla_func_apply(th, one)), Value::SmallInt(7));
        let two = handle_from_value(&Value::SmallInt(2));
        assert_eq!(handle_to_value(tla_func_apply(th, two)), Value::SmallInt(8));
    }

    #[test]
    fn func_apply_on_record_with_string_arg() {
        clear_tla_arena();
        let rh = handle_from_value(&record_ab());
        let key = handle_from_value(&Value::String(Arc::from("a")));
        assert_eq!(handle_to_value(tla_func_apply(rh, key)), Value::SmallInt(1));
    }

    #[test]
    fn func_apply_on_non_function_returns_nil() {
        clear_tla_arena();
        let not_callable = handle_from_value(&Value::SmallInt(5));
        let arg = handle_from_value(&Value::SmallInt(1));
        assert_eq!(tla_func_apply(not_callable, arg), NIL_HANDLE);
    }

    #[test]
    fn domain_of_func_is_sorted_domain_set() {
        clear_tla_arena();
        let f = func_from_pairs(vec![
            (Value::SmallInt(3), Value::SmallInt(30)),
            (Value::SmallInt(1), Value::SmallInt(10)),
            (Value::SmallInt(2), Value::SmallInt(20)),
        ]);
        let fh = handle_from_value(&f);
        let d = tla_domain(fh);
        assert_eq!(handle_to_value(d), small_int_set(&[1, 2, 3]));
    }

    #[test]
    fn domain_of_seq_is_one_through_len() {
        clear_tla_arena();
        let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
            Value::SmallInt(40),
        ])));
        let sh = handle_from_value(&seq);
        let d = tla_domain(sh);
        let v = handle_to_value(d);
        let sorted = v.to_sorted_set().expect("domain is enumerable");
        let vals: Vec<i64> = sorted.iter().filter_map(|x| x.as_i64()).collect();
        assert_eq!(vals, vec![1, 2, 3, 4]);
    }

    #[test]
    fn domain_of_empty_seq_is_empty_set() {
        clear_tla_arena();
        let seq = Value::Seq(Arc::new(SeqValue::from_vec(vec![])));
        let sh = handle_from_value(&seq);
        let d = tla_domain(sh);
        assert_eq!(handle_to_value(d), Value::empty_set());
    }

    #[test]
    fn domain_of_tuple_is_one_through_len() {
        clear_tla_arena();
        let tup: Arc<[Value]> = Arc::from(vec![
            Value::Bool(true),
            Value::SmallInt(2),
            Value::String(Arc::from("x")),
        ]);
        let th = handle_from_value(&Value::Tuple(tup));
        let d = tla_domain(th);
        let v = handle_to_value(d);
        let sorted = v.to_sorted_set().expect("domain is enumerable");
        assert_eq!(sorted.len(), 3);
    }

    #[test]
    fn domain_of_record_is_set_of_field_names() {
        clear_tla_arena();
        let rh = handle_from_value(&record_ab());
        let d = tla_domain(rh);
        let v = handle_to_value(d);
        let sorted = v.to_sorted_set().expect("record domain is enumerable");
        let names: Vec<String> = sorted
            .iter()
            .filter_map(|x| x.as_string().map(|s| s.to_string()))
            .collect();
        assert_eq!(names, vec!["a".to_string(), "b".to_string()]);
    }

    #[test]
    fn domain_of_non_function_returns_nil() {
        clear_tla_arena();
        let not_a_fn = handle_from_value(&Value::SmallInt(42));
        assert_eq!(tla_domain(not_a_fn), NIL_HANDLE);
    }

    #[test]
    fn apply_then_domain_round_trip_on_func() {
        // Property: for every d in DOMAIN f, f[d] must succeed.
        clear_tla_arena();
        let f = func_from_pairs(vec![
            (Value::SmallInt(10), Value::SmallInt(100)),
            (Value::SmallInt(20), Value::SmallInt(200)),
        ]);
        let fh = handle_from_value(&f);
        let d = tla_domain(fh);
        let sorted = handle_to_value(d)
            .to_sorted_set()
            .expect("domain of Func is a set");
        for key in sorted.iter() {
            let arg = handle_from_value(key);
            let r = tla_func_apply(fh, arg);
            assert_ne!(r, NIL_HANDLE, "f[{key:?}] should be defined");
        }
    }
}
