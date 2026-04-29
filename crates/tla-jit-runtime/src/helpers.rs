// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared Value <-> JIT i64 helpers.
//!
//! These helpers convert between `tla_value::Value` scalar forms and the
//! raw i64 register representation used by JIT-compiled code. They live in
//! `tla-jit-runtime` so that both the Cranelift backend (`tla-jit`) and the
//! model checker (`tla-check`) can call them without depending on the
//! Cranelift pipeline.
//!
//! Part of #4267 Wave 11e (epic #4251 Stage 2d): migrate shared Value-shape
//! helpers out of `tla-jit` into the surviving `tla-jit-runtime` crate so
//! `tla-check` can drop its remaining `tla_jit::*` references.

use num_traits::ToPrimitive;
use tla_jit_abi::SpecType;
use tla_value::Value;

/// Convert a scalar `Value` to its JIT i64 register representation.
///
/// Mirrors the JIT `LoadConst` semantics:
/// - `SmallInt(n)` -> `Some(n)`
/// - `Int(n)` -> `n.to_i64()` (if it fits in i64)
/// - `Bool(b)` -> `Some(1)` / `Some(0)`
/// - `String(s)` / `ModelValue(s)` -> interned NameId as i64
///
/// Returns `None` for compound types (sets, sequences, records, functions,
/// tuples) that cannot be represented as a single i64 register value.
///
/// Part of #3984 / #4267 Wave 11e: moved from `tla-jit::bytecode_lower`.
#[must_use]
pub fn value_to_jit_i64(value: &Value) -> Option<i64> {
    match value {
        Value::SmallInt(n) => Some(*n),
        Value::Int(n) => n.to_i64(),
        Value::Bool(b) => Some(i64::from(*b)),
        Value::String(s) => {
            let name_id = tla_core::intern_name(s);
            Some(i64::from(name_id.0))
        }
        Value::ModelValue(s) => {
            let name_id = tla_core::intern_name(s);
            Some(i64::from(name_id.0))
        }
        _ => None,
    }
}

/// Convert a slice of `(name, Value)` bindings to their JIT i64 representations.
///
/// Returns `Some(Vec<i64>)` if ALL binding values can be converted to i64.
/// Returns `None` if ANY binding value is a compound type that cannot be
/// specialized.
///
/// Part of #3984 / #4267 Wave 11e: moved from `tla-jit::bytecode_lower`.
#[must_use]
pub fn bindings_to_jit_i64(bindings: &[(std::sync::Arc<str>, Value)]) -> Option<Vec<i64>> {
    bindings
        .iter()
        .map(|(_, val)| value_to_jit_i64(val))
        .collect()
}

/// Classify a concrete runtime value into a specialization-friendly type.
///
/// Used by the tiered JIT pipeline to decide whether a monomorphic
/// specialization is safe. Lives here (not in `tla-jit`) so `tla-check`
/// can sample values without depending on the Cranelift stack.
///
/// Part of #3850 / #4267 Wave 11e: moved from `tla-jit::type_profile`.
#[must_use]
pub fn classify_value(value: &Value) -> SpecType {
    match value {
        Value::SmallInt(_) => SpecType::Int,
        Value::Bool(_) => SpecType::Bool,
        Value::String(_) => SpecType::String,
        Value::Set(_) => SpecType::FiniteSet,
        Value::Record(_) => SpecType::Record,
        Value::Seq(_) => SpecType::Seq,
        Value::Func(_) | Value::IntFunc(_) => SpecType::Func,
        Value::Tuple(_) => SpecType::Tuple,
        _ => SpecType::Other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn test_value_to_jit_i64_small_int() {
        assert_eq!(value_to_jit_i64(&Value::SmallInt(42)), Some(42));
        assert_eq!(value_to_jit_i64(&Value::SmallInt(-1)), Some(-1));
    }

    #[test]
    fn test_value_to_jit_i64_bool() {
        assert_eq!(value_to_jit_i64(&Value::Bool(true)), Some(1));
        assert_eq!(value_to_jit_i64(&Value::Bool(false)), Some(0));
    }

    #[test]
    fn test_value_to_jit_i64_compound_returns_none() {
        let seq = Value::seq([Value::SmallInt(1), Value::SmallInt(2)]);
        assert_eq!(value_to_jit_i64(&seq), None);
    }

    #[test]
    fn test_value_to_jit_i64_big_int_overflow() {
        // Value that overflows i64.
        let huge: BigInt = BigInt::from(i64::MAX) * BigInt::from(2i64);
        assert_eq!(value_to_jit_i64(&Value::Int(huge.into())), None);
    }

    #[test]
    fn test_bindings_to_jit_i64_empty() {
        let bindings: Vec<(std::sync::Arc<str>, Value)> = vec![];
        assert_eq!(bindings_to_jit_i64(&bindings), Some(vec![]));
    }

    #[test]
    fn test_bindings_to_jit_i64_all_scalar() {
        let bindings: Vec<(std::sync::Arc<str>, Value)> = vec![
            (std::sync::Arc::from("i"), Value::SmallInt(3)),
            (std::sync::Arc::from("b"), Value::Bool(true)),
        ];
        assert_eq!(bindings_to_jit_i64(&bindings), Some(vec![3, 1]));
    }

    #[test]
    fn test_bindings_to_jit_i64_compound_returns_none() {
        let bindings: Vec<(std::sync::Arc<str>, Value)> = vec![
            (std::sync::Arc::from("i"), Value::SmallInt(3)),
            (std::sync::Arc::from("s"), Value::seq([Value::SmallInt(1)])),
        ];
        assert_eq!(bindings_to_jit_i64(&bindings), None);
    }

    #[test]
    fn test_classify_value_scalars() {
        assert_eq!(classify_value(&Value::SmallInt(1)), SpecType::Int);
        assert_eq!(classify_value(&Value::Bool(true)), SpecType::Bool);
        assert_eq!(classify_value(&Value::string("hi")), SpecType::String);
    }

    #[test]
    fn test_classify_value_compounds() {
        assert_eq!(
            classify_value(&Value::set([Value::SmallInt(1)])),
            SpecType::FiniteSet
        );
        assert_eq!(
            classify_value(&Value::seq([Value::SmallInt(1)])),
            SpecType::Seq
        );
        assert_eq!(
            classify_value(&Value::record([("a", Value::SmallInt(1))])),
            SpecType::Record
        );
        assert_eq!(
            classify_value(&Value::tuple([Value::SmallInt(1)])),
            SpecType::Tuple
        );
    }
}
