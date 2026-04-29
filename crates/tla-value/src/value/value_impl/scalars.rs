// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `impl Value` scalar extractors and error-facing type names.

use super::super::*;

impl Value {
    /// Arc pointer equality: returns true if two Values share the same Arc
    /// allocation, implying value equality without deep comparison.
    ///
    /// For UNCHANGED evaluation in BFS, when a variable is not modified by an
    /// action, the primed and unprimed values share the same Arc pointer.
    /// This check is O(1) regardless of value size (functions, sequences,
    /// records, sets can be arbitrarily large).
    ///
    /// Returns false for scalar types (Bool, SmallInt) since they are cheap
    /// to compare directly and are not Arc-wrapped.
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::String(a), Value::String(b)) => Arc::ptr_eq(a, b),
            (Value::Int(a), Value::Int(b)) => Arc::ptr_eq(a, b),
            (Value::Set(a), Value::Set(b)) => Arc::ptr_eq(a, b),
            (Value::Interval(a), Value::Interval(b)) => Arc::ptr_eq(a, b),
            (Value::Func(a), Value::Func(b)) => Arc::ptr_eq(a, b),
            (Value::IntFunc(a), Value::IntFunc(b)) => Arc::ptr_eq(a, b),
            (Value::LazyFunc(a), Value::LazyFunc(b)) => Arc::ptr_eq(a, b),
            (Value::Seq(a), Value::Seq(b)) => Arc::ptr_eq(a, b),
            (Value::Record(a), Value::Record(b)) => a.ptr_eq(b),
            (Value::Tuple(a), Value::Tuple(b)) => Arc::ptr_eq(a, b),
            (Value::Closure(a), Value::Closure(b)) => Arc::ptr_eq(a, b),
            (Value::ModelValue(a), Value::ModelValue(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }

    #[inline]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Returns the integer value as i64 if it fits.
    /// Fast path for SmallInt, conversion for BigInt.
    #[inline]
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Value::SmallInt(n) => Some(*n),
            Value::Int(n) => n.to_i64(),
            _ => None,
        }
    }

    /// Returns true if this value is an integer (SmallInt or BigInt).
    pub fn is_int(&self) -> bool {
        matches!(self, Value::SmallInt(_) | Value::Int(_))
    }

    /// Converts the integer to BigInt (owned).
    /// Returns None if not an integer type.
    pub fn to_bigint(&self) -> Option<BigInt> {
        match self {
            Value::SmallInt(n) => Some(BigInt::from(*n)),
            Value::Int(n) => Some((**n).clone()),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&str> {
        match self {
            Value::String(s) => Some(s),
            _ => None,
        }
    }

    // === Type name for error messages ===

    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Bool(_) => "BOOLEAN",
            Value::SmallInt(_) | Value::Int(_) => "Int",
            Value::String(_) => "STRING",
            Value::Set(_)
            | Value::Interval(_)
            | Value::Subset(_)
            | Value::FuncSet(_)
            | Value::RecordSet(_)
            | Value::TupleSet(_)
            | Value::SetCup(_)
            | Value::SetCap(_)
            | Value::SetDiff(_)
            | Value::SetPred(_)
            | Value::KSubset(_)
            | Value::BigUnion(_)
            | Value::StringSet
            | Value::AnySet
            | Value::SeqSet(_) => "Set",
            Value::Func(_) | Value::IntFunc(_) | Value::LazyFunc(_) => "Function",
            Value::Seq(_) => "Seq",
            Value::Record(_) => "Record",
            Value::Tuple(_) => "Tuple",
            Value::ModelValue(_) => "ModelValue",
            Value::Closure(_) => "Closure",
        }
    }

    /// Extract closure value
    pub fn as_closure(&self) -> Option<&ClosureValue> {
        match self {
            Value::Closure(c) => Some(c),
            _ => None,
        }
    }
}
