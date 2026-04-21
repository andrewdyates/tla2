// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Backward-compat re-exports for compound-layout serialization.
//!
//! As of #4267 Wave 11d, the canonical definitions for:
//!
//! - `CompoundLayout`, `StateLayout`, `VarLayout`, `TAG_*` constants — layout descriptors
//! - `serialize_value`, `deserialize_value`, `infer_layout`, `infer_var_layout` — Value ↔ flat i64 conversion
//!
//! all live in `tla_jit_abi` (the leaf crate). This module now re-exports them
//! so existing callers that import `tla_jit_runtime::compound_layout::*` (or the
//! flat `tla_jit_runtime::*` surface) continue to resolve unchanged. Stage 2d
//! (#4267) removes this crate entirely; the canonical types survive in
//! `tla-jit-abi`.
//!
//! Part of #3848, #4267.

pub use tla_jit_abi::compound_runtime::{
    deserialize_value, infer_layout, infer_var_layout, serialize_value,
};
pub use tla_jit_abi::layout::{
    CompoundLayout, StateLayout, VarLayout, TAG_BOOL, TAG_FUNC, TAG_INT, TAG_RECORD, TAG_SEQ,
    TAG_SET, TAG_STRING, TAG_TUPLE,
};

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use tla_value::value::{FuncValue, RecordValue, SeqValue, SortedSet, Value};

    // ========================================================================
    // Scalar round-trips (smoke tests; deeper coverage lives in
    // `tla_jit_abi::compound_runtime::tests`)
    // ========================================================================

    #[test]
    fn test_roundtrip_bool_true() {
        let val = Value::Bool(true);
        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize bool");
        assert_eq!(written, 2);
        assert_eq!(buf, vec![TAG_BOOL, 1]);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize bool");
        assert_eq!(consumed, 2);
        assert_eq!(deserialized, Value::Bool(true));
    }

    #[test]
    fn test_roundtrip_int() {
        let val = Value::SmallInt(42);
        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize int");
        assert_eq!(written, 2);
        assert_eq!(buf, vec![TAG_INT, 42]);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize int");
        assert_eq!(consumed, 2);
        assert_eq!(deserialized, Value::SmallInt(42));
    }

    #[test]
    fn test_roundtrip_record() {
        let rec = RecordValue::from_sorted_str_entries(vec![
            (Arc::from("a"), Value::SmallInt(1)),
            (Arc::from("b"), Value::Bool(true)),
        ]);
        let val = Value::Record(rec);

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize record");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_RECORD);
        assert_eq!(buf[1], 2);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize record");
        assert_eq!(consumed, written);
        match &deserialized {
            Value::Record(rec) => assert_eq!(rec.len(), 2),
            other => panic!("expected Record, got {other:?}"),
        }
    }

    #[test]
    fn test_roundtrip_sequence() {
        let seq = SeqValue::from_vec(vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ]);
        let val = Value::Seq(Arc::new(seq));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize seq");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_SEQ);
        assert_eq!(buf[1], 3);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize seq");
        assert_eq!(consumed, written);
        match &deserialized {
            Value::Seq(seq) => {
                assert_eq!(seq.len(), 3);
                assert_eq!(*seq.get(0).expect("elem 0"), Value::SmallInt(10));
                assert_eq!(*seq.get(2).expect("elem 2"), Value::SmallInt(30));
            }
            other => panic!("expected Seq, got {other:?}"),
        }
    }

    #[test]
    fn test_roundtrip_set() {
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let val = Value::Set(Arc::new(set));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize set");
        assert!(written > 0);
        assert_eq!(buf[0], TAG_SET);
        assert_eq!(buf[1], 3);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize set");
        assert_eq!(consumed, written);
        match &deserialized {
            Value::Set(s) => assert_eq!(s.len(), 3),
            other => panic!("expected Set, got {other:?}"),
        }
    }

    #[test]
    fn test_roundtrip_function() {
        let func = FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Bool(true)),
            (Value::SmallInt(2), Value::Bool(false)),
        ]);
        let val = Value::Func(Arc::new(func));

        let mut buf = Vec::new();
        let written = serialize_value(&val, &mut buf).expect("serialize func");
        assert!(written > 0);

        let (deserialized, consumed) = deserialize_value(&buf, 0).expect("deserialize func");
        assert_eq!(consumed, written);
        match &deserialized {
            Value::Func(f) => assert_eq!(f.domain_len(), 2),
            other => panic!("expected Func, got {other:?}"),
        }
    }
}
