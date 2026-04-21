// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fingerprint determinism and sensitivity harnesses (P1, P7, P21, per-type FP).

#[cfg(kani)]
mod kani_proofs {
    use super::super::kani_generators::*;
    use crate::state::{value_fingerprint, State};
    use crate::value::{IntervalValue, Value};
    use std::sync::Arc;

    // P1: Fingerprint Determinism

    #[kani::proof]
    fn verify_bool_fingerprint_deterministic() {
        let v = any_bool_value();
        let fp1 = value_fingerprint(&v);
        let fp2 = value_fingerprint(&v);
        assert!(fp1 == fp2, "Fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_int_fingerprint_deterministic() {
        let v = any_small_int_value();
        let fp1 = value_fingerprint(&v);
        let fp2 = value_fingerprint(&v);
        assert!(fp1 == fp2, "Fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_string_fingerprint_deterministic() {
        let v = any_short_string_value();
        let fp1 = value_fingerprint(&v);
        let fp2 = value_fingerprint(&v);
        assert!(fp1 == fp2, "Fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_value_fingerprint_deterministic() {
        let v = any_primitive_value();
        let fp1 = value_fingerprint(&v);
        let fp2 = value_fingerprint(&v);
        assert!(fp1 == fp2, "Fingerprint must be deterministic");
    }

    // P7: Fingerprint Sensitivity

    #[kani::proof]
    fn verify_bool_fingerprint_sensitive() {
        let v1 = Value::Bool(true);
        let v2 = Value::Bool(false);
        let fp1 = value_fingerprint(&v1);
        let fp2 = value_fingerprint(&v2);
        assert!(
            fp1 != fp2,
            "Different booleans should have different fingerprints"
        );
    }

    #[kani::proof]
    fn verify_int_fingerprint_equality_consistency() {
        let n: i8 = kani::any();
        let v1 = Value::SmallInt(n as i64);
        let v2 = Value::SmallInt(n as i64);
        let fp1 = value_fingerprint(&v1);
        let fp2 = value_fingerprint(&v2);
        assert!(fp1 == fp2, "Equal integers must have equal fingerprints");
    }

    // P21: Hash-Equality Consistency

    #[kani::proof]
    fn verify_equal_values_equal_fingerprints() {
        let v1 = any_primitive_value();
        let v2 = v1.clone();

        assert!(v1 == v2, "Cloned values must be equal");
        assert!(
            value_fingerprint(&v1) == value_fingerprint(&v2),
            "Equal values must have equal fingerprints"
        );
    }

    #[kani::proof]
    fn verify_equal_states_equal_fingerprints() {
        let v = any_primitive_value();
        let s1 = State::from_pairs([("x", v.clone())]);
        let s2 = State::from_pairs([("x", v)]);

        assert!(s1 == s2, "States with same content must be equal");
        assert!(
            s1.fingerprint() == s2.fingerprint(),
            "Equal states must have equal fingerprints"
        );
    }

    // Per-type fingerprint determinism

    #[kani::proof]
    fn verify_set_fingerprint_deterministic() {
        let s = any_small_set();
        let fp1 = value_fingerprint(&s);
        let fp2 = value_fingerprint(&s);
        assert!(fp1 == fp2, "Set fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_interval_fingerprint_deterministic() {
        let iv = any_small_interval();
        let v = Value::Interval(Arc::new(iv));
        let fp1 = value_fingerprint(&v);
        let fp2 = value_fingerprint(&v);
        assert!(fp1 == fp2, "Interval fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_func_fingerprint_deterministic() {
        let f = any_small_func();
        let v = Value::Func(Arc::new(f));
        let fp1 = value_fingerprint(&v);
        let fp2 = value_fingerprint(&v);
        assert!(fp1 == fp2, "Function fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_record_fingerprint_deterministic() {
        let r = any_small_record();
        let fp1 = value_fingerprint(&r);
        let fp2 = value_fingerprint(&r);
        assert!(fp1 == fp2, "Record fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_seq_fingerprint_deterministic() {
        let s = any_small_seq();
        let fp1 = value_fingerprint(&s);
        let fp2 = value_fingerprint(&s);
        assert!(fp1 == fp2, "Sequence fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_tuple_fingerprint_deterministic() {
        let t = any_small_tuple();
        let fp1 = value_fingerprint(&t);
        let fp2 = value_fingerprint(&t);
        assert!(fp1 == fp2, "Tuple fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_model_value_fingerprint_deterministic() {
        let name = any_model_value_name();
        let v = Value::ModelValue(name);
        let fp1 = value_fingerprint(&v);
        let fp2 = value_fingerprint(&v);
        assert!(fp1 == fp2, "ModelValue fingerprint must be deterministic");
    }

    // P-BoolOnly fingerprint

    #[kani::proof]
    fn verify_set_fingerprint_deterministic_boolonly() {
        let s = any_small_set_boolonly();
        let fp1 = value_fingerprint(&s);
        let fp2 = value_fingerprint(&s);
        assert!(fp1 == fp2, "Set fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_seq_fingerprint_deterministic_boolonly() {
        let s = any_small_seq_boolonly();
        let fp1 = value_fingerprint(&s);
        let fp2 = value_fingerprint(&s);
        assert!(fp1 == fp2, "Sequence fingerprint must be deterministic");
    }
}

#[cfg(test)]
mod tests {
    use crate::state::{value_fingerprint, State};
    use crate::value::{IntervalValue, SortedSet, Value};
    use num_bigint::BigInt;
    use std::sync::Arc;

    use super::super::test_helpers::make_func;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bool_fingerprint_deterministic() {
        for b in [true, false] {
            let v = Value::Bool(b);
            let fp1 = value_fingerprint(&v);
            let fp2 = value_fingerprint(&v);
            assert_eq!(fp1, fp2, "Fingerprint must be deterministic");
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_int_fingerprint_deterministic() {
        for n in [-128i64, -1, 0, 1, 127] {
            let v = Value::int(n);
            let fp1 = value_fingerprint(&v);
            let fp2 = value_fingerprint(&v);
            assert_eq!(fp1, fp2, "Fingerprint must be deterministic");
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_fingerprint_deterministic() {
        let s = State::from_pairs([("x", Value::Bool(true)), ("y", Value::int(42))]);
        let fp1 = s.fingerprint();
        let fp2 = s.fingerprint();
        assert_eq!(fp1, fp2, "State fingerprint must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_content_fingerprint_consistency() {
        let s1 = State::from_pairs([("x", Value::Bool(true)), ("y", Value::int(42))]);
        let s2 = State::from_pairs([("y", Value::int(42)), ("x", Value::Bool(true))]);
        assert_eq!(
            s1.fingerprint(),
            s2.fingerprint(),
            "States with same content must have same fingerprint"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bool_fingerprint_sensitive() {
        let v1 = Value::Bool(true);
        let v2 = Value::Bool(false);
        assert_ne!(
            value_fingerprint(&v1),
            value_fingerprint(&v2),
            "Different booleans should have different fingerprints"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_equal_values_equal_fingerprints() {
        let values = vec![Value::Bool(true), Value::int(42), Value::string("test")];

        for v in values {
            let v_clone = v.clone();
            assert_eq!(v, v_clone);
            assert_eq!(
                value_fingerprint(&v),
                value_fingerprint(&v_clone),
                "Equal values must have equal fingerprints"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_equal_states_equal_fingerprints() {
        let v = Value::int(42);
        let s1 = State::from_pairs([("x", v.clone())]);
        let s2 = State::from_pairs([("x", v)]);

        assert_eq!(s1, s2);
        assert_eq!(
            s1.fingerprint(),
            s2.fingerprint(),
            "Equal states must have equal fingerprints"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_set_fingerprint_deterministic() {
        let s = Value::Set(Arc::new(SortedSet::from_iter(vec![
            Value::int(1),
            Value::int(2),
        ])));

        let fp1 = value_fingerprint(&s);
        let fp2 = value_fingerprint(&s);
        assert_eq!(fp1, fp2, "Set fingerprint must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_fingerprint_deterministic() {
        let iv = IntervalValue::new(BigInt::from(1), BigInt::from(10));
        let v = Value::Interval(Arc::new(iv));
        let fp1 = value_fingerprint(&v);
        let fp2 = value_fingerprint(&v);
        assert_eq!(fp1, fp2, "Interval fingerprint must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_fingerprint_deterministic() {
        let f = Value::Func(Arc::new(make_func(vec![(Value::int(1), Value::int(42))])));
        let fp1 = value_fingerprint(&f);
        let fp2 = value_fingerprint(&f);
        assert_eq!(fp1, fp2, "Function fingerprint must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_record_fingerprint_deterministic() {
        use crate::value::RecordBuilder;
        let mut builder = RecordBuilder::new();
        builder.insert_str("x", Value::Bool(true));
        let r = Value::Record(builder.build());

        let fp1 = value_fingerprint(&r);
        let fp2 = value_fingerprint(&r);
        assert_eq!(fp1, fp2, "Record fingerprint must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_seq_fingerprint_deterministic() {
        let s = Value::Seq(Arc::new(vec![Value::Bool(true), Value::Bool(false)].into()));
        let fp1 = value_fingerprint(&s);
        let fp2 = value_fingerprint(&s);
        assert_eq!(fp1, fp2, "Sequence fingerprint must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tuple_fingerprint_deterministic() {
        let t = Value::Tuple(vec![Value::Bool(true)].into());
        let fp1 = value_fingerprint(&t);
        let fp2 = value_fingerprint(&t);
        assert_eq!(fp1, fp2, "Tuple fingerprint must be deterministic");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_model_value_fingerprint_deterministic() {
        use crate::state::value_fingerprint;
        for name in ["m1", "m2", "m3", "a", "b", "c"] {
            let v = Value::ModelValue(Arc::from(name));
            let fp1 = value_fingerprint(&v);
            let fp2 = value_fingerprint(&v);
            assert_eq!(fp1, fp2, "ModelValue fingerprint must be deterministic");
        }
    }
}
