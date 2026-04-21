// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State fingerprint, insert/get, update isolation, construction consistency (P4, P6, P16, P17, P22).

#[cfg(kani)]
mod kani_proofs {
    use super::super::kani_generators::*;
    use crate::state::State;

    // P4: State Fingerprint Determinism

    #[kani::proof]
    fn verify_empty_state_fingerprint_deterministic() {
        let s = State::new();
        let fp1 = s.fingerprint();
        let fp2 = s.fingerprint();
        assert!(fp1 == fp2, "State fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_single_var_state_fingerprint_deterministic() {
        let v = any_primitive_value();
        let s = State::from_pairs([("x", v)]);
        let fp1 = s.fingerprint();
        let fp2 = s.fingerprint();
        assert!(fp1 == fp2, "State fingerprint must be deterministic");
    }

    #[kani::proof]
    fn verify_two_var_state_fingerprint_deterministic() {
        let v1 = any_bool_value();
        let v2 = any_small_int_value();
        let s = State::from_pairs([("x", v1), ("y", v2)]);
        let fp1 = s.fingerprint();
        let fp2 = s.fingerprint();
        assert!(fp1 == fp2, "State fingerprint must be deterministic");
    }

    // P6: State Equality Properties

    #[kani::proof]
    fn verify_state_equality_reflexive() {
        let v = any_primitive_value();
        let s = State::from_pairs([("x", v)]);
        assert!(s == s, "State equality must be reflexive");
    }

    #[kani::proof]
    fn verify_state_content_fingerprint_consistency() {
        let v1 = any_bool_value();
        let v2 = any_small_int_value();

        let s1 = State::from_pairs([("x", v1.clone()), ("y", v2.clone())]);
        let s2 = State::from_pairs([("y", v2), ("x", v1)]);

        assert!(
            s1.fingerprint() == s2.fingerprint(),
            "States with same content must have same fingerprint"
        );
    }

    // P16: State Insert-Get Consistency

    #[kani::proof]
    fn verify_state_insert_get_consistency() {
        let v = any_primitive_value();
        let s = State::new().with_var("x", v.clone());
        let retrieved = s.get("x");
        assert!(retrieved.is_some(), "Get must return inserted value");
        assert!(
            *retrieved.unwrap() == v,
            "Retrieved value must equal inserted value"
        );
    }

    #[kani::proof]
    fn verify_state_insert_get_any_name() {
        let v = any_bool_value();
        let choice: u8 = kani::any();
        kani::assume(choice < 4);
        let name = match choice {
            0 => "x",
            1 => "y",
            2 => "var1",
            _ => "state_var",
        };
        let s = State::new().with_var(name, v.clone());
        let retrieved = s.get(name);
        assert!(retrieved.is_some(), "Get must return inserted value");
        assert!(
            *retrieved.unwrap() == v,
            "Retrieved value must equal inserted value"
        );
    }

    // P17: State Update Isolation

    #[kani::proof]
    fn verify_state_update_isolation() {
        let v1 = any_bool_value();
        let v2 = any_small_int_value();
        let v3 = any_short_string_value();

        let s1 = State::from_pairs([("x", v1.clone()), ("y", v2.clone())]);
        let s2 = s1.with_var("z", v3);

        assert!(s2.get("x") == s1.get("x"), "Updating z must not affect x");
        assert!(s2.get("y") == s1.get("y"), "Updating z must not affect y");
    }

    #[kani::proof]
    fn verify_state_update_preserves_others() {
        let v1 = any_bool_value();
        let v2 = any_small_int_value();
        let v3 = any_short_string_value();

        let s1 = State::from_pairs([("x", v1), ("y", v2.clone())]);
        let s2 = s1.with_var("x", v3);

        assert!(s2.get("y") == s1.get("y"), "Updating x must not affect y");
        assert!(*s2.get("y").unwrap() == v2, "y value must be preserved");
    }

    // P22: State Construction Consistency

    #[kani::proof]
    fn verify_state_construction_equivalence() {
        let v1 = any_bool_value();
        let v2 = any_small_int_value();

        let s1 = State::new()
            .with_var("x", v1.clone())
            .with_var("y", v2.clone());

        let s2 = State::from_pairs([("x", v1), ("y", v2)]);

        assert!(
            s1 == s2,
            "Different construction methods must yield equal states"
        );
        assert!(
            s1.fingerprint() == s2.fingerprint(),
            "Different construction methods must yield same fingerprint"
        );
    }

    #[kani::proof]
    fn verify_state_insertion_order_invariance() {
        let v1 = any_bool_value();
        let v2 = any_small_int_value();

        let s1 = State::new()
            .with_var("x", v1.clone())
            .with_var("y", v2.clone());

        let s2 = State::new().with_var("y", v2).with_var("x", v1);

        assert!(s1 == s2, "Insertion order must not affect state equality");
        assert!(
            s1.fingerprint() == s2.fingerprint(),
            "Insertion order must not affect fingerprint"
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::state::State;
    use crate::value::Value;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_insert_get_consistency() {
        let values = vec![Value::Bool(true), Value::int(42), Value::string("hello")];

        for v in values {
            let s = State::from_pairs([("x", v.clone())]);
            let retrieved = s.get("x");
            assert!(retrieved.is_some(), "Get must return inserted value");
            assert_eq!(
                *retrieved.unwrap(),
                v,
                "Retrieved value must equal inserted value"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_insert_get_various_names() {
        let names = ["x", "y", "myVar", "state_var", "CamelCase"];
        let v = Value::Bool(true);

        for name in names {
            let s = State::from_pairs([(name, v.clone())]);
            let retrieved = s.get(name);
            assert!(
                retrieved.is_some(),
                "Get must return inserted value for {}",
                name
            );
            assert_eq!(*retrieved.unwrap(), v);
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_update_isolation() {
        let v1 = Value::Bool(true);
        let v2 = Value::int(42);
        let v3 = Value::string("new");

        let s1 = State::from_pairs([("x", v1.clone()), ("y", v2.clone())]);
        let s2 = s1.with_var("z", v3);

        assert_eq!(s2.get("x"), s1.get("x"), "Updating z must not affect x");
        assert_eq!(s2.get("y"), s1.get("y"), "Updating z must not affect y");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_update_preserves_others() {
        let v1 = Value::Bool(true);
        let v2 = Value::int(42);
        let v3 = Value::string("updated");

        let s1 = State::from_pairs([("x", v1), ("y", v2.clone())]);
        let s2 = s1.with_var("x", v3);

        assert_eq!(s2.get("y"), s1.get("y"), "Updating x must not affect y");
        assert_eq!(*s2.get("y").unwrap(), v2, "y value must be preserved");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_construction_equivalence() {
        let v1 = Value::Bool(true);
        let v2 = Value::int(42);

        let s1 = State::new()
            .with_var("x", v1.clone())
            .with_var("y", v2.clone());

        let s2 = State::from_pairs([("x", v1), ("y", v2)]);

        assert_eq!(
            s1, s2,
            "Different construction methods must yield equal states"
        );
        assert_eq!(
            s1.fingerprint(),
            s2.fingerprint(),
            "Different construction methods must yield same fingerprint"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_state_insertion_order_invariance() {
        let v1 = Value::Bool(true);
        let v2 = Value::int(42);

        let s1 = State::new()
            .with_var("x", v1.clone())
            .with_var("y", v2.clone());

        let s2 = State::new().with_var("y", v2).with_var("x", v1);

        assert_eq!(s1, s2, "Insertion order must not affect state equality");
        assert_eq!(
            s1.fingerprint(),
            s2.fingerprint(),
            "Insertion order must not affect fingerprint"
        );
    }
}
