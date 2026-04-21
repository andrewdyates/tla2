// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function operations harnesses: apply, domain, EXCEPT, nested EXCEPT, construction (P11, P43, P49, P52, P57-func, P60).

#[cfg(kani)]
mod kani_proofs {
    use super::super::kani_generators::*;
    use crate::value::{FuncValue, SortedSet, Value};
    use std::sync::Arc;

    fn collected_domain(func: &FuncValue) -> SortedSet {
        SortedSet::from_sorted_vec(func.domain_iter().cloned().collect())
    }

    // P11: Function Operations

    #[kani::proof]
    fn verify_func_apply_in_domain() {
        let f = any_small_func();
        if !f.domain_is_empty() {
            if let Some(d) = f.domain_iter().next() {
                let result = f.mapping_get(d);
                assert!(
                    result.is_some(),
                    "Function must have mapping for domain elements"
                );
            }
        }
    }

    #[kani::proof]
    fn verify_func_domain_mapping_consistent() {
        let f = any_small_func();
        // Every domain key must have a mapping entry
        for key in f.domain_iter() {
            assert!(
                f.mapping_get(key).is_some(),
                "Every domain element must have a mapping"
            );
        }
    }

    // P43: Function EXCEPT Semantics

    #[kani::proof]
    fn verify_func_except_preserves_domain() {
        let f = any_small_func_fixed();
        let original_domain = collected_domain(&f);
        if !f.domain_is_empty() {
            let key = f.domain_iter().next().unwrap().clone();
            let new_val = Value::Bool(false);
            let f_new = f.except(key, new_val);
            assert!(
                f_new.domain_eq_sorted_set(&original_domain),
                "EXCEPT must preserve domain"
            );
        }
    }

    #[kani::proof]
    fn verify_func_except_updates_value() {
        let f = make_func(vec![(Value::int(1), Value::Bool(true))]);
        let key = Value::int(1);
        let new_val = Value::Bool(false);
        let f_new = f.except(key.clone(), new_val.clone());
        let result = f_new.apply(&key);
        assert!(result.is_some(), "Key must still be in function");
        assert!(
            *result.unwrap() == new_val,
            "EXCEPT must update to new value"
        );
    }

    #[kani::proof]
    fn verify_func_except_isolates_other_keys() {
        let f = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), Value::Bool(false)),
        ]);
        let k2 = Value::int(2);
        let v2 = Value::Bool(false);
        let f_new = f.except(Value::int(1), Value::int(42));
        let result = f_new.apply(&k2);
        assert!(result.is_some(), "Other key must still exist");
        assert!(*result.unwrap() == v2, "EXCEPT must not affect other keys");
    }

    // P49: Function Application Semantics

    #[kani::proof]
    fn verify_func_apply_in_domain_specific() {
        let key = Value::int(1);
        let val = Value::Bool(true);
        let f = make_func(vec![(key.clone(), val.clone())]);
        let result = f.apply(&key);
        assert!(result.is_some(), "Apply must succeed for domain element");
        assert!(*result.unwrap() == val, "Apply must return mapped value");
    }

    #[kani::proof]
    fn verify_func_apply_outside_domain() {
        let f = make_func(vec![(Value::int(1), Value::Bool(true))]);
        let result = f.apply(&Value::int(2));
        assert!(
            result.is_none(),
            "Apply must return None for non-domain element"
        );
    }

    #[kani::proof]
    fn verify_func_domain_apply_consistency() {
        let f = any_small_func();
        let key = any_small_int_value();
        let in_domain = f.domain_contains(&key);
        let apply_succeeds = f.apply(&key).is_some();
        if in_domain {
            assert!(apply_succeeds, "If key in DOMAIN, apply must succeed");
        }
    }

    // P52: Nested EXCEPT Paths

    #[kani::proof]
    fn verify_nested_except_preserves_outer_domain() {
        let outer = create_nested_func();
        let original_domain = collected_domain(&outer);
        if let Some(Value::Func(ref inner)) = outer.apply(&Value::int(1)).cloned() {
            let new_inner = inner.except(Value::int(1), Value::Bool(false));
            let new_outer = outer.except(Value::int(1), Value::Func(Arc::new(new_inner)));
            assert!(
                new_outer.domain_eq_sorted_set(&original_domain),
                "Nested EXCEPT must preserve outer domain"
            );
        }
    }

    #[kani::proof]
    fn verify_nested_except_updates_inner_value() {
        let outer = create_nested_func();
        if let Some(Value::Func(ref inner)) = outer.apply(&Value::int(1)).cloned() {
            let new_inner = inner.except(Value::int(1), Value::Bool(false));
            let new_outer = outer.except(Value::int(1), Value::Func(Arc::new(new_inner)));
            if let Some(Value::Func(ref result_inner)) = new_outer.apply(&Value::int(1)).cloned() {
                let result = result_inner.apply(&Value::int(1));
                assert!(result.is_some());
                assert!(
                    *result.unwrap() == Value::Bool(false),
                    "Nested EXCEPT must update inner value"
                );
            }
        }
    }

    #[kani::proof]
    fn verify_nested_except_preserves_other_inner_keys() {
        let outer = create_nested_func();
        if let Some(Value::Func(ref inner)) = outer.apply(&Value::int(1)).cloned() {
            let original_inner_2 = inner.apply(&Value::int(2)).cloned();
            let new_inner = inner.except(Value::int(1), Value::Bool(false));
            let new_outer = outer.except(Value::int(1), Value::Func(Arc::new(new_inner)));
            if let Some(Value::Func(ref result_inner)) = new_outer.apply(&Value::int(1)).cloned() {
                let result_inner_2 = result_inner.apply(&Value::int(2)).cloned();
                assert!(
                    result_inner_2 == original_inner_2,
                    "Nested EXCEPT must preserve other inner keys"
                );
            }
        }
    }

    // P57: Empty Function

    #[kani::proof]
    fn verify_empty_function_properties() {
        let f = make_func(vec![]);
        assert!(f.domain_is_empty(), "Empty function has empty domain");
        let v = any_primitive_value();
        assert!(
            f.apply(&v).is_none(),
            "Empty function returns None for any input"
        );
    }

    // P60: Function Construction Semantics

    #[kani::proof]
    fn verify_func_domain_equals_construction_domain() {
        let f = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), Value::Bool(false)),
        ]);
        let expected = SortedSet::from_iter(vec![Value::int(1), Value::int(2)]);
        assert!(
            f.domain_eq_sorted_set(&expected),
            "Function domain must equal construction domain"
        );
    }

    #[kani::proof]
    fn verify_func_mapping_size_equals_domain() {
        let f = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), Value::Bool(false)),
        ]);
        assert!(
            f.domain_len() == 2,
            "Function domain size must equal number of inserted keys"
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::value::{FuncValue, SortedSet, Value};
    use std::sync::Arc;

    use super::super::test_helpers::{create_nested_func, make_func};

    fn collected_domain(func: &FuncValue) -> SortedSet {
        SortedSet::from_sorted_vec(func.domain_iter().cloned().collect())
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_domain_mapping_consistent() {
        let f = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), Value::Bool(false)),
        ]);
        assert_eq!(f.domain_len(), 2, "Domain size must equal mapping size");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_apply_in_domain() {
        let d = Value::int(1);
        let f = make_func(vec![(d.clone(), Value::Bool(true))]);
        let result = f.mapping_get(&d);
        assert!(
            result.is_some(),
            "Function must have mapping for domain elements"
        );
        assert_eq!(*result.unwrap(), Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_except_preserves_domain() {
        let f = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), Value::Bool(false)),
        ]);
        let original_domain = collected_domain(&f);
        let f_new = f.except(Value::int(1), Value::int(42));
        assert!(
            f_new.domain_eq_sorted_set(&original_domain),
            "EXCEPT must preserve domain"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_except_updates_value() {
        let key = Value::int(1);
        let f = make_func(vec![(key.clone(), Value::Bool(true))]);
        let new_val = Value::Bool(false);
        let f_new = f.except(key.clone(), new_val.clone());
        let result = f_new.apply(&key);
        assert!(result.is_some());
        assert_eq!(*result.unwrap(), new_val, "EXCEPT must update to new value");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_except_isolates_other_keys() {
        let v2 = Value::Bool(false);
        let f = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), v2.clone()),
        ]);
        let f_new = f.except(Value::int(1), Value::int(42));
        let result = f_new.apply(&Value::int(2));
        assert!(result.is_some());
        assert_eq!(*result.unwrap(), v2, "EXCEPT must not affect other keys");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_apply_in_domain_returns_value() {
        let key = Value::int(1);
        let val = Value::Bool(true);
        let f = make_func(vec![(key.clone(), val.clone())]);
        let result = f.apply(&key);
        assert!(result.is_some(), "Apply must succeed for domain element");
        assert_eq!(*result.unwrap(), val, "Apply must return mapped value");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_apply_outside_domain_returns_none() {
        let f = make_func(vec![(Value::int(1), Value::Bool(true))]);
        let result = f.apply(&Value::int(2));
        assert!(
            result.is_none(),
            "Apply must return None for non-domain element"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_domain_apply_consistency() {
        let f = make_func(vec![
            (Value::int(1), Value::Bool(false)),
            (Value::int(2), Value::Bool(true)),
            (Value::int(3), Value::Bool(false)),
            (Value::int(4), Value::Bool(true)),
            (Value::int(5), Value::Bool(false)),
        ]);
        for i in 1..=5 {
            let k = Value::int(i);
            assert!(f.domain_contains(&k));
            assert!(
                f.apply(&k).is_some(),
                "If key in DOMAIN, apply must succeed"
            );
        }
        for i in [0, 6, 10] {
            let k = Value::int(i);
            assert!(!f.domain_contains(&k));
            assert!(
                f.apply(&k).is_none(),
                "If key not in DOMAIN, apply must return None"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_nested_except_preserves_outer_domain() {
        let outer = create_nested_func();
        let original_domain = collected_domain(&outer);
        if let Some(Value::Func(ref inner)) = outer.apply(&Value::int(1)).cloned() {
            let new_inner = inner.as_ref().clone().except(Value::int(1), Value::Bool(false));
            let new_outer = outer.except(Value::int(1), Value::Func(Arc::new(new_inner)));
            assert!(
                new_outer.domain_eq_sorted_set(&original_domain),
                "Nested EXCEPT must preserve outer domain"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_nested_except_updates_inner_value() {
        let outer = create_nested_func();
        if let Some(Value::Func(ref inner)) = outer.apply(&Value::int(1)).cloned() {
            let new_inner = inner.as_ref().clone().except(Value::int(1), Value::Bool(false));
            let new_outer = outer.except(Value::int(1), Value::Func(Arc::new(new_inner)));
            if let Some(Value::Func(ref result_inner)) = new_outer.apply(&Value::int(1)).cloned() {
                let result = result_inner.apply(&Value::int(1));
                assert!(result.is_some());
                assert_eq!(
                    *result.unwrap(),
                    Value::Bool(false),
                    "Nested EXCEPT must update inner value"
                );
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_nested_except_preserves_other_inner_keys() {
        let outer = create_nested_func();
        if let Some(Value::Func(ref inner)) = outer.apply(&Value::int(1)).cloned() {
            let original_inner_2 = inner.apply(&Value::int(2)).cloned();
            let new_inner = inner.as_ref().clone().except(Value::int(1), Value::Bool(false));
            let new_outer = outer.except(Value::int(1), Value::Func(Arc::new(new_inner)));
            if let Some(Value::Func(ref result_inner)) = new_outer.apply(&Value::int(1)).cloned() {
                let result_inner_2 = result_inner.apply(&Value::int(2)).cloned();
                assert_eq!(
                    result_inner_2, original_inner_2,
                    "Nested EXCEPT must preserve other inner keys"
                );
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_function_properties() {
        let f = make_func(vec![]);
        assert!(f.domain_is_empty(), "Empty function has empty domain");
        let v = Value::int(1);
        assert!(
            f.apply(&v).is_none(),
            "Empty function returns None for any input"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_domain_equals_construction_domain() {
        let f = make_func(vec![
            (Value::int(1), Value::Bool(true)),
            (Value::int(2), Value::Bool(false)),
        ]);
        let expected = SortedSet::from_iter(vec![Value::int(1), Value::int(2)]);
        assert!(
            f.domain_eq_sorted_set(&expected),
            "Function domain must equal construction domain"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_func_mapping_size_equals_domain() {
        for size in 0..=4i64 {
            let entries: Vec<(Value, Value)> = (0..size)
                .map(|i| (Value::int(i), Value::Bool(i % 2 == 0)))
                .collect();
            let f = make_func(entries);
            assert_eq!(
                f.domain_len(),
                size as usize,
                "Function domain size must equal mapping size"
            );
        }
    }
}
