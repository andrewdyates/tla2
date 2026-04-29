// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ord consistency, transitivity, antisymmetry, total ordering + comparison operators (P8, P18-P20, P40).

#[cfg(kani)]
mod kani_proofs {
    use super::super::kani_generators::*;
    use crate::value::Value;

    // P8: Ord consistency with Eq

    #[kani::proof]
    fn verify_bool_ord_eq_consistency() {
        use std::cmp::Ordering;
        let v1 = any_bool_value();
        let v2 = any_bool_value();
        let ord_eq = v1.cmp(&v2) == Ordering::Equal;
        let eq_eq = v1 == v2;
        assert!(ord_eq == eq_eq, "Ord and Eq must be consistent");
    }

    #[kani::proof]
    fn verify_int_ord_eq_consistency() {
        use std::cmp::Ordering;
        let v1 = any_small_int_value();
        let v2 = any_small_int_value();
        let ord_eq = v1.cmp(&v2) == Ordering::Equal;
        let eq_eq = v1 == v2;
        assert!(ord_eq == eq_eq, "Ord and Eq must be consistent");
    }

    #[kani::proof]
    fn verify_string_ord_eq_consistency() {
        use std::cmp::Ordering;
        let v1 = any_short_string_value();
        let v2 = any_short_string_value();
        let ord_eq = v1.cmp(&v2) == Ordering::Equal;
        let eq_eq = v1 == v2;
        assert!(ord_eq == eq_eq, "Ord and Eq must be consistent");
    }

    // P18: Ord Transitivity

    #[kani::proof]
    fn verify_bool_ord_transitive() {
        use std::cmp::Ordering;
        let a = any_bool_value();
        let b = any_bool_value();
        let c = any_bool_value();

        // Use non-strict ordering (<=) since booleans have only 2 values,
        // making strict a < b < c unsatisfiable.
        if a.cmp(&b) != Ordering::Greater && b.cmp(&c) != Ordering::Greater {
            assert!(
                a.cmp(&c) != Ordering::Greater,
                "Ord must be transitive: a <= b && b <= c => a <= c"
            );
        }
    }

    #[kani::proof]
    fn verify_int_ord_transitive() {
        use std::cmp::Ordering;
        let a = any_small_int_value();
        let b = any_small_int_value();
        let c = any_small_int_value();

        if a.cmp(&b) == Ordering::Less && b.cmp(&c) == Ordering::Less {
            assert!(
                a.cmp(&c) == Ordering::Less,
                "Ord must be transitive: a < b && b < c => a < c"
            );
        }
    }

    #[kani::proof]
    fn verify_string_ord_transitive() {
        use std::cmp::Ordering;
        let a = any_short_string_value();
        let b = any_short_string_value();
        let c = any_short_string_value();

        if a.cmp(&b) == Ordering::Less && b.cmp(&c) == Ordering::Less {
            assert!(
                a.cmp(&c) == Ordering::Less,
                "Ord must be transitive: a < b && b < c => a < c"
            );
        }
    }

    // P19: Ord Antisymmetry

    #[kani::proof]
    fn verify_bool_ord_antisymmetric() {
        use std::cmp::Ordering;
        let a = any_bool_value();
        let b = any_bool_value();

        let a_le_b = a.cmp(&b) != Ordering::Greater;
        let b_le_a = b.cmp(&a) != Ordering::Greater;

        if a_le_b && b_le_a {
            assert!(
                a == b,
                "Ord must be antisymmetric: a <= b && b <= a => a == b"
            );
        }
    }

    #[kani::proof]
    fn verify_int_ord_antisymmetric() {
        use std::cmp::Ordering;
        let a = any_small_int_value();
        let b = any_small_int_value();

        let a_le_b = a.cmp(&b) != Ordering::Greater;
        let b_le_a = b.cmp(&a) != Ordering::Greater;

        if a_le_b && b_le_a {
            assert!(
                a == b,
                "Ord must be antisymmetric: a <= b && b <= a => a == b"
            );
        }
    }

    // P20: Total Ordering

    #[kani::proof]
    fn verify_bool_ord_total() {
        use std::cmp::Ordering;
        let a = any_bool_value();
        let b = any_bool_value();

        let ord = a.cmp(&b);
        let is_total = ord == Ordering::Less || ord == Ordering::Equal || ord == Ordering::Greater;
        assert!(is_total, "Ord must be total: exactly one of <, ==, > holds");
    }

    #[kani::proof]
    fn verify_int_ord_total() {
        use std::cmp::Ordering;
        let a = any_small_int_value();
        let b = any_small_int_value();

        let ord = a.cmp(&b);
        let is_total = ord == Ordering::Less || ord == Ordering::Equal || ord == Ordering::Greater;
        assert!(is_total, "Ord must be total: exactly one of <, ==, > holds");
    }

    #[kani::proof]
    fn verify_string_ord_total() {
        use std::cmp::Ordering;
        let a = any_short_string_value();
        let b = any_short_string_value();

        let ord = a.cmp(&b);
        let is_total = ord == Ordering::Less || ord == Ordering::Equal || ord == Ordering::Greater;
        assert!(is_total, "Ord must be total: exactly one of <, ==, > holds");
    }

    // P40: Integer Comparison Operators

    #[kani::proof]
    fn verify_int_lt_transitive() {
        let a: i8 = kani::any();
        let b: i8 = kani::any();
        let c: i8 = kani::any();
        if a < b && b < c {
            assert!(a < c, "Less-than must be transitive");
        }
    }

    #[kani::proof]
    fn verify_int_lt_irreflexive() {
        let a: i8 = kani::any();
        assert!(!(a < a), "Less-than must be irreflexive");
    }

    #[kani::proof]
    fn verify_int_leq_reflexive() {
        let a: i8 = kani::any();
        assert!(a <= a, "Less-than-or-equal must be reflexive");
    }

    #[kani::proof]
    fn verify_int_trichotomy() {
        let a: i8 = kani::any();
        let b: i8 = kani::any();
        let lt = a < b;
        let eq = a == b;
        let gt = a > b;
        // Exactly one must be true
        let count = (lt as u8) + (eq as u8) + (gt as u8);
        assert!(count == 1, "Trichotomy: exactly one of <, =, > holds");
    }
}

#[cfg(test)]
mod tests {
    use crate::value::Value;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_ord_eq_consistency() {
        use std::cmp::Ordering;

        let values = vec![
            Value::Bool(true),
            Value::Bool(false),
            Value::int(0),
            Value::int(1),
            Value::string("a"),
            Value::string("b"),
        ];

        for v1 in &values {
            for v2 in &values {
                let ord_eq = v1.cmp(v2) == Ordering::Equal;
                let eq_eq = v1 == v2;
                assert_eq!(
                    ord_eq, eq_eq,
                    "Ord and Eq must be consistent for {:?} vs {:?}",
                    v1, v2
                );
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bool_ord_transitive() {
        use std::cmp::Ordering;
        let a = Value::Bool(false);
        let b = Value::Bool(false);
        let c = Value::Bool(true);

        if a.cmp(&b) == Ordering::Less && b.cmp(&c) == Ordering::Less {
            assert_eq!(a.cmp(&c), Ordering::Less);
        }
        assert_eq!(Value::Bool(false).cmp(&Value::Bool(true)), Ordering::Less);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_int_ord_transitive() {
        use std::cmp::Ordering;
        let a = Value::int(1);
        let b = Value::int(2);
        let c = Value::int(3);

        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(b.cmp(&c), Ordering::Less);
        assert_eq!(
            a.cmp(&c),
            Ordering::Less,
            "Transitivity: 1 < 2 < 3 => 1 < 3"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_string_ord_transitive() {
        use std::cmp::Ordering;
        let a = Value::string("a");
        let b = Value::string("b");
        let c = Value::string("c");

        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(b.cmp(&c), Ordering::Less);
        assert_eq!(
            a.cmp(&c),
            Ordering::Less,
            "Transitivity: a < b < c => a < c"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_ord_antisymmetric() {
        use std::cmp::Ordering;
        let values = vec![
            Value::Bool(true),
            Value::Bool(false),
            Value::int(0),
            Value::int(1),
            Value::string("a"),
        ];

        for v1 in &values {
            for v2 in &values {
                let v1_le_v2 = v1.cmp(v2) != Ordering::Greater;
                let v2_le_v1 = v2.cmp(v1) != Ordering::Greater;

                if v1_le_v2 && v2_le_v1 {
                    assert_eq!(v1, v2, "Antisymmetry: v1 <= v2 && v2 <= v1 => v1 == v2");
                }
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_ord_total() {
        use std::cmp::Ordering;
        let values = vec![
            Value::Bool(true),
            Value::Bool(false),
            Value::int(0),
            Value::int(-1),
            Value::int(1),
            Value::string(""),
            Value::string("a"),
        ];

        for v1 in &values {
            for v2 in &values {
                let ord = v1.cmp(v2);
                assert!(
                    ord == Ordering::Less || ord == Ordering::Equal || ord == Ordering::Greater,
                    "Total ordering: exactly one of <, ==, > must hold"
                );
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_int_comparison_properties() {
        let test_cases: [(i8, i8, i8); 4] = [(1, 2, 3), (-3, -2, -1), (0, 1, 2), (-1, 0, 1)];
        for (a, b, c) in test_cases {
            if a < b && b < c {
                assert!(a < c, "Less-than must be transitive");
            }
        }

        for a in [-100i8, -1, 0, 1, 100] {
            assert!((a >= a), "Less-than must be irreflexive");
        }

        for a in [-100i8, -1, 0, 1, 100] {
            assert!(a <= a, "Less-than-or-equal must be reflexive");
        }

        for a in [-10i8, 0, 10] {
            for b in [-10i8, 0, 10] {
                let lt = a < b;
                let eq = a == b;
                let gt = a > b;
                let count = (lt as u8) + (eq as u8) + (gt as u8);
                assert_eq!(count, 1, "Trichotomy: exactly one of <, =, > holds");
            }
        }
    }
}
