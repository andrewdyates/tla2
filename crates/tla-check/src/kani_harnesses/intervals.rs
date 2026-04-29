// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Interval operations harnesses (P10, P23, P56-interval, P59).

#[cfg(kani)]
mod kani_proofs {
    use super::super::kani_generators::*;
    use crate::value::{IntervalValue, Value};
    use num_bigint::BigInt;

    // P10: Interval Operations

    #[kani::proof]
    fn verify_interval_contains_bounds() {
        let iv = any_small_interval();
        if !iv.is_empty() {
            assert!(
                iv.contains(&Value::big_int(iv.low().clone())),
                "Interval must contain low bound"
            );
            assert!(
                iv.contains(&Value::big_int(iv.high().clone())),
                "Interval must contain high bound"
            );
        }
    }

    #[kani::proof]
    fn verify_interval_excludes_outside() {
        let iv = any_small_interval();
        if !iv.is_empty() {
            let below = Value::big_int(iv.low() - 1);
            let above = Value::big_int(iv.high() + 1);
            assert!(!iv.contains(&below), "Interval must not contain below low");
            assert!(!iv.contains(&above), "Interval must not contain above high");
        }
    }

    #[kani::proof]
    fn verify_interval_length() {
        let iv = any_small_interval();
        let len = iv.len();
        if iv.is_empty() {
            assert!(len == BigInt::from(0), "Empty interval has length 0");
        } else {
            let expected = iv.high() - iv.low() + 1;
            assert!(len == expected, "Interval length must be high - low + 1");
        }
    }

    // P23: Interval Membership Correctness

    #[kani::proof]
    fn verify_interval_membership_correctness() {
        let low: i8 = kani::any();
        let high: i8 = kani::any();
        let k: i8 = kani::any();
        kani::assume(low >= -50 && low <= 50);
        kani::assume(high >= -50 && high <= 50);
        kani::assume(k >= -50 && k <= 50);

        let iv = IntervalValue::new(BigInt::from(low as i64), BigInt::from(high as i64));
        let contains = iv.contains(&Value::int(k as i64));

        let expected = low <= k && k <= high;
        assert!(
            contains == expected,
            "Interval contains k iff low <= k <= high"
        );
    }

    #[kani::proof]
    fn verify_empty_interval_contains_nothing() {
        let k: i8 = kani::any();
        let iv = IntervalValue::new(BigInt::from(5), BigInt::from(1));
        let contains = iv.contains(&Value::int(k as i64));
        assert!(!contains, "Empty interval must contain nothing");
    }

    // P56: Interval Cardinality

    #[kani::proof]
    fn verify_interval_cardinality() {
        let low: i8 = kani::any();
        let high: i8 = kani::any();
        kani::assume(low <= high);
        kani::assume(high - low < 100);

        let iv = IntervalValue::new(BigInt::from(low as i64), BigInt::from(high as i64));
        let expected = BigInt::from((high - low + 1) as i64);

        assert!(
            iv.len() == expected,
            "Interval cardinality must be high - low + 1"
        );
    }

    #[kani::proof]
    fn verify_empty_interval_cardinality() {
        let low: i8 = kani::any();
        let high: i8 = kani::any();
        kani::assume(low > high);

        let iv = IntervalValue::new(BigInt::from(low as i64), BigInt::from(high as i64));

        assert!(
            iv.len() == BigInt::from(0),
            "Empty interval must have cardinality 0"
        );
    }

    #[kani::proof]
    fn verify_singleton_interval_cardinality() {
        let n: i8 = kani::any();
        let iv = IntervalValue::new(BigInt::from(n as i64), BigInt::from(n as i64));

        assert!(
            iv.len() == BigInt::from(1),
            "Singleton interval must have cardinality 1"
        );
    }

    // P59: Interval Enumeration Correctness

    #[kani::proof]
    fn verify_interval_iteration_order() {
        let iv = IntervalValue::new(BigInt::from(1), BigInt::from(3));
        let elements: Vec<BigInt> = iv.iter().collect();

        assert!(elements.len() == 3);
        assert!(elements[0] == BigInt::from(1));
        assert!(elements[1] == BigInt::from(2));
        assert!(elements[2] == BigInt::from(3));
    }

    #[kani::proof]
    fn verify_interval_contains_all_iterated() {
        let low: i8 = kani::any();
        let high: i8 = kani::any();
        kani::assume(low <= high);
        kani::assume(high - low < 10);

        let iv = IntervalValue::new(BigInt::from(low as i64), BigInt::from(high as i64));

        for n in iv.iter() {
            assert!(
                iv.contains(&Value::big_int(n)),
                "Interval must contain all iterated elements"
            );
        }
    }

    #[kani::proof]
    fn verify_interval_iteration_count() {
        let low: i8 = kani::any();
        let high: i8 = kani::any();
        kani::assume(low <= high);
        kani::assume(high - low < 10);

        let iv = IntervalValue::new(BigInt::from(low as i64), BigInt::from(high as i64));
        let count = iv.iter().count();
        let cardinality = iv.len();

        assert!(
            BigInt::from(count) == cardinality,
            "Iteration count must equal cardinality"
        );
    }

    #[kani::proof]
    fn verify_empty_interval_iteration() {
        let iv = IntervalValue::new(BigInt::from(5), BigInt::from(2));
        let count = iv.iter().count();

        assert!(
            count == 0,
            "Empty interval iteration must yield no elements"
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::value::{IntervalValue, Value};
    use num_bigint::BigInt;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_contains_bounds() {
        let iv = IntervalValue::new(BigInt::from(1), BigInt::from(5));
        assert!(iv.contains(&Value::int(1)), "Must contain low");
        assert!(iv.contains(&Value::int(5)), "Must contain high");
        assert!(iv.contains(&Value::int(3)), "Must contain middle");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_excludes_outside() {
        let iv = IntervalValue::new(BigInt::from(1), BigInt::from(5));
        assert!(!iv.contains(&Value::int(0)), "Must not contain below");
        assert!(!iv.contains(&Value::int(6)), "Must not contain above");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_length() {
        let iv1 = IntervalValue::new(BigInt::from(1), BigInt::from(5));
        assert_eq!(iv1.len(), BigInt::from(5), "1..5 has length 5");

        let iv2 = IntervalValue::new(BigInt::from(5), BigInt::from(1));
        assert_eq!(iv2.len(), BigInt::from(0), "Empty interval has length 0");

        let iv3 = IntervalValue::new(BigInt::from(3), BigInt::from(3));
        assert_eq!(iv3.len(), BigInt::from(1), "3..3 has length 1");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_membership_correctness() {
        let iv = IntervalValue::new(BigInt::from(1), BigInt::from(10));

        assert!(iv.contains(&Value::int(1)));
        assert!(iv.contains(&Value::int(5)));
        assert!(iv.contains(&Value::int(10)));

        assert!(!iv.contains(&Value::int(0)));
        assert!(!iv.contains(&Value::int(11)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_interval_contains_nothing() {
        let iv = IntervalValue::new(BigInt::from(5), BigInt::from(1));
        assert!(iv.is_empty());

        for k in -10..=10 {
            assert!(
                !iv.contains(&Value::int(k)),
                "Empty interval must contain nothing"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_membership_boundary() {
        for (low, high, tests) in [
            (0, 0, vec![(0, true), (-1, false), (1, false)]),
            (
                -5,
                5,
                vec![(-5, true), (0, true), (5, true), (-6, false), (6, false)],
            ),
        ] {
            let iv = IntervalValue::new(BigInt::from(low), BigInt::from(high));
            for (k, expected) in tests {
                assert_eq!(
                    iv.contains(&Value::int(k)),
                    expected,
                    "Interval {}..{} contains {} should be {}",
                    low,
                    high,
                    k,
                    expected
                );
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_cardinality() {
        let iv1 = IntervalValue::new(BigInt::from(1), BigInt::from(5));
        assert_eq!(iv1.len(), BigInt::from(5), "1..5 has cardinality 5");

        let iv2 = IntervalValue::new(BigInt::from(-2), BigInt::from(2));
        assert_eq!(iv2.len(), BigInt::from(5), "-2..2 has cardinality 5");

        let iv3 = IntervalValue::new(BigInt::from(0), BigInt::from(0));
        assert_eq!(iv3.len(), BigInt::from(1), "0..0 has cardinality 1");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_interval_cardinality() {
        let iv = IntervalValue::new(BigInt::from(5), BigInt::from(2));
        assert_eq!(
            iv.len(),
            BigInt::from(0),
            "Empty interval has cardinality 0"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_iteration_order() {
        let iv = IntervalValue::new(BigInt::from(1), BigInt::from(5));
        let elements: Vec<BigInt> = iv.iter().collect();

        assert_eq!(elements.len(), 5);
        assert_eq!(elements[0], BigInt::from(1));
        assert_eq!(elements[1], BigInt::from(2));
        assert_eq!(elements[2], BigInt::from(3));
        assert_eq!(elements[3], BigInt::from(4));
        assert_eq!(elements[4], BigInt::from(5));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_contains_all_iterated() {
        let iv = IntervalValue::new(BigInt::from(1), BigInt::from(5));

        for n in iv.iter() {
            assert!(
                iv.contains(&Value::big_int(n)),
                "Interval must contain all iterated elements"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_interval_iteration_count() {
        let test_cases = [(1, 5, 5), (0, 0, 1), (-2, 2, 5), (3, 3, 1)];

        for (low, high, expected) in test_cases {
            let iv = IntervalValue::new(BigInt::from(low), BigInt::from(high));
            let count = iv.iter().count();
            assert_eq!(
                count, expected,
                "Iteration count must equal cardinality for {}..{}",
                low, high
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_empty_interval_iteration() {
        let iv = IntervalValue::new(BigInt::from(5), BigInt::from(2));
        let count = iv.iter().count();
        assert_eq!(count, 0, "Empty interval iteration must yield no elements");
    }
}
