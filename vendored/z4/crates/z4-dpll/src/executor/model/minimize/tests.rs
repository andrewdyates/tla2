// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_int_candidates_zero_returns_zero() {
    let candidates = int_candidates(&BigInt::zero());
    assert_eq!(candidates, vec![BigInt::zero()]);
}

#[test]
fn test_int_candidates_large_positive() {
    let candidates = int_candidates(&BigInt::from(100));
    assert!(candidates[0].is_zero());
    assert_eq!(candidates[1], BigInt::one());
    assert!(candidates.len() > 2);
}

#[test]
fn test_int_candidates_one_includes_neg_one() {
    let candidates = int_candidates(&BigInt::one());
    // 0, 1, -1 all have magnitude <= 1
    assert_eq!(
        candidates,
        vec![BigInt::zero(), BigInt::one(), BigInt::from(-1)]
    );
}

#[test]
fn test_bv_candidates_zero_returns_zero() {
    let candidates = bv_candidates(&BigInt::zero(), 8);
    assert_eq!(candidates, vec![BigInt::zero()]);
}

#[test]
fn test_bv_candidates_has_expected_values() {
    let candidates = bv_candidates(&BigInt::from(255), 8);
    assert!(candidates.contains(&BigInt::zero()));
    assert!(candidates.contains(&BigInt::one()));
    assert!(candidates.contains(&BigInt::from(255))); // max unsigned
}

#[test]
fn test_rational_candidates_zero_returns_zero() {
    let candidates = rational_candidates(&BigRational::zero());
    assert_eq!(candidates, vec![BigRational::zero()]);
}

#[test]
fn test_int_candidates_large_includes_powers_of_10() {
    // For a large value like 1000, candidates should include powers of 10
    let candidates = int_candidates(&BigInt::from(1000));
    assert!(candidates.contains(&BigInt::zero()));
    assert!(candidates.contains(&BigInt::one()));
    assert!(
        candidates.contains(&BigInt::from(10)),
        "should include 10 for large positive values"
    );
    assert!(
        candidates.contains(&BigInt::from(100)),
        "should include 100 for large positive values"
    );
}

#[test]
fn test_int_candidates_negative_large_includes_negative_powers_of_10() {
    let candidates = int_candidates(&BigInt::from(-500));
    assert!(candidates.contains(&BigInt::zero()));
    assert!(
        candidates.contains(&BigInt::from(-10)),
        "should include -10 for large negative values"
    );
    assert!(
        candidates.contains(&BigInt::from(-100)),
        "should include -100 for large negative values"
    );
}

#[test]
fn test_int_candidates_respects_max_count() {
    // Even for very large values, should not exceed MAX_CANDIDATES_PER_VAR
    let candidates = int_candidates(&BigInt::from(1_000_000_000i64));
    assert!(candidates.len() <= MAX_CANDIDATES_PER_VAR);
}

#[test]
fn test_array_minimize_empty_stores_noop() {
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp);
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert!(interp.stores.is_empty());
}

#[test]
fn test_array_minimize_removes_default_matching_stores() {
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![
            ("#x01".to_owned(), "#xFF".to_owned()),
            ("#x02".to_owned(), "#x00".to_owned()), // matches default
            ("#x03".to_owned(), "#x00".to_owned()), // matches default
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp);
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert_eq!(interp.stores.len(), 1);
    assert_eq!(interp.stores[0], ("#x01".to_owned(), "#xFF".to_owned()));
}

#[test]
fn test_array_minimize_changes_default_to_most_frequent() {
    // 3 stores with #xFF, 1 with #x01. Default is #x00.
    // Changing default to #xFF removes 3 stores, keeping only #x01.
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![
            ("#x01".to_owned(), "#xFF".to_owned()),
            ("#x02".to_owned(), "#xFF".to_owned()),
            ("#x03".to_owned(), "#xFF".to_owned()),
            ("#x04".to_owned(), "#x01".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp);
    assert_eq!(interp.default.as_deref(), Some("#xFF"));
    assert_eq!(interp.stores.len(), 1);
    assert_eq!(interp.stores[0], ("#x04".to_owned(), "#x01".to_owned()));
}

#[test]
fn test_array_minimize_no_default_picks_most_frequent() {
    // No default, 3 stores with value "42". Should set default to "42".
    let mut interp = ArrayInterpretation {
        default: None,
        stores: vec![
            ("0".to_owned(), "42".to_owned()),
            ("1".to_owned(), "42".to_owned()),
            ("2".to_owned(), "42".to_owned()),
            ("3".to_owned(), "7".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp);
    assert_eq!(interp.default.as_deref(), Some("42"));
    assert_eq!(interp.stores.len(), 1);
    assert_eq!(interp.stores[0], ("3".to_owned(), "7".to_owned()));
}

#[test]
fn test_array_minimize_no_default_tie_prefers_zero_like_value() {
    let mut interp = ArrayInterpretation {
        default: None,
        stores: vec![
            ("0".to_owned(), "#xFF".to_owned()),
            ("1".to_owned(), "#x00".to_owned()),
            ("2".to_owned(), "#xFF".to_owned()),
            ("3".to_owned(), "#x00".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp);
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert_eq!(interp.stores.len(), 2);
    assert!(interp.stores.iter().all(|(_, val)| val == "#xFF"));
}

#[test]
fn test_array_minimize_keeps_default_on_tie() {
    // Two stores each with different values, current default is one of them.
    // Should keep current default.
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![
            ("0".to_owned(), "#xFF".to_owned()),
            ("1".to_owned(), "#x00".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp);
    // Both have freq 1, but #x00 is current default → keep it
    assert_eq!(interp.default.as_deref(), Some("#x00"));
    assert_eq!(interp.stores.len(), 1);
    assert_eq!(interp.stores[0], ("0".to_owned(), "#xFF".to_owned()));
}

#[test]
fn test_array_minimize_all_same_value() {
    let mut interp = ArrayInterpretation {
        default: Some("#x00".to_owned()),
        stores: vec![
            ("0".to_owned(), "#x42".to_owned()),
            ("1".to_owned(), "#x42".to_owned()),
            ("2".to_owned(), "#x42".to_owned()),
        ],
        index_sort: None,
        element_sort: None,
    };
    minimize_array_interpretation(&mut interp);
    assert_eq!(interp.default.as_deref(), Some("#x42"));
    assert!(interp.stores.is_empty());
}

#[test]
fn test_is_zero_like() {
    assert!(is_zero_like("0"));
    assert!(is_zero_like("#x00"));
    assert!(is_zero_like("#x0000"));
    assert!(is_zero_like("#x00000000"));
    assert!(is_zero_like("#b0"));
    assert!(is_zero_like("#b00000000"));
    assert!(!is_zero_like("1"));
    assert!(!is_zero_like("#xFF"));
    assert!(!is_zero_like("hello"));
}
