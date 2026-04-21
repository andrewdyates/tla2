// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `FingerprintHasher` identity property and `FpHashMap`/`FpHashSet`
//! correctness. Part of #4134: Wave 3 performance optimization test coverage.
//!
//! The identity hasher replaces FxHash for all Fingerprint-keyed maps (seen
//! states, depths, successor witnesses, InMemory storage). It must preserve
//! the invariant: `hash(Fingerprint(x)) == x` for any `x: u64`.

use super::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Core identity property: hashing a Fingerprint through FingerprintHasher
/// must return the raw u64 value unchanged.
#[test]
fn test_fingerprint_hasher_identity_property() {
    let test_values: &[u64] = &[
        0,
        1,
        u64::MAX,
        u64::MAX - 1,
        0x0123_4567_89AB_CDEF,
        0xDEAD_BEEF_CAFE_BABE,
        // Fibonacci hash constant (what FxHash multiplies by — should NOT appear)
        0x517cc1b727220a95,
    ];

    for &raw in test_values {
        let fp = Fingerprint(raw);
        let mut hasher = FingerprintHasher::default();
        fp.hash(&mut hasher);
        let result = hasher.finish();
        assert_eq!(
            result, raw,
            "FingerprintHasher must return raw value unchanged for {raw:#018x}"
        );
    }
}

/// BuildFingerprintHasher produces hashers with the identity property.
#[test]
fn test_build_fingerprint_hasher_produces_identity() {
    use std::hash::BuildHasher;

    let builder = BuildFingerprintHasher;
    let fp = Fingerprint(0xAAAA_BBBB_CCCC_DDDD);
    let mut hasher = builder.build_hasher();
    fp.hash(&mut hasher);
    assert_eq!(hasher.finish(), 0xAAAA_BBBB_CCCC_DDDD);
}

/// FpHashMap insert/lookup/contains operations work correctly at scale.
/// 10K entries as specified in acceptance criteria.
#[test]
fn test_fp_hashmap_operations_10k() {
    let count = 10_000u64;
    let mut map: FpHashMap<u64> = fp_hashmap_with_capacity(count as usize);

    // Insert 10K entries
    for i in 0..count {
        let fp = Fingerprint(i * 0x9E37_79B9_7F4A_7C15 + 1); // spread via golden ratio
        map.insert(fp, i);
    }

    assert_eq!(map.len(), count as usize);

    // Verify all entries are retrievable
    for i in 0..count {
        let fp = Fingerprint(i * 0x9E37_79B9_7F4A_7C15 + 1);
        assert_eq!(map.get(&fp), Some(&i), "Missing entry for i={i}");
    }

    // Verify non-existent keys are absent
    let missing = Fingerprint(0xFFFF_FFFF_FFFF_FFFF);
    assert!(!map.contains_key(&missing));
}

/// FpHashSet insert/contains operations work correctly at scale.
#[test]
fn test_fp_hashset_operations_10k() {
    let count = 10_000u64;
    let mut set: FpHashSet = fp_hashset_with_capacity(count as usize);

    for i in 0..count {
        let fp = Fingerprint(i * 0x9E37_79B9_7F4A_7C15 + 1);
        assert!(set.insert(fp), "Duplicate detected for fresh entry i={i}");
    }

    assert_eq!(set.len(), count as usize);

    // Verify all entries exist
    for i in 0..count {
        let fp = Fingerprint(i * 0x9E37_79B9_7F4A_7C15 + 1);
        assert!(set.contains(&fp), "Missing entry for i={i}");
    }

    // Verify duplicate insertion fails
    let dup = Fingerprint(1 * 0x9E37_79B9_7F4A_7C15 + 1);
    assert!(!set.insert(dup), "Duplicate insert should return false");
    assert_eq!(set.len(), count as usize, "Length should not change on dup insert");
}

/// No collision anomalies: inserting Fingerprints with sequential raw values
/// (worst case for identity hasher since HashMap uses lower bits for bucket
/// selection) must still have correct insert/lookup behavior.
#[test]
fn test_fp_hashmap_sequential_keys_no_collision_anomaly() {
    let count = 1_000u64;
    let mut map: FpHashMap<u64> = fp_hashmap();

    // Sequential keys stress the hash table's bucket distribution
    for i in 0..count {
        map.insert(Fingerprint(i), i);
    }

    assert_eq!(map.len(), count as usize);

    for i in 0..count {
        assert_eq!(map.get(&Fingerprint(i)), Some(&i));
    }
}

/// FpHashMap works correctly with values clustered in high bits only.
/// This tests that the identity hasher doesn't fail when low bits are similar.
#[test]
fn test_fp_hashmap_high_bit_clustering() {
    let mut map: FpHashMap<u64> = fp_hashmap();
    let base: u64 = 0xFF00_0000_0000_0000;

    for i in 0..256u64 {
        map.insert(Fingerprint(base + i), i);
    }

    assert_eq!(map.len(), 256);

    for i in 0..256u64 {
        assert_eq!(map.get(&Fingerprint(base + i)), Some(&i));
    }
}

/// FingerprintHasher and DefaultHasher produce different results, confirming
/// FingerprintHasher is NOT the standard hasher.
#[test]
fn test_fingerprint_hasher_differs_from_default() {
    let fp = Fingerprint(42);

    let mut identity = FingerprintHasher::default();
    fp.hash(&mut identity);
    let identity_result = identity.finish();

    let mut default = DefaultHasher::new();
    fp.hash(&mut default);
    let default_result = default.finish();

    // The identity hasher returns 42; the default SipHash will not.
    assert_eq!(identity_result, 42);
    assert_ne!(
        identity_result, default_result,
        "Identity hasher should differ from DefaultHasher"
    );
}

/// FpHashMap entry removal works correctly.
#[test]
fn test_fp_hashmap_remove() {
    let mut map: FpHashMap<&str> = fp_hashmap();
    map.insert(Fingerprint(100), "alpha");
    map.insert(Fingerprint(200), "beta");
    map.insert(Fingerprint(300), "gamma");

    assert_eq!(map.remove(&Fingerprint(200)), Some("beta"));
    assert_eq!(map.len(), 2);
    assert!(!map.contains_key(&Fingerprint(200)));
    assert!(map.contains_key(&Fingerprint(100)));
    assert!(map.contains_key(&Fingerprint(300)));
}
