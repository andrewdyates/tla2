// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_basic_operations() {
    let set = MmapFingerprintSet::new(1000, None).unwrap();

    // Initially empty
    assert!(set.is_empty());
    assert_eq!(set.len(), 0);

    // Insert new fingerprint
    assert!(set.insert(fp(12345)).unwrap());
    assert_eq!(set.len(), 1);
    assert!(set.contains(fp(12345)));

    // Insert same fingerprint again
    assert!(!set.insert(fp(12345)).unwrap());
    assert_eq!(set.len(), 1);

    // Insert different fingerprint
    assert!(set.insert(fp(67890)).unwrap());
    assert_eq!(set.len(), 2);
    assert!(set.contains(fp(67890)));

    // Check non-existent
    assert!(!set.contains(fp(99999)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_fingerprint_zero() {
    // Fingerprint 0 is special-cased
    let set = MmapFingerprintSet::new(100, None).unwrap();

    assert!(!set.contains(fp(0)));
    assert!(set.insert(fp(0)).unwrap());
    assert!(set.contains(fp(0)));
    assert!(!set.insert(fp(0)).unwrap());
}

/// Regression test for #1535: FP(0) and FP(u64::MAX) must be stored as distinct entries.
/// Before the fix, both encoded to u64::MAX, so inserting one after the other would
/// silently skip the second — conflating two distinct states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_fingerprint_zero_vs_max_distinct() {
    let set = MmapFingerprintSet::new(100, None).unwrap();

    // Insert FP(0) — stored via has_zero flag (not in mmap array)
    assert!(set.insert(fp(0)).unwrap());
    assert!(set.contains(fp(0)));
    assert_eq!(set.len(), 1);

    // Insert FP(u64::MAX) — stored in mmap array as identity encoding
    assert!(
        set.insert(fp(u64::MAX)).unwrap(),
        "#1535: FP(u64::MAX) must be distinct from FP(0)"
    );
    assert!(set.contains(fp(u64::MAX)));
    assert_eq!(set.len(), 2);

    // Both must still be present
    assert!(set.contains(fp(0)));
    assert!(set.contains(fp(u64::MAX)));

    // Re-inserting either should return false (already present)
    assert!(!set.insert(fp(0)).unwrap());
    assert!(!set.insert(fp(u64::MAX)).unwrap());

    // Also verify FP(u64::MAX - 1) is distinct from both
    assert!(set.insert(fp(u64::MAX - 1)).unwrap());
    assert_eq!(set.len(), 3);
    assert!(set.contains(fp(0)));
    assert!(set.contains(fp(u64::MAX - 1)));
    assert!(set.contains(fp(u64::MAX)));
}

/// Unit test for encode/decode round-trip on non-zero values.
/// FP(0) uses a separate has_zero flag and is not encoded.
///
/// The MSB (bit 63) is reserved for the flushed flag (TLC parity:
/// MSBDiskFPSet.MARK_FLUSHED), reducing effective FP space to 63 bits.
/// Values within 63-bit range round-trip exactly; values with MSB set
/// lose that bit on encoding (accepted trade-off, same as TLC).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_encode_decode_fingerprint_non_zero_roundtrip() {
    use crate::storage::open_addressing::FP_MASK;

    // Values within 63-bit space (no MSB set) round-trip exactly.
    // Note: u64::MAX / 2 == FP_MASK == 0x7FFFFFFFFFFFFFFF.
    let lossless_values: &[u64] = &[1, 2, FP_MASK / 2, FP_MASK - 1, FP_MASK];
    for &v in lossless_values {
        let encoded = encode_fingerprint(fp(v));
        assert_ne!(encoded, EMPTY, "FP({v}) must not encode to EMPTY sentinel");
        let decoded = decode_fingerprint(encoded);
        assert_eq!(
            decoded, v,
            "round-trip failed for FP({v}): encoded={encoded}, decoded={decoded}"
        );
    }

    // All lossless encodings must be distinct
    let encodings: Vec<u64> = lossless_values
        .iter()
        .map(|&v| encode_fingerprint(fp(v)))
        .collect();
    for i in 0..encodings.len() {
        for j in (i + 1)..encodings.len() {
            assert_ne!(
                encodings[i], encodings[j],
                "FP({}) and FP({}) must encode to different values, both got {}",
                lossless_values[i], lossless_values[j], encodings[i]
            );
        }
    }

    // Values with MSB set lose bit 63 (flushed flag reservation).
    // This is by design — TLC's MSBDiskFPSet uses the same 63-bit space.
    let msb_val = u64::MAX; // 0xFFFFFFFFFFFFFFFF
    let encoded_msb = encode_fingerprint(fp(msb_val));
    let decoded_msb = decode_fingerprint(encoded_msb);
    assert_eq!(decoded_msb, msb_val & FP_MASK, "MSB should be stripped");
    assert_ne!(decoded_msb, msb_val, "MSB loss is intentional");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_many_fingerprints() {
    let set = MmapFingerprintSet::new(10000, None).unwrap();

    // Insert 5000 fingerprints
    for i in 0..5000u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0); // Spread values
        assert!(set.insert(fp(v)).unwrap(), "failed to insert fp {}", i);
    }

    assert_eq!(set.len(), 5000);

    // Verify all present
    for i in 0..5000u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert!(set.contains(fp(v)), "missing fp {}", i);
    }

    // Verify non-present
    for i in 5000..5100u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert!(!set.contains(fp(v)), "unexpected fp {}", i);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_load_factor_limit() {
    // Small set with low load factor
    let set = MmapFingerprintSet::with_load_factor(100, None, 0.5).unwrap();

    // Insert 50 items (50% load factor)
    for i in 0..50u64 {
        set.insert(fp(i + 1)).unwrap(); // +1 to avoid 0
    }

    // Next insert should fail due to load factor
    let result = set.insert(fp(1000));
    assert!(
        result.is_err(),
        "expected TableFull error, got {:?}",
        result
    );

    match result {
        Err(MmapError::TableFull { count, capacity }) => {
            assert_eq!(count, 50);
            assert_eq!(capacity, 100);
        }
        _ => panic!("expected TableFull error"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_stats_report_resident_count_and_reserved_bytes() {
    let set = MmapFingerprintSet::new(128, None).expect("mmap storage should initialize");
    assert!(set.insert(fp(1)).expect("insert fp(1) should succeed"));
    assert!(set.insert(fp(2)).expect("insert fp(2) should succeed"));

    let stats = FingerprintSet::stats(&set);
    assert_eq!(stats.memory_count, 2);
    assert_eq!(stats.disk_count, 0);
    assert_eq!(stats.disk_lookups, 0);
    assert_eq!(stats.disk_hits, 0);
    assert_eq!(stats.eviction_count, 0);
    assert_eq!(stats.memory_bytes, 128 * std::mem::size_of::<u64>());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_concurrent_insert() {
    use std::sync::Arc;
    use std::thread;

    let set = Arc::new(MmapFingerprintSet::new(100000, None).unwrap());
    let num_threads = 8;
    let items_per_thread = 1000;

    let handles: Vec<_> = (0..num_threads)
        .map(|t| {
            let set = Arc::clone(&set);
            thread::spawn(move || {
                for i in 0..items_per_thread {
                    let v = (t * items_per_thread + i + 1) as u64;
                    let _ = set.insert(fp(v));
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(set.len(), num_threads * items_per_thread);

    // Verify all entries are actually findable, not just that the count is correct.
    // A concurrent insert bug could silently drop entries while incrementing the count.
    for t in 0..num_threads {
        for i in 0..items_per_thread {
            let v = (t * items_per_thread + i + 1) as u64;
            assert!(
                set.contains(fp(v)),
                "Entry fp({v}) missing after concurrent insert (thread {t}, item {i})"
            );
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_concurrent_contains() {
    use std::sync::Arc;
    use std::thread;

    let set = Arc::new(MmapFingerprintSet::new(10000, None).unwrap());

    // Pre-populate
    for i in 0..1000u64 {
        set.insert(fp(i + 1)).unwrap();
    }

    // Concurrent reads
    let handles: Vec<_> = (0..8)
        .map(|_| {
            let set = Arc::clone(&set);
            thread::spawn(move || {
                for i in 0..1000u64 {
                    assert!(set.contains(fp(i + 1)));
                }
                for i in 1000..2000u64 {
                    assert!(!set.contains(fp(i + 1)));
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_file_backed() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set = MmapFingerprintSet::new(1000, Some(tmp_dir.path().to_path_buf())).unwrap();

    assert!(set.insert(fp(12345)).unwrap());
    assert!(set.contains(fp(12345)));

    // Flush to ensure data is written
    set.flush().unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_trait_impl() {
    let set: Box<dyn FingerprintSet> = Box::new(MmapFingerprintSet::new(1000, None).unwrap());

    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(set.contains_checked(fp(12345)), LookupOutcome::Present);
    assert_eq!(set.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_dashset_trait_impl() {
    let set: Box<dyn FingerprintSet> = Box::new(dashmap::DashSet::<Fingerprint>::new());

    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(set.contains_checked(fp(12345)), LookupOutcome::Present);
    assert_eq!(set.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_in_memory() {
    let storage = FingerprintStorage::in_memory();

    assert!(storage.is_empty());
    assert_eq!(storage.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(
        storage.insert_checked(fp(12345)),
        InsertOutcome::AlreadyPresent
    ); // duplicate
    assert_eq!(storage.contains_checked(fp(12345)), LookupOutcome::Present);
    assert_eq!(storage.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_in_memory_stats_report_memory_counts() {
    let storage = FingerprintStorage::in_memory();

    assert_eq!(storage.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(storage.insert_checked(fp(67890)), InsertOutcome::Inserted);

    let stats = storage.stats();
    assert_eq!(stats.memory_count, 2);
    assert_eq!(stats.disk_count, 0);
    assert_eq!(stats.disk_lookups, 0);
    assert_eq!(stats.disk_hits, 0);
    assert_eq!(stats.eviction_count, 0);
    // Part of #4080: InMemory now reports memory_bytes estimated from capacity.
    // After inserting 2 entries, the HashSet has some internal capacity.
    // Just verify it's non-zero (exact value depends on hashbrown internals).
    assert!(
        stats.memory_bytes > 0,
        "InMemory stats should report non-zero memory_bytes, got {}",
        stats.memory_bytes
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_mmap() {
    let storage = FingerprintStorage::mmap(1000, None).unwrap();

    assert!(storage.is_empty());
    assert_eq!(storage.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(
        storage.insert_checked(fp(12345)),
        InsertOutcome::AlreadyPresent
    ); // duplicate
    assert_eq!(storage.contains_checked(fp(12345)), LookupOutcome::Present);
    assert_eq!(storage.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_disk() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let storage = FingerprintStorage::disk(100, tmp_dir.path()).unwrap();

    assert!(storage.is_empty());
    assert_eq!(storage.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(
        storage.insert_checked(fp(12345)),
        InsertOutcome::AlreadyPresent
    ); // duplicate
    assert_eq!(storage.contains_checked(fp(12345)), LookupOutcome::Present);
    assert_eq!(storage.len(), 1);

    // Insert more to trigger eviction
    for i in 1..=150 {
        storage.insert_checked(fp(i));
    }

    // Verify all are accessible
    for i in 1..=150 {
        assert_eq!(
            storage.contains_checked(fp(i)),
            LookupOutcome::Present,
            "Missing fingerprint {}",
            i
        );
    }

    // Disk storage reports Normal capacity (unlimited due to eviction)
    assert_eq!(storage.capacity_status(), CapacityStatus::Normal);
    assert!(!storage.has_errors());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_as_trait() {
    // Test that FingerprintStorage works as FingerprintSet
    let storage: Box<dyn FingerprintSet> = Box::new(FingerprintStorage::mmap(1000, None).unwrap());

    assert_eq!(storage.insert_checked(fp(111)), InsertOutcome::Inserted);
    assert_eq!(storage.contains_checked(fp(111)), LookupOutcome::Present);
    assert_eq!(storage.len(), 1);
}
