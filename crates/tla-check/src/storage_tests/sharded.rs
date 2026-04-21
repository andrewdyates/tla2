// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;

// ========== ShardedFingerprintSet tests ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_basic_operations() {
    let set = ShardedFingerprintSet::new(4); // 16 shards

    // Initially empty
    assert!(set.is_empty());
    assert_eq!(set.len(), 0);

    // Insert new fingerprint
    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(set.len(), 1);
    assert_eq!(set.contains_checked(fp(12345)), LookupOutcome::Present);

    // Insert same fingerprint again
    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::AlreadyPresent);
    assert_eq!(set.len(), 1);

    // Insert different fingerprint
    assert_eq!(set.insert_checked(fp(67890)), InsertOutcome::Inserted);
    assert_eq!(set.len(), 2);
    assert_eq!(set.contains_checked(fp(67890)), LookupOutcome::Present);

    // Check non-existent
    assert_eq!(set.contains_checked(fp(99999)), LookupOutcome::Absent);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_fingerprint_zero() {
    // Fingerprint 0 should work correctly
    let set = ShardedFingerprintSet::new(4);

    assert_eq!(set.contains_checked(fp(0)), LookupOutcome::Absent);
    assert_eq!(set.insert_checked(fp(0)), InsertOutcome::Inserted);
    assert_eq!(set.contains_checked(fp(0)), LookupOutcome::Present);
    assert_eq!(set.insert_checked(fp(0)), InsertOutcome::AlreadyPresent);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_many_fingerprints() {
    let set = ShardedFingerprintSet::new(6); // 64 shards

    // Insert 5000 fingerprints
    for i in 0..5000u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert_eq!(
            set.insert_checked(fp(v)),
            InsertOutcome::Inserted,
            "failed to insert fp {}",
            i
        );
    }

    assert_eq!(set.len(), 5000);

    // Verify all present
    for i in 0..5000u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert_eq!(
            set.contains_checked(fp(v)),
            LookupOutcome::Present,
            "missing fp {}",
            i
        );
    }

    // Verify non-present
    for i in 5000..5100u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert_eq!(
            set.contains_checked(fp(v)),
            LookupOutcome::Absent,
            "unexpected fp {}",
            i
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_concurrent_insert() {
    use std::sync::Arc;
    use std::thread;

    let set = Arc::new(ShardedFingerprintSet::new(6)); // 64 shards
    let num_threads = 8;
    let items_per_thread = 1000;

    let handles: Vec<_> = (0..num_threads)
        .map(|t| {
            let set = Arc::clone(&set);
            thread::spawn(move || {
                for i in 0..items_per_thread {
                    let v = (t * items_per_thread + i + 1) as u64;
                    let _ = set.insert_checked(fp(v));
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(set.len(), num_threads * items_per_thread);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_concurrent_contains() {
    use std::sync::Arc;
    use std::thread;

    let set = Arc::new(ShardedFingerprintSet::new(6));

    // Pre-populate
    for i in 0..1000u64 {
        set.insert_checked(fp(i + 1));
    }

    // Concurrent reads
    let handles: Vec<_> = (0..8)
        .map(|_| {
            let set = Arc::clone(&set);
            thread::spawn(move || {
                for i in 0..1000u64 {
                    assert_eq!(set.contains_checked(fp(i + 1)), LookupOutcome::Present);
                }
                for i in 1000..2000u64 {
                    assert_eq!(set.contains_checked(fp(i + 1)), LookupOutcome::Absent);
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
fn test_sharded_trait_impl() {
    let set: Box<dyn FingerprintSet> = Box::new(ShardedFingerprintSet::new(4));

    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(set.contains_checked(fp(12345)), LookupOutcome::Present);
    assert_eq!(set.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_with_shards() {
    let set = ShardedFingerprintSet::with_shards(32);
    assert_eq!(set.num_shards(), 32);
    assert_eq!(set.shard_bits(), 5); // log2(32) = 5

    let set2 = ShardedFingerprintSet::with_shards(64);
    assert_eq!(set2.num_shards(), 64);
    assert_eq!(set2.shard_bits(), 6); // log2(64) = 6
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "shard_bits must be 1-16")]
fn test_sharded_invalid_shard_bits_zero() {
    ShardedFingerprintSet::new(0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "shard_bits must be 1-16")]
fn test_sharded_invalid_shard_bits_too_large() {
    ShardedFingerprintSet::new(17);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "num_shards must be power of 2")]
fn test_sharded_with_shards_not_power_of_2() {
    ShardedFingerprintSet::with_shards(7);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_new_with_capacity() {
    // Part of #229: Test pre-allocated capacity for sharded storage
    let total_capacity = 1000;
    let shard_bits = 4; // 16 shards
    let set = ShardedFingerprintSet::new_with_capacity(shard_bits, total_capacity);

    assert_eq!(set.num_shards(), 16);
    assert_eq!(set.shard_bits(), 4);
    assert!(set.is_empty());

    // Insert many fingerprints (should not cause resize due to pre-allocation)
    for i in 0..800u64 {
        set.insert_checked(fp(i));
    }
    assert_eq!(set.len(), 800);

    // Verify all fingerprints are present
    for i in 0..800u64 {
        assert_eq!(
            set.contains_checked(fp(i)),
            LookupOutcome::Present,
            "should contain fp {}",
            i
        );
    }

    // Verify non-existent is not found
    assert_eq!(set.contains_checked(fp(9999)), LookupOutcome::Absent);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_with_capacity_distribution() {
    // Verify fingerprints distribute across shards (using MSB routing)
    let set = ShardedFingerprintSet::new_with_capacity(4, 10000); // 16 shards

    // Insert fingerprints with different high bits
    // Since we use MSB for routing, fingerprints with different high bits
    // should go to different shards
    for shard in 0..16u64 {
        // Create a fingerprint that will route to shard `shard`
        // Shift is 64 - 4 = 60, so high 4 bits determine shard
        let fp_val = shard << 60;
        set.insert_checked(fp(fp_val));
    }

    assert_eq!(set.len(), 16);

    // All should be present
    for shard in 0..16u64 {
        let fp_val = shard << 60;
        assert_eq!(set.contains_checked(fp(fp_val)), LookupOutcome::Present);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_trait_stats_report_memory_counts() {
    let set: Box<dyn FingerprintSet> = Box::new(ShardedFingerprintSet::new(4));

    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(set.contains_checked(fp(12345)), LookupOutcome::Present);

    let stats = FingerprintSet::stats(&*set);
    assert_eq!(stats.memory_count, 1);
    assert_eq!(stats.disk_count, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_disk_stats_aggregate_across_shards() {
    let tmp_dir = tempfile::tempdir().expect("tempdir should initialize");
    let set = ShardedFingerprintSet::new_disk(1, 16, tmp_dir.path())
        .expect("sharded disk storage should initialize");

    for i in 1..=40 {
        assert_eq!(set.insert_checked(fp(i)), InsertOutcome::Inserted);
    }
    assert_eq!(set.contains_checked(fp(1)), LookupOutcome::Present);

    let stats = FingerprintSet::stats(&set);
    assert!(
        stats.disk_count > 0,
        "disk-backed shards should report disk data"
    );
    assert!(
        stats.disk_lookups > 0,
        "disk-backed shards should aggregate lookups"
    );
    assert!(
        stats.disk_hits > 0,
        "disk-backed shards should aggregate hits"
    );
    assert!(
        stats.eviction_count > 0,
        "disk-backed shards should aggregate evictions"
    );
    assert_eq!(stats.memory_count + stats.disk_count, set.len());
}
