// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;

// ========== Memory safety tests for mmap storage ==========

/// Verify that the mmap base pointer is properly aligned for AtomicU64 access.
///
/// The unsafe slot()/fp_slot()/offset_slot() methods cast the mmap pointer to
/// `*const AtomicU64`. This requires 8-byte alignment. While mmap returns
/// page-aligned memory (typically 4096 bytes), this test makes the invariant
/// explicit and guards against future changes that could break alignment.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_alignment_for_atomic_u64() {
    // Test anonymous mmap (in-memory)
    let set = MmapFingerprintSet::new(100, None).unwrap();
    let ptr = set.mmap.as_ptr();
    assert_eq!(
        ptr as usize % std::mem::align_of::<AtomicU64>(),
        0,
        "MmapFingerprintSet anonymous mmap base pointer is not aligned for AtomicU64 \
         (alignment: {}, ptr: {:p})",
        std::mem::align_of::<AtomicU64>(),
        ptr
    );

    // Test file-backed mmap
    let tmp_dir = tempfile::tempdir().unwrap();
    let set_fb = MmapFingerprintSet::new(100, Some(tmp_dir.path().to_path_buf())).unwrap();
    let ptr_fb = set_fb.mmap.as_ptr();
    assert_eq!(
        ptr_fb as usize % std::mem::align_of::<AtomicU64>(),
        0,
        "MmapFingerprintSet file-backed mmap base pointer is not aligned for AtomicU64 \
         (alignment: {}, ptr: {:p})",
        std::mem::align_of::<AtomicU64>(),
        ptr_fb
    );

    // Test MmapTraceLocations anonymous mmap
    let locs = MmapTraceLocations::new(100, None).unwrap();
    let ptr_locs = locs.mmap.as_ptr();
    assert_eq!(
        ptr_locs as usize % std::mem::align_of::<AtomicU64>(),
        0,
        "MmapTraceLocations anonymous mmap base pointer is not aligned for AtomicU64 \
         (alignment: {}, ptr: {:p})",
        std::mem::align_of::<AtomicU64>(),
        ptr_locs
    );

    // Test MmapTraceLocations file-backed mmap
    let locs_fb = MmapTraceLocations::new(100, Some(tmp_dir.path().to_path_buf())).unwrap();
    let ptr_locs_fb = locs_fb.mmap.as_ptr();
    assert_eq!(
        ptr_locs_fb as usize % std::mem::align_of::<AtomicU64>(),
        0,
        "MmapTraceLocations file-backed mmap base pointer is not aligned for AtomicU64 \
         (alignment: {}, ptr: {:p})",
        std::mem::align_of::<AtomicU64>(),
        ptr_locs_fb
    );
}

/// Verify that the highest-index slot access in MmapTraceLocations is within
/// the allocated mmap region.
///
/// MmapTraceLocations uses a 2-word stride: fp_slot accesses `index * 2` and
/// offset_slot accesses `index * 2 + 1`. The highest valid index is
/// `capacity - 1`, so the last byte accessed is at offset
/// `((capacity - 1) * 2 + 1 + 1) * 8 = capacity * 16`.
/// The mmap region is allocated as `capacity * TRACE_ENTRY_SIZE` = `capacity * 16`.
/// This test verifies boundary access doesn't overrun.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_trace_boundary_index_slot_access() {
    // Use a small capacity to make the boundary test meaningful
    let capacity = 7;
    let locs = MmapTraceLocations::new(capacity, None).unwrap();

    // Insert at high-index positions by using fingerprints that hash near the end
    // We verify the boundary by inserting and reading back at every possible index
    // through the hash table probing mechanism.
    for i in 1..=5u64 {
        // Use values that will land at different indices
        assert!(
            locs.insert(fp(i), i * 100).unwrap(),
            "failed to insert fp({})",
            i
        );
    }

    // Read them all back to exercise both fp_slot and offset_slot at various indices
    for i in 1..=5u64 {
        assert_eq!(
            locs.get(&fp(i)),
            Some(i * 100),
            "wrong offset for fp({})",
            i
        );
    }

    // Also verify direct boundary: capacity-1 is the maximum index passed to
    // fp_slot/offset_slot (via `% capacity`). We can't call these directly
    // (they're private), but we can verify the mmap size is sufficient.
    let mmap_len = locs.mmap.len();
    let required_bytes = capacity * TRACE_ENTRY_SIZE;
    assert_eq!(
        mmap_len, required_bytes,
        "mmap region size ({mmap_len}) must equal capacity * TRACE_ENTRY_SIZE ({required_bytes})"
    );

    // The highest slot address is ((capacity - 1) * 2 + 1) * 8 + 8 (one u64 past)
    let highest_byte_accessed = ((capacity - 1) * 2 + 2) * 8;
    assert!(
        highest_byte_accessed <= mmap_len,
        "highest slot access ({highest_byte_accessed}) exceeds mmap region ({mmap_len})"
    );
}

/// Concurrent insert test for MmapTraceLocations.
///
/// Mirrors test_mmap_concurrent_insert for MmapFingerprintSet but exercises
/// the two-word (fingerprint + offset) insert path. Each thread inserts
/// distinct fingerprints with distinct offsets, then all threads verify
/// all entries are present with correct offsets.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_mmap_trace_concurrent_insert() {
    use std::sync::Arc;
    use std::thread;

    let locs = Arc::new(MmapTraceLocations::new(100_000, None).unwrap());
    let num_threads = 8;
    let items_per_thread = 1000;

    // Phase 1: Concurrent inserts
    let handles: Vec<_> = (0..num_threads)
        .map(|t| {
            let locs = Arc::clone(&locs);
            thread::spawn(move || {
                for i in 0..items_per_thread {
                    let v = (t * items_per_thread + i + 1) as u64;
                    let offset = v * 16; // Distinct offset per fingerprint
                    let _ = locs.insert(fp(v), offset);
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(
        locs.len(),
        num_threads * items_per_thread,
        "total count after concurrent inserts"
    );

    // Phase 2: Concurrent reads — verify all entries have correct offsets
    let handles: Vec<_> = (0..num_threads)
        .map(|_| {
            let locs = Arc::clone(&locs);
            thread::spawn(move || {
                let mut mismatches = Vec::new();
                for t in 0..num_threads {
                    for i in 0..items_per_thread {
                        let v = (t * items_per_thread + i + 1) as u64;
                        let expected_offset = v * 16;
                        match locs.get(&fp(v)) {
                            Some(actual) if actual == expected_offset => {}
                            Some(actual) => {
                                mismatches.push((v, expected_offset, actual));
                            }
                            None => {
                                mismatches.push((v, expected_offset, u64::MAX));
                            }
                        }
                    }
                }
                mismatches
            })
        })
        .collect();

    for h in handles {
        let mismatches = h.join().unwrap();
        assert!(
            mismatches.is_empty(),
            "Offset mismatches found (first 5): {:?}",
            &mismatches[..mismatches.len().min(5)]
        );
    }
}

/// Offset encoding for atomicity tests: fp_value * 7 + 1 (never zero).
fn atomicity_test_offset(fp_value: u64) -> u64 {
    fp_value * 7 + 1
}

/// Test concurrent mixed insert + get on MmapTraceLocations (#2138).
///
/// Targets the atomicity gap: CAS writes fingerprint, then separate store
/// writes offset. Concurrent readers may see the fingerprint but read
/// stale-zero offset. We verify no corrupted (non-zero wrong) offsets appear
/// and that all entries are correct after writers complete.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_mmap_trace_concurrent_insert_and_get_atomicity() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;
    use std::thread;

    let locs = Arc::new(MmapTraceLocations::new(100_000, None).unwrap());
    let done = Arc::new(AtomicBool::new(false));
    let num_writers: usize = 4;
    let items_per_writer: usize = 2000;
    let total_items = num_writers * items_per_writer;

    // Writers: insert with non-zero offsets so stale-zero reads are detectable
    let writer_handles: Vec<_> = (0..num_writers)
        .map(|t| {
            let locs = Arc::clone(&locs);
            let done = Arc::clone(&done);
            thread::spawn(move || {
                for i in 0..items_per_writer {
                    let v = (t * items_per_writer + i + 1) as u64;
                    let _ = locs.insert(fp(v), atomicity_test_offset(v));
                }
                done.store(true, Ordering::Release);
            })
        })
        .collect();

    // Readers: probe entries concurrently with writers
    let reader_handles: Vec<_> = (0..4)
        .map(|_| {
            let (locs, done) = (Arc::clone(&locs), Arc::clone(&done));
            thread::spawn(move || {
                let mut wrong = 0u64;
                while !done.load(Ordering::Acquire) {
                    for v in 1..=total_items as u64 {
                        if let Some(off) = locs.get(&fp(v)) {
                            if off != 0 && off != atomicity_test_offset(v) {
                                wrong += 1;
                            }
                        }
                    }
                }
                wrong
            })
        })
        .collect();

    for h in writer_handles {
        h.join().unwrap();
    }
    let total_wrong: u64 = reader_handles.into_iter().map(|h| h.join().unwrap()).sum();

    assert_eq!(
        total_wrong, 0,
        "corrupted (non-zero wrong) offsets detected"
    );

    // Post-completion: all entries must have correct offsets
    for v in 1..=total_items as u64 {
        let expected = atomicity_test_offset(v);
        assert_eq!(locs.get(&fp(v)), Some(expected), "fp({v})");
    }
}

/// Verify that MmapFingerprintSet::slot() bounds are consistent with mmap size.
///
/// The slot() method uses `ptr.add(index)` where index is always computed as
/// `(start + probe) % capacity`. This test verifies that `capacity * 8` equals
/// the mmap length, ensuring all valid indices access memory within bounds.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_fingerprint_set_slot_bounds_consistency() {
    for &capacity in &[1, 7, 100, 1024, 65536] {
        let set = MmapFingerprintSet::new(capacity, None).unwrap();
        let mmap_len = set.mmap.len();
        let expected_len = capacity * 8; // 8 bytes per u64 slot
        assert_eq!(
            mmap_len, expected_len,
            "capacity={capacity}: mmap len ({mmap_len}) != capacity * 8 ({expected_len})"
        );
    }
}

/// Verify that MmapTraceLocations slot bounds are consistent for various capacities.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_trace_locations_slot_bounds_consistency() {
    for &capacity in &[1, 7, 100, 1024, 65536] {
        let locs = MmapTraceLocations::new(capacity, None).unwrap();
        let mmap_len = locs.mmap.len();
        let expected_len = capacity * TRACE_ENTRY_SIZE;
        assert_eq!(
            mmap_len, expected_len,
            "capacity={capacity}: mmap len ({mmap_len}) != capacity * TRACE_ENTRY_SIZE ({expected_len})"
        );

        // Verify the highest index * 2 + 1 fits within the allocation
        // (capacity - 1) * 2 + 1 is the max AtomicU64 index, each taking 8 bytes
        let max_u64_index = (capacity - 1) * 2 + 1;
        let max_byte_offset = (max_u64_index + 1) * 8; // one past last accessed byte
        assert!(
            max_byte_offset <= mmap_len,
            "capacity={capacity}: max byte offset ({max_byte_offset}) exceeds mmap len ({mmap_len})"
        );
    }
}

/// Part of #2058: Verify that MmapFingerprintSet returns ProbeExceeded (not TableFull)
/// when all slots are occupied but the load factor check passes.
/// This validates that DiskFingerprintSet's explicit match on MmapError variants
/// would correctly distinguish probe exhaustion from table-full conditions.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_mmap_probe_exceeded_distinct_from_table_full() {
    // Use load_factor > 1.0 so the load-factor pre-check never fires,
    // even when the table is completely full.
    let capacity = 128;
    let set = MmapFingerprintSet::with_load_factor(capacity, None, 2.0).unwrap();

    // Fill all slots. Some inserts may fail if the hash function causes
    // probe exhaustion before we fill all slots; use a large range to ensure
    // we fill the table.
    let mut inserted = 0;
    for i in 1..=10_000u64 {
        match set.insert(fp(i)) {
            Ok(true) => {
                inserted += 1;
                if inserted >= capacity {
                    break;
                }
            }
            Ok(false) => {} // duplicate
            Err(_) => {}    // table issues, keep trying different fps
        }
    }
    assert!(
        inserted >= capacity - 1,
        "Should have filled most of the table: inserted={inserted}, capacity={capacity}"
    );

    // Now try to insert a new fingerprint. With all slots occupied,
    // the probe sequence exhausts MAX_PROBE and returns ProbeExceeded.
    let mut saw_probe_exceeded = false;
    for i in 10_001..=20_000u64 {
        match set.insert(fp(i)) {
            Err(MmapError::ProbeExceeded { .. }) => {
                saw_probe_exceeded = true;
                break;
            }
            Err(MmapError::TableFull { .. }) => {
                panic!("Should not get TableFull with load_factor=2.0 and count < 2*capacity");
            }
            Ok(_) => {} // might still find a slot via duplicate or rare empty
        }
    }
    assert!(
        saw_probe_exceeded,
        "Should observe ProbeExceeded when all probe slots are occupied"
    );

    // Verify the error preserves detail when surfaced as StorageFault
    // via the FingerprintSet trait's insert_checked.
    let trait_set: &dyn FingerprintSet = &set;
    for i in 20_001..=30_000u64 {
        match trait_set.insert_checked(fp(i)) {
            InsertOutcome::StorageFault(fault) => {
                assert_eq!(fault.backend, "mmap");
                assert_eq!(fault.operation, "insert");
                assert!(
                    fault.detail.contains("probe") || fault.detail.contains("exceeded"),
                    "StorageFault detail should mention probe exhaustion: {}",
                    fault.detail
                );
                break;
            }
            InsertOutcome::Inserted | InsertOutcome::AlreadyPresent => {}
            _ => unreachable!(),
        }
    }
}
