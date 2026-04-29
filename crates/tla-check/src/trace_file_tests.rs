// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `TraceFile` disk-based trace storage.

use super::*;
use tempfile::tempdir;

fn fp(v: u64) -> Fingerprint {
    Fingerprint(v)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_file_create() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let trace = TraceFile::create(&path).unwrap();

    assert!(path.exists());
    assert_eq!(trace.record_count(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_write_initial_state() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    let loc = trace.write_initial(fp(12345)).unwrap();
    assert_eq!(loc, 0); // First record at offset 0
    assert_eq!(trace.record_count(), 1);

    // Write another initial state
    let loc2 = trace.write_initial(fp(67890)).unwrap();
    assert_eq!(loc2, 16); // Second record at offset 16
    assert_eq!(trace.record_count(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_write_successor_state() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    let init_loc = trace.write_initial(fp(100)).unwrap();
    let succ_loc = trace.write_state(init_loc, fp(200)).unwrap();

    assert_eq!(init_loc, 0);
    assert_eq!(succ_loc, 16);
    assert_eq!(trace.record_count(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_read_record() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    let init_loc = trace.write_initial(fp(100)).unwrap();
    let succ_loc = trace.write_state(init_loc, fp(200)).unwrap();

    // Read initial state
    let (pred, fingerprint) = trace.read_record(init_loc).unwrap();
    assert_eq!(pred, NO_PREDECESSOR);
    assert_eq!(fingerprint, fp(100));

    // Read successor state
    let (pred, fingerprint) = trace.read_record(succ_loc).unwrap();
    assert_eq!(pred, init_loc);
    assert_eq!(fingerprint, fp(200));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_fingerprint_path_single() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    let init_loc = trace.write_initial(fp(100)).unwrap();

    let fps = trace.get_fingerprint_path(init_loc).unwrap();
    assert_eq!(fps, vec![fp(100)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_fingerprint_path_chain() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    // Build a chain: 100 -> 200 -> 300 -> 400
    let loc0 = trace.write_initial(fp(100)).unwrap();
    let loc1 = trace.write_state(loc0, fp(200)).unwrap();
    let loc2 = trace.write_state(loc1, fp(300)).unwrap();
    let loc3 = trace.write_state(loc2, fp(400)).unwrap();

    // Get path to end
    let fps = trace.get_fingerprint_path(loc3).unwrap();
    assert_eq!(fps, vec![fp(100), fp(200), fp(300), fp(400)]);

    // Get path to middle
    let fps = trace.get_fingerprint_path(loc2).unwrap();
    assert_eq!(fps, vec![fp(100), fp(200), fp(300)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_fingerprint_path_branching() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    // Build a tree:
    //       100
    //      /   \
    //    200   300
    //    /
    //  400
    let loc0 = trace.write_initial(fp(100)).unwrap();
    let loc1 = trace.write_state(loc0, fp(200)).unwrap();
    let loc2 = trace.write_state(loc0, fp(300)).unwrap();
    let loc3 = trace.write_state(loc1, fp(400)).unwrap();

    // Path to 400 (through 200)
    let fps = trace.get_fingerprint_path(loc3).unwrap();
    assert_eq!(fps, vec![fp(100), fp(200), fp(400)]);

    // Path to 300 (direct from 100)
    let fps = trace.get_fingerprint_path(loc2).unwrap();
    assert_eq!(fps, vec![fp(100), fp(300)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations() {
    let mut locs = TraceLocations::new();

    assert!(locs.is_empty());

    locs.insert(fp(100), 0);
    locs.insert(fp(200), 16);

    assert_eq!(locs.len(), 2);
    assert!(locs.contains(&fp(100)));
    assert!(locs.contains(&fp(200)));
    assert!(!locs.contains(&fp(300)));

    assert_eq!(locs.get(&fp(100)), Some(0));
    assert_eq!(locs.get(&fp(200)), Some(16));
    assert_eq!(locs.get(&fp(300)), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_large_trace() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    // Build a long chain
    let mut prev_loc = trace.write_initial(fp(0)).unwrap();
    for i in 1..1000u64 {
        prev_loc = trace.write_state(prev_loc, fp(i)).unwrap();
    }

    assert_eq!(trace.record_count(), 1000);

    // Reconstruct full path
    let fps = trace.get_fingerprint_path(prev_loc).unwrap();
    assert_eq!(fps.len(), 1000);
    for (i, fp) in fps.iter().enumerate() {
        assert_eq!(fp.0, i as u64);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temp_file() {
    let path;
    {
        let mut trace = TraceFile::create_temp().unwrap();

        let loc = trace.write_initial(fp(12345)).unwrap();
        assert_eq!(trace.record_count(), 1);

        let fps = trace.get_fingerprint_path(loc).unwrap();
        assert_eq!(fps, vec![fp(12345)]);

        // File should exist while trace is alive
        assert!(trace.path().exists());
        path = trace.path().to_path_buf();
    }
    // File should be deleted after drop
    assert!(!path.exists());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_explicit_path_not_deleted_on_drop() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    {
        let mut trace = TraceFile::create(&path).unwrap();
        trace.write_initial(fp(100)).unwrap();
    }
    // Explicitly created files should NOT be deleted on drop
    assert!(path.exists());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_fingerprint_path_rejects_unaligned_offset() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();
    trace.write_initial(fp(100)).unwrap();

    // Offset 7 is not aligned to RECORD_SIZE (16)
    let err = trace.get_fingerprint_path(7).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    assert!(err.to_string().contains("not aligned"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_fingerprint_path_detects_cycle() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");

    // Manually write records that form a cycle:
    // Record 0 (offset 0): predecessor=16, fp=100
    // Record 1 (offset 16): predecessor=0, fp=200
    // This creates a cycle: record 0 -> record 1 -> record 0 -> ...
    {
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&path)
            .unwrap();
        let mut writer = std::io::BufWriter::new(file);

        // Record 0: predecessor = 16 (points to record 1)
        writer.write_all(&16u64.to_le_bytes()).unwrap();
        writer.write_all(&100u64.to_le_bytes()).unwrap();

        // Record 1: predecessor = 0 (points to record 0 — cycle!)
        writer.write_all(&0u64.to_le_bytes()).unwrap();
        writer.write_all(&200u64.to_le_bytes()).unwrap();

        writer.flush().unwrap();
    }

    // Open via TraceFile — write_pos must reflect the 2 existing records
    // so record_count() is correct for cycle detection.
    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&path)
        .unwrap();
    let metadata = file.metadata().unwrap();
    let mut trace = TraceFile {
        path: path.clone(),
        writer: std::io::BufWriter::new(file),
        write_pos: metadata.len(),
        delete_on_drop: false,
    };
    assert_eq!(trace.record_count(), 2);

    // Walking from record 1 should detect the cycle
    let err = trace.get_fingerprint_path(16).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err.to_string().contains("cycle detected"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_fingerprint_path_detects_corrupted_predecessor_alignment() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");

    // Manually write records where predecessor has bad alignment:
    // Record 0 (offset 0): predecessor=NO_PREDECESSOR, fp=100 (valid initial)
    // Record 1 (offset 16): predecessor=5 (misaligned!), fp=200
    {
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&path)
            .unwrap();
        let mut writer = std::io::BufWriter::new(file);

        // Record 0: valid initial state
        writer.write_all(&NO_PREDECESSOR.to_le_bytes()).unwrap();
        writer.write_all(&100u64.to_le_bytes()).unwrap();

        // Record 1: corrupted predecessor (offset 5, not aligned)
        writer.write_all(&5u64.to_le_bytes()).unwrap();
        writer.write_all(&200u64.to_le_bytes()).unwrap();

        writer.flush().unwrap();
    }

    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&path)
        .unwrap();
    let metadata = file.metadata().unwrap();
    let mut trace = TraceFile {
        path: path.clone(),
        writer: std::io::BufWriter::new(file),
        write_pos: metadata.len(),
        delete_on_drop: false,
    };

    let err = trace.get_fingerprint_path(16).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err.to_string().contains("not aligned"));
}

/// Part of #2881: read_all_records scans the trace file and returns
/// (fingerprint, offset) pairs. This is used by the lazy trace index
/// to build the fp→location map on demand.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_read_all_records_empty() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    let records = trace.read_all_records().unwrap();
    assert!(records.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_read_all_records_single() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    trace.write_initial(fp(100)).unwrap();

    let records = trace.read_all_records().unwrap();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0], (fp(100), 0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_read_all_records_chain() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    let loc0 = trace.write_initial(fp(100)).unwrap();
    let _loc1 = trace.write_state(loc0, fp(200)).unwrap();
    let _loc2 = trace.write_state(loc0, fp(300)).unwrap();

    let records = trace.read_all_records().unwrap();
    assert_eq!(records.len(), 3);
    assert_eq!(records[0], (fp(100), 0));
    assert_eq!(records[1], (fp(200), 16));
    assert_eq!(records[2], (fp(300), 32));
}

/// Verify read_all_records produces the same fp→offset mapping as
/// manually tracking write locations — ensuring the lazy trace index
/// produces an equivalent index to eager insertion.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_read_all_records_matches_eager_index() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.st");
    let mut trace = TraceFile::create(&path).unwrap();

    // Build a branching trace and track locations eagerly
    let mut eager_index = std::collections::HashMap::new();
    let loc0 = trace.write_initial(fp(10)).unwrap();
    eager_index.insert(fp(10), loc0);
    let loc1 = trace.write_state(loc0, fp(20)).unwrap();
    eager_index.insert(fp(20), loc1);
    let loc2 = trace.write_state(loc0, fp(30)).unwrap();
    eager_index.insert(fp(30), loc2);
    let loc3 = trace.write_state(loc1, fp(40)).unwrap();
    eager_index.insert(fp(40), loc3);
    let loc4 = trace.write_state(loc2, fp(50)).unwrap();
    eager_index.insert(fp(50), loc4);

    // Lazy scan should produce the same mapping
    let records = trace.read_all_records().unwrap();
    let lazy_index: std::collections::HashMap<_, _> = records.into_iter().collect();

    assert_eq!(eager_index.len(), lazy_index.len());
    for (fp, expected_loc) in &eager_index {
        assert_eq!(
            lazy_index.get(fp),
            Some(expected_loc),
            "fp {:?} location mismatch: eager={}, lazy={:?}",
            fp,
            expected_loc,
            lazy_index.get(fp)
        );
    }
}
