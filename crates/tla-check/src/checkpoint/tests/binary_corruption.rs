// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for binary I/O corruption detection: fingerprints, parents, depths.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_fingerprints_rejects_corrupted_length() {
    let dir = tempdir().unwrap();
    let fp_path = dir.path().join("fingerprints.bin");

    let mut data = Vec::new();
    data.extend_from_slice(binary_io::FINGERPRINT_MAGIC);
    data.extend_from_slice(&u64::MAX.to_le_bytes());
    fs::write(&fp_path, &data).unwrap();

    let err = Checkpoint::load_fingerprints(&fp_path).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("exceeds safety limit"),
        "error message should mention safety limit: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_fingerprints_rejects_payload_mismatch_length() {
    let dir = tempdir().unwrap();
    let fp_path = dir.path().join("fingerprints.bin");

    let mut data = Vec::new();
    data.extend_from_slice(binary_io::FINGERPRINT_MAGIC);
    data.extend_from_slice(&2u64.to_le_bytes());
    data.extend_from_slice(&Fingerprint(1).0.to_le_bytes());
    fs::write(&fp_path, &data).unwrap();

    let err = Checkpoint::load_fingerprints(&fp_path).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(
        err.to_string().contains("payload capacity"),
        "error should reference payload capacity: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_parents_rejects_corrupted_length() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("parents.bin");

    let mut data = Vec::new();
    data.extend_from_slice(binary_io::PARENTS_MAGIC);
    data.extend_from_slice(&(binary_io::MAX_BINARY_ENTRIES + 1).to_le_bytes());
    fs::write(&path, &data).unwrap();

    let err = Checkpoint::load_parents(&path).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err.to_string().contains("exceeds safety limit"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_parents_rejects_payload_mismatch_length() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("parents.bin");

    let mut data = Vec::new();
    data.extend_from_slice(binary_io::PARENTS_MAGIC);
    data.extend_from_slice(&2u64.to_le_bytes());
    data.extend_from_slice(&Fingerprint(2).0.to_le_bytes());
    data.extend_from_slice(&Fingerprint(1).0.to_le_bytes());
    fs::write(&path, &data).unwrap();

    let err = Checkpoint::load_parents(&path).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err.to_string().contains("payload capacity"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_depths_rejects_corrupted_length() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("depths.bin");

    let mut data = Vec::new();
    data.extend_from_slice(binary_io::DEPTHS_MAGIC);
    data.extend_from_slice(&(binary_io::MAX_BINARY_ENTRIES + 1).to_le_bytes());
    fs::write(&path, &data).unwrap();

    let err = Checkpoint::load_depths(&path).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err.to_string().contains("exceeds safety limit"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_depths_rejects_payload_mismatch_length() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("depths.bin");

    let mut data = Vec::new();
    data.extend_from_slice(binary_io::DEPTHS_MAGIC);
    data.extend_from_slice(&2u64.to_le_bytes());
    data.extend_from_slice(&Fingerprint(1).0.to_le_bytes());
    data.extend_from_slice(&0u64.to_le_bytes());
    fs::write(&path, &data).unwrap();

    let err = Checkpoint::load_depths(&path).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert!(err.to_string().contains("payload capacity"));
}
