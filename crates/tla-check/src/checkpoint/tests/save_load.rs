// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for checkpoint save/load lifecycle, first_violation persistence,
//! binary fingerprint format, atomic save recovery, and fsync roundtrip.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_load() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(100), Fingerprint(200), Fingerprint(300)];

    let mut state = State::new();
    state = state.with_var("x", Value::int(42));
    checkpoint.frontier = vec![state];

    checkpoint
        .parents
        .insert(Fingerprint(200), Fingerprint(100));
    checkpoint
        .parents
        .insert(Fingerprint(300), Fingerprint(200));

    checkpoint.depths.insert(Fingerprint(100), 0);
    checkpoint.depths.insert(Fingerprint(200), 1);
    checkpoint.depths.insert(Fingerprint(300), 2);

    checkpoint.save(&checkpoint_dir).unwrap();

    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();

    assert_eq!(loaded.fingerprints.len(), 3);
    assert_eq!(loaded.frontier.len(), 1);
    assert_eq!(loaded.parents.len(), 2);
    assert_eq!(loaded.depths.len(), 3);

    assert_eq!(
        loaded.parents.get(&Fingerprint(200)),
        Some(&Fingerprint(100))
    );
    assert_eq!(loaded.depths.get(&Fingerprint(300)), Some(&2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprints_binary_format() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("fingerprints.bin");

    let checkpoint = Checkpoint {
        metadata: CheckpointMetadata {
            version: CHECKPOINT_VERSION,
            created_at: "0".to_string(),
            spec_path: None,
            config_path: None,
            spec_hash: None,
            config_hash: None,
            stats: CheckpointStats::default(),
        },
        fingerprints: vec![
            Fingerprint(0x1234567890ABCDEF),
            Fingerprint(0xFEDCBA0987654321),
        ],
        frontier: vec![],
        parents: HashMap::new(),
        depths: HashMap::new(),
        first_violation: None,
        first_action_property_violation: None,
        first_violation_trace: Vec::new(),
    };

    checkpoint.save_fingerprints(&path).unwrap();
    let loaded = Checkpoint::load_fingerprints(&path).unwrap();

    assert_eq!(loaded.len(), 2);
    assert_eq!(loaded[0].0, 0x1234567890ABCDEF);
    assert_eq!(loaded[1].0, 0xFEDCBA0987654321);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_load_with_first_violation() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(100)];
    checkpoint.depths.insert(Fingerprint(100), 0);
    checkpoint.first_violation = Some(("InvariantX".to_string(), Fingerprint(100)));

    checkpoint.save(&checkpoint_dir).unwrap();
    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();

    let (invariant, fp) = loaded
        .first_violation
        .expect("first_violation should persist");
    assert_eq!(invariant, "InvariantX");
    assert_eq!(fp, Fingerprint(100));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_load_with_first_action_property_violation() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(101)];
    checkpoint.depths.insert(Fingerprint(101), 0);
    checkpoint.first_action_property_violation = Some(("PropX".to_string(), Fingerprint(101)));

    checkpoint.save(&checkpoint_dir).unwrap();
    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();

    let (property, fp) = loaded
        .first_action_property_violation
        .expect("first_action_property_violation should persist");
    assert_eq!(property, "PropX");
    assert_eq!(fp, Fingerprint(101));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_load_with_first_violation_trace() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut first = State::new();
    first = first.with_var("x", Value::int(0));
    let mut second = State::new();
    second = second.with_var("x", Value::int(1));
    let expected_trace = vec![first, second];

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(100)];
    checkpoint.depths.insert(Fingerprint(100), 0);
    checkpoint.first_violation = Some(("InvariantX".to_string(), Fingerprint(100)));
    checkpoint.first_violation_trace = expected_trace.clone();

    checkpoint.save(&checkpoint_dir).unwrap();
    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();

    assert_eq!(loaded.first_violation_trace, expected_trace);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_load_without_first_violation_is_backwards_compatible() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let checkpoint = Checkpoint::new();
    checkpoint.save(&checkpoint_dir).unwrap();

    let violation_path = checkpoint_dir.join("first_violation.json");
    assert!(!violation_path.exists(), "no violation file when None");

    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();
    assert!(loaded.first_violation.is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_clears_stale_first_violation() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(100)];
    checkpoint.depths.insert(Fingerprint(100), 0);
    checkpoint.first_violation = Some(("StaleInvariant".to_string(), Fingerprint(100)));
    checkpoint.save(&checkpoint_dir).unwrap();

    let violation_path = checkpoint_dir.join("first_violation.json");
    assert!(
        violation_path.exists(),
        "violation file should exist after first save"
    );

    let mut checkpoint2 = Checkpoint::new();
    checkpoint2.fingerprints = vec![Fingerprint(200)];
    checkpoint2.depths.insert(Fingerprint(200), 0);
    checkpoint2.save(&checkpoint_dir).unwrap();

    assert!(
        !violation_path.exists(),
        "stale violation file must be removed"
    );

    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();
    assert!(
        loaded.first_violation.is_none(),
        "loaded checkpoint must not have stale first_violation"
    );
}

/// Regression test for #1780: save() must not leave stale .saving or .old
/// directories after a successful save.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_atomic_save_no_stale_temp_dirs() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(42)];
    checkpoint.depths.insert(Fingerprint(42), 0);

    checkpoint.save(&checkpoint_dir).unwrap();
    assert!(checkpoint_dir.exists());
    assert!(!checkpoint_dir.with_extension("saving").exists());
    assert!(!checkpoint_dir.with_extension("old").exists());

    checkpoint.fingerprints.push(Fingerprint(99));
    checkpoint.depths.insert(Fingerprint(99), 1);
    checkpoint.save(&checkpoint_dir).unwrap();
    assert!(checkpoint_dir.exists());
    assert!(!checkpoint_dir.with_extension("saving").exists());
    assert!(!checkpoint_dir.with_extension("old").exists());

    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();
    assert_eq!(loaded.fingerprints.len(), 2);
}

/// Regression test for #1780: load() recovers from interrupted save.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_load_recovers_from_interrupted_save() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");
    let old_dir = checkpoint_dir.with_extension("old");

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(77)];
    checkpoint.depths.insert(Fingerprint(77), 0);
    checkpoint.save(&checkpoint_dir).unwrap();

    fs::rename(&checkpoint_dir, &old_dir).unwrap();
    assert!(!checkpoint_dir.exists());
    assert!(old_dir.exists());

    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();
    assert_eq!(loaded.fingerprints.len(), 1);
    assert_eq!(loaded.fingerprints[0], Fingerprint(77));
    assert!(!old_dir.exists());
}

/// Regression test for #1780: save() cleans up stale .saving dir.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_cleans_stale_saving_dir() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");
    let saving_dir = checkpoint_dir.with_extension("saving");

    fs::create_dir_all(&saving_dir).unwrap();
    fs::write(saving_dir.join("garbage.txt"), b"stale data").unwrap();

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(88)];
    checkpoint.depths.insert(Fingerprint(88), 0);

    checkpoint.save(&checkpoint_dir).unwrap();
    assert!(checkpoint_dir.exists());
    assert!(!saving_dir.exists());

    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();
    assert_eq!(loaded.fingerprints.len(), 1);
}

/// Unit test for `compute_file_hash`: known content produces expected SHA-256 digest.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compute_file_hash_returns_expected_sha256() {
    use std::io::Write;
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.tla");
    {
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(b"hello world").unwrap();
    }
    let hash = compute_file_hash(&path).expect("should compute hash of existing file");
    // SHA-256("hello world") is a well-known value.
    assert_eq!(
        hash,
        "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
    );
}

/// `compute_file_hash` returns `None` for non-existent files instead of erroring.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compute_file_hash_returns_none_for_missing_file() {
    let result = compute_file_hash(std::path::Path::new("/nonexistent/file.tla"));
    assert!(result.is_none(), "should return None for missing file");
}

/// Content hash is included in checkpoint metadata when spec/config paths
/// point to real files.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_load_preserves_content_hashes() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let spec_hash = "abc123".to_string();
    let config_hash = "def456".to_string();

    let mut checkpoint = Checkpoint::new();
    checkpoint.metadata.spec_hash = Some(spec_hash.clone());
    checkpoint.metadata.config_hash = Some(config_hash.clone());

    checkpoint.save(&checkpoint_dir).unwrap();
    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();

    assert_eq!(loaded.metadata.spec_hash.as_deref(), Some("abc123"));
    assert_eq!(loaded.metadata.config_hash.as_deref(), Some("def456"));
}

/// Checkpoints without content hashes (old format) load successfully with None hashes.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_load_without_hashes_backwards_compatible() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    // Save a checkpoint without hashes (the default)
    let checkpoint = Checkpoint::new();
    checkpoint.save(&checkpoint_dir).unwrap();

    // Verify the JSON doesn't contain hash fields (skip_serializing_if)
    let meta_json = std::fs::read_to_string(checkpoint_dir.join("checkpoint.json")).unwrap();
    assert!(
        !meta_json.contains("spec_hash"),
        "checkpoint.json should not contain spec_hash when None"
    );
    assert!(
        !meta_json.contains("config_hash"),
        "checkpoint.json should not contain config_hash when None"
    );

    // Load should succeed with None hashes
    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();
    assert!(loaded.metadata.spec_hash.is_none());
    assert!(loaded.metadata.config_hash.is_none());
}

/// Verify checkpoint save produces files that survive fsync roundtrip.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_save_fsync_roundtrip() {
    let dir = tempdir().unwrap();
    let checkpoint_dir = dir.path().join("checkpoint");

    let mut checkpoint = Checkpoint::new();
    checkpoint.fingerprints = vec![Fingerprint(1), Fingerprint(2), Fingerprint(3)];
    checkpoint.depths.insert(Fingerprint(1), 0);
    checkpoint.depths.insert(Fingerprint(2), 1);
    checkpoint.depths.insert(Fingerprint(3), 2);
    checkpoint.parents.insert(Fingerprint(2), Fingerprint(1));
    checkpoint.parents.insert(Fingerprint(3), Fingerprint(2));

    checkpoint.save(&checkpoint_dir).unwrap();

    let loaded = Checkpoint::load(&checkpoint_dir).unwrap();
    assert_eq!(loaded.fingerprints.len(), 3);
    assert_eq!(loaded.parents.len(), 2);
    assert_eq!(loaded.depths.len(), 3);
}
