// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cache signature and load/save tests.

use super::*;
use std::time::{SystemTime, UNIX_EPOCH};

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new() -> Self {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("time went backwards")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "tla2-check-cache-test-{}-{nanos}",
            std::process::id()
        ));
        Self { path }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn write_file(path: &Path, bytes: &[u8]) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create temp dir");
    }
    fs::write(path, bytes).expect("write temp file");
}

fn default_opts() -> CheckOptions {
    CheckOptions {
        no_deadlock: false,
        check_deadlock: true,
        max_states: 0,
        max_depth: 0,
        bmc_depth: 0,
        pdr_enabled: false,
        por_enabled: false,
        continue_on_error: false,
    }
}

/// Use `compute_signature_with_env` with fixed empty env vars for tests
/// that check non-env-var signature properties. This prevents test flakiness
/// from parallel tests mutating process-global env vars.
fn sig(
    spec_path: &Path,
    spec_bytes: &[u8],
    cfg_path: &Path,
    cfg_bytes: &[u8],
    deps: &[String],
    opts: &CheckOptions,
) -> String {
    compute_signature_with_env(spec_path, spec_bytes, cfg_path, cfg_bytes, deps, opts, &[]).unwrap()
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn signature_ignores_dependency_order() {
    let dir = TempDir::new();

    let spec_path = dir.path.join("Spec.tla");
    let cfg_path = dir.path.join("Spec.cfg");
    write_file(&spec_path, b"---- MODULE Spec ----\n====\n");
    write_file(&cfg_path, b"INIT Init\nNEXT Next\n");

    let dep_a = canonical_string(&dir.path.join("A.tla"));
    let dep_b = canonical_string(&dir.path.join("B.tla"));

    let sig_ab = sig(
        &spec_path,
        &fs::read(&spec_path).unwrap(),
        &cfg_path,
        &fs::read(&cfg_path).unwrap(),
        &[dep_a.clone(), dep_b.clone()],
        &default_opts(),
    );

    let sig_ba = sig(
        &spec_path,
        &fs::read(&spec_path).unwrap(),
        &cfg_path,
        &fs::read(&cfg_path).unwrap(),
        &[dep_b, dep_a],
        &default_opts(),
    );

    assert_eq!(sig_ab, sig_ba);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn signature_changes_on_content_change() {
    let dir = TempDir::new();

    let spec_path = dir.path.join("Spec.tla");
    let cfg_path = dir.path.join("Spec.cfg");
    write_file(&spec_path, b"---- MODULE Spec ----\n====\n");
    write_file(&cfg_path, b"INIT Init\nNEXT Next\n");

    let deps: Vec<String> = Vec::new();
    let opts = default_opts();

    let sig1 = sig(
        &spec_path,
        &fs::read(&spec_path).unwrap(),
        &cfg_path,
        &fs::read(&cfg_path).unwrap(),
        &deps,
        &opts,
    );

    write_file(&spec_path, b"---- MODULE Spec ----\n\\* changed\n====\n");

    let sig2 = sig(
        &spec_path,
        &fs::read(&spec_path).unwrap(),
        &cfg_path,
        &fs::read(&cfg_path).unwrap(),
        &deps,
        &opts,
    );

    assert_ne!(sig1, sig2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn load_cache_clears_entries_on_tool_fingerprint_mismatch() {
    let dir = TempDir::new();
    let cache_path = dir.path.join("cache.json");

    let mut cache = CacheFile::empty();
    cache.tool_version = "some-other-tool-fingerprint".to_string();
    cache.entries.insert(
        "Spec.tla".to_string(),
        CacheEntry {
            config: "Spec.cfg".to_string(),
            signature: "deadbeef".to_string(),
            result: CacheResult::Pass,
            state_count: None,
            invariants_checked: Vec::new(),
            duration_secs: None,
            verified_at: "1970-01-01T00:00:00Z".to_string(),
            dependencies: Vec::new(),
            options: default_opts(),
            stats: None,
        },
    );

    save_cache(&cache_path, &cache).unwrap();

    let loaded = load_cache(&cache_path).unwrap();
    assert_eq!(loaded.tool_version, tool_fingerprint());
    assert!(loaded.entries.is_empty());
}

/// Part of #3283: verify that TLA2_* env vars change the cache signature.
/// Uses `compute_signature_with_env` with explicit env var lists to avoid
/// process-global state mutation and test parallelism issues.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn signature_changes_with_tla2_env_var() {
    let dir = TempDir::new();

    let spec_path = dir.path.join("Spec.tla");
    let cfg_path = dir.path.join("Spec.cfg");
    write_file(&spec_path, b"---- MODULE Spec ----\n====\n");
    write_file(&cfg_path, b"INIT Init\nNEXT Next\n");

    let deps: Vec<String> = Vec::new();
    let opts = default_opts();
    let spec_bytes = fs::read(&spec_path).unwrap();
    let cfg_bytes = fs::read(&cfg_path).unwrap();

    let no_env: Vec<(String, String)> = vec![];
    let sig_without = compute_signature_with_env(
        &spec_path,
        &spec_bytes,
        &cfg_path,
        &cfg_bytes,
        &deps,
        &opts,
        &no_env,
    )
    .unwrap();

    let tir_env = vec![("TLA2_TIR_EVAL".to_string(), "all".to_string())];
    let sig_with_tir = compute_signature_with_env(
        &spec_path,
        &spec_bytes,
        &cfg_path,
        &cfg_bytes,
        &deps,
        &opts,
        &tir_env,
    )
    .unwrap();

    assert_ne!(
        sig_without, sig_with_tir,
        "cache signature must differ when TLA2_TIR_EVAL is set"
    );

    // Different env var values must also produce different signatures.
    let parity_env = vec![("TLA2_TIR_PARITY".to_string(), "Next".to_string())];
    let sig_with_parity = compute_signature_with_env(
        &spec_path,
        &spec_bytes,
        &cfg_path,
        &cfg_bytes,
        &deps,
        &opts,
        &parity_env,
    )
    .unwrap();

    assert_ne!(sig_with_tir, sig_with_parity);
    assert_ne!(sig_without, sig_with_parity);
}

#[test]
fn collect_behavior_env_vars_includes_tla2_prefix() {
    // We can't safely test env var collection in parallel tests (process-global state),
    // but we can verify the function filters on TLA2_ prefix and sorts.
    let vars = collect_behavior_env_vars();
    for (key, _) in &vars {
        assert!(
            key.starts_with("TLA2_"),
            "collect_behavior_env_vars should only return TLA2_* vars, got: {key}"
        );
    }
    // Verify sorted order
    assert!(vars.windows(2).all(|w| w[0].0 <= w[1].0));
}
