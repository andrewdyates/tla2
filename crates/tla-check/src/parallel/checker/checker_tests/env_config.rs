// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FPSet backend env var tests (Part of #3285).
//!
//! IMPORTANT: env vars are process-global, not per-thread. These tests use
//! a static Mutex + RAII guard to serialize access and guarantee cleanup
//! (including on panic from #[should_panic] tests). Without this, the
//! `unknown_panics` test leaks "invalid_backend" into 83+ concurrent tests.

use crate::storage::factory::StorageMode;

static FPSET_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

struct FpsetEnvGuard {
    previous: Option<std::ffi::OsString>,
    _lock: std::sync::MutexGuard<'static, ()>,
}

impl FpsetEnvGuard {
    fn set(value: Option<&str>) -> Self {
        let lock = FPSET_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let previous = std::env::var_os("TLA2_PARALLEL_FPSET");
        match value {
            Some(v) => std::env::set_var("TLA2_PARALLEL_FPSET", v),
            None => std::env::remove_var("TLA2_PARALLEL_FPSET"),
        }
        Self {
            previous,
            _lock: lock,
        }
    }
}

impl Drop for FpsetEnvGuard {
    fn drop(&mut self) {
        match self.previous.take() {
            Some(v) => std::env::set_var("TLA2_PARALLEL_FPSET", v),
            None => std::env::remove_var("TLA2_PARALLEL_FPSET"),
        }
    }
}

#[test]
fn test_parallel_fpset_mode_default_is_sharded_cas() {
    let _guard = FpsetEnvGuard::set(None);
    let mode = super::super::parallel_fpset_mode().expect("default should succeed");
    assert!(
        matches!(mode, StorageMode::ShardedCas),
        "default should be ShardedCas"
    );
}

#[test]
fn test_parallel_fpset_mode_cas_explicit() {
    let _guard = FpsetEnvGuard::set(Some("cas"));
    let mode = super::super::parallel_fpset_mode().expect("cas should succeed");
    assert!(
        matches!(mode, StorageMode::ShardedCas),
        "cas should select ShardedCas"
    );
}

#[test]
fn test_parallel_fpset_mode_sharded() {
    let _guard = FpsetEnvGuard::set(Some("sharded"));
    let mode = super::super::parallel_fpset_mode().expect("sharded should succeed");
    assert!(
        matches!(mode, StorageMode::Sharded),
        "sharded should select Sharded"
    );
}

#[test]
fn test_parallel_fpset_mode_unknown_returns_error() {
    let _guard = FpsetEnvGuard::set(Some("invalid_backend"));
    let result = super::super::parallel_fpset_mode();
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("unrecognized env var should return Err"),
    };
    let err_msg = err.to_string();
    assert!(
        err_msg.contains("is not recognized"),
        "error should mention unrecognized value, got: {err_msg}"
    );
}
