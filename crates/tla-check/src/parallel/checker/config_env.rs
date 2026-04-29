// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Environment-variable configuration parsing for parallel checker.

use super::*;

/// Part of #3285: Read `TLA2_PARALLEL_FPSET` env var to select the FPSet backend
/// for parallel checking. This is a diagnostic-only override; the production
/// default (`ShardedCas`) is unchanged when the env var is absent.
///
/// - absent / empty → `ShardedCas` (current default)
/// - `"cas"` → `ShardedCas`
/// - `"sharded"` → `Sharded` (striped RwLock + FxHashSet)
/// - `"atomic"` → `AtomicLockFree` (128-bit lock-free with auto-resize)
/// - anything else → `ConfigCheckError::Setup`
///
/// Env var cached via `OnceLock` (Part of #4114).
/// Part of #3991: added `"atomic"` for the 128-bit lock-free backend.
pub(super) fn parallel_fpset_mode() -> Result<StorageMode, CheckError> {
    #[cfg(test)]
    let val = std::env::var("TLA2_PARALLEL_FPSET").ok();
    #[cfg(not(test))]
    let val = {
        use std::sync::OnceLock;
        static CACHED: OnceLock<Option<String>> = OnceLock::new();
        CACHED
            .get_or_init(|| std::env::var("TLA2_PARALLEL_FPSET").ok())
            .clone()
    };
    match val.as_deref() {
        None | Some("") | Some("cas") => Ok(StorageMode::ShardedCas),
        Some("sharded") => Ok(StorageMode::Sharded),
        Some("atomic") => Ok(StorageMode::AtomicLockFree),
        Some(other) => Err(ConfigCheckError::Setup(format!(
            "TLA2_PARALLEL_FPSET={other:?} is not recognized. \
             Use \"cas\", \"sharded\", or \"atomic\" (or unset for the default)."
        ))
        .into()),
    }
}

/// Part of #3285: diagnostic gate for the read-only embedded value-cache slice.
///
/// - absent / empty / `"0"` -> disabled (same-build control run)
/// - `"1"` -> enabled (same-build treatment run)
/// - anything else -> `ConfigCheckError::Setup`
///
/// Env var cached via `OnceLock` (Part of #4114).
pub(super) fn parallel_readonly_value_caches_enabled() -> Result<bool, CheckError> {
    #[cfg(test)]
    let val = std::env::var("TLA2_PARALLEL_READONLY_VALUE_CACHES").ok();
    #[cfg(not(test))]
    let val = {
        use std::sync::OnceLock;
        static CACHED: OnceLock<Option<String>> = OnceLock::new();
        CACHED
            .get_or_init(|| std::env::var("TLA2_PARALLEL_READONLY_VALUE_CACHES").ok())
            .clone()
    };
    match val.as_deref() {
        None | Some("") | Some("0") => Ok(false),
        Some("1") => Ok(true),
        Some(other) => Err(ConfigCheckError::Setup(format!(
            "TLA2_PARALLEL_READONLY_VALUE_CACHES={other:?} is not recognized. \
             Use \"1\" for the diagnostic treatment run or unset/\"0\" for control."
        ))
        .into()),
    }
}
