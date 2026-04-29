// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Profile-guided optimization (PGO) workflow (design doc §6/§7).
//!
//! # Plan
//!
//! 1. **Canary pass** — compile the module at O1 with profile-generation
//!    instrumentation. Run one BFS pass over a subset of the frontier (≤
//!    16k states or a user-specified count), collecting call/edge counts
//!    and loop-trip profiles.
//! 2. **Profile merge** — fold the counters into a `.profdata` file stored
//!    next to the cached artifact at
//!    `~/.cache/tla2/compiled/<spec-hash>.profdata` (see
//!    [`crate::artifact_cache`]).
//! 3. **Real run** — recompile at O3 with profile-use. The profdata drives
//!    (a) function-level inlining decisions, (b) loop unroll trip counts,
//!    (c) block layout / branch hinting, (d) register allocation hot paths.
//!
//! # Status
//!
//! LLVM2 currently exposes only JIT-side call counting
//! ([`llvm2_codegen::jit::ProfileHookMode`]). Full `-fprofile-generate` /
//! `-fprofile-use` with on-disk profdata does **not** exist in LLVM2 at
//! revision 0.9.0+tmir-supremacy-stream3. The surface area needed:
//!
//! - Instrumentation pass: insert `llvm.instrprof.increment` intrinsics on
//!   function entry and key loop back-edges
//! - Profile writer runtime hook: serialize counters to `.profdata`
//! - Profile reader + `-fprofile-use`: consume `.profdata` to drive
//!   inlining / unroll / block layout decisions
//!
//! Tracking upstream: `andrewdyates/LLVM2#390`. Until that lands,
//! this module stubs the API so `tla-check` / `tla-cli` can wire it now
//! and switch to the real implementation without call-site churn.

use crate::artifact_cache::{ArtifactCache, CacheKey};
use thiserror::Error;

/// Profile-generation mode for the canary run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProfileMode {
    /// Skip PGO entirely. Fall back to static heuristics.
    Off,
    /// Run canary pass, collect profile, persist as `.profdata`.
    Generate,
    /// Use an existing `.profdata` for the real run.
    Use,
    /// First Generate, then Use in a single pipeline (typical workflow).
    GenerateThenUse,
}

impl Default for ProfileMode {
    fn default() -> Self {
        Self::Off
    }
}

/// Errors returned by the PGO workflow.
#[derive(Debug, Error)]
pub enum PgoError {
    /// Upstream LLVM2 does not yet support profile-generate /
    /// profile-use. See `andrewdyates/LLVM2#390`.
    #[error("LLVM2 PGO not available: {feature} (upstream LLVM2#390)")]
    Unsupported {
        /// Specific sub-feature that was requested.
        feature: &'static str,
    },
    /// Failed to read/write a profdata file.
    #[error("PGO I/O: {0}")]
    Io(String),
    /// Cache error while loading/storing a profile.
    #[error("PGO cache: {0}")]
    Cache(#[from] crate::artifact_cache::CacheError),
}

/// Request to run the canary BFS pass and emit a `.profdata`.
///
/// `canary_states` bounds the number of states the canary explores — the
/// profile is only useful if the canary reaches the hot code paths, but
/// explosion on large specs defeats the purpose. Default: 16k.
#[derive(Debug, Clone)]
pub struct CanaryConfig {
    /// Hard cap on states explored during the canary pass.
    pub canary_states: u64,
    /// Optional wall-clock timeout, in milliseconds. `None` = unlimited.
    pub canary_timeout_ms: Option<u64>,
}

impl Default for CanaryConfig {
    fn default() -> Self {
        Self {
            canary_states: 16_384,
            canary_timeout_ms: Some(30_000),
        }
    }
}

/// Run the profile-generation canary and persist the resulting profdata
/// into the compilation cache alongside `key`.
///
/// # Returns
///
/// `Ok(profdata_bytes_written)` on success.
///
/// # Errors
///
/// Returns [`PgoError::Unsupported`] until LLVM2#390 lands. The function
/// exists now so the CLI / model-checker plumbing can be wired; switching
/// to a real implementation is a single-function change.
pub fn run_canary(
    _cache: &ArtifactCache,
    _key: &CacheKey,
    _config: &CanaryConfig,
) -> Result<u64, PgoError> {
    // TODO(LLVM2#390): once LLVM2 exposes profile-generate,
    // 1. compile module with instrumentation passes via
    //    `llvm2_codegen::pipeline::Pipeline` configured with
    //    `PipelineConfig::profile_generate = true`
    // 2. load the compiled canary via `cache.load_library`
    // 3. drive one BFS pass bounded by `config.canary_states` and
    //    `config.canary_timeout_ms`
    // 4. serialize accumulated counters into profdata bytes
    // 5. `cache.store(key, existing_artifact, Some(&profdata_bytes))`
    Err(PgoError::Unsupported {
        feature: "profile-generate canary",
    })
}

/// Re-compile the module with `-fprofile-use` against a previously
/// persisted `.profdata`. On success the freshly-compiled artifact is
/// stored in the cache under `key`.
///
/// # Errors
///
/// Returns [`PgoError::Unsupported`] until LLVM2#390 lands.
pub fn compile_with_profile(_cache: &ArtifactCache, _key: &CacheKey) -> Result<(), PgoError> {
    // TODO(LLVM2#390): load `<key>.profdata`, configure
    // `PipelineConfig::profile_use = Some(profdata_bytes)`, recompile,
    // store the resulting artifact back into the cache under the same key.
    Err(PgoError::Unsupported {
        feature: "profile-use compilation",
    })
}

/// Convenience wrapper running the full Generate→Use cycle.
pub fn run(
    cache: &ArtifactCache,
    key: &CacheKey,
    mode: ProfileMode,
    canary: &CanaryConfig,
) -> Result<(), PgoError> {
    match mode {
        ProfileMode::Off => Ok(()),
        ProfileMode::Generate => run_canary(cache, key, canary).map(|_| ()),
        ProfileMode::Use => compile_with_profile(cache, key),
        ProfileMode::GenerateThenUse => {
            run_canary(cache, key, canary)?;
            compile_with_profile(cache, key)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_mode_off_is_noop() {
        let tmp = TempDir::new().unwrap();
        let cache = ArtifactCache::open_at(tmp.path()).unwrap();
        let key = CacheKey::for_raw(b"m", "O3", "t");
        // Off never errors.
        run(&cache, &key, ProfileMode::Off, &CanaryConfig::default()).expect("off succeeds");
    }

    #[test]
    fn test_generate_returns_unsupported_until_llvm2_390() {
        let tmp = TempDir::new().unwrap();
        let cache = ArtifactCache::open_at(tmp.path()).unwrap();
        let key = CacheKey::for_raw(b"m", "O3", "t");
        let err = run_canary(&cache, &key, &CanaryConfig::default()).unwrap_err();
        assert!(
            matches!(err, PgoError::Unsupported { .. }),
            "PGO generate must return Unsupported stub error, got {err:?}"
        );
    }

    #[test]
    fn test_use_returns_unsupported_until_llvm2_390() {
        let tmp = TempDir::new().unwrap();
        let cache = ArtifactCache::open_at(tmp.path()).unwrap();
        let key = CacheKey::for_raw(b"m", "O3", "t");
        let err = compile_with_profile(&cache, &key).unwrap_err();
        assert!(matches!(err, PgoError::Unsupported { .. }));
    }

    #[test]
    fn test_canary_config_defaults_are_bounded() {
        let c = CanaryConfig::default();
        assert!(c.canary_states > 0);
        assert!(c.canary_states <= 1 << 20, "default canary cap is bounded");
        assert!(
            c.canary_timeout_ms.is_some(),
            "default canary has a timeout"
        );
    }
}
