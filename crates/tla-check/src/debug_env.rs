// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Debug environment flag utilities for tla-check.
//!
//! `env_flag_is_set` is re-exported from `tla_core` because the
//! `tla_debug_flag!` macro references `$crate::env_flag_is_set`.
//! The remaining helpers (`env_flag_eq`, `env_opt_usize`, `env_usize_or`) are
//! defined locally — `tla-check` is their sole consumer outside `tla-core`.
//! `env_flag_eq` and `env_opt_usize` are `#[cfg(debug_assertions)]`-only since
//! their sole callers (`debug_flag_strict!`, `debug_opt_limit!`) are debug-gated.
//! Part of #2384, localized in #3039.

use std::sync::OnceLock;

// Re-export env_flag_is_set — needed by the tla_debug_flag! macro path.
pub(crate) use tla_core::env_flag_is_set;

/// Check if an environment variable equals a specific value.
/// Only used by `debug_flag_strict!` which compiles to `false` in release builds.
#[cfg(debug_assertions)]
#[inline]
pub(crate) fn env_flag_eq(cache: &OnceLock<bool>, var: &'static str, expected: &str) -> bool {
    *cache.get_or_init(|| std::env::var(var).map(|v| v == expected).unwrap_or(false))
}

/// Read an optional `usize` from an environment variable.
/// Only used by `debug_opt_limit!` which is `#[cfg(debug_assertions)]`-gated.
#[cfg(debug_assertions)]
#[inline]
pub(crate) fn env_opt_usize(cache: &OnceLock<Option<usize>>, var: &'static str) -> Option<usize> {
    *cache.get_or_init(|| {
        std::env::var(var)
            .ok()
            .and_then(|s| s.trim().parse::<usize>().ok())
    })
}

/// Read a `usize` from an environment variable with a default fallback.
#[inline]
pub(crate) fn env_usize_or(cache: &OnceLock<usize>, var: &'static str, default: usize) -> usize {
    *cache.get_or_init(|| {
        std::env::var(var)
            .ok()
            .and_then(|s| s.trim().parse::<usize>().ok())
            .unwrap_or(default)
    })
}

macro_rules! debug_eprintln {
    ($flag:expr, $($arg:tt)*) => {
        #[cfg(debug_assertions)]
        if $flag {
            eprintln!($($arg)*);
        }
    };
}

macro_rules! debug_block {
    ($flag:expr, $block:block) => {
        #[cfg(debug_assertions)]
        if $flag $block
    };
}

macro_rules! debug_flag {
    ($($arg:tt)*) => {
        tla_core::tla_debug_flag!($($arg)*);
    };
}

/// Define an always-active cached bool flag backed by an env var.
/// Unlike `debug_flag!`, this is NOT gated by `cfg(debug_assertions)` —
/// use for operational/feature flags that affect behavior in release builds.
///
/// Usage:
///   `feature_flag!(pub(crate) my_flag, "TLA2_MY_FLAG");`
macro_rules! feature_flag {
    ($vis:vis $name:ident, $env:literal) => {
        $vis fn $name() -> bool {
            static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            crate::debug_env::env_flag_is_set(&FLAG, $env)
        }
    };
}

/// Define an always-active cached usize limit backed by an env var.
/// Unlike `debug_limit!`, this is NOT gated by `cfg(debug_assertions)` —
/// use for limits that need to work in release builds.
///
/// Usage:
///   `feature_limit!(pub(crate) my_limit, "TLA2_MY_LIMIT", 10);`
macro_rules! feature_limit {
    ($vis:vis $name:ident, $env:literal, $default:expr) => {
        $vis fn $name() -> usize {
            static LIMIT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
            crate::debug_env::env_usize_or(&LIMIT, $env, $default)
        }
    };
}

/// Check if a feature is enabled by default, with opt-out via `ENV=0`.
///
/// Returns `true` unless the env var is explicitly set to `"0"`.
/// This is the inverse of `env_flag_is_set`: default ON, opt-out with `0`.
#[inline]
#[allow(dead_code)]
pub(crate) fn env_flag_default_on(cache: &OnceLock<bool>, var: &'static str) -> bool {
    *cache.get_or_init(|| !matches!(std::env::var(var).ok().as_deref(), Some("0")))
}

/// Define a debug flag that requires the env var to equal "1" (not just be set).
/// Compiles to `false` in release builds.
///
/// Usage:
///   `debug_flag_strict!(pub(crate) my_flag, "TLA2_MY_FLAG");`
macro_rules! debug_flag_strict {
    ($vis:vis $name:ident, $env:literal) => {
        #[cfg(debug_assertions)]
        $vis fn $name() -> bool {
            static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            crate::debug_env::env_flag_eq(&FLAG, $env, "1")
        }
        #[cfg(not(debug_assertions))]
        $vis fn $name() -> bool {
            false
        }
    };
}
