// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Debug environment flag utilities (canonical definitions).
//!
//! Provides cached environment variable lookups for debug/feature flags.
//! Only `env_flag_is_set` is re-exported at the crate root — it is required
//! by the `tla_debug_flag!` macro's `$crate::env_flag_is_set` path.
//! The remaining helpers (`env_flag_eq`, `env_opt_usize`, `env_usize_or`)
//! are crate-internal here; `tla-check` owns its own copies (#3039).
//!
//! Part of #2384: consolidated from duplicated copies across crates.

use std::sync::OnceLock;

/// Check if an environment variable is set (any value).
#[inline]
pub fn env_flag_is_set(cache: &OnceLock<bool>, var: &'static str) -> bool {
    *cache.get_or_init(|| std::env::var(var).is_ok())
}

// env_flag_eq, env_opt_usize, env_usize_or: production copies live in
// tla-check/src/debug_env.rs (#3039). Kept here only for test coverage.
#[cfg(test)]
fn env_flag_eq(cache: &OnceLock<bool>, var: &'static str, expected: &str) -> bool {
    *cache.get_or_init(|| std::env::var(var).map(|v| v == expected).unwrap_or(false))
}

#[cfg(test)]
fn env_opt_usize(cache: &OnceLock<Option<usize>>, var: &'static str) -> Option<usize> {
    *cache.get_or_init(|| {
        std::env::var(var)
            .ok()
            .and_then(|s| s.trim().parse::<usize>().ok())
    })
}

#[cfg(test)]
fn env_usize_or(cache: &OnceLock<usize>, var: &'static str, default: usize) -> usize {
    *cache.get_or_init(|| {
        std::env::var(var)
            .ok()
            .and_then(|s| s.trim().parse::<usize>().ok())
            .unwrap_or(default)
    })
}

/// Shared debug flag helper macro backed by an environment variable.
#[macro_export]
macro_rules! tla_debug_flag {
    ($vis:vis $name:ident, $env:literal) => {
        #[cfg(debug_assertions)]
        $vis fn $name() -> bool {
            static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            $crate::env_flag_is_set(&FLAG, $env)
        }
        #[cfg(not(debug_assertions))]
        $vis fn $name() -> bool {
            false
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    static ENV_LOCK: Mutex<()> = Mutex::new(());

    const FLAG_VAR: &str = "TLA2_CORE_DEBUG_ENV_TEST_FLAG";
    const EQ_VAR: &str = "TLA2_CORE_DEBUG_ENV_TEST_EQ";
    const OPT_USIZE_VAR: &str = "TLA2_CORE_DEBUG_ENV_TEST_OPT_USIZE";
    const USIZE_OR_VAR: &str = "TLA2_CORE_DEBUG_ENV_TEST_USIZE_OR";

    #[test]
    fn env_flag_is_set_caches_first_read() {
        let _guard = ENV_LOCK.lock().expect("env lock poisoned");
        std::env::remove_var(FLAG_VAR);

        let cache = OnceLock::new();
        assert!(!env_flag_is_set(&cache, FLAG_VAR));

        std::env::set_var(FLAG_VAR, "1");
        assert!(
            !env_flag_is_set(&cache, FLAG_VAR),
            "cached result should not change after environment mutation"
        );

        let fresh_cache = OnceLock::new();
        assert!(env_flag_is_set(&fresh_cache, FLAG_VAR));
        std::env::remove_var(FLAG_VAR);
    }

    #[test]
    fn env_flag_eq_matches_exact_value() {
        let _guard = ENV_LOCK.lock().expect("env lock poisoned");
        std::env::set_var(EQ_VAR, "enabled");
        let cache = OnceLock::new();
        assert!(env_flag_eq(&cache, EQ_VAR, "enabled"));
        std::env::remove_var(EQ_VAR);
    }

    #[test]
    fn env_opt_usize_returns_none_for_invalid_values() {
        let _guard = ENV_LOCK.lock().expect("env lock poisoned");
        std::env::set_var(OPT_USIZE_VAR, "invalid");
        let cache = OnceLock::new();
        assert_eq!(env_opt_usize(&cache, OPT_USIZE_VAR), None);
        std::env::remove_var(OPT_USIZE_VAR);
    }

    #[test]
    fn env_usize_or_falls_back_to_default() {
        let _guard = ENV_LOCK.lock().expect("env lock poisoned");
        std::env::remove_var(USIZE_OR_VAR);
        let cache = OnceLock::new();
        assert_eq!(env_usize_or(&cache, USIZE_OR_VAR, 42), 42);
    }
}
