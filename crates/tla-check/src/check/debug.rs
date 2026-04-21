// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::fingerprint::FP64_INIT;
#[cfg(debug_assertions)]
use crate::state::Fingerprint;
use crate::Value;
#[cfg(debug_assertions)]
use std::sync::atomic::AtomicUsize;
#[cfg(debug_assertions)]
use std::sync::atomic::Ordering as AtomicOrdering;
#[cfg(debug_assertions)]
use std::sync::OnceLock;
use tla_value::FingerprintResult;

// debug_flag! and feature_flag! macros defined in crate::debug_env (via #[macro_use])

/// Define a cached optional usize limit backed by an env var.
/// Debug-only: all invocations are #[cfg(debug_assertions)]-gated.
#[cfg(debug_assertions)]
macro_rules! debug_opt_limit {
    ($vis:vis $name:ident, $env:literal) => {
        $vis fn $name() -> Option<usize> {
            static LIMIT: OnceLock<Option<usize>> = OnceLock::new();
            crate::debug_env::env_opt_usize(&LIMIT, $env)
        }
    };
}

/// Define a cached usize limit with a default, backed by an env var.
/// Debug-only: all invocations are #[cfg(debug_assertions)]-gated.
#[cfg(debug_assertions)]
macro_rules! debug_limit {
    ($vis:vis $name:ident, $env:literal, $default:expr) => {
        $vis fn $name() -> usize {
            static LIMIT: OnceLock<usize> = OnceLock::new();
            crate::debug_env::env_usize_or(&LIMIT, $env, $default)
        }
    };
}

// Cached debug flags — compile to constant false in release builds
debug_flag!(pub(super) debug_states, "TLA2_DEBUG_STATES");
debug_flag!(pub(super) debug_invariants, "TLA2_DEBUG_INVARIANTS");
debug_flag!(pub(super) debug_successors, "TLA2_DEBUG_SUCCESSORS");
debug_flag!(pub(super) debug_successors_actions, "TLA2_DEBUG_SUCCESSORS_ACTIONS");
debug_flag!(pub(super) debug_successors_actions_all_states, "TLA2_DEBUG_SUCCESSORS_ACTIONS_ALL");
debug_flag!(pub(super) debug_successors_actions_counts_only, "TLA2_DEBUG_SUCCESSORS_ACTION_COUNTS_ONLY");
debug_flag!(pub(super) debug_successors_tlc_fp, "TLA2_DEBUG_SUCCESSORS_TLCFP");
debug_flag!(pub(super) debug_successors_dump_state, "TLA2_DEBUG_SUCCESSORS_DUMP_STATE");
debug_flag!(pub(super) debug_symmetry_invariant, "TLA2_DEBUG_SYMMETRY_INVARIANT");
debug_flag!(pub(super) debug_symmetry_invariant_panic, "TLA2_DEBUG_SYMMETRY_INVARIANT_PANIC");
debug_flag!(pub(super) debug_symmetry_invariant_dump_state, "TLA2_DEBUG_SYMMETRY_INVARIANT_DUMP_STATE");
// FP collision detection — active in both debug and release builds (opt-in via env var).
// Part of #2841: moved from debug_flag! to feature_flag! so collision detection
// works in production (release) builds when explicitly enabled.
feature_flag!(pub(crate) debug_seen_tlc_fp_dedup, "TLA2_DEBUG_SEEN_TLCFP_DEDUP");
debug_flag!(pub(super) debug_tlcfp_decimal, "TLA2_TLCFP_DECIMAL"); // Part of #599
debug_flag!(pub(super) debug_lazy_values_in_state, "TLA2_DEBUG_LAZY_VALUES_IN_STATE");
feature_flag!(pub(crate) debug_internal_fp_collision, "TLA2_DEBUG_INTERNAL_FP_COLLISION");
debug_flag!(pub(super) debug_liveness_formula, "TLA2_DEBUG_LIVENESS_FORMULA"); // Part of #246
debug_flag!(pub(super) debug_safety_parts, "TLA2_DEBUG_SAFETY_PARTS");
debug_flag!(pub(super) debug_safety_temporal, "TLA2_DEBUG_SAFETY_TEMPORAL");
debug_flag!(pub(crate) tla2_debug, "TLA2_DEBUG");
feature_flag!(pub(crate) debug_bytecode_vm, "TLA2_DEBUG_BYTECODE_VM");
/// Whether `TLA2_BYTECODE_VM_STATS=1` is set. Cached via `OnceLock`.
/// Part of #4114: replaces ~15 scattered `std::env::var("TLA2_BYTECODE_VM_STATS")`
/// calls across `run_prepare.rs`, `run_finalize.rs`, `prepare.rs`, and `eval.rs`.
pub(crate) fn bytecode_vm_stats_enabled() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| matches!(std::env::var("TLA2_BYTECODE_VM_STATS").as_deref(), Ok("1")))
}
debug_flag!(pub(super) debug_init, "TLA2_DEBUG_INIT");
debug_flag!(pub(crate) debug_state_succs, "TLA2_DEBUG_STATE_SUCCS"); // #3019
debug_flag!(pub(crate) debug_dump_succs, "TLA2_DUMP_SUCCS"); // #3019

// Feature/operational flags — remain active in release builds
feature_flag!(pub(crate) skip_liveness, "TLA2_SKIP_LIVENESS");

/// Whether FlatState-based BFS is force-enabled via env var.
///
/// When set, the BFS loop uses FlatState as the native representation,
/// converting to ArrayState only for interpreter evaluation (Tier 0
/// cold path). This is the interpreter sandwich:
///   FlatState -> ArrayState -> eval actions -> ArrayState -> FlatState
///
/// This env var force-enables flat BFS even for non-fully-flat layouts
/// (as long as roundtrip verification passes). For auto-detection that
/// activates flat BFS when all state variables are scalar, see
/// `ModelChecker::should_use_flat_bfs()`.
///
/// Part of #4126: FlatState as native BFS representation (Phase E).
feature_flag!(pub(crate) flat_bfs_enabled, "TLA2_FLAT_BFS");

/// Whether FlatState-based BFS is force-disabled via env var.
///
/// When set, flat BFS auto-detection is suppressed even when the layout
/// is fully flat and roundtrip verification passes. Useful for debugging
/// or benchmarking the non-flat path.
///
/// Part of #4126: Auto-detect flat BFS for scalar specs.
feature_flag!(pub(crate) flat_bfs_disabled, "TLA2_NO_FLAT_BFS");

/// Whether the compiled (fused) BFS level loop is force-enabled via env var.
///
/// When set, the compiled BFS loop uses the fused JIT-compiled level function
/// that processes entire BFS frontiers in a single native call, eliminating
/// per-parent Rust-to-JIT boundary crossings.
///
/// Part of #4171: End-to-end compiled BFS wiring.
feature_flag!(pub(crate) compiled_bfs_enabled, "TLA2_COMPILED_BFS");

/// Whether the compiled (fused) BFS level loop is force-disabled via env var.
///
/// When set, compiled BFS auto-detection is suppressed. The standard
/// per-parent CompiledBfsStep path or interpreter path will be used instead.
///
/// Part of #4171: End-to-end compiled BFS wiring.
feature_flag!(pub(crate) compiled_bfs_disabled, "TLA2_NO_COMPILED_BFS");

/// Whether JIT compilation of invariants is enabled.
///
/// Default: OFF. The CLI `--jit` flag sets `TLA2_JIT=1` before this is first called.
/// Can also be enabled directly via `TLA2_JIT=1` env var.
///
/// Part of #4035: JIT opt-in to eliminate 11-17% interpreter baseline regression.
/// When JIT is not enabled, no background compilation thread is spawned, no
/// eligibility checking happens, and no JIT-related TLS is initialized.
#[cfg(feature = "jit")]
pub(crate) fn jit_enabled() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    crate::debug_env::env_flag_is_set(&FLAG, "TLA2_JIT")
}
feature_flag!(pub(super) profile_enum, "TLA2_PROFILE_ENUM");
// Re-export from liveness/debug.rs where it's defined (fixes layering violation).
pub(crate) use crate::liveness::debug::liveness_profile;
feature_flag!(pub(crate) force_no_diffs, "TLA2_FORCE_NO_DIFFS");

// Cached debug limits — only compiled in debug builds (Part of #3026).
// Callers are all behind #[cfg(debug_assertions)].
#[cfg(debug_assertions)]
debug_opt_limit!(pub(super) debug_successors_limit, "TLA2_DEBUG_SUCCESSORS_LIMIT");
// Part of #2841: collision limits active in release builds too.
feature_limit!(pub(crate) debug_seen_tlc_fp_dedup_collision_limit, "TLA2_DEBUG_SEEN_TLCFP_DEDUP_COLLISION_LIMIT", 10);
#[cfg(debug_assertions)]
debug_limit!(pub(super) debug_lazy_values_in_state_log_limit, "TLA2_DEBUG_LAZY_VALUES_IN_STATE_LOG_LIMIT", 50);
feature_limit!(pub(crate) debug_internal_fp_collision_limit, "TLA2_DEBUG_INTERNAL_FP_COLLISION_LIMIT", 10);

// Special-purpose debug helpers that don't fit the macro patterns.
// All callers are behind #[cfg(debug_assertions)] — gate definitions to suppress
// release-mode dead-code warnings (Part of #3026).

#[cfg(debug_assertions)]
pub(super) fn debug_successors_action_filter() -> Option<Vec<String>> {
    static FILTER: OnceLock<Option<Vec<String>>> = OnceLock::new();
    FILTER
        .get_or_init(|| {
            let raw = std::env::var("TLA2_DEBUG_SUCCESSORS_ACTION_FILTER").ok()?;
            let items: Vec<String> = raw
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(std::string::ToString::to_string)
                .collect();
            if items.is_empty() {
                None
            } else {
                Some(items)
            }
        })
        .clone()
}

#[cfg(debug_assertions)]
pub(super) fn debug_successors_filter_state_fp() -> Option<Fingerprint> {
    static FILTER: OnceLock<Option<Fingerprint>> = OnceLock::new();
    *FILTER.get_or_init(|| parse_u64_env("TLA2_DEBUG_SUCCESSORS_STATE").map(Fingerprint))
}

#[cfg(debug_assertions)]
pub(super) fn debug_successors_filter_state_tlc_fp() -> Option<u64> {
    static FILTER: OnceLock<Option<u64>> = OnceLock::new();
    *FILTER.get_or_init(|| parse_u64_env("TLA2_DEBUG_SUCCESSORS_TLC_STATE"))
}

/// Part of #599: Format TLC fingerprint with optional signed decimal.
pub(crate) fn fmt_tlc_fp(fp: u64) -> String {
    #[cfg(debug_assertions)]
    {
        if debug_tlcfp_decimal() {
            format!("{:016x}/{}", fp, fp as i64)
        } else {
            format!("{:016x}", fp)
        }
    }
    #[cfg(not(debug_assertions))]
    {
        format!("{:016x}", fp)
    }
}

#[cfg(debug_assertions)]
pub(super) fn action_filter_matches(label: &str, filter: &[String]) -> bool {
    if filter.is_empty() {
        return true;
    }
    label
        .split('|')
        .any(|part| filter.iter().any(|f| f == part))
}

#[cfg(debug_assertions)]
pub(super) fn parse_u64_env(var: &str) -> Option<u64> {
    let raw = std::env::var(var).ok()?;
    parse_u64_str(&raw)
}

pub(crate) fn tlc_fp_for_state_values(values: &[Value]) -> FingerprintResult<u64> {
    let mut fp = FP64_INIT;
    for v in values {
        fp = v.fingerprint_extend(fp)?;
    }
    Ok(fp)
}

/// Parse a string as u64, supporting decimal, hex with 0x prefix, and auto-detecting
/// hex when string contains a-f/A-F characters.
#[cfg(any(debug_assertions, test))]
pub(super) fn parse_u64_str(s: &str) -> Option<u64> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    let s_no_prefix = s.strip_prefix("0x").unwrap_or(s);
    let looks_hex = s.starts_with("0x")
        || s_no_prefix
            .chars()
            .any(|c| matches!(c, 'a'..='f' | 'A'..='F'));
    if looks_hex {
        u64::from_str_radix(s_no_prefix, 16).ok()
    } else {
        s_no_prefix.parse::<u64>().ok()
    }
}

#[cfg(debug_assertions)]
static DEBUG_SUCCESSOR_LINES: AtomicUsize = AtomicUsize::new(0);
#[cfg(debug_assertions)]
pub(super) static DEBUG_LAZY_VALUES_IN_STATE_LINES: AtomicUsize = AtomicUsize::new(0);

#[cfg(debug_assertions)]
pub(super) fn should_print_successor_debug_line(force: bool) -> bool {
    if force {
        return true;
    }
    let Some(limit) = debug_successors_limit() else {
        return true;
    };
    let line = DEBUG_SUCCESSOR_LINES.fetch_add(1, AtomicOrdering::Relaxed);
    line < limit
}

#[cfg(debug_assertions)]
pub(super) fn should_debug_successors_for_state(fp: Fingerprint, tlc_fp: Option<u64>) -> bool {
    debug_successors_filter_state_fp().is_some_and(|target| target == fp)
        || debug_successors_filter_state_tlc_fp().is_some_and(|target| tlc_fp == Some(target))
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- action_filter_matches tests (debug-only: function is #[cfg(debug_assertions)]) ---

    #[cfg(debug_assertions)]
    #[test]
    fn test_action_filter_matches_empty_filter_matches_all() {
        assert!(action_filter_matches("anything", &[]));
        assert!(action_filter_matches("", &[]));
    }

    #[cfg(debug_assertions)]
    #[test]
    fn test_action_filter_matches_exact_match() {
        let filter = vec!["MoveRobot".to_string()];
        assert!(action_filter_matches("MoveRobot", &filter));
    }

    #[cfg(debug_assertions)]
    #[test]
    fn test_action_filter_matches_no_match() {
        let filter = vec!["MoveRobot".to_string()];
        assert!(!action_filter_matches("OpenDoor", &filter));
    }

    #[cfg(debug_assertions)]
    #[test]
    fn test_action_filter_matches_pipe_separated_label() {
        let filter = vec!["MoveRobot".to_string()];
        assert!(action_filter_matches("Init|MoveRobot|Done", &filter));
    }

    #[cfg(debug_assertions)]
    #[test]
    fn test_action_filter_matches_multiple_filters() {
        let filter = vec!["MoveRobot".to_string(), "OpenDoor".to_string()];
        assert!(action_filter_matches("MoveRobot", &filter));
        assert!(action_filter_matches("OpenDoor", &filter));
        assert!(!action_filter_matches("CloseDoor", &filter));
    }

    #[cfg(debug_assertions)]
    #[test]
    fn test_action_filter_matches_partial_mismatch() {
        let filter = vec!["Move".to_string()];
        assert!(!action_filter_matches("MoveRobot", &filter));
    }

    // --- parse_u64_str tests ---

    #[test]
    fn test_parse_u64_str_decimal() {
        assert_eq!(parse_u64_str("42"), Some(42));
        assert_eq!(parse_u64_str("0"), Some(0));
        assert_eq!(parse_u64_str("18446744073709551615"), Some(u64::MAX));
    }

    #[test]
    fn test_parse_u64_str_hex_with_prefix() {
        assert_eq!(parse_u64_str("0xff"), Some(255));
        assert_eq!(parse_u64_str("0xDEADBEEF"), Some(0xDEADBEEF));
        assert_eq!(parse_u64_str("0x0"), Some(0));
    }

    #[test]
    fn test_parse_u64_str_auto_detect_hex() {
        // Contains a-f chars, so auto-detected as hex
        assert_eq!(parse_u64_str("ff"), Some(255));
        assert_eq!(parse_u64_str("deadbeef"), Some(0xDEADBEEF));
        assert_eq!(parse_u64_str("ABCDEF"), Some(0xABCDEF));
    }

    #[test]
    fn test_parse_u64_str_trims_whitespace() {
        assert_eq!(parse_u64_str("  42  "), Some(42));
        assert_eq!(parse_u64_str("  0xff  "), Some(255));
    }

    #[test]
    fn test_parse_u64_str_empty_and_whitespace() {
        assert_eq!(parse_u64_str(""), None);
        assert_eq!(parse_u64_str("   "), None);
    }

    #[test]
    fn test_parse_u64_str_invalid() {
        assert_eq!(parse_u64_str("not_a_number"), None);
        assert_eq!(parse_u64_str("-1"), None);
        assert_eq!(parse_u64_str("0xZZZ"), None);
    }
}
