// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! System memory detection for dynamic exploration sizing.
//!
//! Queries available system memory to compute optimal `max_states` based on
//! per-state memory footprint. This converts many `CANNOT_COMPUTE` results
//! into correct answers by allowing the explorer to use available RAM rather
//! than a hardcoded 10M state limit.

use crate::marking::TokenWidth;
use std::mem::size_of;

/// Bytes per state when using fingerprint-based dedup.
///
/// 16 bytes for the u128 fingerprint + 16 bytes for FxHashSet entry overhead.
pub(crate) const FINGERPRINT_BYTES_PER_STATE: usize = 32;

/// `explore_full` stores the unpacked `Vec<u64>` marking for every state.
const FULL_GRAPH_MARKING_BYTES_PER_PLACE: usize = size_of::<u64>();

/// Base per-state heap/header overhead for full-graph CTL storage:
/// fingerprint registry entry + marking Vec header + adjacency Vec header.
const FULL_GRAPH_BASE_BYTES_PER_STATE: usize =
    FINGERPRINT_BYTES_PER_STATE + size_of::<Vec<u64>>() + size_of::<Vec<(u32, u32)>>();

/// Conservative amortized edge payload allowance per state.
///
/// `(u32, u32)` is 8 bytes; reserve room for roughly two outgoing edges on
/// average so auto-sized CTL full-graph runs do not size themselves as if the
/// graph stored fingerprints alone.
const FULL_GRAPH_EDGE_BYTES_PER_STATE_ESTIMATE: usize = size_of::<(u32, u32)>() * 2;

/// Default max_states when memory detection fails.
const FALLBACK_MAX_STATES: usize = 10_000_000;

/// Minimum max_states to preserve exploration of the initial marking.
const MIN_MAX_STATES: usize = 1;

/// Estimate available system memory in bytes.
///
/// On Linux, reads `/proc/meminfo` and caps the host-level available memory by
/// the active cgroup limit when running inside a memory-constrained container.
/// On macOS, reads total physical memory via `sysctl`. Returns `None` if
/// detection fails on the current platform.
pub(crate) fn available_memory_bytes() -> Option<usize> {
    #[cfg(target_os = "linux")]
    {
        linux_available_memory()
    }
    #[cfg(target_os = "macos")]
    {
        macos_total_memory()
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        None
    }
}

/// Compute optimal max_states from available memory and per-state cost.
///
/// Each explored state consumes:
/// - `num_places * width.bytes()` for the packed marking (hash key)
/// - ~48 bytes overhead per state (Box, FxHashSet entry, queue amortization)
///
/// The `memory_fraction` controls what fraction of available memory to budget
/// for state storage (default 0.25 — conservative to leave room for queue,
/// graph adjacency lists, and marking vectors in `explore_full`).
///
/// When `fingerprint_dedup` is true, uses 32 bytes per state (u128 hash +
/// overhead) instead of `packed_size + 48`.
///
/// Returns `FALLBACK_MAX_STATES` (10M) if memory detection fails.
pub(crate) fn compute_max_states(
    num_places: usize,
    width: TokenWidth,
    memory_fraction: f64,
    fingerprint_dedup: bool,
) -> usize {
    let available = match available_memory_bytes() {
        Some(bytes) => bytes,
        None => return FALLBACK_MAX_STATES,
    };

    compute_max_states_from_available_memory(
        available,
        num_places,
        width,
        memory_fraction,
        fingerprint_dedup,
    )
}

/// Compute optimal `max_states` for full-graph CTL/LTL exploration.
///
/// Unlike plain exploration, `explore_full` stores both the packed frontier
/// state and the unpacked `Vec<u64>` marking for every state, plus adjacency.
/// Auto-sized CTL runs therefore need a tighter budget than the fingerprint-
/// only sizing used by observer-mode exploration.
pub(crate) fn compute_max_states_for_full_graph(
    num_places: usize,
    packed_places: usize,
    width: TokenWidth,
    memory_fraction: f64,
) -> usize {
    let available = match available_memory_bytes() {
        Some(bytes) => bytes,
        None => return FALLBACK_MAX_STATES,
    };

    compute_max_states_for_full_graph_from_available_memory(
        available,
        num_places,
        packed_places,
        width,
        memory_fraction,
    )
}

fn compute_max_states_from_available_memory(
    available: usize,
    num_places: usize,
    width: TokenWidth,
    memory_fraction: f64,
    fingerprint_dedup: bool,
) -> usize {
    let fraction = sanitize_memory_fraction(memory_fraction);
    let budget = (available as f64 * fraction) as usize;
    let bytes_per_state = if fingerprint_dedup {
        // Fingerprint mode: u128 (16) + hash entry overhead (~16)
        FINGERPRINT_BYTES_PER_STATE
    } else {
        let packed_size = num_places.saturating_mul(width.bytes());
        // Full marking mode: Box<[u8]> (16) + hash entry (~16) + queue (~16)
        packed_size.saturating_add(48).max(1)
    };

    let max = budget / bytes_per_state;

    // Clamp: at least the initial marking, at most u32::MAX (ReachabilityGraph uses u32 IDs)
    max.clamp(MIN_MAX_STATES, u32::MAX as usize)
}

fn compute_max_states_for_full_graph_from_available_memory(
    available: usize,
    num_places: usize,
    packed_places: usize,
    width: TokenWidth,
    memory_fraction: f64,
) -> usize {
    let fraction = sanitize_memory_fraction(memory_fraction);
    let budget = (available as f64 * fraction) as usize;
    let packed_bytes = packed_places.saturating_mul(width.bytes());
    let marking_bytes = num_places.saturating_mul(FULL_GRAPH_MARKING_BYTES_PER_PLACE);
    let bytes_per_state = FULL_GRAPH_BASE_BYTES_PER_STATE
        .saturating_add(FULL_GRAPH_EDGE_BYTES_PER_STATE_ESTIMATE)
        .saturating_add(packed_bytes)
        .saturating_add(marking_bytes)
        .max(1);
    let max = budget / bytes_per_state;

    max.clamp(MIN_MAX_STATES, u32::MAX as usize)
}

fn sanitize_memory_fraction(memory_fraction: f64) -> f64 {
    if !memory_fraction.is_finite() {
        return 0.0;
    }
    memory_fraction.clamp(0.0, 1.0)
}

#[cfg(target_os = "linux")]
fn linux_available_memory() -> Option<usize> {
    let contents = std::fs::read_to_string("/proc/meminfo").ok()?;
    let host_available = parse_linux_meminfo_available(&contents)?;
    Some(cap_available_memory(
        host_available,
        linux_cgroup_available_memory(),
    ))
}

#[cfg(any(target_os = "linux", test))]
fn parse_linux_meminfo_available(contents: &str) -> Option<usize> {
    parse_linux_meminfo_field(contents, "MemAvailable:")
        .or_else(|| parse_linux_meminfo_field(contents, "MemFree:"))
}

#[cfg(any(target_os = "linux", test))]
fn parse_linux_meminfo_field(contents: &str, field: &str) -> Option<usize> {
    contents.lines().find_map(|line| {
        let rest = line.strip_prefix(field)?;
        let kb_str = rest.trim().strip_suffix("kB")?.trim();
        let kb: usize = kb_str.parse().ok()?;
        kb.checked_mul(1024)
    })
}

#[cfg(any(target_os = "linux", test))]
fn cap_available_memory(host_available: usize, cgroup_available: Option<usize>) -> usize {
    cgroup_available.map_or(host_available, |available| host_available.min(available))
}

#[cfg(target_os = "linux")]
fn linux_cgroup_available_memory() -> Option<usize> {
    read_cgroup_available_memory("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory.current")
        .or_else(|| {
            read_cgroup_available_memory(
                "/sys/fs/cgroup/memory/memory.limit_in_bytes",
                "/sys/fs/cgroup/memory/memory.usage_in_bytes",
            )
        })
}

#[cfg(target_os = "linux")]
fn read_cgroup_available_memory(limit_path: &str, usage_path: &str) -> Option<usize> {
    let limit = std::fs::read_to_string(limit_path).ok()?;
    let usage = std::fs::read_to_string(usage_path).ok()?;
    cgroup_available_memory_from_raw(&limit, &usage)
}

#[cfg(any(target_os = "linux", test))]
fn cgroup_available_memory_from_raw(limit_raw: &str, usage_raw: &str) -> Option<usize> {
    let limit = parse_cgroup_limit_bytes(limit_raw)?;
    let Some(limit) = limit else {
        return None;
    };
    let current = parse_cgroup_bytes(usage_raw)?;
    Some(limit.saturating_sub(current))
}

#[cfg(any(target_os = "linux", test))]
fn parse_cgroup_limit_bytes(raw: &str) -> Option<Option<usize>> {
    let trimmed = raw.trim();
    if trimmed == "max" {
        return Some(None);
    }
    trimmed.parse::<usize>().ok().map(Some)
}

#[cfg(any(target_os = "linux", test))]
fn parse_cgroup_bytes(raw: &str) -> Option<usize> {
    raw.trim().parse().ok()
}

#[cfg(target_os = "macos")]
fn macos_total_memory() -> Option<usize> {
    let output = std::process::Command::new("sysctl")
        .args(["-n", "hw.memsize"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let s = std::str::from_utf8(&output.stdout).ok()?.trim();
    s.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_max_states_small_markings() {
        // With fingerprint: 32 bytes/state, 4GB budget → ~134M states
        let max = compute_max_states(50, TokenWidth::U8, 0.25, true);
        // Should always explore at least the initial marking.
        assert!(max >= MIN_MAX_STATES);
        // On any machine with ≥1GB RAM, should exceed fallback 10M
        if available_memory_bytes().unwrap_or(0) >= 4_000_000_000 {
            assert!(max > FALLBACK_MAX_STATES);
        }
    }

    #[test]
    fn test_compute_max_states_large_markings() {
        // 1000 places × 8 bytes (U64) = 8000 bytes + 48 overhead = 8048 bytes/state (non-fingerprint)
        // Even with large markings, should return at least the initial marking.
        let max = compute_max_states(1000, TokenWidth::U64, 0.25, false);
        assert!(max >= MIN_MAX_STATES);
    }

    #[test]
    fn test_compute_max_states_zero_places() {
        // Edge case: no places means 48 bytes overhead only (non-fingerprint)
        let max = compute_max_states(0, TokenWidth::U8, 0.25, false);
        assert!(max >= MIN_MAX_STATES);
    }

    #[test]
    fn test_compute_max_states_respects_low_memory_budget() {
        let max = compute_max_states_from_available_memory(
            64 * 1024 * 1024,
            1000,
            TokenWidth::U64,
            0.25,
            false,
        );
        assert_eq!(max, 2084);
    }

    #[test]
    fn test_compute_max_states_fingerprint_increases_budget() {
        // Same memory, fingerprint mode gives more states because 32 bytes/state
        // instead of 8048 bytes/state (1000 places × U64)
        let max_full = compute_max_states_from_available_memory(
            64 * 1024 * 1024,
            1000,
            TokenWidth::U64,
            0.25,
            false,
        );
        let max_fp = compute_max_states_from_available_memory(
            64 * 1024 * 1024,
            1000,
            TokenWidth::U64,
            0.25,
            true,
        );
        assert!(
            max_fp > max_full,
            "fingerprint mode should allow more states: {max_fp} vs {max_full}"
        );
    }

    #[test]
    fn test_compute_max_states_for_full_graph_accounts_for_markings_and_edges() {
        let max = compute_max_states_for_full_graph_from_available_memory(
            64 * 1024 * 1024,
            1_000,
            1_000,
            TokenWidth::U64,
            0.25,
        );
        assert_eq!(max, 1_042);
    }

    #[test]
    fn test_compute_max_states_for_full_graph_is_tighter_than_fingerprint_budget() {
        let max_fp = compute_max_states_from_available_memory(
            64 * 1024 * 1024,
            1_000,
            TokenWidth::U64,
            0.25,
            true,
        );
        let max_full = compute_max_states_for_full_graph_from_available_memory(
            64 * 1024 * 1024,
            1_000,
            1_000,
            TokenWidth::U64,
            0.25,
        );
        assert!(
            max_full < max_fp,
            "full-graph budget should be tighter than fingerprint-only sizing: \
             {max_full} vs {max_fp}"
        );
    }

    #[test]
    fn test_compute_max_states_zero_fraction_keeps_initial_state_only() {
        let max = compute_max_states_from_available_memory(
            16 * 1024 * 1024,
            50,
            TokenWidth::U8,
            0.0,
            false,
        );
        assert_eq!(max, 1);
    }

    #[test]
    fn test_compute_max_states_clamped_to_u32_max() {
        // Even with tiny states and huge memory, should not exceed u32::MAX
        let max =
            compute_max_states_from_available_memory(usize::MAX, 1, TokenWidth::U8, 1.0, false);
        assert!(max <= u32::MAX as usize);
    }

    #[test]
    fn test_available_memory_returns_some() {
        // On supported platforms (Linux/macOS), this should succeed
        let mem = available_memory_bytes();
        if cfg!(any(target_os = "linux", target_os = "macos")) {
            assert!(
                mem.is_some(),
                "memory detection should work on this platform"
            );
            assert!(mem.unwrap() > 0);
        }
    }

    #[test]
    fn test_parse_linux_meminfo_prefers_memavailable() {
        let contents = "MemFree: 128 kB\nMemAvailable: 256 kB\n";
        assert_eq!(parse_linux_meminfo_available(contents), Some(256 * 1024));
    }

    #[test]
    fn test_parse_linux_meminfo_falls_back_to_memfree() {
        let contents = "MemFree: 64 kB\n";
        assert_eq!(parse_linux_meminfo_available(contents), Some(64 * 1024));
    }

    #[test]
    fn test_cap_available_memory_prefers_cgroup_limit_when_smaller() {
        assert_eq!(cap_available_memory(8 * 1024, Some(3 * 1024)), 3 * 1024);
    }

    #[test]
    fn test_cap_available_memory_keeps_host_budget_without_cgroup_limit() {
        assert_eq!(cap_available_memory(8 * 1024, None), 8 * 1024);
    }

    #[test]
    fn test_cgroup_available_memory_uses_remaining_budget() {
        assert_eq!(
            cgroup_available_memory_from_raw("1048576\n", "262144\n"),
            Some(786_432)
        );
    }

    #[test]
    fn test_cgroup_available_memory_saturates_when_usage_exceeds_limit() {
        assert_eq!(
            cgroup_available_memory_from_raw("4096\n", "8192\n"),
            Some(0)
        );
    }

    #[test]
    fn test_cgroup_available_memory_ignores_unlimited_cgroup() {
        assert_eq!(cgroup_available_memory_from_raw("max\n", "262144\n"), None);
    }

    #[test]
    fn test_sanitize_memory_fraction_nan_returns_zero() {
        assert_eq!(sanitize_memory_fraction(f64::NAN), 0.0);
    }

    #[test]
    fn test_sanitize_memory_fraction_infinity_clamped() {
        assert_eq!(sanitize_memory_fraction(f64::INFINITY), 0.0);
        assert_eq!(sanitize_memory_fraction(f64::NEG_INFINITY), 0.0);
    }

    #[test]
    fn test_sanitize_memory_fraction_negative_clamped_to_zero() {
        assert_eq!(sanitize_memory_fraction(-0.5), 0.0);
    }

    #[test]
    fn test_sanitize_memory_fraction_above_one_clamped() {
        assert_eq!(sanitize_memory_fraction(2.0), 1.0);
    }

    #[test]
    fn test_sanitize_memory_fraction_valid_passthrough() {
        assert_eq!(sanitize_memory_fraction(0.5), 0.5);
        assert_eq!(sanitize_memory_fraction(0.0), 0.0);
        assert_eq!(sanitize_memory_fraction(1.0), 1.0);
    }

    #[test]
    fn test_compute_max_states_nan_fraction_returns_initial_only() {
        // NaN fraction → sanitize returns 0.0 → budget = 0 → clamp to MIN_MAX_STATES
        let max = compute_max_states_from_available_memory(
            16 * 1024 * 1024,
            50,
            TokenWidth::U8,
            f64::NAN,
            false,
        );
        assert_eq!(max, MIN_MAX_STATES);
    }

    #[test]
    fn test_compute_max_states_negative_fraction_returns_initial_only() {
        let max = compute_max_states_from_available_memory(
            16 * 1024 * 1024,
            50,
            TokenWidth::U8,
            -1.0,
            false,
        );
        assert_eq!(max, MIN_MAX_STATES);
    }
}
