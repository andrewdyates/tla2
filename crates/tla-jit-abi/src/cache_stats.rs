// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pure-data compilation statistics for the JIT/AOT ABI.
//!
//! These structs capture Cranelift compile-time and outcome counts for each
//! per-action compilation pass. They are pure data (no Cranelift handles)
//! and live here so `tla-check` can hold `Option<CacheBuildStats>` fields
//! without depending on `tla-jit` and its Cranelift forks. Originally moved
//! in Wave 16 Gate 1 Batches A/B and landed via TL-W14 cherry-pick from
//! TL-W13's preserved checkpoint (Part of #4267 / #4291).

use std::fmt;
use std::time::Duration;

/// Per-action JIT compilation statistics.
///
/// Captures the wall-clock compile time for a single next-state action
/// along with its bytecode size and success flag. Lives in `tla-jit-abi`
/// so `tla-check` can read compilation metrics without pulling in the
/// Cranelift crate.
///
/// Part of #3910 (JIT compilation latency instrumentation) /
/// #4267 Gate 1 Batch E.
#[derive(Debug, Clone)]
pub struct CompileStats {
    /// Name of the compiled action (e.g., "Increment" or "Next").
    pub action_name: String,
    /// Number of bytecode opcodes in the compiled function.
    pub opcode_count: usize,
    /// Wall-clock time for the Cranelift compilation pass.
    pub compile_time: Duration,
    /// Whether compilation succeeded.
    pub success: bool,
}

impl fmt::Display for CompileStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let status = if self.success { "ok" } else { "FAIL" };
        write!(
            f,
            "[jit] Compiled action {:?} in {:.1}ms ({} opcodes) [{}]",
            self.action_name,
            self.compile_time.as_secs_f64() * 1000.0,
            self.opcode_count,
            status,
        )
    }
}

/// Aggregate statistics from building a `JitNextStateCache`.
///
/// Pure-data record holding per-action compile stats plus totals. Lives in
/// `tla-jit-abi` so `tla-check` can own an `Option<CacheBuildStats>` field
/// without depending on `tla-jit`.
///
/// Part of #3910 / #4267 Gate 1 Batch E.
#[derive(Debug, Clone, Default)]
pub struct CacheBuildStats {
    /// Per-action compilation statistics.
    pub per_action: Vec<CompileStats>,
    /// Total wall-clock time for the entire cache build (including
    /// eligibility checks, not just Cranelift compilation).
    pub total_build_time: Duration,
    /// Number of actions that were successfully JIT-compiled.
    pub compiled_count: usize,
    /// Number of actions that were skipped (ineligible or failed).
    pub skipped_count: usize,
}

impl CacheBuildStats {
    /// Sum of all individual compile times (excludes eligibility overhead).
    #[must_use]
    pub fn total_compile_time(&self) -> Duration {
        self.per_action
            .iter()
            .filter(|s| s.success)
            .map(|s| s.compile_time)
            .sum()
    }
}

impl fmt::Display for CacheBuildStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[jit] Cache build: {}/{} actions compiled in {:.1}ms (compile={:.1}ms)",
            self.compiled_count,
            self.compiled_count + self.skipped_count,
            self.total_build_time.as_secs_f64() * 1000.0,
            self.total_compile_time().as_secs_f64() * 1000.0,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_stats_display_success() {
        let stats = CompileStats {
            action_name: "Increment".to_string(),
            opcode_count: 42,
            compile_time: Duration::from_millis(5),
            success: true,
        };
        let s = stats.to_string();
        assert!(s.contains("Increment"));
        assert!(s.contains("42"));
        assert!(s.contains("ok"));
    }

    #[test]
    fn test_compile_stats_display_failure() {
        let stats = CompileStats {
            action_name: "BadAction".to_string(),
            opcode_count: 10,
            compile_time: Duration::from_millis(1),
            success: false,
        };
        assert!(stats.to_string().contains("FAIL"));
    }

    #[test]
    fn test_cache_build_stats_total_compile_time_excludes_failed() {
        let stats = CacheBuildStats {
            per_action: vec![
                CompileStats {
                    action_name: "A".to_string(),
                    opcode_count: 1,
                    compile_time: Duration::from_millis(10),
                    success: true,
                },
                CompileStats {
                    action_name: "B".to_string(),
                    opcode_count: 2,
                    compile_time: Duration::from_millis(100),
                    success: false,
                },
                CompileStats {
                    action_name: "C".to_string(),
                    opcode_count: 3,
                    compile_time: Duration::from_millis(20),
                    success: true,
                },
            ],
            total_build_time: Duration::from_millis(200),
            compiled_count: 2,
            skipped_count: 1,
        };
        assert_eq!(stats.total_compile_time(), Duration::from_millis(30));
    }

    #[test]
    fn test_cache_build_stats_display() {
        let stats = CacheBuildStats {
            per_action: vec![],
            total_build_time: Duration::from_millis(50),
            compiled_count: 5,
            skipped_count: 2,
        };
        let s = stats.to_string();
        assert!(s.contains("5/7"));
        assert!(s.contains("50.0ms"));
    }
}
