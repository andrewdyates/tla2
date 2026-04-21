// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Timeout handling for MCC cooperative time confinement.
//!
//! MCC sets `BK_TIME_CONFINEMENT` as the wall-clock budget in seconds.
//! We leave a safety margin for output formatting and cleanup.

use std::time::{Duration, Instant};

/// Safety margin in seconds subtracted from the time budget.
const SAFETY_MARGIN_SECS: u64 = 5;

/// Compute the exploration deadline from CLI timeout or MCC environment.
///
/// Priority: CLI `--timeout` flag > `BK_TIME_CONFINEMENT` env var > None.
/// Subtracts a safety margin to ensure output is written before the
/// MCC infrastructure kills the process.
#[must_use]
pub fn compute_deadline(cli_timeout_secs: Option<u64>) -> Option<Instant> {
    let budget = cli_timeout_secs.or_else(|| {
        std::env::var("BK_TIME_CONFINEMENT")
            .ok()?
            .parse::<u64>()
            .ok()
    });

    budget.map(|secs| {
        let adjusted = secs.saturating_sub(SAFETY_MARGIN_SECS);
        Instant::now() + Duration::from_secs(adjusted)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    /// Serialize tests that mutate BK_TIME_CONFINEMENT to prevent env var races.
    /// Rust runs tests in parallel; concurrent set/remove of the same env var
    /// causes non-deterministic failures.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn test_compute_deadline_cli_timeout_returns_some() {
        let deadline = compute_deadline(Some(60));
        assert!(deadline.is_some());
        // Deadline should be in the future (60 - 5 = 55 seconds from now)
        let remaining = deadline.unwrap().duration_since(Instant::now());
        // Allow 2s tolerance for test execution time
        assert!(remaining.as_secs() >= 50);
        assert!(remaining.as_secs() <= 55);
    }

    #[test]
    fn test_compute_deadline_none_without_env() {
        let _guard = ENV_LOCK.lock().unwrap();
        let prev = std::env::var("BK_TIME_CONFINEMENT").ok();
        std::env::remove_var("BK_TIME_CONFINEMENT");
        let deadline = compute_deadline(None);
        assert!(deadline.is_none());
        if let Some(val) = prev {
            std::env::set_var("BK_TIME_CONFINEMENT", val);
        }
    }

    #[test]
    fn test_compute_deadline_safety_margin_subtracted() {
        // With a 10s timeout, deadline should be ~5s away (10 - SAFETY_MARGIN_SECS)
        let deadline = compute_deadline(Some(10));
        let remaining = deadline.unwrap().duration_since(Instant::now());
        assert!(remaining.as_secs() <= 5);
    }

    #[test]
    fn test_compute_deadline_small_timeout_saturates_to_zero() {
        // Timeout smaller than safety margin should not underflow
        let deadline = compute_deadline(Some(2));
        assert!(deadline.is_some());
        // 2 - 5 saturates to 0, so deadline is essentially now
    }

    #[test]
    fn test_compute_deadline_cli_overrides_env() {
        let _guard = ENV_LOCK.lock().unwrap();
        let prev = std::env::var("BK_TIME_CONFINEMENT").ok();
        std::env::set_var("BK_TIME_CONFINEMENT", "3600");
        // CLI says 20, env says 3600 — CLI wins
        let deadline = compute_deadline(Some(20));
        let remaining = deadline.unwrap().duration_since(Instant::now());
        // Should be ~15s (20-5), not ~3595s (3600-5)
        assert!(remaining.as_secs() <= 15);
        if let Some(val) = prev {
            std::env::set_var("BK_TIME_CONFINEMENT", val);
        } else {
            std::env::remove_var("BK_TIME_CONFINEMENT");
        }
    }
}
