// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State hash collision detection for fingerprint-based state storage.
//!
//! The model checker uses 64-bit fingerprints to detect previously-seen states.
//! Hash collisions could cause the checker to miss states, leading to unsound
//! verification. TLC computes the minimum distance between sorted fingerprints
//! (`checkFPs`) and reports the observed collision probability.
//!
//! This module provides three collision detection modes:
//!
//! - **None**: Zero overhead. Only the theoretical (birthday-paradox) collision
//!   probability is reported (default behavior, matching TLC).
//! - **Sampling**: Store full state for every Nth state and verify fingerprint
//!   uniqueness. Catches collisions with 1/N probability. Low memory overhead.
//! - **Full**: Store all states and verify every fingerprint maps to exactly one
//!   state. Catches all collisions but doubles memory usage.
//!
//! When a collision is detected (two distinct states with the same fingerprint),
//! it is reported as a soundness warning — the verification result may be
//! unsound because the checker may have skipped reachable states.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

use rustc_hash::FxHashMap;

use crate::state::{ArrayState, Fingerprint};

/// Collision detection mode, configurable via `--collision-check`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CollisionCheckMode {
    /// No collision detection beyond theoretical probability estimate.
    /// Zero runtime overhead. This is the default (matching TLC).
    #[default]
    None,
    /// Sample every Nth state for collision verification.
    /// Detects collisions with probability 1/N per colliding pair.
    /// Memory: O(states_found / N) full states stored.
    Sampling {
        /// Store one full state out of every `interval` states.
        /// Default: 1000 (one per thousand states sampled).
        interval: u64,
    },
    /// Store all states and verify every fingerprint is unique.
    /// Catches all collisions. Memory: O(states_found) full states.
    Full,
}

impl CollisionCheckMode {
    /// Parse a mode from a CLI string argument.
    pub fn from_str_arg(s: &str) -> Result<Self, String> {
        match s {
            "none" | "off" => Ok(CollisionCheckMode::None),
            "full" | "all" => Ok(CollisionCheckMode::Full),
            _ if s.starts_with("sampling") => {
                // "sampling" (default interval) or "sampling:N"
                if let Some(rest) = s.strip_prefix("sampling:") {
                    let interval: u64 = rest
                        .parse()
                        .map_err(|_| format!("invalid sampling interval: {rest:?}"))?;
                    if interval == 0 {
                        return Err("sampling interval must be > 0".to_string());
                    }
                    Ok(CollisionCheckMode::Sampling { interval })
                } else if s == "sampling" {
                    Ok(CollisionCheckMode::Sampling { interval: 1000 })
                } else {
                    Err(format!("unknown collision check mode: {s:?}"))
                }
            }
            _ => Err(format!(
                "unknown collision check mode: {s:?} (expected: none, sampling, sampling:N, full)"
            )),
        }
    }

    /// Whether this mode is active (not None).
    pub fn is_active(&self) -> bool {
        !matches!(self, CollisionCheckMode::None)
    }
}

/// Statistics collected during collision detection.
#[derive(Debug, Clone, Default)]
pub struct CollisionStats {
    /// Number of states sampled for collision verification.
    pub states_sampled: u64,
    /// Number of fingerprint collisions detected (distinct states, same fingerprint).
    pub collisions_detected: u64,
    /// Details of first N collisions (fingerprint, description).
    pub collision_details: Vec<CollisionDetail>,
}

/// Detail of a single detected collision.
#[derive(Debug, Clone)]
pub struct CollisionDetail {
    /// The fingerprint shared by two distinct states.
    pub fingerprint: Fingerprint,
    /// Number of variables in the states.
    pub num_vars: usize,
    /// Whether the two states differ (always true for real collisions).
    pub states_differ: bool,
}

/// Thread-safe collision detector.
///
/// Designed for integration into the BFS hot path with minimal contention.
/// The sampling counter uses an atomic; the state store uses a mutex-guarded
/// map (only accessed for sampled states, not every state).
pub(crate) struct CollisionDetector {
    mode: CollisionCheckMode,
    /// Counter for sampling: tracks how many states have been seen.
    state_counter: AtomicU64,
    /// Map from fingerprint -> stored ArrayState (serialized as compact values).
    /// Only populated for sampled states.
    sampled_states: Mutex<FxHashMap<Fingerprint, Vec<u8>>>,
    /// Collision statistics (protected by mutex for multi-thread safety).
    stats: Mutex<CollisionStats>,
    /// Maximum collision details to store (avoid unbounded growth).
    max_details: usize,
}

impl CollisionDetector {
    /// Create a new collision detector with the given mode.
    pub(crate) fn new(mode: CollisionCheckMode) -> Self {
        Self {
            mode,
            state_counter: AtomicU64::new(0),
            sampled_states: Mutex::new(FxHashMap::default()),
            stats: Mutex::new(CollisionStats::default()),
            max_details: 100,
        }
    }

    /// Check whether this detector is active (not None mode).
    #[inline]
    #[allow(dead_code)] // Retained for future use by collision reporting
    pub(crate) fn is_active(&self) -> bool {
        self.mode.is_active()
    }

    /// Record a state and check for collisions.
    ///
    /// This is called on the BFS hot path for every newly-admitted state.
    /// In `None` mode, this is a no-op. In `Sampling` mode, only every Nth
    /// state is stored and checked. In `Full` mode, every state is stored.
    ///
    /// Returns `true` if a collision was detected.
    pub(crate) fn record_state(&self, fp: Fingerprint, state: &ArrayState) -> bool {
        match self.mode {
            CollisionCheckMode::None => false,
            CollisionCheckMode::Sampling { interval } => {
                let count = self.state_counter.fetch_add(1, Ordering::Relaxed);
                if count % interval != 0 {
                    return false;
                }
                self.check_and_store(fp, state)
            }
            CollisionCheckMode::Full => {
                self.state_counter.fetch_add(1, Ordering::Relaxed);
                self.check_and_store(fp, state)
            }
        }
    }

    /// Store a state and check for collision with any previously-stored state
    /// that has the same fingerprint.
    fn check_and_store(&self, fp: Fingerprint, state: &ArrayState) -> bool {
        let serialized = serialize_array_state(state);

        let mut map = self.sampled_states.lock().unwrap();
        let mut stats = self.stats.lock().unwrap();
        stats.states_sampled += 1;

        match map.entry(fp) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(serialized);
                false
            }
            std::collections::hash_map::Entry::Occupied(entry) => {
                // Same fingerprint seen before — check if the state is different.
                let existing = entry.get();
                if *existing != serialized {
                    // COLLISION DETECTED: two distinct states with the same fingerprint.
                    stats.collisions_detected += 1;
                    if stats.collision_details.len() < self.max_details {
                        stats.collision_details.push(CollisionDetail {
                            fingerprint: fp,
                            num_vars: state.len(),
                            states_differ: true,
                        });
                    }
                    true
                } else {
                    // Same state, same fingerprint — not a collision, just a
                    // re-encounter (can happen in sampling mode if the same state
                    // is sampled twice before the fingerprint set dedup fires).
                    false
                }
            }
        }
    }

    /// Get a snapshot of the collision statistics.
    pub(crate) fn stats(&self) -> CollisionStats {
        self.stats.lock().unwrap().clone()
    }

    /// Get the collision detection mode.
    pub(crate) fn mode(&self) -> CollisionCheckMode {
        self.mode
    }
}

/// Serialize an ArrayState into a compact byte representation for comparison.
///
/// Uses the compact value bytes from the ArrayState's internal representation.
/// Two states are "the same" iff their serialized forms are byte-equal.
fn serialize_array_state(state: &ArrayState) -> Vec<u8> {
    // Use the materialized values for comparison. This ensures we compare
    // actual values, not internal representation details.
    let values = state.materialize_values();
    let mut buf = String::with_capacity(values.len() * 16);
    for v in &values {
        // Use Debug formatting as a deterministic serialization.
        // This is not the most efficient approach, but collision detection
        // is not on the hot path (only sampled states are serialized).
        use std::fmt::Write;
        write!(buf, "{:?}|", v).unwrap();
    }
    buf.into_bytes()
}

/// Format a collision detection summary for human output.
pub fn format_collision_report(stats: &CollisionStats, mode: CollisionCheckMode) -> String {
    let mut report = String::new();

    match mode {
        CollisionCheckMode::None => {
            report.push_str("  Collision detection: off");
        }
        CollisionCheckMode::Sampling { interval } => {
            report.push_str(&format!(
                "  Collision detection: sampling (1/{} states)\n",
                interval
            ));
            report.push_str(&format!("  States sampled: {}\n", stats.states_sampled));
            report.push_str(&format!(
                "  Collisions detected: {}",
                stats.collisions_detected
            ));
        }
        CollisionCheckMode::Full => {
            report.push_str("  Collision detection: full\n");
            report.push_str(&format!("  States verified: {}\n", stats.states_sampled));
            report.push_str(&format!(
                "  Collisions detected: {}",
                stats.collisions_detected
            ));
        }
    }

    if stats.collisions_detected > 0 {
        report.push_str("\n\n  WARNING: Fingerprint collisions detected!");
        report.push_str("\n  The verification result may be UNSOUND.");
        report.push_str("\n  Two or more distinct states share the same 64-bit fingerprint,");
        report.push_str("\n  causing the model checker to treat them as identical.");
        for detail in &stats.collision_details {
            report.push_str(&format!(
                "\n    - FP {:016x} ({} vars)",
                detail.fingerprint.0, detail.num_vars
            ));
        }
    }

    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Value;

    fn make_state(values: &[i64]) -> ArrayState {
        ArrayState::from_values(values.iter().copied().map(Value::int).collect())
    }

    #[test]
    fn test_mode_parsing() {
        assert_eq!(
            CollisionCheckMode::from_str_arg("none").unwrap(),
            CollisionCheckMode::None
        );
        assert_eq!(
            CollisionCheckMode::from_str_arg("off").unwrap(),
            CollisionCheckMode::None
        );
        assert_eq!(
            CollisionCheckMode::from_str_arg("full").unwrap(),
            CollisionCheckMode::Full
        );
        assert_eq!(
            CollisionCheckMode::from_str_arg("all").unwrap(),
            CollisionCheckMode::Full
        );
        assert_eq!(
            CollisionCheckMode::from_str_arg("sampling").unwrap(),
            CollisionCheckMode::Sampling { interval: 1000 }
        );
        assert_eq!(
            CollisionCheckMode::from_str_arg("sampling:500").unwrap(),
            CollisionCheckMode::Sampling { interval: 500 }
        );
        assert!(CollisionCheckMode::from_str_arg("sampling:0").is_err());
        assert!(CollisionCheckMode::from_str_arg("garbage").is_err());
    }

    #[test]
    fn test_none_mode_no_overhead() {
        let detector = CollisionDetector::new(CollisionCheckMode::None);
        let state = make_state(&[1, 2, 3]);
        assert!(!detector.record_state(Fingerprint(0x1234), &state));
        let stats = detector.stats();
        assert_eq!(stats.states_sampled, 0);
        assert_eq!(stats.collisions_detected, 0);
    }

    #[test]
    fn test_full_mode_no_collision() {
        let detector = CollisionDetector::new(CollisionCheckMode::Full);
        let s1 = make_state(&[1, 2]);
        let s2 = make_state(&[3, 4]);

        assert!(!detector.record_state(Fingerprint(0xAAAA), &s1));
        assert!(!detector.record_state(Fingerprint(0xBBBB), &s2));

        let stats = detector.stats();
        assert_eq!(stats.states_sampled, 2);
        assert_eq!(stats.collisions_detected, 0);
    }

    #[test]
    fn test_full_mode_detects_collision() {
        let detector = CollisionDetector::new(CollisionCheckMode::Full);
        let s1 = make_state(&[1, 2]);
        let s2 = make_state(&[3, 4]); // Different state

        // Same fingerprint, different states => collision
        let fp = Fingerprint(0xDEAD);
        assert!(!detector.record_state(fp, &s1)); // First insert, no collision
        assert!(detector.record_state(fp, &s2)); // Collision!

        let stats = detector.stats();
        assert_eq!(stats.states_sampled, 2);
        assert_eq!(stats.collisions_detected, 1);
        assert_eq!(stats.collision_details.len(), 1);
        assert_eq!(stats.collision_details[0].fingerprint, fp);
        assert!(stats.collision_details[0].states_differ);
    }

    #[test]
    fn test_full_mode_same_state_no_collision() {
        let detector = CollisionDetector::new(CollisionCheckMode::Full);
        let s1 = make_state(&[1, 2]);
        let s2 = make_state(&[1, 2]); // Same state

        let fp = Fingerprint(0xBEEF);
        assert!(!detector.record_state(fp, &s1));
        assert!(!detector.record_state(fp, &s2)); // Same state, not a collision

        let stats = detector.stats();
        assert_eq!(stats.collisions_detected, 0);
    }

    #[test]
    fn test_sampling_mode_interval() {
        let detector = CollisionDetector::new(CollisionCheckMode::Sampling { interval: 3 });

        // States 0, 1, 2, 3, 4, 5 — only 0 and 3 should be sampled
        for i in 0..6 {
            let state = make_state(&[i]);
            detector.record_state(Fingerprint(i as u64), &state);
        }

        let stats = detector.stats();
        // States at indices 0 and 3 are sampled (count % 3 == 0)
        assert_eq!(stats.states_sampled, 2);
    }

    #[test]
    fn test_sampling_mode_detects_collision_on_sampled_state() {
        let detector = CollisionDetector::new(CollisionCheckMode::Sampling { interval: 1 });
        // interval=1 means every state is sampled (same as Full)
        let s1 = make_state(&[10]);
        let s2 = make_state(&[20]);

        let fp = Fingerprint(0xCAFE);
        assert!(!detector.record_state(fp, &s1));
        assert!(detector.record_state(fp, &s2));

        let stats = detector.stats();
        assert_eq!(stats.collisions_detected, 1);
    }

    #[test]
    fn test_format_collision_report_none() {
        let stats = CollisionStats::default();
        let report = format_collision_report(&stats, CollisionCheckMode::None);
        assert!(report.contains("off"));
    }

    #[test]
    fn test_format_collision_report_with_collisions() {
        let stats = CollisionStats {
            states_sampled: 1000,
            collisions_detected: 2,
            collision_details: vec![
                CollisionDetail {
                    fingerprint: Fingerprint(0xDEAD),
                    num_vars: 3,
                    states_differ: true,
                },
                CollisionDetail {
                    fingerprint: Fingerprint(0xBEEF),
                    num_vars: 3,
                    states_differ: true,
                },
            ],
        };
        let report = format_collision_report(&stats, CollisionCheckMode::Full);
        assert!(report.contains("UNSOUND"));
        assert!(report.contains("000000000000dead"));
        assert!(report.contains("000000000000beef"));
    }

    #[test]
    fn test_multiple_collisions_capped() {
        let detector = CollisionDetector::new(CollisionCheckMode::Full);
        // The detector caps stored details at max_details (100).
        // Insert 200 colliding pairs.
        let base_state = make_state(&[0]);
        let fp = Fingerprint(0x1111);
        assert!(!detector.record_state(fp, &base_state));

        for i in 1..=150 {
            let state = make_state(&[i]);
            detector.record_state(fp, &state);
        }

        let stats = detector.stats();
        assert_eq!(stats.collisions_detected, 150);
        assert_eq!(stats.collision_details.len(), 100); // Capped at max_details
    }
}
