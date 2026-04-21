// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel fingerprint-collision diagnostics (#2841).

use super::{ArrayState, Fingerprint, FxBuildHasher, ParallelChecker};
use dashmap::mapref::entry::Entry;
use dashmap::DashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

#[derive(Clone, Copy, Debug)]
pub(crate) struct CollisionDebugConfig {
    pub(super) track_seen_tlc_fp_dedup: bool,
    pub(super) seen_tlc_fp_dedup_collision_limit: usize,
    pub(super) track_internal_fp_collision: bool,
    pub(super) internal_fp_collision_limit: usize,
}

impl CollisionDebugConfig {
    pub(super) fn from_env() -> Option<Self> {
        let track_seen_tlc_fp_dedup = crate::check::debug::debug_seen_tlc_fp_dedup();
        let track_internal_fp_collision = crate::check::debug::debug_internal_fp_collision();
        if !track_seen_tlc_fp_dedup && !track_internal_fp_collision {
            return None;
        }

        Some(Self {
            track_seen_tlc_fp_dedup,
            seen_tlc_fp_dedup_collision_limit:
                crate::check::debug::debug_seen_tlc_fp_dedup_collision_limit(),
            track_internal_fp_collision,
            internal_fp_collision_limit: crate::check::debug::debug_internal_fp_collision_limit(),
        })
    }
}

pub(crate) struct ParallelCollisionDiagnostics {
    seen_tlc_fp_dedup: Option<DashMap<u64, Fingerprint, FxBuildHasher>>,
    seen_tlc_fp_dedup_collisions: AtomicU64,
    seen_tlc_fp_dedup_collision_limit: usize,
    internal_fp_collision: Option<DashMap<Fingerprint, u64, FxBuildHasher>>,
    internal_fp_collisions: AtomicU64,
    internal_fp_collision_limit: usize,
}

impl ParallelCollisionDiagnostics {
    pub(super) fn from_env(shard_amount: usize) -> Option<Arc<Self>> {
        CollisionDebugConfig::from_env().map(|config| Arc::new(Self::new(config, shard_amount)))
    }

    pub(super) fn new(config: CollisionDebugConfig, shard_amount: usize) -> Self {
        Self {
            seen_tlc_fp_dedup: config.track_seen_tlc_fp_dedup.then(|| {
                DashMap::with_hasher_and_shard_amount(FxBuildHasher::default(), shard_amount)
            }),
            seen_tlc_fp_dedup_collisions: AtomicU64::new(0),
            seen_tlc_fp_dedup_collision_limit: config.seen_tlc_fp_dedup_collision_limit,
            internal_fp_collision: config.track_internal_fp_collision.then(|| {
                DashMap::with_hasher_and_shard_amount(FxBuildHasher::default(), shard_amount)
            }),
            internal_fp_collisions: AtomicU64::new(0),
            internal_fp_collision_limit: config.internal_fp_collision_limit,
        }
    }

    pub(super) fn record_state(&self, fp: Fingerprint, array_state: &ArrayState, depth: usize) {
        let tlc_fp = if self.seen_tlc_fp_dedup.is_some() || self.internal_fp_collision.is_some() {
            let vals = array_state.materialize_values();
            crate::check::debug::tlc_fp_for_state_values(&vals).ok()
        } else {
            None
        };

        if let (Some(seen), Some(tlc_fp)) = (&self.seen_tlc_fp_dedup, tlc_fp) {
            match seen.entry(tlc_fp) {
                Entry::Vacant(entry) => {
                    entry.insert(fp);
                }
                Entry::Occupied(entry) => {
                    let first = *entry.get();
                    if first != fp {
                        let collisions = self
                            .seen_tlc_fp_dedup_collisions
                            .fetch_add(1, Ordering::Relaxed)
                            + 1;
                        if collisions <= self.seen_tlc_fp_dedup_collision_limit as u64 {
                            eprintln!(
                                "Warning: TLC FP dedup collision tlc={} first={:016x} now={:016x} depth={}",
                                crate::check::debug::fmt_tlc_fp(tlc_fp),
                                first.0,
                                fp.0,
                                depth
                            );
                        }
                    }
                }
            }
        }

        if let (Some(seen), Some(tlc_fp)) = (&self.internal_fp_collision, tlc_fp) {
            match seen.entry(fp) {
                Entry::Vacant(entry) => {
                    entry.insert(tlc_fp);
                }
                Entry::Occupied(entry) => {
                    let first_tlc = *entry.get();
                    if first_tlc != tlc_fp {
                        let collisions =
                            self.internal_fp_collisions.fetch_add(1, Ordering::Relaxed) + 1;
                        if collisions <= self.internal_fp_collision_limit as u64 {
                            eprintln!(
                                "Warning: internal FP collision internal={:016x} first_tlc={} now_tlc={} depth={}",
                                fp.0,
                                crate::check::debug::fmt_tlc_fp(first_tlc),
                                crate::check::debug::fmt_tlc_fp(tlc_fp),
                                depth
                            );
                        }
                    }
                }
            }
        }
    }

    pub(super) fn fp_dedup_collisions(&self) -> u64 {
        self.seen_tlc_fp_dedup_collisions.load(Ordering::Relaxed)
    }

    pub(super) fn internal_fp_collisions(&self) -> u64 {
        self.internal_fp_collisions.load(Ordering::Relaxed)
    }
}

impl ParallelChecker {
    pub(super) fn fp_dedup_collisions(&self) -> u64 {
        self.collision_diagnostics
            .as_ref()
            .map_or(0, |diag| diag.fp_dedup_collisions())
    }

    pub(super) fn internal_fp_collisions(&self) -> u64 {
        self.collision_diagnostics
            .as_ref()
            .map_or(0, |diag| diag.internal_fp_collisions())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Value;

    fn state(values: &[i64]) -> ArrayState {
        ArrayState::from_values(values.iter().copied().map(Value::int).collect())
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parallel_collision_counters_track_tlc_fp_dedup() {
        let diagnostics = ParallelCollisionDiagnostics::new(
            CollisionDebugConfig {
                track_seen_tlc_fp_dedup: true,
                seen_tlc_fp_dedup_collision_limit: 0,
                track_internal_fp_collision: false,
                internal_fp_collision_limit: 0,
            },
            4,
        );
        let arr = state(&[1, 2]);

        diagnostics.record_state(Fingerprint(0x1111), &arr, 0);
        diagnostics.record_state(Fingerprint(0x2222), &arr, 1);

        assert_eq!(diagnostics.fp_dedup_collisions(), 1);
        assert_eq!(diagnostics.internal_fp_collisions(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parallel_collision_counters_track_internal_fp() {
        let diagnostics = ParallelCollisionDiagnostics::new(
            CollisionDebugConfig {
                track_seen_tlc_fp_dedup: false,
                seen_tlc_fp_dedup_collision_limit: 0,
                track_internal_fp_collision: true,
                internal_fp_collision_limit: 0,
            },
            4,
        );

        diagnostics.record_state(Fingerprint(0x1111), &state(&[1]), 0);
        diagnostics.record_state(Fingerprint(0x1111), &state(&[2]), 1);

        assert_eq!(diagnostics.fp_dedup_collisions(), 0);
        assert_eq!(diagnostics.internal_fp_collisions(), 1);
    }
}
