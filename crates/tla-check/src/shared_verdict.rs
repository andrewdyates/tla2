// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Portfolio racing primitive for parallel verification lanes.
//!
//! Provides a lock-free [`SharedVerdict`] that enables parallel BFS and z4
//! PDR/BMC to race: the first lane to reach a definitive result publishes its
//! verdict, and the other lane(s) observe it via [`SharedVerdict::is_resolved`]
//! to stop early.
//!
//! Ported from `tla-petri/src/portfolio.rs` (Part of #3717).
//!
//! # Usage
//!
//! ```rust
//! use tla_check::shared_verdict::{SharedVerdict, Verdict};
//! use std::sync::Arc;
//!
//! let verdict = Arc::new(SharedVerdict::new());
//!
//! // Lane 1 (e.g., BFS) publishes a result:
//! assert!(verdict.publish(Verdict::Satisfied));
//!
//! // Lane 2 (e.g., PDR) observes the resolution:
//! assert!(verdict.is_resolved());
//! assert_eq!(verdict.get(), Some(Verdict::Satisfied));
//! ```

use std::sync::atomic::{AtomicU8, Ordering};

/// Possible verification outcomes for a TLA+ property.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The property holds (all reachable states satisfy the invariant).
    Satisfied,
    /// The property is violated (a counterexample exists).
    Violated,
    /// The verification was inconclusive (e.g., timeout, unsupported logic).
    Unknown,
}

const UNRESOLVED: u8 = 0;
const VERDICT_SATISFIED: u8 = 1;
const VERDICT_VIOLATED: u8 = 2;
const VERDICT_CANCELLED: u8 = 3;
// Unknown intentionally does not resolve the slot — other lanes should
// continue when one lane gives up without a definitive answer.
// Cancelled forces resolution when a lane panics (Part of #3867).

/// Thread-safe single-property verdict shared between portfolio lanes.
///
/// Uses a single `AtomicU8` with compare-exchange for lock-free, wait-free
/// coordination. The first lane to publish a definitive verdict (Satisfied
/// or Violated) wins; subsequent publishes are no-ops.
///
/// `Unknown` verdicts are never published — if a lane cannot determine the
/// result, it should let other lanes continue rather than claiming resolution.
#[derive(Debug)]
pub struct SharedVerdict {
    slot: AtomicU8,
}

impl SharedVerdict {
    /// Create a new unresolved verdict slot.
    pub fn new() -> Self {
        Self {
            slot: AtomicU8::new(UNRESOLVED),
        }
    }

    /// Publish a verdict. Returns `true` if this was the first resolution.
    ///
    /// Only `Satisfied` and `Violated` are published. `Unknown` is a no-op
    /// (returns `false`) because an inconclusive result from one lane should
    /// not prevent other lanes from finding a definitive answer.
    pub fn publish(&self, verdict: Verdict) -> bool {
        let val = match verdict {
            Verdict::Satisfied => VERDICT_SATISFIED,
            Verdict::Violated => VERDICT_VIOLATED,
            Verdict::Unknown => return false,
        };
        self.slot
            .compare_exchange(UNRESOLVED, val, Ordering::Release, Ordering::Relaxed)
            .is_ok()
    }

    /// Force-cancel the verdict, causing `is_resolved()` to return `true`.
    ///
    /// Used when a lane panics — the panic handler calls `cancel()` so that
    /// other lanes polling `is_resolved()` will exit their loops instead of
    /// spinning forever. Unlike `publish(Unknown)` (which is a no-op),
    /// `cancel()` unconditionally forces the slot to a resolved state.
    ///
    /// `get()` returns `None` for a cancelled verdict (there is no meaningful
    /// result to report). `is_resolved()` returns `true`.
    ///
    /// Part of #3867.
    pub fn cancel(&self) {
        // Use compare_exchange: if a real verdict was already published,
        // the slot is already resolved and we leave it alone. If no verdict
        // was published, this forces resolution with CANCELLED.
        let _ = self.slot.compare_exchange(
            UNRESOLVED,
            VERDICT_CANCELLED,
            Ordering::Release,
            Ordering::Relaxed,
        );
    }

    /// Check whether any lane has published a definitive verdict.
    ///
    /// Intended to be called periodically (e.g., every 4096 BFS states or
    /// between BMC depth iterations) as a cheap poll.
    #[inline]
    pub fn is_resolved(&self) -> bool {
        self.slot.load(Ordering::Acquire) != UNRESOLVED
    }

    /// Read the published verdict, if any.
    ///
    /// Returns `None` if no lane has published yet.
    pub fn get(&self) -> Option<Verdict> {
        match self.slot.load(Ordering::Acquire) {
            VERDICT_SATISFIED => Some(Verdict::Satisfied),
            VERDICT_VIOLATED => Some(Verdict::Violated),
            _ => None,
        }
    }
}

impl Default for SharedVerdict {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn test_initial_state_unresolved() {
        let sv = SharedVerdict::new();
        assert!(!sv.is_resolved());
        assert_eq!(sv.get(), None);
    }

    #[test]
    fn test_publish_satisfied() {
        let sv = SharedVerdict::new();
        assert!(sv.publish(Verdict::Satisfied));
        assert!(sv.is_resolved());
        assert_eq!(sv.get(), Some(Verdict::Satisfied));
    }

    #[test]
    fn test_publish_violated() {
        let sv = SharedVerdict::new();
        assert!(sv.publish(Verdict::Violated));
        assert!(sv.is_resolved());
        assert_eq!(sv.get(), Some(Verdict::Violated));
    }

    #[test]
    fn test_publish_unknown_does_not_resolve() {
        let sv = SharedVerdict::new();
        assert!(!sv.publish(Verdict::Unknown));
        assert!(!sv.is_resolved());
        assert_eq!(sv.get(), None);
    }

    #[test]
    fn test_cancel_forces_resolution() {
        let sv = SharedVerdict::new();
        assert!(!sv.is_resolved());
        sv.cancel();
        assert!(sv.is_resolved());
        // Cancelled verdict has no meaningful result.
        assert_eq!(sv.get(), None);
    }

    #[test]
    fn test_cancel_after_publish_preserves_verdict() {
        let sv = SharedVerdict::new();
        sv.publish(Verdict::Satisfied);
        sv.cancel(); // Should be a no-op since already resolved.
        assert_eq!(sv.get(), Some(Verdict::Satisfied));
    }

    #[test]
    fn test_first_writer_wins() {
        let sv = SharedVerdict::new();
        assert!(sv.publish(Verdict::Satisfied));
        // Second publish is a no-op.
        assert!(!sv.publish(Verdict::Violated));
        assert_eq!(sv.get(), Some(Verdict::Satisfied));
    }

    #[test]
    fn test_concurrent_publish() {
        let sv = Arc::new(SharedVerdict::new());
        let handles: Vec<_> = (0..8)
            .map(|i| {
                let sv = sv.clone();
                std::thread::spawn(move || {
                    let v = if i % 2 == 0 {
                        Verdict::Satisfied
                    } else {
                        Verdict::Violated
                    };
                    sv.publish(v)
                })
            })
            .collect();
        let wins: Vec<bool> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        // Exactly one thread should win.
        assert_eq!(wins.iter().filter(|&&w| w).count(), 1);
        assert!(sv.is_resolved());
        let v = sv.get().unwrap();
        assert!(v == Verdict::Satisfied || v == Verdict::Violated);
    }
}
