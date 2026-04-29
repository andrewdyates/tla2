// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Portfolio execution primitive for racing parallel verification lanes.
//!
//! Provides a single-slot [`SharedVerdict`] for coordinating one SMT lane
//! against one BFS lane. The first lane to resolve publishes its verdict
//! and the other lane observes it via `is_resolved()` to stop early.

use std::sync::atomic::{AtomicU8, Ordering};

use crate::output::Verdict;

const UNRESOLVED: u8 = 0;
const VERDICT_TRUE: u8 = 1;
const VERDICT_FALSE: u8 = 2;

/// Thread-safe single-property verdict shared between portfolio lanes.
pub(crate) struct SharedVerdict {
    slot: AtomicU8,
}

impl SharedVerdict {
    pub(crate) fn new() -> Self {
        Self {
            slot: AtomicU8::new(UNRESOLVED),
        }
    }

    /// Publish a verdict. Returns `true` if this was the first resolution.
    pub(crate) fn publish(&self, verdict: Verdict) -> bool {
        let val = match verdict {
            Verdict::True => VERDICT_TRUE,
            Verdict::False => VERDICT_FALSE,
            Verdict::CannotCompute => return false,
        };
        self.slot
            .compare_exchange(UNRESOLVED, val, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }

    /// Check if the verdict has been resolved by either lane.
    pub(crate) fn is_resolved(&self) -> bool {
        self.slot.load(Ordering::Acquire) != UNRESOLVED
    }

    /// Read the final verdict. Returns `None` if still unresolved.
    pub(crate) fn verdict(&self) -> Option<Verdict> {
        match self.slot.load(Ordering::Acquire) {
            VERDICT_TRUE => Some(Verdict::True),
            VERDICT_FALSE => Some(Verdict::False),
            _ => None,
        }
    }
}
