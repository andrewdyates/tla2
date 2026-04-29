// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed seen-set contract for sequential observer-mode exploration.
//!
//! Parallel exploration now uses the shared `tla-mc-core` fingerprint storage,
//! so this module retains only the sequential helper used by the pilot and
//! checkpointable paths.

use rustc_hash::FxHashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InsertOutcome {
    Inserted,
    AlreadyPresent,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LookupOutcome {
    Present,
    Absent,
}

/// Single-threaded fingerprint membership set for sequential observer exploration.
pub(crate) struct LocalSeenSet {
    inner: FxHashSet<u128>,
}

impl LocalSeenSet {
    pub(crate) fn new() -> Self {
        Self {
            inner: FxHashSet::default(),
        }
    }

    pub(crate) fn insert_checked(&mut self, fp: u128) -> InsertOutcome {
        if self.inner.insert(fp) {
            InsertOutcome::Inserted
        } else {
            InsertOutcome::AlreadyPresent
        }
    }

    pub(crate) fn contains_checked(&self, fp: &u128) -> LookupOutcome {
        if self.inner.contains(fp) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.inner.len()
    }

    pub(crate) fn collect_fingerprints(&self) -> Vec<u128> {
        self.inner.iter().copied().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_local_seen_set_insert_and_lookup_roundtrip() {
        let mut set = LocalSeenSet::new();
        assert_eq!(set.len(), 0);
        assert_eq!(set.contains_checked(&42), LookupOutcome::Absent);

        assert_eq!(set.insert_checked(42), InsertOutcome::Inserted);
        assert_eq!(set.len(), 1);
        assert_eq!(set.contains_checked(&42), LookupOutcome::Present);
    }

    #[test]
    fn test_local_seen_set_duplicate_returns_already_present() {
        let mut set = LocalSeenSet::new();
        assert_eq!(set.insert_checked(99), InsertOutcome::Inserted);
        assert_eq!(set.insert_checked(99), InsertOutcome::AlreadyPresent);
        assert_eq!(set.len(), 1);
    }
}
