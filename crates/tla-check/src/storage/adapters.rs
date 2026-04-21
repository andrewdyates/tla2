// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DashSet adapter implementations for the [`FingerprintSet`] trait.
//!
//! These adapters allow `dashmap::DashSet` variants to be used as fingerprint
//! storage backends. The standard `DashSet<Fingerprint>` uses SipHash, while
//! the `DashSet<Fingerprint, FxBuildHasher>` variant uses FxHasher for faster
//! hashing of already-hashed fingerprint keys.

use crate::state::Fingerprint;
use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

use super::contracts::{FingerprintSet, StorageStats};
use tla_mc_core::InsertOutcome;
use tla_mc_core::LookupOutcome;

/// FxHasher-based BuildHasher for faster hashing of Fingerprint keys.
pub(crate) type FxBuildHasher = BuildHasherDefault<FxHasher>;

impl tla_mc_core::FingerprintSet<Fingerprint> for dashmap::DashSet<Fingerprint> {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        if dashmap::DashSet::insert(self, fp) {
            InsertOutcome::Inserted
        } else {
            InsertOutcome::AlreadyPresent
        }
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        if dashmap::DashSet::contains(self, &fp) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        dashmap::DashSet::len(self)
    }
}

impl FingerprintSet for dashmap::DashSet<Fingerprint> {
    fn stats(&self) -> StorageStats {
        StorageStats {
            memory_count: dashmap::DashSet::len(self),
            ..StorageStats::default()
        }
    }
}

/// FxHasher-based DashSet for faster fingerprint storage.
/// Since Fingerprint is already a 64-bit hash, FxHasher avoids redundant SipHash overhead.
impl tla_mc_core::FingerprintSet<Fingerprint> for dashmap::DashSet<Fingerprint, FxBuildHasher> {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        if dashmap::DashSet::insert(self, fp) {
            InsertOutcome::Inserted
        } else {
            InsertOutcome::AlreadyPresent
        }
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        if dashmap::DashSet::contains(self, &fp) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        dashmap::DashSet::len(self)
    }
}

impl FingerprintSet for dashmap::DashSet<Fingerprint, FxBuildHasher> {
    fn stats(&self) -> StorageStats {
        StorageStats {
            memory_count: dashmap::DashSet::len(self),
            ..StorageStats::default()
        }
    }
}
