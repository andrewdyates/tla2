// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FingerprintSet trait implementation for MmapFingerprintSet.

use crate::state::Fingerprint;

use crate::storage::contracts::{FingerprintSet, StorageStats};
use tla_mc_core::{CapacityStatus, InsertOutcome, LookupOutcome, StorageFault};

use super::MmapFingerprintSet;

impl tla_mc_core::FingerprintSet<Fingerprint> for MmapFingerprintSet {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        match MmapFingerprintSet::insert(self, fp) {
            Ok(true) => InsertOutcome::Inserted,
            Ok(false) => InsertOutcome::AlreadyPresent,
            Err(err) => {
                // Record the error so callers can detect dropped fingerprints.
                self.record_error();
                InsertOutcome::StorageFault(StorageFault::new("mmap", "insert", err.to_string()))
            }
        }
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        if MmapFingerprintSet::contains(self, fp) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        MmapFingerprintSet::len(self)
    }

    fn has_errors(&self) -> bool {
        MmapFingerprintSet::has_errors(self)
    }

    fn dropped_count(&self) -> usize {
        MmapFingerprintSet::dropped_count(self)
    }

    fn capacity_status(&self) -> CapacityStatus {
        MmapFingerprintSet::capacity_status(self)
    }
}

impl FingerprintSet for MmapFingerprintSet {
    fn stats(&self) -> StorageStats {
        StorageStats {
            memory_count: MmapFingerprintSet::len(self),
            memory_bytes: self.capacity.saturating_mul(std::mem::size_of::<u64>()),
            ..StorageStats::default()
        }
    }

    fn begin_checkpoint(&self) -> Result<(), StorageFault> {
        self.flush().map_err(|e: std::io::Error| {
            StorageFault::new("mmap", "begin_checkpoint", e.to_string())
        })
    }
    fn collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        Ok(self.collect_all().into_iter().map(Fingerprint).collect())
    }
}
