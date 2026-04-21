// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::Value;
use super::{FuncBuilder, FuncValue, FP_UNSET};
use std::sync::atomic::AtomicU64;
use std::sync::{Arc, OnceLock};

impl FuncBuilder {
    /// Create a new empty builder.
    pub fn new() -> Self {
        FuncBuilder {
            entries: Vec::new(),
        }
    }

    /// Create a builder with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        FuncBuilder {
            entries: Vec::with_capacity(capacity),
        }
    }

    /// Insert a key-value pair. Duplicate keys will be deduplicated during build.
    #[inline]
    pub fn insert(&mut self, key: Value, value: Value) {
        self.entries.push((key, value));
    }

    /// Build the FuncValue, sorting and deduplicating entries.
    pub fn build(mut self) -> FuncValue {
        self.entries.sort_by(|a, b| a.0.cmp(&b.0));
        self.entries.dedup_by(|a, b| a.0 == b.0);
        #[cfg(feature = "memory-stats")]
        crate::value::memory_stats::inc_func_entries(self.entries.len());

        let (domain, values): (Vec<Value>, Vec<Value>) = self.entries.into_iter().unzip();

        FuncValue {
            domain: domain.into(),
            values: Arc::new(values),
            overrides: None,
            additive_fp: AtomicU64::new(FP_UNSET),
            tlc_normalized: OnceLock::new(),
        }
    }
}

impl Default for FuncBuilder {
    fn default() -> Self {
        Self::new()
    }
}
