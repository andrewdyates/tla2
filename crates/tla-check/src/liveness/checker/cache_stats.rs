// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Thread-local cache hit/miss counters for liveness caches.

use std::cell::Cell;

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
}

pub(crate) struct LocalCacheStats {
    hits: Cell<u64>,
    misses: Cell<u64>,
    evictions: Cell<u64>,
}

impl LocalCacheStats {
    const fn new() -> Self {
        Self {
            hits: Cell::new(0),
            misses: Cell::new(0),
            evictions: Cell::new(0),
        }
    }

    fn record_hit(&self) {
        self.hits.set(self.hits.get().saturating_add(1));
    }

    fn record_miss(&self) {
        self.misses.set(self.misses.get().saturating_add(1));
    }

    fn record_eviction(&self, count: u64) {
        self.evictions
            .set(self.evictions.get().saturating_add(count));
    }

    fn snapshot(&self) -> CacheStats {
        CacheStats {
            hits: self.hits.get(),
            misses: self.misses.get(),
            evictions: self.evictions.get(),
        }
    }

    fn take(&self) -> CacheStats {
        CacheStats {
            hits: self.hits.replace(0),
            misses: self.misses.replace(0),
            evictions: self.evictions.replace(0),
        }
    }
}

thread_local! {
    pub(crate) static SUBSCRIPT_CACHE_STATS: LocalCacheStats = const { LocalCacheStats::new() };
    pub(crate) static ENABLED_CACHE_STATS: LocalCacheStats = const { LocalCacheStats::new() };
}

#[inline]
pub(crate) fn record_subscript_hit() {
    SUBSCRIPT_CACHE_STATS.with(LocalCacheStats::record_hit);
}

#[inline]
pub(crate) fn record_subscript_miss() {
    SUBSCRIPT_CACHE_STATS.with(LocalCacheStats::record_miss);
}

#[inline]
pub(crate) fn record_subscript_eviction(count: u64) {
    SUBSCRIPT_CACHE_STATS.with(|stats| stats.record_eviction(count));
}

#[inline]
pub(crate) fn record_enabled_hit() {
    ENABLED_CACHE_STATS.with(LocalCacheStats::record_hit);
}

#[inline]
pub(crate) fn record_enabled_miss() {
    ENABLED_CACHE_STATS.with(LocalCacheStats::record_miss);
}

#[inline]
pub(crate) fn record_enabled_eviction(count: u64) {
    ENABLED_CACHE_STATS.with(|stats| stats.record_eviction(count));
}

pub(crate) fn take_cache_stats() -> (CacheStats, CacheStats) {
    (
        SUBSCRIPT_CACHE_STATS.with(LocalCacheStats::take),
        ENABLED_CACHE_STATS.with(LocalCacheStats::take),
    )
}

pub(crate) fn log_cache_stats() {
    let subscript = SUBSCRIPT_CACHE_STATS.with(LocalCacheStats::snapshot);
    let enabled = ENABLED_CACHE_STATS.with(LocalCacheStats::snapshot);

    eprintln!(
        "[liveness cache] subscript: hits={}, misses={}, evictions={}",
        subscript.hits, subscript.misses, subscript.evictions
    );
    eprintln!(
        "[liveness cache] enabled: hits={}, misses={}, evictions={}",
        enabled.hits, enabled.misses, enabled.evictions
    );
}
