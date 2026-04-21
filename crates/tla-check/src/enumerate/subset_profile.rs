// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fmt::Write as _;
use std::sync::atomic::{AtomicUsize, Ordering};

feature_flag!(pub(crate) enabled_for_process, "TLA2_SUBSET_PROFILE");

static CONSTRAINED_RUNTIME_ENTRIES: AtomicUsize = AtomicUsize::new(0);
static CONSTRAINED_FALLBACKS: AtomicUsize = AtomicUsize::new(0);
static CONSTRAINED_SUCCESSES: AtomicUsize = AtomicUsize::new(0);
static GENERATED_RESULT_TOTAL: AtomicUsize = AtomicUsize::new(0);
static GENERATED_RESULT_MAX: AtomicUsize = AtomicUsize::new(0);
static FREE_ELEMENTS_TOTAL: AtomicUsize = AtomicUsize::new(0);
static FREE_ELEMENTS_MAX: AtomicUsize = AtomicUsize::new(0);

#[allow(clippy::struct_field_names)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct SubsetProfileSnapshot {
    pub(crate) constrained_runtime_entries: usize,
    pub(crate) constrained_fallbacks: usize,
    pub(crate) constrained_successes: usize,
    pub(crate) generated_result_total: usize,
    pub(crate) generated_result_max: usize,
    pub(crate) free_elements_total: usize,
    pub(crate) free_elements_max: usize,
}

pub(crate) struct RunGuard {
    enabled: bool,
}

impl RunGuard {
    #[must_use]
    pub(crate) fn begin() -> Self {
        let enabled = enabled_for_process();
        if enabled {
            reset();
        }
        Self { enabled }
    }
}

impl Drop for RunGuard {
    fn drop(&mut self) {
        if !self.enabled {
            return;
        }
        let rendered = render(take_and_reset());
        eprint!("{rendered}");
    }
}

#[inline]
pub(crate) fn reset() {
    CONSTRAINED_RUNTIME_ENTRIES.store(0, Ordering::Relaxed);
    CONSTRAINED_FALLBACKS.store(0, Ordering::Relaxed);
    CONSTRAINED_SUCCESSES.store(0, Ordering::Relaxed);
    GENERATED_RESULT_TOTAL.store(0, Ordering::Relaxed);
    GENERATED_RESULT_MAX.store(0, Ordering::Relaxed);
    FREE_ELEMENTS_TOTAL.store(0, Ordering::Relaxed);
    FREE_ELEMENTS_MAX.store(0, Ordering::Relaxed);
}

#[inline]
pub(crate) fn record_entry() {
    if !enabled_for_process() {
        return;
    }
    CONSTRAINED_RUNTIME_ENTRIES.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn record_fallback() {
    if !enabled_for_process() {
        return;
    }
    CONSTRAINED_FALLBACKS.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn record_success(free_elements: usize, generated_results: usize) {
    if !enabled_for_process() {
        return;
    }
    CONSTRAINED_SUCCESSES.fetch_add(1, Ordering::Relaxed);
    GENERATED_RESULT_TOTAL.fetch_add(generated_results, Ordering::Relaxed);
    GENERATED_RESULT_MAX.fetch_max(generated_results, Ordering::Relaxed);
    FREE_ELEMENTS_TOTAL.fetch_add(free_elements, Ordering::Relaxed);
    FREE_ELEMENTS_MAX.fetch_max(free_elements, Ordering::Relaxed);
}

#[must_use]
pub(crate) fn take_and_reset() -> SubsetProfileSnapshot {
    SubsetProfileSnapshot {
        constrained_runtime_entries: CONSTRAINED_RUNTIME_ENTRIES.swap(0, Ordering::Relaxed),
        constrained_fallbacks: CONSTRAINED_FALLBACKS.swap(0, Ordering::Relaxed),
        constrained_successes: CONSTRAINED_SUCCESSES.swap(0, Ordering::Relaxed),
        generated_result_total: GENERATED_RESULT_TOTAL.swap(0, Ordering::Relaxed),
        generated_result_max: GENERATED_RESULT_MAX.swap(0, Ordering::Relaxed),
        free_elements_total: FREE_ELEMENTS_TOTAL.swap(0, Ordering::Relaxed),
        free_elements_max: FREE_ELEMENTS_MAX.swap(0, Ordering::Relaxed),
    }
}

#[must_use]
pub(crate) fn render(snapshot: SubsetProfileSnapshot) -> String {
    let mut out = String::new();
    let successes = snapshot.constrained_successes;
    let avg_generated_subsets = if successes > 0 {
        snapshot.generated_result_total as f64 / successes as f64
    } else {
        0.0
    };
    let avg_free_elements = if successes > 0 {
        snapshot.free_elements_total as f64 / successes as f64
    } else {
        0.0
    };

    writeln!(out, "=== SUBSET Profile ===").expect("invariant: String write must succeed");
    writeln!(
        out,
        "  constrained entries:      {}",
        snapshot.constrained_runtime_entries
    )
    .expect("invariant: String write must succeed");
    writeln!(
        out,
        "  constrained successes:    {}",
        snapshot.constrained_successes
    )
    .expect("invariant: String write must succeed");
    writeln!(
        out,
        "  constrained fallbacks:    {}",
        snapshot.constrained_fallbacks
    )
    .expect("invariant: String write must succeed");
    writeln!(
        out,
        "  avg generated subsets:    {avg_generated_subsets:.1}"
    )
    .expect("invariant: String write must succeed");
    writeln!(
        out,
        "  max generated subsets:    {}",
        snapshot.generated_result_max
    )
    .expect("invariant: String write must succeed");
    writeln!(out, "  avg free elements:        {avg_free_elements:.1}")
        .expect("invariant: String write must succeed");
    writeln!(
        out,
        "  max free elements:        {}",
        snapshot.free_elements_max
    )
    .expect("invariant: String write must succeed");
    writeln!(out, "======================").expect("invariant: String write must succeed");

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn render_includes_zero_entry_snapshot() {
        let rendered = render(SubsetProfileSnapshot::default());
        assert!(rendered.contains("=== SUBSET Profile ==="));
        assert!(rendered.contains("constrained entries:      0"));
        assert!(rendered.contains("avg generated subsets:    0.0"));
        assert!(rendered.contains("avg free elements:        0.0"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn render_uses_successes_for_averages() {
        let rendered = render(SubsetProfileSnapshot {
            constrained_runtime_entries: 5,
            constrained_fallbacks: 2,
            constrained_successes: 3,
            generated_result_total: 12,
            generated_result_max: 8,
            free_elements_total: 6,
            free_elements_max: 4,
        });

        assert!(rendered.contains("constrained entries:      5"));
        assert!(rendered.contains("constrained successes:    3"));
        assert!(rendered.contains("constrained fallbacks:    2"));
        assert!(rendered.contains("avg generated subsets:    4.0"));
        assert!(rendered.contains("max generated subsets:    8"));
        assert!(rendered.contains("avg free elements:        2.0"));
        assert!(rendered.contains("max free elements:        4"));
    }
}
