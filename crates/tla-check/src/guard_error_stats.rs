// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicUsize, Ordering};

// Guard-eval suppression diagnostics — always-on.
// The checker counts action-level guard evaluation errors that are intentionally
// treated as "not a guard" during guard pre-check. The cost is one atomic
// increment per suppressed error, which is negligible. After model checking
// completes, if the count is >0 we emit a warning that the state count may be
// incorrect. Part of #1467.
static SUPPRESSED_GUARD_EVAL_ERRORS: AtomicUsize = AtomicUsize::new(0);

#[inline]
pub(crate) fn reset() {
    SUPPRESSED_GUARD_EVAL_ERRORS.store(0, Ordering::Relaxed);
}

#[inline]
pub(crate) fn record_suppressed_action_level_error() {
    SUPPRESSED_GUARD_EVAL_ERRORS.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub(crate) fn take_and_reset() -> usize {
    SUPPRESSED_GUARD_EVAL_ERRORS.swap(0, Ordering::Relaxed)
}

#[cfg(test)]
pub(crate) fn with_test_lock<T>(f: impl FnOnce() -> T) -> T {
    use std::sync::{Mutex, OnceLock};

    static TEST_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    let lock = TEST_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    f()
}

/// Take the count, reset it, and emit a warning to stderr if non-zero.
///
/// Used as a convenience wrapper for Drop-based flush in the parallel checker.
pub(crate) fn emit_warning_and_reset() {
    let count = take_and_reset();
    if let Some(msg) = render_warning(count) {
        eprintln!("{}", msg);
    }
}

#[must_use]
pub(crate) fn render_warning(suppressed_count: usize) -> Option<String> {
    if suppressed_count == 0 {
        return None;
    }
    Some(format!(
        "Warning: {} guard evaluation errors were suppressed during guard checks — state count may be incorrect.",
        suppressed_count
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_render_warning_none_for_zero() {
        assert_eq!(render_warning(0), None);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_render_warning_message_for_nonzero() {
        let msg = render_warning(3).expect("nonzero suppression count should render");
        assert!(msg.contains("Warning: 3 guard evaluation errors were suppressed"));
        assert!(msg.contains("state count may be incorrect"));
    }
}
