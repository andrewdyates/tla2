// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test synchronization for global interning state.
//!
//! Tests that call `freeze_value_interners()`, `unfreeze_value_interners()`,
//! `clear_*_intern_table()`, or assert on global intern table counts must
//! serialize access to the global DashMap/OnceLock tables. The helper below is
//! reentrant on a single thread so test helpers can call `intern_string()`,
//! `tlc_string_token()`, etc. while already holding the guard.
//!
//! Uses a helper function that recovers from mutex poison (a previous test
//! panic does not cascade to all subsequent mutex-acquiring tests).

pub(crate) static INTERN_STATE_TEST_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

std::thread_local! {
    static INTERN_STATE_TEST_LOCK_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) struct InternStateTestGuard(Option<std::sync::MutexGuard<'static, ()>>);

impl Drop for InternStateTestGuard {
    fn drop(&mut self) {
        if let Some(guard) = self.0.take() {
            drop(guard);
        }
        INTERN_STATE_TEST_LOCK_DEPTH.with(|depth| {
            let current = depth.get();
            assert!(current > 0, "lock_intern_state depth underflow");
            depth.set(current - 1);
        });
    }
}

pub(crate) fn lock_intern_state() -> InternStateTestGuard {
    let needs_lock = INTERN_STATE_TEST_LOCK_DEPTH.with(|depth| {
        let current = depth.get();
        depth.set(current + 1);
        current == 0
    });

    let guard = needs_lock.then(|| {
        INTERN_STATE_TEST_MUTEX
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    });

    InternStateTestGuard(guard)
}
