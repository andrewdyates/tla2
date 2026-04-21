// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Verify that EvictGuard clears evicting and notifies condvar on normal drop.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evict_guard_resets_flag_on_drop() {
    let barrier = EvictionBarrier {
        state: parking_lot::Mutex::new(EvictionState {
            evicting: true,
            epoch: 0,
            status: EVICTION_STATUS_SUCCESS,
        }),
        condvar: parking_lot::Condvar::new(),
    };
    {
        let _guard = EvictGuard { barrier: &barrier };
        assert!(
            barrier.state.lock().evicting,
            "evicting should be true while guard is alive"
        );
    }
    assert!(
        !barrier.state.lock().evicting,
        "evicting should be false after guard drops"
    );
}

/// Verify that EvictGuard clears evicting on panic unwind.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evict_guard_resets_flag_on_panic() {
    let barrier = EvictionBarrier {
        state: parking_lot::Mutex::new(EvictionState {
            evicting: true,
            epoch: 0,
            status: EVICTION_STATUS_SUCCESS,
        }),
        condvar: parking_lot::Condvar::new(),
    };
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = EvictGuard { barrier: &barrier };
        panic!("simulated do_evict panic");
    }));
    assert!(result.is_err(), "panic should propagate");
    assert!(
        !barrier.state.lock().evicting,
        "evicting must be cleared after panic unwind — without this, waiting threads block forever"
    );
}

/// Verify that the eviction condvar-wait terminates when peer success is published.
/// Simulates a concurrent eviction thread that completes after a short delay.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evict_condvar_wait_terminates_when_peer_success_published() {
    let tmp = tempfile::tempdir().unwrap();
    let set = std::sync::Arc::new(DiskFingerprintSet::new(100, tmp.path()).unwrap());

    // Manually set the evicting flag to simulate a concurrent eviction
    set.eviction_barrier.state.lock().evicting = true;

    // Spawn a thread that publishes success after a short delay
    let set_clone = std::sync::Arc::clone(&set);
    let handle = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(50));
        {
            let mut state = set_clone.eviction_barrier.state.lock();
            state.epoch = state.epoch.wrapping_add(1);
            state.status = EVICTION_STATUS_SUCCESS;
            state.evicting = false;
        }
        set_clone.eviction_barrier.condvar.notify_all();
    });

    // evict() should enter the condvar-wait path (evicting=true),
    // then succeed once the background thread publishes a successful outcome
    let result = set.evict();
    handle.join().unwrap();
    assert!(
        result.is_ok(),
        "evict should succeed after peer publishes: {:?}",
        result.err()
    );
}

/// Regression test for #2161: waiter threads must observe peer eviction failure.
#[cfg(unix)]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evict_waiter_observes_peer_failure() {
    use std::os::unix::fs::PermissionsExt;
    use std::sync::{Arc, Barrier};

    let tmp_dir = tempfile::tempdir().unwrap();
    let set = Arc::new(DiskFingerprintSet::new(100, tmp_dir.path()).unwrap());

    // Fill primary to ensure do_evict() has work and reaches disk I/O.
    for i in 1..=70 {
        assert_eq!(
            set.insert_checked(fp(i)),
            InsertOutcome::Inserted,
            "initial insert {i} should succeed"
        );
    }

    // Force eviction I/O failure.
    std::fs::set_permissions(tmp_dir.path(), std::fs::Permissions::from_mode(0o444)).unwrap();

    // Hold the barrier lock so the leader stays in do_evict() long enough for the
    // second thread to enter the waiter path.
    let barrier_lock = set.primary_barrier.write();
    let start = Arc::new(Barrier::new(3));

    let set_a = Arc::clone(&set);
    let start_a = Arc::clone(&start);
    let worker_a = std::thread::spawn(move || {
        start_a.wait();
        set_a.evict()
    });

    let set_b = Arc::clone(&set);
    let start_b = Arc::clone(&start);
    let worker_b = std::thread::spawn(move || {
        start_b.wait();
        set_b.evict()
    });

    start.wait();
    std::thread::sleep(std::time::Duration::from_millis(20));
    drop(barrier_lock);

    let result_a = worker_a.join().unwrap();
    let result_b = worker_b.join().unwrap();

    // Restore permissions for tempdir cleanup.
    std::fs::set_permissions(tmp_dir.path(), std::fs::Permissions::from_mode(0o755)).unwrap();

    let err_a = result_a.expect_err("one thread should return eviction error");
    let err_b = result_b.expect_err("second thread should return eviction error");
    let msg_a = err_a.to_string();
    let msg_b = err_b.to_string();

    assert!(
        msg_a.contains("peer eviction failed") || msg_b.contains("peer eviction failed"),
        "waiter must report peer failure; got: '{msg_a}' and '{msg_b}'"
    );
    assert_eq!(
        set.eviction_count(),
        1,
        "only one leader eviction should execute do_evict()"
    );
}

/// Regression test for #2280: waiter must not return spurious error when
/// eviction epoch advances by more than one (e.g., under contention where
/// multiple evictions complete before the waiter wakes).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evict_waiter_accepts_epoch_jump() {
    let tmp = tempfile::tempdir().unwrap();
    let set = std::sync::Arc::new(DiskFingerprintSet::new(100, tmp.path()).unwrap());

    // Simulate concurrent eviction already in progress.
    set.eviction_barrier.state.lock().evicting = true;

    // Spawn a thread that advances epoch by +2 (simulating two evictions
    // completing before the waiter wakes) with success status.
    let set_clone = std::sync::Arc::clone(&set);
    let handle = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(50));
        {
            let mut state = set_clone.eviction_barrier.state.lock();
            state.epoch = state.epoch.wrapping_add(2);
            state.status = EVICTION_STATUS_SUCCESS;
            state.evicting = false;
        }
        set_clone.eviction_barrier.condvar.notify_all();
    });

    let result = set.evict();
    handle.join().unwrap();
    assert!(
        result.is_ok(),
        "evict should succeed on epoch jump (> +1): {:?}",
        result.err()
    );
}

/// Regression test for #2280: waiter correctly reports peer failure even
/// when epoch advances by more than one.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evict_waiter_reports_failure_on_epoch_jump() {
    let tmp = tempfile::tempdir().unwrap();
    let set = std::sync::Arc::new(DiskFingerprintSet::new(100, tmp.path()).unwrap());

    set.eviction_barrier.state.lock().evicting = true;

    let set_clone = std::sync::Arc::clone(&set);
    let handle = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(50));
        {
            let mut state = set_clone.eviction_barrier.state.lock();
            state.epoch = state.epoch.wrapping_add(3);
            state.status = EVICTION_STATUS_FAILURE;
            state.evicting = false;
        }
        set_clone.eviction_barrier.condvar.notify_all();
    });

    let result = set.evict();
    handle.join().unwrap();
    assert!(
        result.is_err(),
        "evict should propagate peer failure on epoch jump"
    );
    assert!(
        result
            .unwrap_err()
            .to_string()
            .contains("peer eviction failed"),
        "error message should indicate peer failure"
    );
}

/// Regression test for #2281: waiter and leader use consistent epoch
/// arithmetic at u64 near-overflow.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_evict_waiter_handles_epoch_near_overflow() {
    let tmp = tempfile::tempdir().unwrap();
    let set = std::sync::Arc::new(DiskFingerprintSet::new(100, tmp.path()).unwrap());

    // Seed epoch near u64::MAX.
    let near_max_epoch = u64::MAX - 1;
    {
        let mut state = set.eviction_barrier.state.lock();
        state.epoch = near_max_epoch;
        state.status = EVICTION_STATUS_SUCCESS;
        state.evicting = true;
    }

    let set_clone = std::sync::Arc::clone(&set);
    let handle = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(50));
        {
            let mut state = set_clone.eviction_barrier.state.lock();
            state.epoch = near_max_epoch.wrapping_add(1);
            state.status = EVICTION_STATUS_SUCCESS;
            state.evicting = false;
        }
        set_clone.eviction_barrier.condvar.notify_all();
    });

    let result = set.evict();
    handle.join().unwrap();
    assert!(
        result.is_ok(),
        "evict should succeed near epoch overflow: {:?}",
        result.err()
    );
}
