// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SubstCacheGuard arm/disarm/panic tests and SubstGuardEntry RAII tests.

use super::*;

/// Part of #2413: Test arm/disarm semantics — disarmed guard does NOT clear on drop.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subst_cache_guard_disarmed_preserves_cache() {
    clear_for_test_reset();
    insert_subst_cache("before_guard", Value::Bool(true));
    assert_eq!(subst_cache_len(), 1, "setup should populate SUBST_CACHE");

    {
        let mut guard = SubstCacheGuard::new();
        // Constructor arms the guard but does NOT clear the cache.
        // Cache clearing is done by on_cache_event(EvalEntry), not the guard.
        assert_eq!(
            subst_cache_len(),
            1,
            "guard ctor should NOT clear cache (arm/disarm semantics)"
        );

        insert_subst_cache("during_guard", Value::Bool(false));
        assert_eq!(subst_cache_len(), 2, "cache entries should accumulate");

        // Success path: disarm before drop.
        guard.disarm();
    }

    // Disarmed guard drop is a no-op — cache entries survive.
    assert_eq!(
        subst_cache_len(),
        2,
        "disarmed guard drop should NOT clear SUBST_CACHE"
    );
    clear_for_test_reset();
}

/// Part of #2413: Test that an armed guard (not disarmed) DOES clear on normal drop.
/// This covers the case where a guard is created but the caller forgets to disarm —
/// the cache is defensively cleared.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subst_cache_guard_armed_clears_on_drop() {
    clear_for_test_reset();
    insert_subst_cache("before_guard", Value::Bool(true));
    assert_eq!(subst_cache_len(), 1, "setup should populate SUBST_CACHE");

    {
        let _guard = SubstCacheGuard::new();
        insert_subst_cache("during_guard", Value::Bool(false));
        assert_eq!(subst_cache_len(), 2, "cache entries should accumulate");
        // Do NOT disarm — guard remains armed.
    }

    // Armed drop clears SUBST_CACHE (same behavior as panic path).
    assert_eq!(
        subst_cache_len(),
        0,
        "armed guard drop should clear SUBST_CACHE"
    );
    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subst_cache_guard_clears_cache_on_panic_unwind() {
    clear_for_test_reset();
    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = SubstCacheGuard::new();
        insert_subst_cache("panic_path", Value::Bool(true));
        assert_eq!(subst_cache_len(), 1, "cache populated before unwind");
        panic!("intentional unwind to exercise SubstCacheGuard::drop");
    }));

    assert!(unwind_result.is_err(), "panic should be caught");
    assert_eq!(
        subst_cache_len(),
        0,
        "guard drop should clear SUBST_CACHE during unwind"
    );
    clear_for_test_reset();
}

/// Verify that `clear_for_test_reset()` clears TLC registers (TLCSet/TLCGet storage).
/// Part of #1331: TLC register clearing was previously only available inside
/// `#[cfg(test)]`. Now `clear_tlc_registers()` is called by `clear_for_test_reset()`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_clear_for_test_reset_clears_tlc_registers() {
    clear_for_test_reset();

    // Populate TLC registers via the eval_debug pub(super) API.
    crate::eval_debug::EVAL_DEBUG_STATE.with(|s| {
        s.borrow_mut().tlc_registers.insert(1, Value::int(100));
        s.borrow_mut().tlc_registers.insert(2, Value::int(200));
    });
    let count_before = crate::eval_debug::EVAL_DEBUG_STATE.with(|s| s.borrow().tlc_registers.len());
    assert_eq!(
        count_before, 2,
        "TLC registers should have 2 entries before clear"
    );

    clear_for_test_reset();

    let count_after = crate::eval_debug::EVAL_DEBUG_STATE.with(|s| s.borrow().tlc_registers.len());
    assert_eq!(
        count_after, 0,
        "TLC registers should be empty after clear_for_test_reset()"
    );
}

// === SubstGuardEntry RAII guard tests (Part of #2413) ===
//
// Tests for the RAII substitution recursion guard that prevents infinite
// loops in chained INSTANCE evaluation. The guard pushes a NameId on creation
// and removes it on drop (including during panic unwind).

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subst_guard_entry_push_pop_lifo() {
    clear_subst_guard();
    let name_a = intern_name("guard_a");
    let name_b = intern_name("guard_b");

    assert!(!is_subst_guarded(name_a));
    assert!(!is_subst_guarded(name_b));

    let guard_a = SubstGuardEntry::new(name_a);
    assert!(is_subst_guarded(name_a));
    assert!(!is_subst_guarded(name_b));

    let guard_b = SubstGuardEntry::new(name_b);
    assert!(is_subst_guarded(name_a));
    assert!(is_subst_guarded(name_b));

    drop(guard_b);
    assert!(is_subst_guarded(name_a));
    assert!(!is_subst_guarded(name_b));

    drop(guard_a);
    assert!(!is_subst_guarded(name_a));
    assert!(!is_subst_guarded(name_b));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subst_guard_entry_out_of_order_drop() {
    clear_subst_guard();
    let name_a = intern_name("ooo_a");
    let name_b = intern_name("ooo_b");

    let guard_a = SubstGuardEntry::new(name_a);
    let guard_b = SubstGuardEntry::new(name_b);

    // Drop A first (out of order relative to push)
    drop(guard_a);
    assert!(!is_subst_guarded(name_a));
    assert!(is_subst_guarded(name_b));

    drop(guard_b);
    assert!(!is_subst_guarded(name_a));
    assert!(!is_subst_guarded(name_b));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subst_guard_entry_duplicate_name_id() {
    clear_subst_guard();
    let name = intern_name("dup_guard");

    let guard1 = SubstGuardEntry::new(name);
    let guard2 = SubstGuardEntry::new(name);
    assert!(is_subst_guarded(name));

    // Drop one — should still be guarded (second entry remains)
    drop(guard1);
    assert!(
        is_subst_guarded(name),
        "Dropping one of two duplicate guards should keep the name guarded"
    );

    drop(guard2);
    assert!(
        !is_subst_guarded(name),
        "Dropping both guards should remove the name from the guard"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subst_guard_entry_survives_clear() {
    // Tests the invariant: clear_subst_guard() called while RAII guards
    // are live makes the guards silently no-op on drop (no panic).
    clear_subst_guard();
    let name = intern_name("survive_clear");
    let guard = SubstGuardEntry::new(name);
    assert!(is_subst_guarded(name));

    clear_subst_guard();
    assert!(
        !is_subst_guarded(name),
        "Guard should not protect after clear"
    );

    // Drop should not panic even though clear already removed the entry
    drop(guard);
    assert!(!is_subst_guarded(name));
}
