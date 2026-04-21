// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Part of #2724: Verify parallel model check lifecycle clears interned markers.

use super::*;

/// Part of #2724: Verify that the parallel model check lifecycle clears interned markers.
///
/// Previous version asserted `get_interner().len() == 0` which is racy under
/// concurrent test execution. Fix: use unique marker values and wait for
/// concurrent runs to finish before asserting markers were cleared.
/// Part of #4067: Wait for quiescence BEFORE acquiring the interner lock
/// to avoid blocking parallel tests while waiting for long-running
/// sequential tests (e.g., real_disruptor) to finish.
#[cfg_attr(test, ntest::timeout(180_000))]
#[test]
fn test_check_module_parallel_clears_value_interner_between_runs() {
    use crate::intern::{clear_global_value_interner, get_interner, wait_for_no_active_runs};
    use crate::state::value_fingerprint;

    // Part of #4067: Wait for ALL concurrent model check runs to finish
    // BEFORE acquiring the lock.
    wait_for_no_active_runs();

    let _serial = crate::test_utils::acquire_interner_lock();

    let src = r#"
---- MODULE InternerCleanupParallel ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;
    let module = parse_module(src);
    let config = crate::config::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    // Use unique marker values that no other test will insert.
    let marker1 = crate::Value::int(888_888_001);
    let marker1_fp = value_fingerprint(&marker1);
    let marker2 = crate::Value::int(888_888_002);
    let marker2_fp = value_fingerprint(&marker2);

    clear_global_value_interner();
    get_interner().intern(marker1);
    assert!(
        get_interner().contains_fp(marker1_fp),
        "precondition: marker1 should be in interner"
    );

    let first = check_module_parallel(&module, &config, 1);
    assert!(matches!(first, CheckResult::Success(_)), "{first:?}");
    wait_for_no_active_runs();
    assert!(
        !get_interner().contains_fp(marker1_fp),
        "marker1 should be cleared after all model check runs complete"
    );

    get_interner().intern(marker2);
    assert!(
        get_interner().contains_fp(marker2_fp),
        "precondition: marker2 should be in interner"
    );

    let second = check_module_parallel(&module, &config, 1);
    assert!(matches!(second, CheckResult::Success(_)), "{second:?}");
    wait_for_no_active_runs();
    assert!(
        !get_interner().contains_fp(marker2_fp),
        "marker2 should be cleared after second run completes"
    );
}
