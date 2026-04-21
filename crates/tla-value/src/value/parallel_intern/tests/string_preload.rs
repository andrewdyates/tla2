// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! String-only preload tests for the parallel interning system.
//!
//! Design: `2026-03-17-3285-frozen-string-token-overlay-preload.md`
//! Extracted from `parallel_intern.rs` as part of #3325.

use super::*;

#[test]
fn no_preload_returns_frozen_arc() {
    let _lock = crate::value::lock_intern_state();
    // When overlays are empty (no preload), a frozen string lookup returns
    // the original frozen Arc<str> (pointer-equal).
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();

    let _ = strings::intern_string("preload_off_hello");
    freeze_value_interners();

    let frozen = FROZEN_SNAPSHOT
        .lock()
        .expect("lock")
        .clone()
        .expect("frozen");
    let frozen_arc = Arc::clone(frozen.strings.get("preload_off_hello").expect("in frozen"));

    // Manually install with empty overlays (bypasses the default preload)
    WORKER_INTERN.with(|c| {
        *c.borrow_mut() = Some(make_worker_state(
            Arc::clone(&frozen),
            FxHashMap::default(),
            FxHashMap::default(),
            FxHashMap::default(),
            FxHashMap::default(),
        ));
    });

    let result = parallel_intern_string("preload_off_hello").expect("found");
    assert!(
        Arc::ptr_eq(&result, &frozen_arc),
        "without preload, lookup must return the frozen snapshot's Arc<str>"
    );

    uninstall_worker_intern_scope();
    unfreeze_value_interners();
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();
}

#[test]
fn string_preload_enabled_returns_independent_arc() {
    let _lock = crate::value::lock_intern_state();
    // Design test 2: with string preload, a frozen string lookup returns a
    // worker-local Arc<str> that is content-equal but NOT pointer-equal.
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();

    let _ = strings::intern_string("preload_on_hello");
    freeze_value_interners();

    let frozen = FROZEN_SNAPSHOT
        .lock()
        .expect("lock")
        .clone()
        .expect("frozen");
    let frozen_arc = Arc::clone(frozen.strings.get("preload_on_hello").expect("in frozen"));

    // Install with forced string preload (bypasses OnceLock env var)
    let (string_overlay, string_token_overlay) = preload_frozen_string_overlays(&frozen);
    WORKER_INTERN.with(|c| {
        *c.borrow_mut() = Some(make_worker_state(
            Arc::clone(&frozen),
            FxHashMap::default(),
            FxHashMap::default(),
            string_overlay,
            string_token_overlay,
        ));
    });

    let result = parallel_intern_string("preload_on_hello").expect("found");
    assert_eq!(&*result, "preload_on_hello", "content must match");
    assert!(
        !Arc::ptr_eq(&result, &frozen_arc),
        "with preload, lookup must return a worker-local Arc, not the frozen one"
    );

    uninstall_worker_intern_scope();
    unfreeze_value_interners();
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();
}

#[test]
fn string_preload_token_matches_frozen_value() {
    let _lock = crate::value::lock_intern_state();
    // Design test 3: worker-local token lookup returns the original frozen
    // token value even though the Arc<str> is a worker-local copy.
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();

    let hello_arc = strings::intern_string("preload_tok_hello");
    let hello_tok = strings::tlc_string_token(&hello_arc);
    freeze_value_interners();

    let frozen = FROZEN_SNAPSHOT
        .lock()
        .expect("lock")
        .clone()
        .expect("frozen");
    let (string_overlay, string_token_overlay) = preload_frozen_string_overlays(&frozen);

    WORKER_INTERN.with(|c| {
        *c.borrow_mut() = Some(make_worker_state(
            Arc::clone(&frozen),
            FxHashMap::default(),
            FxHashMap::default(),
            string_overlay,
            string_token_overlay,
        ));
    });

    // Lookup returns worker-local Arc<str>
    let local_hello = parallel_intern_string("preload_tok_hello").expect("found");
    // Token lookup on that worker-local Arc must return the original frozen token
    let tok = parallel_tlc_string_token(&local_hello).expect("token");
    assert_eq!(
        tok, hello_tok,
        "preloaded token must match the original frozen token value"
    );

    uninstall_worker_intern_scope();
    unfreeze_value_interners();
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();
}

#[test]
fn string_preload_preserves_frozen_set_and_intfunc_sharing() {
    let _lock = crate::value::lock_intern_state();
    // Design test 4: set and int-function frozen hits remain pointer-equal
    // to the frozen snapshot under string-only preload, proving the slice
    // stayed string-only.
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();
    clear_set_intern_table();
    clear_int_func_intern_table();

    let _ = strings::intern_string("preload_share_hello");
    let set_elems = vec![Value::SmallInt(100), Value::SmallInt(200)];
    let _ = intern_tables::intern_set_array(set_elems.clone());
    let func_vals = vec![Value::SmallInt(300), Value::SmallInt(400)];
    let _ = intern_tables::intern_int_func_array(0, 1, func_vals.clone());
    freeze_value_interners();

    let frozen = FROZEN_SNAPSHOT
        .lock()
        .expect("lock")
        .clone()
        .expect("frozen");
    let set_fp = intern_tables::set_fingerprint(&set_elems);
    let func_fp = intern_tables::int_func_fingerprint(0, 1, &func_vals);
    let frozen_set = Arc::clone(frozen.sets.get(&set_fp).expect("set in frozen"));
    let frozen_func = Arc::clone(frozen.int_funcs.get(&func_fp).expect("func in frozen"));

    // Install with string-only preload (set_overlay and int_func_overlay empty)
    let (string_overlay, string_token_overlay) = preload_frozen_string_overlays(&frozen);
    WORKER_INTERN.with(|c| {
        *c.borrow_mut() = Some(make_worker_state(
            Arc::clone(&frozen),
            FxHashMap::default(),
            FxHashMap::default(),
            string_overlay,
            string_token_overlay,
        ));
    });

    // Set lookup hits frozen path — must be pointer-equal
    let result_set = parallel_intern_set(set_fp, &set_elems).expect("found set");
    assert!(
        Arc::ptr_eq(&result_set, &frozen_set),
        "set must remain pointer-equal to frozen under string-only preload"
    );

    // Int-func lookup hits frozen path — must be pointer-equal
    let result_func = parallel_intern_int_func(func_fp, &func_vals).expect("found func");
    assert!(
        Arc::ptr_eq(&result_func, &frozen_func),
        "int-func must remain pointer-equal to frozen under string-only preload"
    );

    uninstall_worker_intern_scope();
    unfreeze_value_interners();
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();
    clear_set_intern_table();
    clear_int_func_intern_table();
}
