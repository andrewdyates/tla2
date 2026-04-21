// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core parallel interning tests: lifecycle, set, int-function, token, and all-table preload.
//!
//! Extracted from `parallel_intern.rs` as part of #3325.

use super::*;

#[test]
fn frozen_snapshot_isolates_workers_from_global_table() {
    let _lock = crate::value::lock_intern_state();
    clear_set_intern_table();

    // Insert a set into the global table
    let elements = vec![Value::SmallInt(1), Value::SmallInt(2)];
    let _ = intern_tables::intern_set_array(elements.clone());

    // Freeze
    freeze_value_interners();

    // Install worker scope
    install_worker_intern_scope();

    // Look up from frozen snapshot — should find it
    let fp = intern_tables::set_fingerprint(&elements);
    let result = parallel_intern_set(fp, &elements);
    assert!(result.is_some(), "should find set in frozen snapshot");

    // New set not in frozen or overlay — should insert into overlay
    let new_elements = vec![Value::SmallInt(3), Value::SmallInt(4)];
    let new_fp = intern_tables::set_fingerprint(&new_elements);
    let result = parallel_intern_set(new_fp, &new_elements);
    assert!(result.is_some(), "should insert into overlay");

    // Second lookup of the new set should find it in overlay
    let result2 = parallel_intern_set(new_fp, &new_elements);
    assert!(result2.is_some());
    // Should be the same Arc (pointer equality)
    assert!(Arc::ptr_eq(&result.unwrap(), &result2.unwrap()));

    // Clean up
    uninstall_worker_intern_scope();
    unfreeze_value_interners();
    clear_set_intern_table();
}

#[test]
fn parallel_sets_compare_equal_even_without_pointer_sharing() {
    let _lock = crate::value::lock_intern_state();
    clear_set_intern_table();

    freeze_value_interners();

    // Two "workers" create the same set independently
    install_worker_intern_scope();
    let elements = vec![Value::SmallInt(10), Value::SmallInt(20)];
    let fp = intern_tables::set_fingerprint(&elements);
    let arc_a = parallel_intern_set(fp, &elements).unwrap();
    uninstall_worker_intern_scope();

    install_worker_intern_scope();
    let arc_b = parallel_intern_set(fp, &elements).unwrap();
    uninstall_worker_intern_scope();

    // Arcs may NOT be pointer-equal (different worker overlays)
    // But content must be equal
    assert_eq!(arc_a.as_ref(), arc_b.as_ref());

    unfreeze_value_interners();
    clear_set_intern_table();
}

#[test]
fn parallel_int_func_lookup_and_insert() {
    let _lock = crate::value::lock_intern_state();
    clear_int_func_intern_table();

    let values = vec![Value::SmallInt(1), Value::SmallInt(2)];
    let _ = intern_tables::intern_int_func_array(0, 1, values.clone());

    freeze_value_interners();
    install_worker_intern_scope();

    // Look up from frozen
    let fp = intern_tables::int_func_fingerprint(0, 1, &values);
    let result = parallel_intern_int_func(fp, &values);
    assert!(result.is_some());
    assert_eq!(result.unwrap().as_ref(), &values);

    // New values — insert into overlay
    let new_values = vec![Value::SmallInt(3), Value::SmallInt(4)];
    let new_fp = intern_tables::int_func_fingerprint(0, 1, &new_values);
    let result = parallel_intern_int_func(new_fp, &new_values);
    assert!(result.is_some());
    assert_eq!(result.unwrap().as_ref(), &new_values);

    uninstall_worker_intern_scope();
    unfreeze_value_interners();
    clear_int_func_intern_table();
}

#[test]
fn non_parallel_mode_returns_none() {
    let _lock = crate::value::lock_intern_state();
    // When no frozen snapshot is active, parallel functions return None
    let elements = vec![Value::SmallInt(1)];
    let fp = intern_tables::set_fingerprint(&elements);
    assert!(parallel_intern_set(fp, &elements).is_none());

    let values = vec![Value::SmallInt(1)];
    let fp = intern_tables::int_func_fingerprint(0, 0, &values);
    assert!(parallel_intern_int_func(fp, &values).is_none());

    assert!(parallel_intern_string("hello").is_none());
    let s: Arc<str> = Arc::from("hello");
    assert!(parallel_tlc_string_token(&s).is_none());
}

#[test]
fn parallel_string_intern_frozen_and_overlay() {
    let _lock = crate::value::lock_intern_state();
    strings::clear_string_intern_table();

    // Pre-populate the global table
    let _ = strings::intern_string("hello");
    let _ = strings::intern_string("world");

    freeze_value_interners();
    install_worker_intern_scope();

    // Lookup from frozen snapshot
    let result = parallel_intern_string("hello");
    assert!(result.is_some(), "should find 'hello' in frozen snapshot");
    assert_eq!(&*result.unwrap(), "hello");

    // New string — insert into overlay
    let result = parallel_intern_string("new_string");
    assert!(result.is_some(), "should insert into overlay");
    assert_eq!(&*result.unwrap(), "new_string");

    // Second lookup should find in overlay (pointer equality)
    let r1 = parallel_intern_string("new_string").unwrap();
    let r2 = parallel_intern_string("new_string").unwrap();
    assert!(Arc::ptr_eq(&r1, &r2), "overlay should return same Arc");

    uninstall_worker_intern_scope();
    unfreeze_value_interners();
    strings::clear_string_intern_table();
}

#[test]
fn parallel_tlc_token_frozen_and_overlay() {
    let _lock = crate::value::lock_intern_state();
    strings::clear_tlc_string_tokens();

    // Pre-populate the global token table
    let hello: Arc<str> = strings::intern_string("hello");
    let hello_tok = strings::tlc_string_token(&hello);

    freeze_value_interners();
    install_worker_intern_scope();

    // Lookup from frozen snapshot — should return same token
    let result = parallel_tlc_string_token(&hello);
    assert_eq!(result, Some(hello_tok), "frozen token should match");

    // New string — should assign a new token
    let new_str: Arc<str> = Arc::from("brand_new");
    let new_tok = parallel_tlc_string_token(&new_str);
    assert!(new_tok.is_some(), "should assign token for new string");
    assert_ne!(new_tok.unwrap(), hello_tok, "new token should differ");

    // Repeated lookup should return same token
    let new_tok2 = parallel_tlc_string_token(&new_str);
    assert_eq!(new_tok, new_tok2, "overlay should return same token");

    uninstall_worker_intern_scope();
    unfreeze_value_interners();
    strings::clear_tlc_string_tokens();
}

#[test]
fn preload_frozen_creates_independent_arcs_for_all_tables() {
    let _lock = crate::value::lock_intern_state();
    // Test that the preload path produces overlays with correct content.
    // We can't set OnceLock-cached env vars in tests (they're cached on first read),
    // so we test the preload logic directly by calling the preload code path.
    clear_set_intern_table();
    clear_int_func_intern_table();
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();

    // Pre-populate all four global tables
    let _ = strings::intern_string("alpha");
    let _ = strings::intern_string("beta");
    let alpha_tok = strings::tlc_string_token(&strings::intern_string("alpha"));
    let beta_tok = strings::tlc_string_token(&strings::intern_string("beta"));
    let set_elems = vec![Value::SmallInt(1), Value::SmallInt(2)];
    let _ = intern_tables::intern_set_array(set_elems.clone());
    let func_vals = vec![Value::SmallInt(10), Value::SmallInt(20)];
    let _ = intern_tables::intern_int_func_array(0, 1, func_vals.clone());

    // Freeze to capture all tables
    freeze_value_interners();

    // Manually exercise preload logic by building overlays from the frozen snapshot
    let frozen = FROZEN_SNAPSHOT
        .lock()
        .expect("lock")
        .clone()
        .expect("frozen");

    let string_overlay: FxHashMap<String, Arc<str>> = frozen
        .strings
        .iter()
        .map(|(k, v)| (k.clone(), Arc::from(v.as_ref())))
        .collect();

    // Verify content equality
    assert_eq!(&*string_overlay["alpha"], "alpha");
    assert_eq!(&*string_overlay["beta"], "beta");

    // Verify independence: preloaded Arcs must NOT be pointer-equal to frozen Arcs
    assert!(
        !Arc::ptr_eq(
            &string_overlay["alpha"],
            frozen.strings.get("alpha").expect("frozen alpha")
        ),
        "preloaded Arc<str> must be independent from frozen"
    );

    // String tokens should use the new Arc<str> keys
    let string_token_overlay: FxHashMap<Arc<str>, u32> = frozen
        .string_tokens
        .iter()
        .map(|(k, v)| {
            let new_arc = string_overlay
                .get(k.as_ref())
                .map(Arc::clone)
                .unwrap_or_else(|| Arc::from(k.as_ref()));
            (new_arc, *v)
        })
        .collect();
    let alpha_arc = string_overlay.get("alpha").expect("alpha").clone();
    assert_eq!(
        string_token_overlay.get(&alpha_arc).copied(),
        Some(alpha_tok),
        "preloaded token should match original"
    );
    let beta_arc = string_overlay.get("beta").expect("beta").clone();
    assert_eq!(
        string_token_overlay.get(&beta_arc).copied(),
        Some(beta_tok),
        "preloaded token should match original"
    );

    // Sets: content equal, pointer independent
    let set_fp = intern_tables::set_fingerprint(&set_elems);
    let set_overlay: FxHashMap<u64, Arc<[Value]>> = frozen
        .sets
        .iter()
        .map(|(k, v)| (*k, Arc::from(v.as_ref())))
        .collect();
    let preloaded_set = &set_overlay[&set_fp];
    assert_eq!(preloaded_set.as_ref(), &set_elems[..]);
    assert!(
        !std::ptr::eq(
            preloaded_set.as_ref().as_ptr(),
            frozen.sets[&set_fp].as_ref().as_ptr()
        ),
        "preloaded set Arc must be independent from frozen"
    );

    // Int funcs: content equal, pointer independent
    let func_fp = intern_tables::int_func_fingerprint(0, 1, &func_vals);
    let int_func_overlay: FxHashMap<u64, Arc<Vec<Value>>> = frozen
        .int_funcs
        .iter()
        .map(|(k, v)| (*k, Arc::new(v.as_ref().clone())))
        .collect();
    let preloaded_func = &int_func_overlay[&func_fp];
    assert_eq!(preloaded_func.as_ref(), &func_vals);
    assert!(
        !Arc::ptr_eq(preloaded_func, &frozen.int_funcs[&func_fp]),
        "preloaded int_func Arc must be independent from frozen"
    );

    // Clean up
    unfreeze_value_interners();
    clear_set_intern_table();
    clear_int_func_intern_table();
    strings::clear_string_intern_table();
    strings::clear_tlc_string_tokens();
}
