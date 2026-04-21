// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for `z4::api` and `z4::prelude` helper utility parity (#6589).
//!
//! Verifies that the helper slice (`VERSION`, panic helpers, `cached_env_flag!`)
//! is accessible through both the explicit-import (`z4::api`) and glob-import
//! (`z4::prelude`) consumer surfaces.

// ---- Packet C: api helper parity ----

#[test]
fn test_api_exports_helper_facade() {
    // VERSION is accessible and non-empty
    let v: &str = z4::api::VERSION;
    assert!(!v.is_empty(), "VERSION must be non-empty");

    // panic_payload_to_string converts &str payloads
    let s =
        z4::api::panic_payload_to_string(&("test payload" as &str) as &(dyn std::any::Any + Send));
    assert_eq!(s, "test payload");

    // panic_payload_to_string converts String payloads
    let s = z4::api::panic_payload_to_string(
        &String::from("owned payload") as &(dyn std::any::Any + Send)
    );
    assert_eq!(s, "owned payload");

    // is_z4_panic_reason is callable
    assert!(z4::api::is_z4_panic_reason("BUG: something broke"));
    assert!(!z4::api::is_z4_panic_reason("user error"));

    // catch_z4_panics can wrap a non-panicking closure
    let result: Result<i32, String> = z4::api::catch_z4_panics(|| Ok(42), Err);
    assert_eq!(result, Ok(42));

    // cached_env_flag! can be imported from api and expanded
    z4::api::cached_env_flag!(test_api_flag_6589, "Z4_TEST_API_FLAG_6589");
    let _ = test_api_flag_6589();
}

// ---- Packet C: prelude helper parity ----

#[test]
fn test_prelude_exports_helper_facade() {
    use z4::prelude::*;

    // VERSION is accessible and non-empty
    let v: &str = VERSION;
    assert!(!v.is_empty(), "VERSION must be non-empty");

    // panic_payload_to_string converts &str payloads
    let s = panic_payload_to_string(&("test payload" as &str) as &(dyn std::any::Any + Send));
    assert_eq!(s, "test payload");

    // panic_payload_to_string converts String payloads
    let s = panic_payload_to_string(&String::from("owned payload") as &(dyn std::any::Any + Send));
    assert_eq!(s, "owned payload");

    // is_z4_panic_reason is callable
    assert!(is_z4_panic_reason("BUG: something broke"));
    assert!(!is_z4_panic_reason("user error"));

    // catch_z4_panics can wrap a non-panicking closure
    // Note: prelude::* imports z4::Result which shadows std::result::Result,
    // so we use the fully qualified path here.
    let result: std::result::Result<i32, String> = catch_z4_panics(|| Ok(42), Err);
    assert_eq!(result, Ok(42));

    // cached_env_flag! can be imported from prelude and expanded
    cached_env_flag!(test_prelude_flag_6589, "Z4_TEST_PRELUDE_FLAG_6589");
    let _ = test_prelude_flag_6589();
}
