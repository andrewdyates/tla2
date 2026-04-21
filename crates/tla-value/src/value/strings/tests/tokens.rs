// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::tokens::get_token_table;
use super::super::{
    clear_string_intern_table, clear_tlc_string_tokens, intern_string, tlc_string_token,
};
use crate::value::Value;
use std::sync::Arc;

/// Part of #3287: Verify that intern_string() eagerly assigns TLC tokens.
/// After interning, the token should already exist in the token table
/// without needing a separate tlc_string_token() call.
#[test]
fn intern_string_eagerly_assigns_tlc_token() {
    let _lock = crate::value::lock_intern_state();
    clear_string_intern_table();
    clear_tlc_string_tokens();

    // Intern three strings in a known order
    let a = intern_string("eager_alpha");
    let b = intern_string("eager_bravo");
    let c = intern_string("eager_charlie");

    // Tokens should already be assigned (by intern_string, not by this test)
    let ta = tlc_string_token(&a);
    let tb = tlc_string_token(&b);
    let tc = tlc_string_token(&c);

    // Tokens should reflect intern order: a < b < c
    assert!(
        ta < tb && tb < tc,
        "Tokens should reflect intern order: ta={ta}, tb={tb}, tc={tc}"
    );

    // Interning the same string again should return the same token
    let a2 = intern_string("eager_alpha");
    let ta2 = tlc_string_token(&a2);
    assert_eq!(ta, ta2, "Re-interning should return the same token");

    clear_string_intern_table();
    clear_tlc_string_tokens();
}

/// Part of #3287 criterion 3: Dynamically created strings (like those from
/// string concatenation `\o` or ToString) get TLC tokens eagerly when
/// routed through intern_string(). This simulates the eval_arith.rs `\o`
/// path which now uses intern_string() instead of Arc::from().
#[test]
fn dynamic_string_concat_gets_eager_token() {
    let _lock = crate::value::lock_intern_state();
    clear_string_intern_table();
    clear_tlc_string_tokens();

    // Simulate parse-time strings (interned at spec load)
    let hello = intern_string("dyn_concat_test_3287_hello");
    let world = intern_string("dyn_concat_test_3287_world");

    // Token should already be assigned by intern_string(), not deferred
    let t_hello = tlc_string_token(&hello);
    let t_world = tlc_string_token(&world);
    assert_ne!(t_hello, 0, "Token should be assigned (non-zero)");
    assert_ne!(t_world, 0, "Token should be assigned (non-zero)");
    assert_ne!(
        t_hello, t_world,
        "Different strings should have different tokens"
    );

    // Simulate dynamically created string via \o concatenation,
    // now routed through intern_string() per #3287.
    let concat = intern_string(&format!("{}{}", &*hello, &*world));
    let t_concat = tlc_string_token(&concat);

    // The concat string should have its own token, eagerly assigned
    assert_ne!(t_concat, 0, "Dynamic concat should get a token");
    assert_ne!(t_concat, t_hello, "Concat should differ from components");
    assert_ne!(t_concat, t_world, "Concat should differ from components");

    // Repeating the same concat should return the same token (deterministic)
    let concat2 = intern_string(&format!("{}{}", &*hello, &*world));
    let t_concat2 = tlc_string_token(&concat2);
    assert_eq!(
        t_concat, t_concat2,
        "Same dynamic string should always get the same token"
    );

    // Contrast: Arc::from() bypasses intern_string() and would NOT assign
    // a token eagerly. After #3287, all production Value::String creation
    // paths go through intern_string(), so this bypass only exists in tests.
    let bypass: Arc<str> = "dyn_concat_test_3287_bypass_no_intern".into();
    let t_before = get_token_table().get(bypass.as_ref()).map(|r| *r.value());
    assert!(
        t_before.is_none(),
        "Arc::from() bypass should NOT pre-assign a token"
    );

    clear_string_intern_table();
    clear_tlc_string_tokens();
}

#[test]
fn value_string_constructor_assigns_tlc_token_at_construction() {
    let _lock = crate::value::lock_intern_state();
    clear_string_intern_table();
    clear_tlc_string_tokens();

    let constructed = Value::string("constructed_first");
    let later = intern_string("constructed_second");
    let Value::String(constructed_arc) = &constructed else {
        panic!("Value::string should produce a string value");
    };

    let constructed_tok = tlc_string_token(constructed_arc);
    let later_tok = tlc_string_token(&later);

    assert!(
        constructed_tok < later_tok,
        "Value::string should assign TLC tokens at construction time: constructed={constructed_tok}, later={later_tok}"
    );

    clear_string_intern_table();
    clear_tlc_string_tokens();
}
