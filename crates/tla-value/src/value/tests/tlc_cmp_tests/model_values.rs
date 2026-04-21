// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Model-value ordering and error tests for `tlc_cmp`.

use super::super::super::*;
use crate::error::EvalError;
use std::cmp::Ordering;
use std::sync::Mutex;

/// Guard for tests that mutate the global model-value registry.
static TLC_MODEL_VALUE_TEST_LOCK: Mutex<()> = Mutex::new(());

struct ModelValueRegistryReset;

impl Drop for ModelValueRegistryReset {
    fn drop(&mut self) {
        clear_model_value_registry();
    }
}

fn assert_internal_message(err: EvalError, needle: &str) {
    match err {
        EvalError::Internal { message, .. } => {
            assert!(
                message.contains(needle),
                "expected error containing {needle:?}, got: {message}"
            );
        }
        other => panic!("expected EvalError::Internal, got: {other:?}"),
    }
}

fn lock_model_value_test_state() -> std::sync::MutexGuard<'static, ()> {
    TLC_MODEL_VALUE_TEST_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_cmp_model_values_use_registration_order() {
    let _guard = lock_model_value_test_state();
    clear_model_value_registry();
    let _reset = ModelValueRegistryReset;

    // Register in reverse lexical order to prove tlc_cmp follows registration order.
    let first_seen = Value::try_model_value("__tlc_test_zulu").unwrap();
    let second_seen = Value::try_model_value("__tlc_test_alpha").unwrap();

    assert_eq!(
        Value::tlc_cmp(&first_seen, &second_seen).unwrap(),
        Ordering::Less
    );
    assert_eq!(
        Value::tlc_cmp(&second_seen, &first_seen).unwrap(),
        Ordering::Greater
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_cmp_typed_model_value_rejects_non_model() {
    let _guard = lock_model_value_test_state();
    clear_model_value_registry();
    let _reset = ModelValueRegistryReset;

    let typed = Value::try_model_value("T_payload").unwrap();
    let err = Value::tlc_cmp(&typed, &Value::int(1)).unwrap_err();
    assert_internal_message(err, "typed model value");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_cmp_special_model_set_rejects_non_model_and_orders_before_user_model_value() {
    let _guard = lock_model_value_test_state();
    clear_model_value_registry();
    let _reset = ModelValueRegistryReset;

    let nat = Value::try_model_value("Nat").unwrap();
    let user = Value::try_model_value("tlcUserModel").unwrap();

    assert_eq!(Value::tlc_cmp(&user, &nat).unwrap(), Ordering::Less);
    assert_eq!(Value::tlc_cmp(&nat, &user).unwrap(), Ordering::Greater);

    let err = Value::tlc_cmp(&nat, &Value::int(1)).unwrap_err();
    assert_internal_message(err, "overridden value");
}
