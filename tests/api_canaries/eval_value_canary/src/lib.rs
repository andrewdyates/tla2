// Copyright 2026 Dropbox.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// API compatibility canary for tla-eval + tla-value (Part of #1325).
// This crate exercises stable public API paths from both crates.
// Compile failure here means a public API contract was broken.
//
// Contract surface: evaluation context, Value types, set/function
// constructors, fingerprinting, error types, cache lifecycle.

// Canary crates intentionally import symbols to verify they exist.
// The imports ARE the test — "unused" is expected.
#![allow(unused_imports, dead_code)]

// --- tla-eval: evaluation entry points ---
use tla_eval::EvalCtx;
use tla_eval::SharedCtx;

// --- tla-eval: cache lifecycle ---
use tla_eval::{clear_for_run_reset, clear_for_test_reset};

// --- tla-value: core Value type ---
use tla_value::Value;

// --- tla-value: error types ---
use tla_value::EvalError;
use tla_value::EvalResult;

// --- tla-value: fingerprinting ---
use tla_value::value_fingerprint;
use tla_value::{FingerprintError, FingerprintResult};

// --- tla-value: value constructors ---
use tla_value::{val_false, val_int, val_true};

// --- tla-value: set types ---
use tla_value::SortedSet;

// --- tla-value: function types ---
use tla_value::FuncValue;

// --- tla-value: record types ---
use tla_value::RecordValue;

// --- tla-value: string interning ---
use tla_value::intern_string;

/// Exercise Value construction contracts.
fn canary_value_constructors() {
    let _t: Value = val_true();
    let _f: Value = val_false();
    let _i: Value = val_int(&num_bigint::BigInt::from(42));
    let _s: std::sync::Arc<str> = intern_string("hello");
    let _sv: Value = Value::String(_s);
}

/// Exercise fingerprint contract (returns Result per #3203).
fn canary_fingerprint(v: &Value) {
    let _fp: FingerprintResult<u64> = value_fingerprint(v);
    let _err: FingerprintError = FingerprintError::I32Overflow {
        value: String::new(),
        context: "",
    };
}

/// Exercise eval cache lifecycle.
fn canary_cache_lifecycle() {
    clear_for_test_reset();
    clear_for_run_reset();
}

/// Exercise EvalResult type alias.
fn canary_eval_result() -> EvalResult<Value> {
    Ok(val_true())
}
