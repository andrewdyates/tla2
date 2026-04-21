// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// API compatibility canary for tla-check (Part of #1325).
// This crate exercises stable public API paths from tla-check.
// Compile failure here means a public API contract was broken.
//
// Contract surface: model checker entry points, config parsing,
// state/fingerprint types, check results, and global state reset.
//
// All imports use crate-root re-exports (not submodule paths) to
// match the intended public API contract.

// Canary crates intentionally import symbols to verify they exist.
// The imports ARE the test — "unused" is expected.
#![allow(unused_imports, dead_code)]

// --- Model checker entry points (root re-exports) ---
use tla_check::check_module;
use tla_check::check_module_adaptive;
use tla_check::check_module_parallel;
use tla_check::AdaptiveChecker;
use tla_check::ModelChecker;
use tla_check::ParallelChecker;

// --- Configuration (root re-exports) ---
use tla_check::Config;
use tla_check::ConfigError;

// --- State and fingerprint types (root re-exports) ---
use tla_check::value_fingerprint;
use tla_check::ArrayState;
use tla_check::Fingerprint;
use tla_check::State;

// --- Check results (root re-exports) ---
use tla_check::CheckError;
use tla_check::CheckResult;
use tla_check::CheckStats;
use tla_check::ResolvedSpec;
use tla_check::Trace;

// --- Liveness (root re-exports) ---
use tla_check::AstToLive;
use tla_check::ConvertError;

// --- Evaluation (root re-exports) ---
use tla_check::Value;
use tla_check::{eval, Env, EvalCtx, OpEnv};
use tla_check::{EvalError, EvalResult};

// --- Storage (root re-exports) ---
use tla_check::FingerprintSet;

// --- Spec formula (root re-exports) ---
use tla_check::{extract_spec_formula, FairnessConstraint, SpecFormula};

/// Exercise config parsing contract.
fn canary_config_parse(text: &str) {
    let _result: Result<Config, Vec<ConfigError>> = Config::parse(text);
}

/// Exercise state/fingerprint type existence.
fn canary_fingerprint_types() {
    let fp: Fingerprint = Fingerprint(0);
    let _: u64 = fp.0;
}

/// Exercise global state reset function.
fn canary_reset() {
    tla_check::reset_global_state();
}

/// Exercise check result matching.
fn canary_check_result(result: CheckResult) {
    match &result {
        CheckResult::Success(stats) => {
            let _: usize = stats.states_found;
        }
        _ => {}
    }
}

/// Exercise Value interop between tla-check re-exports.
fn canary_value_fingerprint(v: &Value) {
    let _fp: u64 = value_fingerprint(v);
}
