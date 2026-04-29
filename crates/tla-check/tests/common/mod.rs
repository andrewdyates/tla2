// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use parking_lot::{const_reentrant_mutex, ReentrantMutex, ReentrantMutexGuard};
use std::ffi::OsString;
use std::path::PathBuf;
use tla_check::EvalCheckError;
use tla_check::{CheckError, CheckResult, EvalError};
use tla_core::{lower, parse_to_syntax_tree, FileId};

static ENV_VAR_LOCK: ReentrantMutex<()> = const_reentrant_mutex(());

#[allow(dead_code)]
fn reset_tir_env_cache_if_needed(key: &str) {
    #[cfg(debug_assertions)]
    if matches!(key, "TLA2_TIR_EVAL" | "TLA2_TIR_PARITY" | "TIR_EVAL_STATS") {
        tla_check::reset_tir_mode_env_cache_for_tests();
    }
}

/// Helper to parse a module from source
#[allow(dead_code)]
pub fn parse_module(src: &str) -> tla_core::ast::Module {
    parse_module_with_id(src, FileId(0))
}

/// Helper to parse a module from source, asserting no lowering errors
#[allow(dead_code)]
pub fn parse_module_strict(src: &str) -> tla_core::ast::Module {
    parse_module_strict_with_id(src, FileId(0))
}

/// Helper to parse a module with a specific FileId
#[allow(dead_code)]
pub fn parse_module_with_id(src: &str, file_id: FileId) -> tla_core::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let result = lower(file_id, &tree);
    let mut module = result.module.expect("Failed to parse module");
    tla_core::compute_is_recursive(&mut module);
    module
}

/// Helper to parse a module with a specific FileId, asserting no lowering errors
#[allow(dead_code)]
pub fn parse_module_strict_with_id(src: &str, file_id: FileId) -> tla_core::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let result = lower(file_id, &tree);
    assert!(
        result.errors.is_empty(),
        "lower errors: {:?}",
        result.errors
    );
    let mut module = result.module.expect("Failed to parse module");
    tla_core::compute_is_recursive(&mut module);
    module
}

/// Returns the path to the TLA+ examples fixture tree.
#[allow(dead_code)]
pub fn tlaplus_examples_dir() -> PathBuf {
    let crate_fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/tlaplus-examples");
    if crate_fixture.is_dir() {
        return crate_fixture;
    }

    let home = std::env::var("HOME").expect("HOME environment variable not set");
    PathBuf::from(home).join("tlaplus-examples")
}

#[allow(dead_code)]
pub fn assert_eval_error_set_too_large(spec_name: &str, mode: &str, result: CheckResult) {
    match result {
        CheckResult::Error {
            error: CheckError::Eval(EvalCheckError::Eval(EvalError::SetTooLarge { .. })),
            ..
        } => {}
        other => panic!("Expected EvalError::SetTooLarge for {spec_name} ({mode}), got: {other:?}"),
    }
}

#[allow(dead_code)]
pub struct EnvVarGuard {
    key: &'static str,
    prev: Option<OsString>,
    lock: Option<ReentrantMutexGuard<'static, ()>>,
}

#[allow(dead_code)]
impl EnvVarGuard {
    pub fn remove(key: &'static str) -> Self {
        let lock = ENV_VAR_LOCK.lock();
        let prev = std::env::var_os(key);
        std::env::remove_var(key);
        reset_tir_env_cache_if_needed(key);
        Self {
            key,
            prev,
            lock: Some(lock),
        }
    }

    pub fn set(key: &'static str, value: Option<&str>) -> Self {
        let lock = ENV_VAR_LOCK.lock();
        let prev = std::env::var_os(key);
        if let Some(v) = value {
            std::env::set_var(key, v);
        } else {
            std::env::remove_var(key);
        }
        reset_tir_env_cache_if_needed(key);
        Self {
            key,
            prev,
            lock: Some(lock),
        }
    }
}

impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        match self.prev.take() {
            Some(v) => std::env::set_var(self.key, v),
            None => std::env::remove_var(self.key),
        }
        reset_tir_env_cache_if_needed(self.key);
        self.lock.take();
    }
}
