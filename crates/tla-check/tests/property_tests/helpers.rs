// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helper functions for property-based tests.

use parking_lot::{const_reentrant_mutex, ReentrantMutex, ReentrantMutexGuard};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};
use tla_check::{FuncValue, Value};
use tla_core::{lower, parse_to_syntax_tree, FileId};
use tla_value::SortedSet;

static ENV_VAR_LOCK: ReentrantMutex<()> = const_reentrant_mutex(());

/// RAII guard that sets an environment variable and restores it on drop.
/// Also holds a reentrant mutex to serialize env var access across threads.
pub struct EnvVarGuard {
    key: String,
    prev: Option<OsString>,
    lock: Option<ReentrantMutexGuard<'static, ()>>,
}

impl EnvVarGuard {
    pub fn set(key: &str, value: Option<&str>) -> Self {
        let lock = ENV_VAR_LOCK.lock();
        let prev = std::env::var_os(key);
        if let Some(v) = value {
            std::env::set_var(key, v);
        } else {
            std::env::remove_var(key);
        }
        Self {
            key: key.to_string(),
            prev,
            lock: Some(lock),
        }
    }
}

impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        match self.prev.take() {
            Some(v) => std::env::set_var(&self.key, v),
            None => std::env::remove_var(&self.key),
        }
        self.lock.take();
    }
}

/// Evaluate a TLA+ expression string and return the result
pub fn eval_str(src: &str) -> Result<Value, String> {
    let module_src = format!("---- MODULE Test ----\n\nOp == {}\n\n====", src);
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return Err(format!("Parse error: {:?}", lower_result.errors)),
    };

    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                return tla_check::eval(&ctx, &def.body).map_err(|e| format!("{:?}", e));
            }
        }
    }
    Err("Op not found".to_string())
}

pub fn parse_module(src: &str) -> tla_core::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    lower_result.module.expect("Failed to parse module")
}

/// Create a Value::Set from a set of integers
pub fn int_set(values: &[i32]) -> Value {
    let mut vals: Vec<Value> = values.iter().map(|&v| Value::int(v.into())).collect();
    vals.sort();
    vals.dedup();
    Value::Set(Arc::new(SortedSet::from_sorted_vec(vals)))
}

/// Create a SortedSet from an unsorted iterator of Values (sort + dedup).
pub fn sorted_set_from_values(iter: impl IntoIterator<Item = Value>) -> SortedSet {
    let mut vals: Vec<Value> = iter.into_iter().collect();
    vals.sort();
    vals.dedup();
    SortedSet::from_sorted_vec(vals)
}

/// Create a FuncValue from unsorted (key, value) pairs (sorts by key).
pub fn func_from_pairs(pairs: Vec<(Value, Value)>) -> FuncValue {
    let mut entries = pairs;
    entries.sort_by(|(a, _), (b, _)| a.cmp(b));
    FuncValue::from_sorted_entries(entries)
}

/// Convert Rust bool to TLA+ boolean string
pub fn tla_bool(b: bool) -> &'static str {
    if b {
        "TRUE"
    } else {
        "FALSE"
    }
}

pub fn unique_temp_path(suffix: &str) -> PathBuf {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before UNIX_EPOCH");
    std::env::temp_dir().join(format!(
        "tla2_property_{pid}_{nanos}.{suffix}",
        pid = std::process::id(),
        nanos = now.as_nanos()
    ))
}

pub fn tla_path_literal(path: &Path) -> String {
    path.to_string_lossy()
        .replace('\\', r#"\\"#)
        .replace('"', r#"\""#)
}

/// Strategy for small sets of integers (for performance)
pub fn small_int_set() -> impl proptest::prelude::Strategy<Value = Vec<i32>> {
    proptest::prelude::prop::collection::vec(-10i32..10, 0..8)
}

/// Create a Value::Set of sequences from vectors
pub fn int_set_of_seqs(seqs: &[Vec<i64>]) -> Value {
    let vals: Vec<Value> = seqs
        .iter()
        .map(|seq| Value::seq(seq.iter().map(|&n| Value::int(n)).collect::<Vec<_>>()))
        .collect();
    Value::Set(sorted_set_from_values(vals).into())
}

/// Evaluate a TLA+ expression with specified EXTENDS modules
pub fn eval_with_extends(src: &str, extends: &[&str]) -> Result<Value, String> {
    let extends_list = extends.join(", ");
    let module_src = format!(
        "---- MODULE Test ----\nEXTENDS {}\n\nOp == {}\n\n====",
        extends_list, src
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return Err(format!("Parse error: {:?}", lower_result.errors)),
    };

    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                return tla_check::eval(&ctx, &def.body).map_err(|e| format!("{:?}", e));
            }
        }
    }
    Err("Op not found".to_string())
}
