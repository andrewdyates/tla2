// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{aggregate_bytecode_vm_stats, bytecode_vm_stats, clear_for_test_reset, core::EvalCtx};
use std::sync::Arc;
use std::sync::{LazyLock, Mutex, MutexGuard};
use tla_core::ast::Unit;
use tla_core::name_intern::intern_name;
use tla_core::{lower, parse_to_syntax_tree, FileId};
use tla_value::error::EvalError;

static BYTECODE_VM_TEST_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

struct BytecodeVmTestGuard {
    _lock: MutexGuard<'static, ()>,
    _overrides: crate::tir::BytecodeVmTestOverridesGuard,
}

impl BytecodeVmTestGuard {
    fn enabled() -> Self {
        let lock = BYTECODE_VM_TEST_LOCK
            .lock()
            .unwrap_or_else(|err| err.into_inner());
        let overrides = crate::tir::set_bytecode_vm_test_overrides(Some(true), None);
        Self {
            _lock: lock,
            _overrides: overrides,
        }
    }

    fn enabled_with_stats() -> Self {
        let lock = BYTECODE_VM_TEST_LOCK
            .lock()
            .unwrap_or_else(|err| err.into_inner());
        let overrides = crate::tir::set_bytecode_vm_test_overrides(Some(true), Some(true));
        Self {
            _lock: lock,
            _overrides: overrides,
        }
    }
}

fn enable_bytecode_vm_for_test() -> BytecodeVmTestGuard {
    BytecodeVmTestGuard::enabled()
}

fn enable_bytecode_vm_with_stats_for_test() -> BytecodeVmTestGuard {
    BytecodeVmTestGuard::enabled_with_stats()
}

fn set_bytecode_vm_overrides_for_current_thread(
    enabled: bool,
    stats_enabled: Option<bool>,
) -> crate::tir::BytecodeVmTestOverridesGuard {
    crate::tir::set_bytecode_vm_test_overrides(Some(enabled), stats_enabled)
}

fn bytecode_vm_enabled_from_value(value: Option<&str>) -> bool {
    crate::tir::bytecode_vm_enabled_from_env_value(value)
}

fn parse_module(src: &str) -> Module {
    let tree = parse_to_syntax_tree(src);
    let result = lower(FileId(0), &tree);
    result.module.expect("module should lower")
}

fn resolve_module_state_vars(module: &mut Module, ctx: &EvalCtx) {
    for unit in &mut module.units {
        let Unit::Operator(def) = &mut unit.node else {
            continue;
        };
        crate::state_var::resolve_state_vars_in_op_def(def, ctx.var_registry());
    }
}

mod bytecode_vm;
mod fallback_boundaries;
mod lookup_and_lowering;
