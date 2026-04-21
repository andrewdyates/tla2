// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR interpreter parity canary — Phase 2b bootstrap (#3194).
//!
//! Each test evaluates the same expression through BOTH the AST eval path
//! and the TIR eval path, then asserts that results match exactly.

use crate::cache::lifecycle::clear_for_test_reset;
use crate::tir::TirProgram;
use crate::{eval, EvalCtx};
use tla_core::ast::Module;
use tla_core::{lower, parse_to_syntax_tree, FileId};
use tla_value::error::EvalError;
use tla_value::Value;

mod closures;
mod collections;
mod counter;
mod disruptor_counterexample;
mod disruptor_real_spec;
mod functions_and_control;
mod prime;

/// Parse a TLA+ module source into an AST Module.
pub(super) fn parse_module(src: &str) -> Module {
    parse_module_with_file_id(FileId(0), src)
}

pub(super) fn parse_module_with_file_id(file_id: FileId, src: &str) -> Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(file_id, &tree);
    if !lower_result.errors.is_empty() {
        eprintln!("Lower errors: {:?}", lower_result.errors);
    }
    lower_result.module.unwrap_or_else(|| {
        eprintln!("Source:\n{src}");
        panic!("Failed to lower module");
    })
}

/// Evaluate a named zero-arg operator from a module through the AST path.
pub(super) fn eval_ast_op(module: &Module, name: &str) -> Value {
    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);
    ctx.eval_op(name).unwrap_or_else(|e| {
        panic!("AST eval of '{name}' failed: {e}");
    })
}

/// Evaluate a named operator through the TIR path.
pub(super) fn eval_tir_op(module: &Module, name: &str) -> Value {
    clear_for_test_reset();
    let program = TirProgram::from_modules(module, &[]);
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);
    program.eval_named_op(&ctx, name).unwrap_or_else(|e| {
        panic!("TIR eval of '{name}' failed: {e}");
    })
}

/// Assert AST and TIR paths produce the same value for a named operator.
pub(super) fn assert_parity(module: &Module, name: &str) {
    let ast_val = eval_ast_op(module, name);
    let tir_val = eval_tir_op(module, name);
    assert_eq!(
        ast_val, tir_val,
        "AST/TIR parity mismatch for '{name}': AST={ast_val:?}, TIR={tir_val:?}"
    );
}

/// Assert AST and TIR paths both fail for a named operator and return the errors.
pub(super) fn assert_error_parity(module: &Module, name: &str) -> (EvalError, EvalError) {
    clear_for_test_reset();
    let mut ast_ctx = EvalCtx::new();
    ast_ctx.load_module(module);
    let ast_err = match ast_ctx.eval_op(name) {
        Ok(value) => panic!("AST eval of '{name}' should fail, got value: {value:?}"),
        Err(err) => err,
    };

    clear_for_test_reset();
    let program = TirProgram::from_modules(module, &[]);
    let mut tir_ctx = EvalCtx::new();
    tir_ctx.load_module(module);
    let tir_err = match program.eval_named_op(&tir_ctx, name) {
        Ok(value) => panic!("TIR eval of '{name}' should fail, got value: {value:?}"),
        Err(err) => err,
    };

    (ast_err, tir_err)
}
