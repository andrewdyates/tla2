// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::cache::lifecycle::clear_for_test_reset;
use crate::error::{EvalError, EvalResult};
use crate::value::Value;
use crate::*;
use std::sync::Arc;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn eval_str(src: &str) -> EvalResult<Value> {
    // BUG FIX #359/#360: Clear literal cache between test calls.
    // All eval_str calls use FileId(0), so span-keyed LITERAL_CACHE can return
    // stale values when different expressions have literals at the same byte offset.
    clear_for_test_reset();

    // Wrap expression in a module for parsing
    let module_src = format!("---- MODULE Test ----\n\nOp == {}\n\n====", src);
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        eprintln!("Lower errors: {:?}", lower_result.errors);
    }
    let module = match lower_result.module {
        Some(m) => m,
        None => {
            eprintln!("Source:\n{}", module_src);
            eprintln!("Lower errors: {:?}", lower_result.errors);
            panic!("Failed to lower module");
        }
    };

    // Find the Op definition and evaluate its body
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = EvalCtx::new();
                return eval(&ctx, &def.body);
            }
        }
    }
    eprintln!("Source:\n{}", module_src);
    eprintln!("Units found: {}", module.units.len());
    for (i, unit) in module.units.iter().enumerate() {
        eprintln!("Unit {}: {:?}", i, &unit.node);
    }
    panic!("Op not found");
}

fn eval_str_with_ctx(src: &str, ctx: &EvalCtx) -> EvalResult<Value> {
    clear_for_test_reset();

    let module_src = format!("---- MODULE Test ----\n\nOp == {}\n\n====", src);
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        eprintln!("Lower errors: {:?}", lower_result.errors);
    }
    let module = match lower_result.module {
        Some(m) => m,
        None => {
            eprintln!("Source:\n{}", module_src);
            eprintln!("Lower errors: {:?}", lower_result.errors);
            panic!("Failed to lower module");
        }
    };

    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                return eval(ctx, &def.body);
            }
        }
    }
    eprintln!("Source:\n{}", module_src);
    eprintln!("Units found: {}", module.units.len());
    for (i, unit) in module.units.iter().enumerate() {
        eprintln!("Unit {}: {:?}", i, &unit.node);
    }
    panic!("Op not found");
}

/// Helper to evaluate with multiple operator definitions
fn eval_with_ops(defs: &str, expr: &str) -> EvalResult<Value> {
    clear_for_test_reset();

    let module_src = format!(
        "---- MODULE Test ----\n\n{}\n\nOp == {}\n\n====",
        defs, expr
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        eprintln!("Lower errors: {:?}", lower_result.errors);
    }
    let module = match lower_result.module {
        Some(m) => m,
        None => {
            eprintln!("Source:\n{}", module_src);
            eprintln!("Lower errors: {:?}", lower_result.errors);
            panic!("Failed to lower module");
        }
    };

    // Load all operator definitions
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // Evaluate the Op
    ctx.eval_op("Op")
}

fn eval_with_extended_modules(
    defs: &str,
    expr: &str,
    extended_modules: &[&str],
) -> EvalResult<Value> {
    clear_for_test_reset();

    let module_src = format!(
        "---- MODULE Test ----\n\n{}\n\nOp == {}\n\n====",
        defs, expr
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        eprintln!("Lower errors: {:?}", lower_result.errors);
    }
    let module = match lower_result.module {
        Some(m) => m,
        None => {
            eprintln!("Source:\n{}", module_src);
            eprintln!("Lower errors: {:?}", lower_result.errors);
            panic!("Failed to lower module");
        }
    };

    let mut ctx = EvalCtx::new();
    {
        let shared = Arc::make_mut(ctx.shared_arc_mut());
        for module_name in extended_modules {
            shared
                .extended_module_names
                .insert((*module_name).to_string());
        }
    }
    ctx.load_module(&module);
    ctx.eval_op("Op")
}

mod apalache;
mod arith_boundary;
mod arith_concat;
mod bags;
mod bagsext;
mod basic_eval;
mod cache_guards;
mod captured_chain_restore;
mod comparison;
mod const_level;
mod errors;
mod eval_ctx_guards;
mod eval_prime;
mod eval_prime_stale_slots;
mod finite_sets_ext;
mod function_setpred_domains;
mod functions;
mod functions_ext;
mod graphs;
mod instance_boundary;
mod ksubset_optimization;
mod lazy_eval;
mod lazy_membership;
mod liveness_bindings;
mod membership;
mod op_cache;
mod param_let_cache;
mod precomputed_constants;
mod quantifiers_and_choose;
mod raw_subst_scope;
mod recursion;
mod relation;
mod sequences;
mod set_builder_membership;
mod setpred_builtins;
mod setpred_membership;
mod sets;
mod state_identity_guards;
mod state_var_fast_path;
mod stdlib_ext;
mod subexpression_labels;
mod tir_contract;
mod tir_contract_direct_apply;
mod tir_parity;
mod tlc_builtins;
mod tuples_and_records;
