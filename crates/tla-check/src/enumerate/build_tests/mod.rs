// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::enumerate::expr_analysis::expr_contains_ident;
use crate::enumerate::*;
use crate::eval::EvalCtx;
use crate::state::State;
use crate::var_index::VarIndex;
use crate::OpEnv;
use crate::Value;
use std::sync::Arc;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn setup_module(src: &str) -> (tla_core::ast::Module, EvalCtx, Vec<Arc<str>>) {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let mut vars = Vec::new();
    for unit in &module.units {
        if let tla_core::ast::Unit::Variable(var_names) = &unit.node {
            for var in var_names {
                let name = Arc::from(var.node.as_str());
                ctx.register_var(Arc::clone(&name));
                vars.push(name);
            }
        }
    }

    (module, ctx, vars)
}

fn find_operator<'a>(
    module: &'a tla_core::ast::Module,
    op_name: &str,
) -> &'a tla_core::ast::OperatorDef {
    module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == op_name => Some(def),
            _ => None,
        })
        .expect("invariant: operator definition must exist in test module")
}

fn assert_scope_restore_cleanup(
    ctx: &EvalCtx,
    initial_stack_len: usize,
    expected_skip_prime: bool,
    expected_local_ops: &Arc<OpEnv>,
) {
    assert_eq!(
        ctx.local_stack_len(),
        initial_stack_len,
        "scope cleanup must restore local binding stack depth"
    );
    assert_eq!(
        ctx.skip_prime_validation(),
        expected_skip_prime,
        "scope cleanup must restore skip_prime_validation flag"
    );
    let restored_ops = ctx
        .local_ops()
        .as_ref()
        .expect("invariant: scope cleanup must restore local_ops");
    assert!(
        Arc::ptr_eq(restored_ops, expected_local_ops),
        "scope cleanup must restore the original local_ops binding"
    );
}

mod builders;
mod error_action_propagation;
mod error_catchall_symbolic;
mod error_classification;
mod error_enabled_eval;
mod halt_propagation;
mod init_extraction;
mod init_function_space;
mod init_if_then_else;
mod init_inequality;
mod init_state_enumeration;
mod scope_and_analysis;
mod scope_id_migration;
mod scope_restore;
mod successor_action;
mod successor_basic;
mod successor_compiled;
mod successor_let_lazy;
mod successor_primed_param;
mod symbolic_action_and_sort;
mod symbolic_evaluation;
mod symbolic_primed_refs;
mod symbolic_progressive_and_inset;
