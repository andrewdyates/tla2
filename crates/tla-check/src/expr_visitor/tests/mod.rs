// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache-2.0.

//! Tests for expr_visitor: prime detection, containment, AST walks,
//! instance/shadowing, conjuncts, and substitutions.
//!
//! Split from monolithic `tests.rs` (Part of #2779) into focused modules.

mod containment;
mod instance_shadowing;
mod prime_detection;
mod substitutions;
mod walk_and_collect;

use super::*;
use num_bigint::BigInt;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use rustc_hash::FxHashSet;
use tla_core::ast::{
    BoundPattern, BoundVar, CaseArm, ExceptPathElement, Expr, ModuleTarget, OperatorDef,
    Substitution,
};
use tla_core::intern_name;
use tla_core::Spanned;

fn sp(expr: Expr) -> Spanned<Expr> {
    Spanned::dummy(expr)
}

fn boxed(expr: Expr) -> Box<Spanned<Expr>> {
    Box::new(sp(expr))
}

fn sp_str(s: &str) -> Spanned<String> {
    Spanned::dummy(s.to_string())
}

fn make_zero_arg_op(
    name: &str,
    body: Expr,
    contains_prime: bool,
    guards_depend_on_prime: bool,
) -> Arc<OperatorDef> {
    Arc::new(OperatorDef {
        name: sp_str(name),
        params: vec![],
        body: sp(body),
        local: false,
        contains_prime,
        guards_depend_on_prime,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    })
}

fn ctx_with_ops(defs: Vec<Arc<OperatorDef>>) -> crate::eval::EvalCtx {
    let mut ops = HashMap::new();
    for def in defs {
        ops.insert(def.name.node.clone(), def);
    }
    crate::eval::EvalCtx::new().with_local_ops(ops.into())
}
