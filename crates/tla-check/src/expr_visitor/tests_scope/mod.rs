// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.

//! Scope tracking tests for ExprVisitor (#1213).

mod deep_nesting;
mod domain_scope;
mod scope_enter_exit;
mod short_circuit;

use super::*;
use num_bigint::BigInt;
use tla_core::ast::{BoundVar, ExceptPathElement, ExceptSpec, Expr, OperatorDef};
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

struct ScopeTrackingVisitor {
    events: Vec<(String, Vec<String>)>,
    depth: usize,
    max_depth: usize,
}

impl ScopeTrackingVisitor {
    fn new() -> Self {
        Self {
            events: Vec::new(),
            depth: 0,
            max_depth: 0,
        }
    }
}

impl ExprVisitor for ScopeTrackingVisitor {
    type Output = bool;

    fn enter_scope(&mut self, names: &[String]) {
        self.depth += 1;
        if self.depth > self.max_depth {
            self.max_depth = self.depth;
        }
        self.events.push(("enter".to_string(), names.to_vec()));
    }

    fn exit_scope(&mut self, names: &[String]) {
        assert!(
            self.depth > 0,
            "exit_scope called without matching enter_scope"
        );
        self.depth -= 1;
        self.events.push(("exit".to_string(), names.to_vec()));
    }
}
