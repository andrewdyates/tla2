// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.

//! Short-circuit exit_scope balance tests for ExprVisitor (#1232).

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

// ======================================================================
// F5: Short-circuit exit_scope balance test (#1232)
// ======================================================================

struct ShortCircuitScopeVisitor {
    sentinel: String,
    scope_depth: usize,
}

impl ShortCircuitScopeVisitor {
    fn new(sentinel: &str) -> Self {
        Self {
            sentinel: sentinel.to_string(),
            scope_depth: 0,
        }
    }
}

impl ExprVisitor for ShortCircuitScopeVisitor {
    type Output = bool;
    fn visit_node(&mut self, expr: &Expr) -> Option<Self::Output> {
        if let Expr::Ident(name, _) = expr {
            if **name == *self.sentinel {
                return Some(true);
            }
        }
        None
    }
    fn enter_scope(&mut self, _names: &[String]) {
        self.scope_depth += 1;
    }
    fn exit_scope(&mut self, _names: &[String]) {
        assert!(
            self.scope_depth > 0,
            "exit_scope called without matching enter_scope (depth underflow)"
        );
        self.scope_depth -= 1;
    }
}

fn bv_with_domain(name: &str, domain: Expr) -> BoundVar {
    BoundVar {
        name: sp_str(name),
        domain: Some(boxed(domain)),
        pattern: None,
    }
}

#[test]
fn test_short_circuit_let_exit_scope_balanced() {
    let let_expr = Expr::Let(
        vec![
            OperatorDef {
                name: sp_str("op_a"),
                params: vec![],
                body: sp(Expr::Ident(
                    "STOP".into(),
                    tla_core::name_intern::NameId::INVALID,
                )),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            },
            OperatorDef {
                name: sp_str("op_b"),
                params: vec![],
                body: sp(Expr::Int(BigInt::from(1))),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            },
        ],
        boxed(Expr::Bool(true)),
    );
    let mut v = ShortCircuitScopeVisitor::new("STOP");
    let result = walk_expr(&mut v, &let_expr);
    assert!(result, "should have short-circuited");
    assert_eq!(v.scope_depth, 0, "Let early-return must call exit_scope");
}

#[test]
fn test_short_circuit_forall_exit_scope_balanced() {
    let forall = Expr::Forall(
        vec![
            bv_with_domain(
                "x",
                Expr::Ident("STOP".into(), tla_core::name_intern::NameId::INVALID),
            ),
            bv_with_domain(
                "y",
                Expr::Ident("S".into(), tla_core::name_intern::NameId::INVALID),
            ),
        ],
        boxed(Expr::Bool(true)),
    );
    let mut v = ShortCircuitScopeVisitor::new("STOP");
    let result = walk_expr(&mut v, &forall);
    assert!(result, "should have short-circuited");
    assert_eq!(v.scope_depth, 0, "Forall early-return must call exit_scope");
}

#[test]
fn test_short_circuit_exists_exit_scope_balanced() {
    let exists = Expr::Exists(
        vec![bv_with_domain(
            "x",
            Expr::Ident("STOP".into(), tla_core::name_intern::NameId::INVALID),
        )],
        boxed(Expr::Bool(true)),
    );
    let mut v = ShortCircuitScopeVisitor::new("STOP");
    let result = walk_expr(&mut v, &exists);
    assert!(result, "should have short-circuited");
    assert_eq!(v.scope_depth, 0, "Exists early-return must call exit_scope");
}

#[test]
fn test_short_circuit_choose_exit_scope_balanced() {
    let choose = Expr::Choose(
        BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "STOP".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        },
        boxed(Expr::Bool(true)),
    );
    let mut v = ShortCircuitScopeVisitor::new("STOP");
    let result = walk_expr(&mut v, &choose);
    assert!(result, "should have short-circuited");
    assert_eq!(v.scope_depth, 0, "Choose early-return must call exit_scope");
}

#[test]
fn test_short_circuit_setbuilder_exit_scope_balanced() {
    let sb = Expr::SetBuilder(
        boxed(Expr::Bool(true)),
        vec![bv_with_domain(
            "x",
            Expr::Ident("STOP".into(), tla_core::name_intern::NameId::INVALID),
        )],
    );
    let mut v = ShortCircuitScopeVisitor::new("STOP");
    let result = walk_expr(&mut v, &sb);
    assert!(result, "should have short-circuited");
    assert_eq!(
        v.scope_depth, 0,
        "SetBuilder early-return must call exit_scope"
    );
}

#[test]
fn test_short_circuit_funcdef_exit_scope_balanced() {
    let fd = Expr::FuncDef(
        vec![bv_with_domain(
            "x",
            Expr::Ident("STOP".into(), tla_core::name_intern::NameId::INVALID),
        )],
        boxed(Expr::Int(BigInt::from(0))),
    );
    let mut v = ShortCircuitScopeVisitor::new("STOP");
    let result = walk_expr(&mut v, &fd);
    assert!(result, "should have short-circuited");
    assert_eq!(
        v.scope_depth, 0,
        "FuncDef early-return must call exit_scope"
    );
}

#[test]
fn test_short_circuit_setfilter_exit_scope_balanced() {
    let sf = Expr::SetFilter(
        BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "STOP".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        },
        boxed(Expr::Bool(true)),
    );
    let mut v = ShortCircuitScopeVisitor::new("STOP");
    let result = walk_expr(&mut v, &sf);
    assert!(result, "should have short-circuited");
    assert_eq!(
        v.scope_depth, 0,
        "SetFilter early-return must call exit_scope"
    );
}

#[test]
fn test_except_field_path_element_not_traversed() {
    let expr = Expr::Except(
        boxed(Expr::Ident(
            "r".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Field(sp_str("key").into())],
            value: sp(Expr::Int(BigInt::from(42))),
        }],
    );
    assert!(
        !expr_contains_prime_v(&expr),
        "no Prime in Field-only Except should return false"
    );
}
