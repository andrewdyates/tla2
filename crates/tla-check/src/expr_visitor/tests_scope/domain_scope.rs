// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.

//! F5: Domain scope ordering regression tests (visit.rs:192 latent P3).
//!
//! In TLA+, `\A x \in S : P(x)` means `x` is NOT in scope for `S`.
//! The domain `S` is evaluated in the outer scope; `x` is only bound
//! within `P`. Fixed in #2765: enter_scope is now called after domain
//! traversal.

use super::*;

/// Visitor that records (ident_name, scope_depth) for each Expr::Ident visited.
struct ScopedIdentVisitor {
    depth: usize,
    ident_depths: Vec<(String, usize)>,
}

impl ScopedIdentVisitor {
    fn new() -> Self {
        Self {
            depth: 0,
            ident_depths: Vec::new(),
        }
    }
}

impl ExprVisitor for ScopedIdentVisitor {
    type Output = ();

    fn visit_node(&mut self, expr: &Expr) -> Option<Self::Output> {
        if let Expr::Ident(name, _) = expr {
            self.ident_depths.push((name.clone(), self.depth));
        }
        None // continue default traversal
    }

    fn enter_scope(&mut self, _names: &[String]) {
        self.depth += 1;
    }

    fn exit_scope(&mut self, _names: &[String]) {
        self.depth -= 1;
    }
}

/// `\A x \in S : P(x)` — domain ident `S` should be at depth 0,
/// body ident `x_ref` should be at depth 1. Fixed in #2765: enter_scope
/// is now called after domain traversal.
#[test]
fn test_forall_domain_scope_depth_documents_early_entry_bug() {
    // \A x \in S : P  (where P is Ident("x_ref"))
    let forall = Expr::Forall(
        vec![BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "S".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        }],
        boxed(Expr::Ident(
            "x_ref".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );

    let mut visitor = ScopedIdentVisitor::new();
    walk_expr(&mut visitor, &forall);

    let s_depth = visitor
        .ident_depths
        .iter()
        .find(|(name, _)| name == "S")
        .map(|(_, d)| *d)
        .expect("S should be visited");
    let xref_depth = visitor
        .ident_depths
        .iter()
        .find(|(name, _)| name == "x_ref")
        .map(|(_, d)| *d)
        .expect("x_ref should be visited");

    // Body ident is inside scope — correct.
    assert_eq!(xref_depth, 1, "body ident should be at depth 1");

    // Domain ident is outside scope — fixed in #2765.
    assert_eq!(
        s_depth, 0,
        "domain ident 'S' should be at depth 0 (outside bound variable scope)"
    );
}

/// Regression: SetBuilder `{expr : x \in S}` — domain `S` should be
/// evaluated outside `x`'s scope.
#[test]
fn test_set_builder_domain_scope_depth_documents_early_entry_bug() {
    // {body : x \in S}
    let set_builder = Expr::SetBuilder(
        boxed(Expr::Ident(
            "body_ref".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        vec![BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "S".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        }],
    );

    let mut visitor = ScopedIdentVisitor::new();
    walk_expr(&mut visitor, &set_builder);

    let s_depth = visitor
        .ident_depths
        .iter()
        .find(|(name, _)| name == "S")
        .map(|(_, d)| *d)
        .expect("S should be visited");

    // Domain ident is outside scope — fixed in #2765.
    assert_eq!(
        s_depth, 0,
        "SetBuilder domain ident 'S' should be at depth 0 (outside bound variable scope)"
    );
}

/// Choose `CHOOSE x \in S : P(x)` — domain `S` should be evaluated outside
/// `x`'s scope. Fixed in #2765.
#[test]
fn test_choose_domain_scope_depth_documents_early_entry_bug() {
    let choose = Expr::Choose(
        BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "S".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        },
        boxed(Expr::Ident(
            "x_ref".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );

    let mut visitor = ScopedIdentVisitor::new();
    walk_expr(&mut visitor, &choose);

    let s_depth = visitor
        .ident_depths
        .iter()
        .find(|(name, _)| name == "S")
        .map(|(_, d)| *d)
        .expect("S should be visited");

    // Domain ident is outside scope — fixed in #2765.
    assert_eq!(
        s_depth, 0,
        "Choose domain ident 'S' should be at depth 0 (outside bound variable scope)"
    );
}

/// FuncDef `[x \in S |-> body]` — domain `S` should be evaluated outside
/// `x`'s scope. Fixed in #2765.
#[test]
fn test_func_def_domain_scope_depth() {
    // [x \in S |-> body_ref]
    let func_def = Expr::FuncDef(
        vec![BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "S".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        }],
        boxed(Expr::Ident(
            "body_ref".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );

    let mut visitor = ScopedIdentVisitor::new();
    walk_expr(&mut visitor, &func_def);

    let s_depth = visitor
        .ident_depths
        .iter()
        .find(|(name, _)| name == "S")
        .map(|(_, d)| *d)
        .expect("S should be visited");
    let body_depth = visitor
        .ident_depths
        .iter()
        .find(|(name, _)| name == "body_ref")
        .map(|(_, d)| *d)
        .expect("body_ref should be visited");

    // Domain ident is outside scope — fixed in #2765.
    assert_eq!(
        s_depth, 0,
        "FuncDef domain ident 'S' should be at depth 0 (outside bound variable scope)"
    );
    // Body ident is inside scope.
    assert_eq!(body_depth, 1, "FuncDef body ident should be at depth 1");
}

/// SetFilter `{x \in S : P(x)}` — domain `S` should be evaluated outside
/// `x`'s scope. Fixed in #2765.
#[test]
fn test_set_filter_domain_scope_depth() {
    // {x \in S : pred_ref}
    let set_filter = Expr::SetFilter(
        BoundVar {
            name: sp_str("x"),
            domain: Some(boxed(Expr::Ident(
                "S".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            pattern: None,
        },
        boxed(Expr::Ident(
            "pred_ref".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );

    let mut visitor = ScopedIdentVisitor::new();
    walk_expr(&mut visitor, &set_filter);

    let s_depth = visitor
        .ident_depths
        .iter()
        .find(|(name, _)| name == "S")
        .map(|(_, d)| *d)
        .expect("S should be visited");
    let pred_depth = visitor
        .ident_depths
        .iter()
        .find(|(name, _)| name == "pred_ref")
        .map(|(_, d)| *d)
        .expect("pred_ref should be visited");

    // Domain ident is outside scope — fixed in #2765.
    assert_eq!(
        s_depth, 0,
        "SetFilter domain ident 'S' should be at depth 0 (outside bound variable scope)"
    );
    // Predicate ident is inside scope.
    assert_eq!(
        pred_depth, 1,
        "SetFilter predicate ident should be at depth 1"
    );
}
