// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Helper operators for the generated TLA+ module.

#![allow(dead_code)] // Some helpers used only in later phases

use tla_core::ast::{Expr, OperatorDef};
use tla_core::name_intern::NameId;

use super::spanned;
use crate::model::ConcurrentModel;

/// Generate helper operator definitions used by Init, Next, and properties.
pub(super) fn generate_helper_operators(model: &ConcurrentModel) -> Vec<OperatorDef> {
    let mut ops = Vec::new();

    // Processes == {"main", "thread_0", "thread_1", ...}
    let process_ids: Vec<_> = model
        .processes
        .iter()
        .map(|p| spanned(Expr::String(p.id.clone())))
        .collect();
    ops.push(make_operator("Processes", Expr::SetEnum(process_ids)));

    // TerminalStates == {"done_main", "done_thread_0", ...}
    let mut terminal_states = Vec::new();
    for process in &model.processes {
        for state in &process.terminal_states {
            terminal_states.push(spanned(Expr::String(state.clone())));
        }
    }
    ops.push(make_operator(
        "TerminalStates",
        Expr::SetEnum(terminal_states),
    ));

    // NoOwner == "none"
    ops.push(make_operator("NoOwner", Expr::String("none".to_string())));

    // Mutexes == {"m0", "m1", ...}
    let mutex_ids: Vec<_> = model
        .sync_primitives
        .iter()
        .filter(|s| matches!(s.kind, crate::sync_kind::SyncKind::Mutex { .. }))
        .map(|s| spanned(Expr::String(s.id.clone())))
        .collect();
    if !mutex_ids.is_empty() {
        ops.push(make_operator("Mutexes", Expr::SetEnum(mutex_ids)));
    }

    // RwLocks == {"rw0", ...}
    let rwlock_ids: Vec<_> = model
        .sync_primitives
        .iter()
        .filter(|s| matches!(s.kind, crate::sync_kind::SyncKind::RwLock { .. }))
        .map(|s| spanned(Expr::String(s.id.clone())))
        .collect();
    if !rwlock_ids.is_empty() {
        ops.push(make_operator("RwLocks", Expr::SetEnum(rwlock_ids)));
    }

    // Channels == {"ch0", ...}
    let channel_ids: Vec<_> = model
        .sync_primitives
        .iter()
        .filter(|s| matches!(s.kind, crate::sync_kind::SyncKind::Channel { .. }))
        .map(|s| spanned(Expr::String(s.id.clone())))
        .collect();
    if !channel_ids.is_empty() {
        ops.push(make_operator("Channels", Expr::SetEnum(channel_ids)));
    }

    // Condvars == {"cv0", ...}
    let condvar_ids: Vec<_> = model
        .sync_primitives
        .iter()
        .filter(|s| matches!(s.kind, crate::sync_kind::SyncKind::Condvar { .. }))
        .map(|s| spanned(Expr::String(s.id.clone())))
        .collect();
    if !condvar_ids.is_empty() {
        ops.push(make_operator("Condvars", Expr::SetEnum(condvar_ids)));
    }

    ops
}

pub(super) fn make_operator(name: &str, body: Expr) -> OperatorDef {
    OperatorDef {
        name: spanned(name.to_string()),
        params: vec![],
        body: spanned(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

pub(super) fn make_operator_with_prime(name: &str, body: Expr) -> OperatorDef {
    OperatorDef {
        name: spanned(name.to_string()),
        params: vec![],
        body: spanned(body),
        local: false,
        contains_prime: true,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

/// Create an Expr::Ident with NameId::INVALID (resolved at check time).
pub(super) fn ident(name: &str) -> Expr {
    Expr::Ident(name.to_string(), NameId::INVALID)
}

/// Create a function application: f[x]
pub(super) fn func_apply(func: Expr, arg: Expr) -> Expr {
    Expr::FuncApply(Box::new(spanned(func)), Box::new(spanned(arg)))
}

/// Create a primed expression: x'
pub(super) fn prime(expr: Expr) -> Expr {
    Expr::Prime(Box::new(spanned(expr)))
}

/// Create an equality: a = b
pub(super) fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Eq(Box::new(spanned(a)), Box::new(spanned(b)))
}

/// Create an inequality: a /= b
pub(super) fn neq(a: Expr, b: Expr) -> Expr {
    Expr::Neq(Box::new(spanned(a)), Box::new(spanned(b)))
}

/// Create a conjunction: a /\ b
pub(super) fn and(a: Expr, b: Expr) -> Expr {
    Expr::And(Box::new(spanned(a)), Box::new(spanned(b)))
}

/// Create a disjunction: a \/ b
pub(super) fn or(a: Expr, b: Expr) -> Expr {
    Expr::Or(Box::new(spanned(a)), Box::new(spanned(b)))
}

/// Create a negation: ~a
pub(super) fn not(a: Expr) -> Expr {
    Expr::Not(Box::new(spanned(a)))
}

/// Create an implication: a => b
pub(super) fn implies(a: Expr, b: Expr) -> Expr {
    Expr::Implies(Box::new(spanned(a)), Box::new(spanned(b)))
}

/// Create set membership: x \in S
pub(super) fn in_set(elem: Expr, set: Expr) -> Expr {
    Expr::In(Box::new(spanned(elem)), Box::new(spanned(set)))
}

/// Create set difference: S \ T
pub(super) fn set_minus(s: Expr, t: Expr) -> Expr {
    Expr::SetMinus(Box::new(spanned(s)), Box::new(spanned(t)))
}

/// Create set union: S \cup T
pub(super) fn set_union(s: Expr, t: Expr) -> Expr {
    Expr::Union(Box::new(spanned(s)), Box::new(spanned(t)))
}

/// Create a string literal
pub(super) fn str_lit(s: &str) -> Expr {
    Expr::String(s.to_string())
}

/// Create an integer literal
pub(super) fn int_lit(n: i64) -> Expr {
    Expr::Int(n.into())
}

/// Create a boolean literal
pub(super) fn bool_lit(b: bool) -> Expr {
    Expr::Bool(b)
}

/// Create an empty set: {}
pub(super) fn empty_set() -> Expr {
    Expr::SetEnum(vec![])
}

/// Create an empty sequence: <<>>
pub(super) fn empty_seq() -> Expr {
    Expr::Tuple(vec![])
}

/// Create UNCHANGED <<v1, v2, ...>>
pub(super) fn unchanged(vars: &[&str]) -> Expr {
    let tuple = Expr::Tuple(vars.iter().map(|v| spanned(ident(v))).collect());
    Expr::Unchanged(Box::new(spanned(tuple)))
}

/// Fold a list of expressions with conjunction. Empty list returns TRUE.
pub(super) fn conjoin(exprs: Vec<Expr>) -> Expr {
    exprs
        .into_iter()
        .reduce(|a, b| and(a, b))
        .unwrap_or(Expr::Bool(true))
}

/// Fold a list of expressions with disjunction. Empty list returns FALSE.
pub(super) fn disjoin(exprs: Vec<Expr>) -> Expr {
    exprs
        .into_iter()
        .reduce(|a, b| or(a, b))
        .unwrap_or(Expr::Bool(false))
}

/// Create [f EXCEPT ![key] = value]
pub(super) fn except(func: Expr, key: Expr, value: Expr) -> Expr {
    use tla_core::ast::{ExceptPathElement, ExceptSpec};
    Expr::Except(
        Box::new(spanned(func)),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(spanned(key))],
            value: spanned(value),
        }],
    )
}
