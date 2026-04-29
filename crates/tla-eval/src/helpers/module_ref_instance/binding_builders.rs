// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Binding chain construction for INSTANCE substitutions.
//!
//! Contains `build_binding_chain_from_eager`, `build_lazy_subst_bindings`,
//! and AST utility wrappers (`expr_has_any_prime`, `expr_has_primed_param`).
//!
//! Part of #1643 (module_ref.rs decomposition).

use super::super::super::OpEvalDeps;
use crate::binding_chain::{BindingChain, BindingValue, LazyBinding};
use crate::value::Value;
use tla_core::ast::{Expr, Substitution};
use tla_core::name_intern::{intern_name, NameId};

/// Part of #2364 Phase 3: Build a BindingChain from pre-evaluated substitution bindings.
///
/// Converts the (NameId, Value, OpEvalDeps) triples into a BindingChain with
/// cons_with_deps. Items are consed in reverse order so that the first Vec entry
/// (highest priority in linear search) ends up at the chain head (found first in
/// chain walk), preserving identical shadowing semantics.
pub(in crate::helpers) fn build_binding_chain_from_eager(
    bindings: &[(NameId, Value, OpEvalDeps)],
) -> BindingChain {
    let mut chain = BindingChain::empty();
    // Reverse iteration: first Vec entry consed last → ends up at head → found first.
    for (name_id, value, deps) in bindings.iter().rev() {
        chain = chain.cons_with_deps(*name_id, BindingValue::eager(value.clone()), deps.clone());
    }
    chain
}

/// Part of #2991 Step 2: Build lazy substitution bindings — TLC Context.cons parity.
/// Each sub becomes a LazyBinding (deferred eval, OnceLock cache). Cost: M × O(1) cons.
///
/// SAFETY: `expr_ptr` points into `subs` — caller must keep owning Arc alive
/// (guaranteed by `EvalCtxStable.instance_substitutions`).
pub(crate) fn build_lazy_subst_bindings(
    def_site_chain: &BindingChain,
    subs: &[Substitution],
) -> BindingChain {
    let mut chain = BindingChain::empty();
    // Reverse iteration: first sub consed last → ends up at head → found first.
    for sub in subs.iter().rev() {
        let name_id = intern_name(sub.from.node.as_str());
        let lazy = LazyBinding::new(std::ptr::addr_of!(sub.to), def_site_chain);
        chain = chain.cons_with_deps(
            name_id,
            BindingValue::Lazy(Box::new(lazy)),
            OpEvalDeps::default(),
        );
    }
    chain
}

/// Check if an expression contains ANY Prime expressions (primed variables).
/// Used to determine whether operator result caching needs next_state context.
pub fn expr_has_any_prime(expr: &Expr) -> bool {
    tla_core::expr_has_any_prime_legacy_v(expr)
}

/// Check if an expression contains a primed reference to a specific parameter name.
/// This is used to detect when call-by-name semantics are needed for operator evaluation.
///
/// For example, in `Action1(c,d) == c' = [c EXCEPT ![1] = d']`:
/// - `expr_has_primed_param(body, "d")` returns true because `d'` appears
/// - `expr_has_primed_param(body, "c")` returns false (c appears but not primed as c')
pub fn expr_has_primed_param(expr: &Expr, param_name: &str) -> bool {
    tla_core::expr_contains_primed_param_v(expr, param_name)
}
