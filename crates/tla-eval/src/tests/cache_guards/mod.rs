// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cache guard and RAII lifecycle tests.
//!
//! Split from monolithic cache_guards.rs (#3484) into focused submodules:
//! - subst_cache_guards: SubstCacheGuard arm/disarm + SubstGuardEntry RAII
//! - eval_identity: StateLookupMode guards, dep tracking, eager bindings, scope ID stability
//! - hoist_generation: Hoist generation invalidation guards + state-eval boundary contracts

use super::*;
#[cfg(debug_assertions)]
use crate::cache::suppress_hoist_lookup;
use crate::cache::{
    clear_subst_guard, enter_quantifier_hoist_scope, eval_with_dep_tracking, is_subst_guarded,
    quantifier_hoist_lookup, quantifier_hoist_store, OpEvalDeps, StateLookupMode,
    StateLookupModeGuard, SubstCacheEntry, SubstCacheGuard, SubstCacheKey, SubstGuardEntry,
    SUBST_STATE,
};
use rustc_hash::FxHashSet;
use std::rc::Rc;
use std::sync::Arc;
use tla_core::ast::{Expr, Substitution};
use tla_core::name_intern::intern_name;
use tla_core::{Span, Spanned};

fn subst_cache_len() -> usize {
    SUBST_STATE.with(|s| s.borrow().cache.len())
}

fn insert_subst_cache(name: &str, value: Value) {
    SUBST_STATE.with(|s| {
        s.borrow_mut().cache.insert(
            SubstCacheKey {
                is_next_state: false,
                name_id: intern_name(name),
                shared_id: 0,
                local_ops_id: 0,
                instance_subs_id: 0,
                chained_ref_eval: false,
            },
            SubstCacheEntry {
                value,
                deps: OpEvalDeps::default(),
            },
        );
    });
}

mod eval_identity;
mod hoist_generation;
mod subst_cache_guards;
