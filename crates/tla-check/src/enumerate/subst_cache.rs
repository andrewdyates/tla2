// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-call-site substitution cache for the unified enumeration dispatch.
//!
//! `apply_substitutions` deep-clones the entire operator body AST on every
//! invocation. Since the AST is immutable (stored in Arc), a given call site
//! always produces the same substituted body. This cache eliminates the O(tree)
//! cloning cost by computing once per call site and reusing across all state
//! transitions.
//!
//! Part of #3063: profiling showed `Expr::clone` (from `apply_substitutions`)
//! at ~20% of MultiPaxos single-worker runtime.

use std::cell::RefCell;
use std::sync::Arc;

use crate::eval::EvalCtx;
use rustc_hash::FxHashMap;
use tla_core::ast::Expr;
use tla_core::Spanned;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct EnumSubstCacheKey {
    shared_id: u64,
    call_site_ptr: usize,
    resolved_def_ptr: usize,
}

thread_local! {
    static CACHE: RefCell<FxHashMap<EnumSubstCacheKey, Arc<Spanned<Expr>>>> =
        RefCell::new(FxHashMap::default());
}

/// Get or compute a substituted operator body.
///
/// The substituted body depends on more than the AST call site: enumeration can
/// resolve the same `Apply`/`ModuleRef` node to different operator bodies across
/// local operator scopes and across independent `SharedCtx` runs. Discriminate
/// by the owning `SharedCtx`, the AST call site, and the resolved operator body.
///
/// On cache hit: O(1) Arc refcount bump. On miss: runs `compute` once and caches.
pub(super) fn cached_substitute(
    ctx: &EvalCtx,
    call_site: *const Spanned<Expr>,
    resolved_def_ptr: usize,
    compute: impl FnOnce() -> Spanned<Expr>,
) -> Arc<Spanned<Expr>> {
    let key = EnumSubstCacheKey {
        shared_id: ctx.shared().id,
        call_site_ptr: call_site as usize,
        resolved_def_ptr,
    };
    CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        cache
            .entry(key)
            .or_insert_with(|| Arc::new(compute()))
            .clone()
    })
}

/// Clear the thread-local substitution cache.
///
/// Must be called between model checking runs. Although the cache keys include
/// `shared_id` for run discrimination, clearing prevents unbounded growth when
/// the same thread runs multiple specs sequentially.
pub(crate) fn clear_enum_subst_cache() {
    CACHE.with(|cache| cache.borrow_mut().clear());
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::span::Spanned;

    fn clear_cache() {
        super::clear_enum_subst_cache();
    }

    #[test]
    fn cached_substitute_discriminates_resolved_operator_identity() {
        clear_cache();

        let ctx = EvalCtx::new();
        let call_site = Spanned::dummy(Expr::Bool(true));

        let first = cached_substitute(&ctx, &call_site, 11, || Spanned::dummy(Expr::Bool(true)));
        let second = cached_substitute(&ctx, &call_site, 22, || Spanned::dummy(Expr::Bool(false)));

        assert!(
            matches!(first.as_ref().node, Expr::Bool(true)),
            "first resolved operator should keep its cached substitution"
        );
        assert!(
            matches!(second.as_ref().node, Expr::Bool(false)),
            "same call site under a different operator scope must not reuse the first body"
        );
    }

    #[test]
    fn cached_substitute_discriminates_shared_context_runs() {
        clear_cache();

        let ctx1 = EvalCtx::new();
        let ctx2 = EvalCtx::new();
        let call_site = Spanned::dummy(Expr::Bool(true));

        assert_ne!(
            ctx1.shared().id,
            ctx2.shared().id,
            "test setup requires distinct SharedCtx ids"
        );

        let first = cached_substitute(&ctx1, &call_site, 11, || Spanned::dummy(Expr::Bool(true)));
        let second = cached_substitute(&ctx2, &call_site, 11, || Spanned::dummy(Expr::Bool(false)));

        assert!(
            matches!(first.as_ref().node, Expr::Bool(true)),
            "first shared context should keep its cached substitution"
        );
        assert!(
            matches!(second.as_ref().node, Expr::Bool(false)),
            "cache entries from one SharedCtx must not leak into a later run on the same thread"
        );
    }
}
