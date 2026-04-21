// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable scope identity for evaluator caches.
//!
//! Part of #3099: Computes content-based u64 fingerprints for
//! `instance_substitutions` and non-recursive `local_ops` scopes. Recursive
//! `LET` operator environments fall back to `Arc` identity so cache keys
//! do not alias distinct captured bindings across recursion levels.
//!
//! The fingerprints are computed once at scope construction time. Cache
//! lookups read the stored u64 from `EvalCtxStable.scope_ids`.

use crate::core::OpEnv;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tla_core::ast::{Expr, Substitution};
use tla_core::name_intern::{intern_name, NameId};

/// Sentinel value indicating the scope id was invalidated by a direct
/// mutation (e.g., `local_ops_mut()`). Cache key builders detect this
/// and lazily recompute from the current scope content.
pub(crate) const INVALIDATED: u64 = u64::MAX;

/// Stable scope identity for cache keys.
///
/// `None` / empty scope produces id `0`. Logically identical non-empty
/// scopes produce the same id. Different scope content produces different
/// ids (with astronomically low collision probability via SipHash).
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct EvalScopeIds {
    pub(crate) local_ops: u64,
    pub(crate) instance_substitutions: u64,
}

/// Compute a stable u64 fingerprint for a `local_ops` OpEnv.
///
/// Key shape: sorted (NameId, body.span.start, body.span.end, params.len())
/// per operator definition. Sorting by NameId ensures deterministic hashing
/// regardless of HashMap iteration order.
pub(crate) fn compute_local_ops_id(ops: &OpEnv) -> u64 {
    if ops.is_empty() {
        return 0;
    }
    // Collect fingerprint tuples and sort by NameId for determinism.
    let mut entries: Vec<(NameId, u32, u32, usize)> = ops
        .iter()
        .map(|(name, def)| {
            let name_id = intern_name(name);
            (
                name_id,
                def.body.span.start,
                def.body.span.end,
                def.params.len(),
            )
        })
        .collect();
    entries.sort_unstable();

    let mut hasher = rustc_hash::FxHasher::default();
    entries.len().hash(&mut hasher);
    for (nid, start, end, arity) in &entries {
        nid.hash(&mut hasher);
        start.hash(&mut hasher);
        end.hash(&mut hasher);
        arity.hash(&mut hasher);
    }
    hasher.finish()
}

/// Recursive `LET` operators change captured variable bindings at each recursion
/// level. Content-based fingerprinting would equate two levels with identical
/// operator bodies but different bound variables, causing incorrect cache hits.
/// Fall back to `Arc` pointer identity so each recursion frame gets a unique key.
#[inline]
fn local_ops_requires_arc_identity(ops: &OpEnv) -> bool {
    ops.values().any(|def| def.is_recursive)
}

/// Compute the effective cache scope id for a shared `local_ops` environment.
///
/// Recursive `LET` operators can capture different variable bindings at each
/// recursion level even when the operator bodies are identical. Those scopes
/// keep `Arc` pointer identity so different recursion frames cannot alias each
/// other in `SUBST_CACHE` / `NARY_OP_CACHE`.
#[inline]
pub(crate) fn compute_local_ops_scope_id(local_ops: &Arc<OpEnv>) -> u64 {
    if local_ops.is_empty() {
        0
    } else if local_ops_requires_arc_identity(local_ops) {
        Arc::as_ptr(local_ops) as usize as u64
    } else {
        compute_local_ops_id(local_ops)
    }
}

/// Hash immediate scalar content of an expression without recursing into children.
///
/// Provides O(1) discrimination between expressions that share the same
/// discriminant and span. Only leaf variants carry hashable content; compound
/// variants rely on span + discriminant (which is correct when source spans differ).
///
/// Part of #3406: fixes aliasing of `Spanned::dummy` INSTANCE substitutions.
fn hash_expr_shallow(hasher: &mut impl Hasher, expr: &Expr) {
    std::mem::discriminant(expr).hash(hasher);
    match expr {
        Expr::Bool(b) => b.hash(hasher),
        Expr::Int(n) => n.hash(hasher),
        Expr::String(s) => s.hash(hasher),
        Expr::Ident(_, name_id) => name_id.hash(hasher),
        Expr::StateVar(_, idx, name_id) => {
            idx.hash(hasher);
            name_id.hash(hasher);
        }
        Expr::OpRef(s) => s.hash(hasher),
        // Compound variants: discriminant already hashed above.
        // In real parsed specs, these have distinct source spans.
        // The Spanned::dummy collision vector only affects leaf values.
        _ => {}
    }
}

/// Compute a stable u64 fingerprint for instance substitutions.
///
/// Key shape: ordered (from_name_id, to.span.start, to.span.end, shallow_expr_hash)
/// per substitution entry. Order preserved from the `Vec<Substitution>`.
///
/// Fix #3406: span + discriminant aliased expressions of same type at same location
/// (e.g., `Int(1)` vs `Int(2)` both with `Spanned::dummy`). Shallow content hash
/// includes immediate scalar content for leaf variants, providing O(1) discrimination
/// without recursing into children (avoiding the #3123 timeout regression).
pub(crate) fn compute_instance_subs_id(subs: &[Substitution]) -> u64 {
    if subs.is_empty() {
        return 0;
    }
    let mut hasher = rustc_hash::FxHasher::default();
    subs.len().hash(&mut hasher);
    for sub in subs {
        let name_id = intern_name(&sub.from.node);
        name_id.hash(&mut hasher);
        sub.to.span.start.hash(&mut hasher);
        sub.to.span.end.hash(&mut hasher);
        hash_expr_shallow(&mut hasher, &sub.to.node);
    }
    hasher.finish()
}

/// Resolve the effective local_ops scope id from context fields.
///
/// Returns the stored scope id if valid, or lazily recomputes from the
/// current `local_ops` content when the id is INVALIDATED (set by
/// `local_ops_mut()` direct mutations).
///
/// Recursive `local_ops` scopes always resolve from the current `Arc` so
/// callers that swap in a different captured scope do not need to keep the
/// stored id in sync manually.
#[inline]
pub(crate) fn resolve_local_ops_id(scope_id: u64, local_ops: &Option<Arc<OpEnv>>) -> u64 {
    match local_ops.as_ref() {
        Some(local_ops) if local_ops_requires_arc_identity(local_ops) => {
            compute_local_ops_scope_id(local_ops)
        }
        _ if scope_id != INVALIDATED => scope_id,
        _ => local_ops.as_ref().map_or(0, compute_local_ops_scope_id),
    }
}

/// Resolve the effective instance_substitutions scope id from context fields.
///
/// Returns the stored scope id if valid, or lazily recomputes from the
/// current `instance_substitutions` content when the id is INVALIDATED.
#[inline]
pub(crate) fn resolve_instance_subs_id(
    scope_id: u64,
    instance_subs: &Option<std::sync::Arc<Vec<Substitution>>>,
) -> u64 {
    if scope_id != INVALIDATED {
        scope_id
    } else {
        instance_subs
            .as_ref()
            .map_or(0, |s| compute_instance_subs_id(s))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::ast::OperatorDef;
    use tla_core::Spanned;

    fn make_def(name: &str, body_start: u32, body_end: u32, local: bool) -> Arc<OperatorDef> {
        let fid = tla_core::span::FileId(0);
        Arc::new(OperatorDef {
            name: Spanned::new(name.into(), tla_core::Span::new(fid, 0, 3)),
            params: vec![],
            body: Spanned::new(
                tla_core::ast::Expr::Bool(true),
                tla_core::Span::new(fid, body_start, body_end),
            ),
            local,
            contains_prime: false,
            guards_depend_on_prime: false,
            is_recursive: false,
            has_primed_param: false,
            self_call_count: 0,
        })
    }

    /// Create a recursive operator def (is_recursive=true, local=false).
    /// Models a `LET RECURSIVE SA[bb \in Ballot] == ...` pattern.
    fn make_recursive_def(name: &str, body_start: u32, body_end: u32) -> Arc<OperatorDef> {
        let fid = tla_core::span::FileId(0);
        Arc::new(OperatorDef {
            name: Spanned::new(name.into(), tla_core::Span::new(fid, 0, 3)),
            params: vec![],
            body: Spanned::new(
                tla_core::ast::Expr::Bool(true),
                tla_core::Span::new(fid, body_start, body_end),
            ),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            is_recursive: true,
            has_primed_param: false,
            self_call_count: 1,
        })
    }

    #[test]
    fn test_empty_ops_returns_zero() {
        let ops = OpEnv::new();
        assert_eq!(compute_local_ops_id(&ops), 0);
    }

    #[test]
    fn test_empty_subs_returns_zero() {
        let subs: Vec<Substitution> = vec![];
        assert_eq!(compute_instance_subs_id(&subs), 0);
    }

    #[test]
    fn test_same_ops_same_id() {
        let mut ops1 = OpEnv::new();
        let mut ops2 = OpEnv::new();
        let def = make_def("foo", 10, 14, false);
        ops1.insert("foo".into(), Arc::clone(&def));
        ops2.insert("foo".into(), Arc::clone(&def));
        // Different Arc wrappers, same content → same id
        assert_eq!(compute_local_ops_id(&ops1), compute_local_ops_id(&ops2));
    }

    #[test]
    fn test_different_ops_different_id() {
        let mut ops1 = OpEnv::new();
        let mut ops2 = OpEnv::new();
        let def1 = make_def("foo", 10, 14, false);
        let def2 = make_def("bar", 20, 24, false);
        ops1.insert("foo".into(), def1);
        ops2.insert("bar".into(), def2);
        assert_ne!(compute_local_ops_id(&ops1), compute_local_ops_id(&ops2));
    }

    #[test]
    fn test_nonlocal_scope_uses_content_id_across_reconstructed_arcs() {
        let mut ops1 = OpEnv::new();
        let mut ops2 = OpEnv::new();
        ops1.insert("foo".into(), make_def("foo", 10, 14, false));
        ops2.insert("foo".into(), make_def("foo", 10, 14, false));
        let arc1 = Arc::new(ops1);
        let arc2 = Arc::new(ops2);

        assert_eq!(
            compute_local_ops_scope_id(&arc1),
            compute_local_ops_scope_id(&arc2)
        );
    }

    #[test]
    fn test_recursive_scope_uses_arc_identity_across_reconstructed_arcs() {
        let mut ops1 = OpEnv::new();
        let mut ops2 = OpEnv::new();
        ops1.insert("foo".into(), make_recursive_def("foo", 10, 14));
        ops2.insert("foo".into(), make_recursive_def("foo", 10, 14));
        let arc1 = Arc::new(ops1);
        let arc2 = Arc::new(ops2);

        // Identical recursive operator bodies but different Arc allocations →
        // different scope ids (Arc identity prevents cross-level aliasing).
        assert_ne!(
            compute_local_ops_scope_id(&arc1),
            compute_local_ops_scope_id(&arc2)
        );
    }

    /// Part of #3156: local-only (non-recursive) operators now use content hash,
    /// since the LOCAL keyword alone does not create scope aliasing risk.
    #[test]
    fn test_local_only_nonrecursive_uses_content_hash() {
        let mut ops1 = OpEnv::new();
        let mut ops2 = OpEnv::new();
        ops1.insert("foo".into(), make_def("foo", 10, 14, true));
        ops2.insert("foo".into(), make_def("foo", 10, 14, true));
        let arc1 = Arc::new(ops1);
        let arc2 = Arc::new(ops2);

        // local=true but is_recursive=false → content hash (same content = same id).
        assert_eq!(
            compute_local_ops_scope_id(&arc1),
            compute_local_ops_scope_id(&arc2)
        );
    }

    #[test]
    fn test_resolve_valid_id() {
        assert_eq!(resolve_local_ops_id(42, &None), 42);
    }

    #[test]
    fn test_resolve_invalidated_id() {
        assert_eq!(resolve_local_ops_id(INVALIDATED, &None), 0);
    }

    #[test]
    fn test_resolve_invalidated_recursive_scope_preserves_arc_identity() {
        let mut ops1 = OpEnv::new();
        let mut ops2 = OpEnv::new();
        ops1.insert("foo".into(), make_recursive_def("foo", 10, 14));
        ops2.insert("foo".into(), make_recursive_def("foo", 10, 14));

        assert_ne!(
            resolve_local_ops_id(INVALIDATED, &Some(Arc::new(ops1))),
            resolve_local_ops_id(INVALIDATED, &Some(Arc::new(ops2)))
        );
    }

    /// Part of #3156: Regression test proving that recursive LET scopes
    /// without module-level LOCAL still use Arc identity. Previously,
    /// the predicate checked `def.local` (LOCAL keyword) instead of
    /// `def.is_recursive`, so non-LOCAL recursive LET operators would
    /// incorrectly take the content-hash path.
    #[test]
    fn test_3156_recursive_let_without_local_uses_arc_identity() {
        let mut ops1 = OpEnv::new();
        let mut ops2 = OpEnv::new();
        // is_recursive=true, local=false — exactly the case #3156 describes.
        let def1 = make_recursive_def("SA", 100, 200);
        let def2 = make_recursive_def("SA", 100, 200);
        assert!(
            !def1.local,
            "regression: recursive LET ops must not need LOCAL"
        );
        assert!(def1.is_recursive, "regression: must be recursive");
        ops1.insert("SA".into(), def1);
        ops2.insert("SA".into(), def2);
        let arc1 = Arc::new(ops1);
        let arc2 = Arc::new(ops2);

        // These two scopes have identical content but represent different
        // recursion levels with different captured variable bindings.
        // They MUST get different scope ids (Arc identity).
        assert_ne!(
            compute_local_ops_scope_id(&arc1),
            compute_local_ops_scope_id(&arc2),
            "recursive LET scopes without LOCAL must use Arc identity"
        );
        assert!(local_ops_requires_arc_identity(&arc1));
    }

    /// Part of #3156: Non-recursive, non-local operators still use content hashing.
    #[test]
    fn test_3156_nonrecursive_nonlocal_uses_content_hash() {
        let mut ops1 = OpEnv::new();
        let mut ops2 = OpEnv::new();
        ops1.insert("bar".into(), make_def("bar", 10, 14, false));
        ops2.insert("bar".into(), make_def("bar", 10, 14, false));
        let arc1 = Arc::new(ops1);
        let arc2 = Arc::new(ops2);

        // Same content → same scope id (content hash, not Arc identity).
        assert_eq!(
            compute_local_ops_scope_id(&arc1),
            compute_local_ops_scope_id(&arc2),
            "non-recursive non-local ops must use content hash"
        );
        assert!(!local_ops_requires_arc_identity(&arc1));
    }

    /// Part of #3099 Step 5: SUBST_CACHE lookup succeeds when the entry was stored
    /// with an eager scope id and the lookup key uses the INVALIDATED -> resolve path.
    #[test]
    fn test_3099_subst_cache_hit_across_eager_and_invalidated_local_ops_id() {
        use crate::cache::dep_tracking::OpEvalDeps;
        use crate::cache::subst_cache::{SubstCacheEntry, SubstCacheKey, SUBST_STATE};
        use tla_core::name_intern::intern_name;
        use tla_value::Value;

        crate::cache::lifecycle::clear_for_test_reset();

        let def = make_def("foo", 10, 14, false);
        let mut ops_a = OpEnv::new();
        ops_a.insert("foo".into(), Arc::clone(&def));
        let eager_id = compute_local_ops_scope_id(&Arc::new(ops_a));

        let name_id = intern_name("test_subst");
        let key_insert = SubstCacheKey {
            is_next_state: false,
            name_id,
            shared_id: 1,
            local_ops_id: eager_id,
            instance_subs_id: 0,
            chained_ref_eval: false,
        };
        SUBST_STATE.with(|s| {
            s.borrow_mut().cache.insert(
                key_insert,
                SubstCacheEntry {
                    value: Value::int(42),
                    deps: OpEvalDeps::default(),
                },
            );
        });

        // INVALIDATED -> resolve path with identical content, different Arc.
        let mut ops_b = OpEnv::new();
        ops_b.insert("foo".into(), Arc::clone(&def));
        let resolved_id = resolve_local_ops_id(INVALIDATED, &Some(Arc::new(ops_b)));
        assert_eq!(eager_id, resolved_id, "same content must produce same id");

        let key_lookup = SubstCacheKey {
            is_next_state: false,
            name_id,
            shared_id: 1,
            local_ops_id: resolved_id,
            instance_subs_id: 0,
            chained_ref_eval: false,
        };
        let found =
            SUBST_STATE.with(|s| s.borrow().cache.get(&key_lookup).map(|e| e.value.clone()));
        assert_eq!(found, Some(Value::int(42)), "SUBST_CACHE must hit");

        crate::cache::lifecycle::clear_for_test_reset();
    }

    /// Part of #3406: Int(1) vs Int(2) with dummy spans must produce different scope ids.
    #[test]
    fn test_3406_distinct_int_subs_with_dummy_span_get_distinct_ids() {
        use tla_core::ast::Expr;

        let sub1 = Substitution {
            from: Spanned::dummy("outer".into()),
            to: Spanned::dummy(Expr::Int(1.into())),
        };
        let sub2 = Substitution {
            from: Spanned::dummy("outer".into()),
            to: Spanned::dummy(Expr::Int(2.into())),
        };
        assert_ne!(
            compute_instance_subs_id(&[sub1]),
            compute_instance_subs_id(&[sub2]),
            "Int(1) and Int(2) with dummy spans must produce different scope ids"
        );
    }

    /// Part of #3406: Ident(channelA) vs Ident(channelB) with dummy spans must differ.
    #[test]
    fn test_3406_distinct_ident_subs_with_dummy_span_get_distinct_ids() {
        use tla_core::ast::Expr;
        use tla_core::name_intern::intern_name;

        let id_a = intern_name("channelA");
        let id_b = intern_name("channelB");
        let sub1 = Substitution {
            from: Spanned::dummy("chan".into()),
            to: Spanned::dummy(Expr::Ident("channelA".into(), id_a)),
        };
        let sub2 = Substitution {
            from: Spanned::dummy("chan".into()),
            to: Spanned::dummy(Expr::Ident("channelB".into(), id_b)),
        };
        assert_ne!(
            compute_instance_subs_id(&[sub1]),
            compute_instance_subs_id(&[sub2]),
            "Ident(channelA) and Ident(channelB) with dummy spans must differ"
        );
    }
}
