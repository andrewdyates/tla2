// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy and eager binding values for the binding chain.
//!
//! Extracted from `binding_chain.rs` for file size compliance.
//! Contains [`BindingValue`] (eager/lazy discriminant) and [`LazyBinding`]
//! (deferred evaluation with context-aware caching).

use std::sync::OnceLock;

use crate::cache::dep_tracking::StateLookupMode;
use crate::OpEvalDeps;
use tla_core::Spanned;
use tla_value::{CompactValue, Value};

use super::{BindingChain, BindingSource, BindingSourceRef, BindingValueRef};

/// A binding value: either pre-computed (eager) or deferred (lazy).
///
/// Part of #2895: Made `pub` (was `pub(crate)`) so tla-check can construct
/// BindingChain entries with `BindingValue::Eager(value)`.
#[allow(private_interfaces)] // LazyBinding is pub(crate); external callers use Eager only
pub enum BindingValue {
    /// Pre-computed value (constants, eager substitutions, quantifier vars).
    /// Part of #3441 Slice 1: Inlined (was `Box<Value>`) to eliminate heap
    /// alloc/dealloc per quantifier iteration.
    /// Part of #3579: Stored as `CompactValue` (8B) instead of `Value` (24B)
    /// so eager BindingChain nodes match the compact state lane.
    Eager(CompactValue),
    /// Deferred computation — captures expression + enclosing chain.
    /// Evaluated on first access, result cached via interior mutability.
    /// Part of #2956: Used for RECURSIVE operator arity-0 arguments (TLC LazyValue parity).
    /// Part of #3063: Boxed to reduce BindingNode from ~484B to ~196B. LazyBinding is only
    /// used for INSTANCE substitution arguments (cold path), not quantifier hot paths.
    Lazy(Box<LazyBinding>),
}

/// Deferred binding that captures expression + enclosing scope.
///
/// Mirrors TLC's `LazyValue(expr, context)` pattern. On first access,
/// evaluates `expr` in `enclosing` scope and caches the result.
/// Part of #2956: Used by RECURSIVE operator lazy argument evaluation in apply.rs.
/// Arity-0 arguments are wrapped in LazyBinding; higher-order args (arity > 0) stay eager.
///
/// # Context-Aware Caching (Part of #3056 Phase 5)
///
/// TLC's `LazyValue.getCachedValue()` validates `(s0, s1, control)` on every read,
/// returning `null` when the evaluation context has changed. TLA2's LazyBinding
/// approximates this with dual OnceLocks: `cached` for `StateLookupMode::Current`
/// and `cached_primed` for `StateLookupMode::Next`. When the same INSTANCE
/// substitution binding is accessed both unprimed (`x`) and primed (`x'`, after
/// eval_prime swaps state), each mode caches independently — preventing the stale
/// value bug where `OnceLock` returns the first-cached value regardless of state.
///
/// # Scope of OnceLock caching
///
/// Part of #3465: the underlying OnceLock is still populated for some lazy
/// bindings, but the `BindingValue` read path keeps all `Lazy` values off that
/// cache until TLA2 has a validity check strong enough to avoid reusing stale
/// values across state evaluations. INSTANCE-sourced lazy bindings instead rely
/// on a per-state cache that is cleared at evaluation boundaries.
///
/// # Safety of `expr_ptr`
///
/// Raw pointer avoids Arc<Spanned<Expr>> alloc cost (~80ns/arg). Points into
/// OperatorDef body's args in SharedCtx (Arc-held, lives entire run).
pub(crate) struct LazyBinding {
    /// Raw pointer to arg expression in OperatorDef body's AST (see struct docs).
    pub expr_ptr: *const Spanned<tla_core::ast::Expr>,
    /// The binding chain at the point of definition (closure semantics).
    pub enclosing: BindingChain,
    /// Cached result for `StateLookupMode::Current` — empty until first evaluation.
    /// Part of #2956: OnceLock instead of Mutex — atomic read on cache hit, no
    /// lock contention. Safe because LazyBinding is write-once (first eval caches).
    pub cached: OnceLock<Value>,
    /// Cached result for `StateLookupMode::Next` (primed context).
    /// Part of #3056 Phase 5: When eval_prime swaps s0/s1 (TLC pattern), INSTANCE
    /// substitution bindings may produce different values than in Current mode.
    /// Separate OnceLock prevents stale cache returns across mode transitions.
    pub cached_primed: OnceLock<Value>,
    /// Part of #2991: Deps captured during first forcing of Instance lazy bindings.
    /// Propagated on OnceLock hits instead of empty BindingSource::Instance deps.
    pub forced_deps: OnceLock<OpEvalDeps>,
    /// Deps for primed-context forcing (Part of #3056 Phase 5).
    pub forced_deps_primed: OnceLock<OpEvalDeps>,
}

// SAFETY: LazyBinding's expr_ptr points into an Arc<OperatorDef> body stored
// in SharedCtx. The Arc guarantees the data is valid and immutable for the
// evaluation's lifetime. Send+Sync are required because Value is stored in
// Arc<[Value]> across threads in the parallel model checker. The OnceLock on
// `cached` provides safe concurrent caching (atomic CAS on first write,
// atomic read on subsequent access).
unsafe impl Send for LazyBinding {}
unsafe impl Sync for LazyBinding {}

impl LazyBinding {
    /// Construct a new LazyBinding with arena-safe enclosing chain.
    ///
    /// Part of #3580 audit fix: always promotes `enclosing` to heap before storing,
    /// preventing arena-backed nodes from escaping the BFS state boundary via the
    /// lazy binding's closure capture. This is the single construction point for
    /// production code — direct struct construction should only appear in tests.
    pub(crate) fn new(
        expr_ptr: *const Spanned<tla_core::ast::Expr>,
        enclosing: &BindingChain,
    ) -> Self {
        LazyBinding {
            expr_ptr,
            enclosing: enclosing.promote_all_to_heap(),
            cached: OnceLock::new(),
            forced_deps: OnceLock::new(),
            cached_primed: OnceLock::new(),
            forced_deps_primed: OnceLock::new(),
        }
    }

    /// Dereference the expression pointer.
    ///
    /// SAFETY: Caller must ensure the OperatorDef that owns this expression
    /// has not been dropped. This is guaranteed during model checking evaluation.
    pub(crate) fn expr(&self) -> &Spanned<tla_core::ast::Expr> {
        // SAFETY: expr_ptr is valid for the evaluation lifetime (see struct docs).
        unsafe { &*self.expr_ptr }
    }

    /// Cache the evaluated value for the given state lookup mode.
    /// Part of #3056 Phase 5: Mode-aware caching.
    pub(crate) fn set_cached(&self, value: Value, mode: StateLookupMode) {
        // Ignore the error if already set (concurrent evaluation race — fine,
        // both evaluations produce the same result for deterministic expressions).
        match mode {
            StateLookupMode::Current => {
                let _ = self.cached.set(value);
            }
            StateLookupMode::Next => {
                let _ = self.cached_primed.set(value);
            }
        }
    }

    /// Get deps captured during forcing for the given mode.
    /// Part of #3056 Phase 5: Mode-aware dep tracking.
    pub(crate) fn get_forced_deps(&self, mode: StateLookupMode) -> Option<&OpEvalDeps> {
        match mode {
            StateLookupMode::Current => self.forced_deps.get(),
            StateLookupMode::Next => self.forced_deps_primed.get(),
        }
    }

    /// Store deps captured during forcing for the given mode.
    /// Part of #3056 Phase 5: Mode-aware dep tracking.
    pub(crate) fn set_forced_deps(&self, deps: OpEvalDeps, mode: StateLookupMode) {
        match mode {
            StateLookupMode::Current => {
                let _ = self.forced_deps.set(deps);
            }
            StateLookupMode::Next => {
                let _ = self.forced_deps_primed.set(deps);
            }
        }
    }
}

impl BindingValue {
    /// Construct an eager binding value.
    #[inline(always)]
    pub fn eager(value: Value) -> Self {
        BindingValue::Eager(CompactValue::from(value))
    }

    /// Get the value if available without forcing.
    ///
    /// For `Eager` values, materializes and returns an owned value.
    /// For `Lazy` values, checks the mode-appropriate cache and returns the cached
    /// value if available. Returns `None` for un-evaluated lazy bindings (caller
    /// must evaluate and cache).
    ///
    /// Part of #3056 Phase 5: Mode-aware caching. `StateLookupMode::Current` checks
    /// `cached`; `StateLookupMode::Next` checks `cached_primed`. This prevents
    /// returning stale current-state values when accessed in primed context.
    ///
    /// Part of #3465: keep `Lazy` reads disabled at the `BindingValue` level.
    /// `MCPaxosSmall` still false-positives if Local lazy bindings are allowed
    /// to reuse the OnceLock through this path, so callers must force the lazy
    /// binding (or use the per-state INSTANCE cache for INSTANCE sources)
    /// instead of reading the per-binding OnceLock directly.
    #[allow(dead_code)]
    pub(crate) fn get_if_ready(
        &self,
        _mode: StateLookupMode,
        _source: &BindingSource,
    ) -> Option<Value> {
        match self {
            BindingValue::Eager(v) => Some(Value::from(v)),
            BindingValue::Lazy(_) => None,
        }
    }

    /// Compare a ready binding against an expected `CompactValue` without
    /// forcing or materializing either side through an intermediate `Value`.
    ///
    /// Part of #3579: CompactValue-to-CompactValue comparison when VarDepMap
    /// stores CompactValue. Enables fully zero-alloc dep validation for
    /// inline types (Bool, SmallInt) on the cache-hit path.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn matches_compact(
        &self,
        _mode: StateLookupMode,
        _source: &BindingSource,
        expected: &CompactValue,
    ) -> bool {
        match self {
            BindingValue::Eager(value) => value == expected,
            BindingValue::Lazy(_) => false,
        }
    }

    /// Get the lazy binding, if this is a lazy value.
    #[allow(dead_code)]
    pub(crate) fn as_lazy(&self) -> Option<&LazyBinding> {
        match self {
            BindingValue::Lazy(lazy) => Some(lazy.as_ref()),
            BindingValue::Eager(_) => None,
        }
    }
}

impl<'a> BindingValueRef<'a> {
    /// Get the value if available without forcing.
    pub(crate) fn get_if_ready(
        self,
        _mode: StateLookupMode,
        _source: BindingSourceRef<'_>,
    ) -> Option<Value> {
        match self {
            BindingValueRef::Eager(value) => Some(Value::from(value)),
            BindingValueRef::Lazy(_) => None,
        }
    }

    /// Compare a ready binding against an expected compact value.
    #[inline]
    pub(crate) fn matches_compact(
        self,
        _mode: StateLookupMode,
        _source: BindingSourceRef<'_>,
        expected: &CompactValue,
    ) -> bool {
        match self {
            BindingValueRef::Eager(value) => value == expected,
            BindingValueRef::Lazy(_) => false,
        }
    }

    /// Get the lazy binding, if this is a lazy value.
    pub(crate) fn as_lazy(self) -> Option<&'a LazyBinding> {
        match self {
            BindingValueRef::Lazy(lazy) => Some(lazy),
            BindingValueRef::Eager(_) => None,
        }
    }
}
