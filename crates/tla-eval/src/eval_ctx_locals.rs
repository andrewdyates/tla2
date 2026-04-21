// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Local binding lifecycle methods for `EvalCtx`.
//!
//! Part of #2955: BindingChain is now the sole source of truth for local
//! bindings. The previous `local_stack: Vector<(Arc<str>, Value, NameId)>` has
//! been replaced by `binding_depth: usize` — a simple counter for mark/pop
//! restoration. All binding data lives in the immutable persistent BindingChain.
//!
//! Extracted from `core.rs` as part of #2764 / #1643.

use super::EvalCtx;
use crate::core::EvalCtxStable;
use crate::value::Value;
use std::rc::Rc;
use std::sync::Arc;
use tla_core::name_intern::{intern_name, lookup_name_id, NameId};

/// Opaque mark for restoring EvalCtx binding state — O(1) save and restore.
///
/// Part of #2955 Step 3: Replaces `chain_snapshots: Vec<(usize, BindingChain)>`
/// with a direct snapshot captured once at mark_stack() time.
/// TLC parity: Context is an immutable cons-list, so "restoring" is just
/// reassigning the saved head. No per-push snapshot overhead needed.
#[derive(Clone)]
pub struct StackMark {
    pub(crate) depth: usize,
    pub(crate) chain: crate::binding_chain::BindingChain,
}

impl StackMark {
    /// Return the binding depth at mark time.
    ///
    /// Useful for callers that need to compare the current stack position
    /// against a previously-saved mark (e.g., to detect whether a
    /// `ScopeRestore` has already popped past this mark).
    #[inline]
    pub fn depth(&self) -> usize {
        self.depth
    }
}

impl std::fmt::Debug for StackMark {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StackMark")
            .field("depth", &self.depth)
            .finish_non_exhaustive()
    }
}

/// Full context mark for EXISTS enumeration loops — O(1) save and restore.
///
/// Part of #3893: Replaces `ctx.clone()` in EXISTS iteration with save/restore.
/// Captures ALL mutable EvalCtx fields that could be modified during body
/// evaluation (through conjunct_let, conjunct_apply, scope_restore, etc.),
/// enabling in-place mutation + restore instead of clone-per-iteration.
///
/// This is sound because:
/// - `stable` (Rc<EvalCtxStable>) is restored to the pre-iteration snapshot,
///   discarding any COW mutations to local_ops, skip_prime_validation, etc.
/// - `bindings` + `binding_depth` are restored (same as StackMark)
/// - `let_def_overlay` is restored (LET defs pushed during body eval are discarded)
/// - `call_by_name_subs` is restored (operator scope changes are discarded)
///
/// Fields NOT captured (invariant: unchanged during EXISTS body eval):
/// - `tlc_action_context`: set at operator entry, not during body eval
/// - `recursion_depth`: recursive function eval restores on return
/// - `active_lazy_func`: recursive function eval restores on return
/// - `sparse_next_state_env`: set by ENABLED, not during normal body eval
#[derive(Clone)]
pub struct EnumMark {
    pub(crate) depth: usize,
    pub(crate) chain: crate::binding_chain::BindingChain,
    pub(crate) let_def_overlay: crate::let_def_chain::LetDefOverlay,
    pub(crate) stable: Rc<EvalCtxStable>,
    pub(crate) call_by_name_subs: Option<Arc<Vec<tla_core::ast::Substitution>>>,
}

impl EnumMark {
    /// Return the binding depth at mark time.
    #[inline]
    pub fn depth(&self) -> usize {
        self.depth
    }
}

impl std::fmt::Debug for EnumMark {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EnumMark")
            .field("depth", &self.depth)
            .finish_non_exhaustive()
    }
}

impl EvalCtx {
    // ---- Local Stack Operations ----

    /// Push a binding — O(1) operation.
    /// Use with mark_stack() and pop_to_mark() for scoped bindings.
    ///
    /// Part of #2955: Writes ONLY to BindingChain (sole source of truth).
    /// No snapshot saving — mark_stack() captures the chain head once;
    /// pop_to_mark() restores directly from the StackMark.
    #[inline]
    pub fn push_binding(&mut self, name: Arc<str>, value: Value) {
        let name_id = intern_name(name.as_ref());
        let depth = self.binding_depth;
        self.bindings = self.bindings.cons_local(
            name_id,
            crate::binding_chain::BindingValue::eager(value),
            depth,
        );
        self.binding_depth += 1;
    }

    /// Push a binding with pre-interned name and NameId — O(1) operation.
    ///
    /// Optimized for hot paths where name and NameId are known (e.g., quantifiers).
    ///
    /// Part of #3395: name parameter kept for API compatibility but no longer stored
    /// in BindingNode.
    /// Part of #3805: Consider using `push_binding_by_id` instead to avoid the
    /// unnecessary `Arc::clone` of the name parameter.
    #[inline]
    pub fn push_binding_preinterned(&mut self, _name: Arc<str>, value: Value, name_id: NameId) {
        let depth = self.binding_depth;
        self.bindings = self.bindings.cons_local(
            name_id,
            crate::binding_chain::BindingValue::eager(value),
            depth,
        );
        self.binding_depth += 1;
    }

    /// Push a binding using only the NameId — O(1) operation, zero Arc overhead.
    ///
    /// Part of #3805: The name string is not stored in BindingNode (#3395), so
    /// callers that only have a NameId can avoid the unnecessary `Arc::clone`
    /// that `push_binding_preinterned` requires for API compatibility. This saves
    /// one atomic refcount increment+decrement per quantifier iteration.
    #[inline]
    pub fn push_binding_by_id(&mut self, name_id: NameId, value: Value) {
        let depth = self.binding_depth;
        self.bindings = self.bindings.cons_local(
            name_id,
            crate::binding_chain::BindingValue::eager(value),
            depth,
        );
        self.binding_depth += 1;
    }

    /// Look up a binding by name in the current scope.
    ///
    /// Returns `Some(value)` if the name is bound in the current binding chain,
    /// `None` otherwise. This is a lightweight lookup for known eager bindings
    /// (e.g., EXISTS-bound variables like `self` in PlusCal).
    ///
    /// Note: only resolves eager bindings. Lazy thunks, INSTANCE substitutions,
    /// and other complex binding forms are not resolved — returns `None` for those.
    #[inline]
    pub fn lookup_binding(&self, name: &str) -> Option<Value> {
        let name_id = lookup_name_id(name)?;
        let (bv, _source) = self.bindings.lookup(name_id)?;
        if let crate::binding_chain::BindingValueRef::Eager(cv) = bv {
            Some(Value::from(cv))
        } else {
            None
        }
    }

    /// Capture current binding state for later restoration — O(1).
    ///
    /// Part of #2955 Step 3: Returns a StackMark capturing the current chain head
    /// and depth. Restoring via pop_to_mark() is O(1) regardless of how many
    /// push_binding calls occurred between mark and pop.
    #[inline]
    pub fn mark_stack(&self) -> StackMark {
        StackMark {
            depth: self.binding_depth,
            chain: self.bindings.clone(),
        }
    }

    /// Pop all bindings back to a marked position — O(1).
    ///
    /// When `mark.depth > binding_depth`, returns immediately (no-op). This occurs when
    /// a `ScopeRestore` in `enumerate_conjuncts`' base case has already popped
    /// past this mark as part of LET/apply scope isolation (#804).
    ///
    /// Part of #2955 Step 3: Direct restore from StackMark — no chain_snapshots
    /// walk needed. The StackMark contains the exact chain head from mark time.
    #[inline]
    pub fn pop_to_mark(&mut self, mark: &StackMark) {
        if mark.depth > self.binding_depth {
            return;
        }
        self.bindings = mark.chain.clone();
        self.binding_depth = mark.depth;
    }

    /// Capture full mutable EvalCtx state for EXISTS enumeration — O(1).
    ///
    /// Part of #3893: Saves all fields that `ctx.clone()` would snapshot,
    /// enabling mark/restore to replace clone-per-iteration in EXISTS loops.
    /// Restore via `pop_to_enum_mark()`.
    ///
    /// Cost: 1 Rc bump (stable) + 2 Rc/Arc bumps (bindings, let_def_overlay) +
    /// 1 Option<Arc> clone (call_by_name_subs) + 1 usize copy.
    /// This is equivalent to ctx.clone() but the restore path is cheaper
    /// because it avoids constructing a new EvalCtx struct each iteration.
    #[inline]
    pub fn mark_enum(&self) -> EnumMark {
        EnumMark {
            depth: self.binding_depth,
            chain: self.bindings.clone(),
            let_def_overlay: self.let_def_overlay.clone(),
            stable: Rc::clone(&self.stable),
            call_by_name_subs: self.call_by_name_subs.clone(),
        }
    }

    /// Restore full EvalCtx state from an EnumMark — O(1).
    ///
    /// Part of #3893: Restores all mutable fields saved by `mark_enum()`.
    /// This is the counterpart of dropping a cloned EvalCtx — it discards
    /// all mutations that occurred during the EXISTS body evaluation.
    #[inline]
    pub fn pop_to_enum_mark(&mut self, mark: &EnumMark) {
        self.bindings = mark.chain.clone();
        self.binding_depth = mark.depth;
        self.let_def_overlay = mark.let_def_overlay.clone();
        self.stable = Rc::clone(&mark.stable);
        self.call_by_name_subs = mark.call_by_name_subs.clone();
    }

    /// Get the current binding depth — used for debug and dependency tracking.
    #[inline]
    pub fn local_stack_len(&self) -> usize {
        self.binding_depth
    }

    /// Debug: return a string representation of current stack bindings.
    ///
    /// Part of #2955: Walks the BindingChain instead of local_stack.
    pub fn stack_bindings_debug(&self) -> String {
        let bindings = self.bindings.collect_local_bindings();
        if bindings.is_empty() {
            return "[]".to_string();
        }
        let strs: Vec<String> = bindings
            .iter()
            .map(|(name, val, _id)| format!("{name}={val}"))
            .collect();
        format!("[{}]", strs.join(", "))
    }

    /// Update the value of the most recent binding in place — O(1).
    ///
    /// # Part of #129: ISpec performance optimization
    ///
    /// This avoids the overhead of push/pop per iteration in quantifier loops.
    /// The caller must ensure binding_depth > 0.
    ///
    /// Part of #2955: Updates ONLY the BindingChain head node.
    #[inline]
    pub fn update_last_binding_value(&mut self, value: Value) {
        self.bindings
            .update_head_value(crate::binding_chain::BindingValue::eager(value));
    }

    // pop_binding removed — Part of #2955 Step 3: no callers, chain_snapshots
    // eliminated. mark_stack/pop_to_mark handles all scoped binding lifecycle.

    /// Get local variable by de Bruijn depth — O(depth) chain walk.
    ///
    /// depth=0 is the most recent Local binding, depth=1 is the next, etc.
    /// Returns None if depth exceeds chain size.
    ///
    /// Part of #2895 Step 4: Unified — both compiled and AST paths use the
    /// BindingChain directly. Eliminates the fast_locals dual-tier lookup.
    /// Typical depth 1-3 for quantifier nesting, matching TLC Context.lookup.
    #[inline]
    pub fn get_local_by_depth(&self, depth: u8) -> Option<Value> {
        self.bindings.get_local_by_depth(depth as usize)
    }

    // fast_locals methods removed — Part of #2895 Step 4.
    // Compiled path now uses the same BindingChain as the AST path:
    //   push_fast_local       → push_binding_preinterned
    //   mark_fast_locals      → mark_stack
    //   pop_fast_locals_to    → pop_to_mark
    //   update_fast_local_top → update_last_binding_value
    //   materialize_fast_locals → no-op (already in chain)
    //   fast_locals_is_empty  → not needed (no dual store)

    /// Get a reference to the current local bindings (EXISTS bounds, operator params).
    /// Used to capture bindings alongside expressions for deferred evaluation.
    ///
    /// Part of #2955, #2895: Walks the BindingChain (sole source of truth for locals).
    #[inline]
    pub fn get_local_bindings(&self) -> Vec<(Arc<str>, Value)> {
        self.bindings
            .collect_local_bindings()
            .into_iter()
            .map(|(name, value, _id)| (name, value))
            .collect()
    }

    // ---- Captured Environment ----

    // captured_env() removed — Part of #2895: All production callers migrated
    // to chain-based capture (create_closure for closures, SetPredCaptures for
    // SetPredValue). The O(n) env HashMap deep clone is no longer needed.

    /// Create a ClosureValue capturing the current BindingChain for O(1) restore.
    ///
    /// Part of #2895, #2989: The BindingChain is the sole source of truth for local
    /// bindings — `captured_env()` (O(n) deep clone + merge) and `get_local_bindings()`
    /// (O(n) Vec allocation) are eliminated. The env field stores only the module-level
    /// environment via Arc::clone (O(1) refcount bump). At application time,
    /// `build_closure_ctx` restores the chain directly in O(1).
    pub fn create_closure(
        &self,
        params: Vec<String>,
        body: tla_core::Spanned<tla_core::ast::Expr>,
        local_ops: Option<Arc<tla_core::OpEnv>>,
    ) -> crate::value::ClosureValue {
        crate::value::ClosureValue::new(params, body, Arc::clone(&self.env), local_ops)
            .with_captured_chain(Box::new(self.bindings.clone()), self.binding_depth)
    }

    /// Create a new context with the given captured bindings restored.
    /// Used to evaluate expressions captured during enumeration.
    ///
    /// Part of #2955: Rebuilds the BindingChain from captured bindings.
    pub fn with_captured_bindings(&self, bindings: &[(Arc<str>, Value)]) -> Self {
        let mut ctx = self.clone();
        // Rebuild chain from captured bindings
        ctx.bindings = crate::binding_chain::BindingChain::empty();
        ctx.binding_depth = 0;
        for (name, value) in bindings {
            let name_id = intern_name(name.as_ref());
            ctx.push_binding_preinterned(Arc::clone(name), value.clone(), name_id);
        }
        ctx
    }

    // ---- Env Scope Management ----

    /// Bind a variable mutably in the current context.
    ///
    /// Part of #3964: Use Arc::get_mut fast path (non-atomic check) when the env
    /// Arc is uniquely owned. Falls back to Arc::make_mut (atomic CAS + clone)
    /// only when shared. In loops that call bind_mut repeatedly (e.g., init
    /// enumeration binding state vars), the first call may clone but subsequent
    /// calls find refcount == 1 and take the fast path.
    pub fn bind_mut(&mut self, name: impl Into<Arc<str>>, value: Value) {
        let env = &mut self.stable_mut().env;
        if let Some(e) = Arc::get_mut(env) {
            e.insert(name.into(), value);
        } else {
            Arc::make_mut(env).insert(name.into(), value);
        }
    }

    /// Unbind a variable from the current context, returning its previous value.
    /// Part of #129: O(1) unbind for efficient Init enumeration.
    /// Part of #3964: Arc::get_mut fast path for non-atomic check.
    #[inline]
    pub fn unbind(&mut self, name: &str) -> Option<Value> {
        let env = &mut self.stable_mut().env;
        if let Some(e) = Arc::get_mut(env) {
            e.remove(name)
        } else {
            Arc::make_mut(env).remove(name)
        }
    }

    // save_scope/restore_scope removed — Part of #2895: zero callers remaining.
    // All scope management uses ScopeGuard (eval_ctx_guards.rs) or mark_stack/pop_to_mark.
    // bind_mut/unbind pattern (above) handles imperative state-variable setup for
    // init enumeration; env restoration is handled by unbind, not save_scope.

    /// Batch-insert next-state variables into env, skipping locally-bound names.
    ///
    /// Part of #3964: Hoists `Arc::make_mut` outside the loop so the Rc::make_mut +
    /// Arc refcount check happens once instead of N times (N = number of state vars).
    /// Uses field-level borrow splitting: `self.stable` (cold, mut) is disjoint from
    /// `self.binding_depth` and `self.bindings` (hot, read-only).
    #[inline]
    pub(crate) fn batch_insert_into_env<'a>(
        &mut self,
        items: impl Iterator<Item = (&'a Arc<str>, &'a Value)>,
    ) {
        let has_locals = self.binding_depth > 0;
        // Part of #3964: Use Rc::get_mut + Arc::get_mut (non-atomic) when both
        // are uniquely owned, falling back to make_mut for the shared case.
        let stable = Rc::make_mut(&mut self.stable);
        let env = if let Some(e) = Arc::get_mut(&mut stable.env) {
            e
        } else {
            Arc::make_mut(&mut stable.env)
        };
        for (name, value) in items {
            if has_locals {
                if let Some(id) = lookup_name_id(name.as_ref()) {
                    if self.bindings.lookup(id).is_some() {
                        continue;
                    }
                }
            }
            env.insert(Arc::clone(name), value.clone());
        }
    }
}
