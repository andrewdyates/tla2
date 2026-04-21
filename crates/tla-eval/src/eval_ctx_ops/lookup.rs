// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EvalCtx variable and operator lookup methods. Part of #2764 / #1643.

use crate::{
    current_state_lookup_mode, eval_entry, record_local_read, record_next_read, record_state_read,
    EvalCtx, EvalError, EvalResult, StateLookupMode, Value,
};
use crate::eval_ident::fast_var_idx_lookup;
use std::sync::Arc;
use tla_core::ast::OperatorDef;
use tla_core::name_intern::{lookup_name_id, NameId};

impl EvalCtx {
    // ---- Variable lookup ----

    /// Look up a value in the environment
    /// Priority order:
    /// 1. BindingChain (local bindings: quantifier vars, LET defs, operator params)
    /// 2. state_env array (O(1) access for state variables when set)
    /// 3. env HashMap (fallback)
    #[inline]
    pub fn lookup(&self, name: &str) -> Option<Value> {
        // Compute NameId once for all interned-name lookups in this method.
        let maybe_name_id = lookup_name_id(name);
        self.lookup_inner(name, maybe_name_id)
    }

    /// Fast-path lookup using a pre-resolved NameId from TIR lowering.
    ///
    /// Skips the `lookup_name_id()` call (global interner HashMap lookup) when
    /// the TIR node already carries a valid NameId. Falls back to string-based
    /// resolution only when `name_id` is `NameId::INVALID`.
    ///
    /// Part of #3392: eliminate per-eval interner overhead on TIR hot path.
    #[inline]
    pub fn lookup_with_id(&self, name: &str, name_id: NameId) -> Option<Value> {
        let maybe_name_id = if name_id != NameId::INVALID {
            Some(name_id)
        } else {
            lookup_name_id(name)
        };
        self.lookup_inner(name, maybe_name_id)
    }

    #[inline]
    fn lookup_inner(&self, name: &str, maybe_name_id: Option<NameId>) -> Option<Value> {
        // Check BindingChain for local bindings (quantified variables that may shadow state vars)
        // Part of #2955: BindingChain is now the sole source of truth for local bindings.
        // Skip this check if binding_depth is 0 (common in state access)
        if self.binding_depth > 0 {
            if let Some(lookup_id) = maybe_name_id {
                if let Some((bv, source)) = self.bindings.lookup(lookup_id) {
                    if let Some(v) = bv.get_if_ready(current_state_lookup_mode(self), source) {
                        if let crate::binding_chain::BindingSourceRef::Local(depth)
                        | crate::binding_chain::BindingSourceRef::Liveness(depth) = source
                        {
                            record_local_read(self, depth, lookup_id, &v);
                        }
                        if current_state_lookup_mode(self) == StateLookupMode::Next {
                            // Part of #3961: Use O(1) var_idx_by_name_id table.
                            if let Some(idx) = fast_var_idx_lookup(self, lookup_id) {
                                record_next_read(self, idx, &v);
                            }
                        }
                        return Some(v);
                    }
                }
            }
        }
        // Part of #3961: Unified state variable lookup using O(1) var_idx_by_name_id
        // table. Resolves VarIndex once, reuses for sparse overlay + state_env.
        if let Some(lookup_id) = maybe_name_id {
            if let Some(idx) = fast_var_idx_lookup(self, lookup_id) {
                // Part of #3365: Sparse next-state overlay from ENABLED WitnessState.
                // In Next mode, bound sparse slots override current-state values.
                if current_state_lookup_mode(self) == StateLookupMode::Next {
                    if let Some(sparse_env) = self.sparse_next_state_env {
                        // SAFETY: idx bounded by VarRegistry, sparse_env has same layout.
                        let slot = unsafe { sparse_env.get_unchecked(idx.as_usize()) };
                        if let Some(v) = slot {
                            record_next_read(self, idx, v);
                            return Some(v.clone());
                        }
                        // None = unbound in witness, fall through to current state
                    }
                }
                // O(1) array access for state variables via pre-resolved index
                if let Some(state_env) = self.state_env {
                    debug_assert!(idx.as_usize() < state_env.env_len());
                    // SAFETY: `state_env` borrows a live `[Value]` slice and `idx` is bounded above.
                    let v = unsafe { state_env.get_value(idx.as_usize()) };
                    record_state_read(self, idx, &v);
                    return Some(v);
                }
            }
        }
        // Part of #2895: env.get() fallback — only needed when state_env is not set
        // or name is not interned. After promotion, env contains only state variables;
        // BindingChain and state_env cover all interned names during BFS.
        if maybe_name_id.is_none() || self.state_env.is_none() {
            let v = self.env.get(name);
            // Record dependency for state variables (fixes Issue #70: cache invalidation
            // when state_env is not set but vars are bound via bind_mut to env)
            if let Some(v) = v {
                if let Some(lookup_id) = maybe_name_id {
                    // Part of #3961: Use O(1) var_idx_by_name_id table.
                    if let Some(idx) = fast_var_idx_lookup(self, lookup_id) {
                        if current_state_lookup_mode(self) == StateLookupMode::Next {
                            record_next_read(self, idx, v);
                        } else {
                            record_state_read(self, idx, v);
                        }
                    }
                }
            }
            return v.cloned();
        }
        None
    }

    /// Returns true if `name` currently has a local (chain) binding.
    ///
    /// This is primarily used to avoid misclassifying patterns like `x' = x` as
    /// UNCHANGED when `x` is a bound/quantified variable shadowing the state var `x`.
    ///
    /// Part of #2955: Uses BindingChain lookup instead of local_stack scan.
    #[inline]
    pub fn has_local_binding(&self, name: &str) -> bool {
        if self.binding_depth == 0 {
            return false;
        }
        // Part of #188, #232: Use lookup_name_id (read lock) for O(1) comparison
        // If name not interned, it can't be in the binding chain
        match lookup_name_id(name) {
            Some(lookup_id) => self.bindings.lookup(lookup_id).is_some(),
            None => false,
        }
    }

    /// Returns true if no local bindings (EXISTS bounds, operator params) are on the stack.
    ///
    /// Part of #2955: Uses binding_depth instead of local_stack.is_empty().
    #[inline]
    pub fn local_stack_is_empty(&self) -> bool {
        self.binding_depth == 0
    }

    // ---- Operator lookup ----

    /// Look up an operator by name.
    /// Resolution order: let_def_overlay → local_ops → shared ops.
    /// Returns Arc reference for O(1) cloning (see #209)
    ///
    /// Part of #1093: let_def_overlay is checked first for cheap zero-arg LET
    /// defs that were pushed without cloning local_ops.
    #[inline]
    pub fn get_op(&self, name: &str) -> Option<&Arc<OperatorDef>> {
        // Part of #1093: Check lightweight overlay first (zero-arg LET defs)
        if let Some(def) = self.let_def_overlay.get(name) {
            return Some(def);
        }
        // Check local ops (for LET expressions with arity>0 defs)
        if let Some(ref local) = self.local_ops {
            if let Some(def) = local.get(name) {
                return Some(def);
            }
        }
        // Fall back to shared ops
        self.shared.ops.get(name)
    }

    /// Check if an operator is defined
    pub fn has_op(&self, name: &str) -> bool {
        if !self.let_def_overlay.is_empty() && self.let_def_overlay.get(name).is_some() {
            return true;
        }
        if let Some(ref local) = self.local_ops {
            if local.contains_key(name) {
                return true;
            }
        }
        self.shared.ops.contains_key(name)
    }

    /// Evaluate a named operator (with no arguments)
    pub fn eval_op(&self, name: &str) -> EvalResult<Value> {
        let def = self.get_op(name).ok_or_else(|| EvalError::UndefinedOp {
            name: name.to_string(),
            span: None,
        })?;

        // For a zero-argument operator, just evaluate its body
        if !def.params.is_empty() {
            return Err(EvalError::ArityMismatch {
                op: name.to_string(),
                expected: def.params.len(),
                got: 0,
                span: None,
            });
        }

        // Part of #250: Use eval_entry() for external entry point
        eval_entry(self, &def.body)
    }

    /// Evaluate a named operator with the given argument values.
    ///
    /// Used by trace invariants (Part of #3752) to call a one-argument operator
    /// with a pre-built `Seq(Record)` value. Delegates to the canonical
    /// `apply_user_op_with_values` path which handles parameter binding,
    /// caching, and body evaluation.
    pub fn eval_op_with_args(&self, name: &str, args: &[Value]) -> EvalResult<Value> {
        let def = self.get_op(name).ok_or_else(|| EvalError::UndefinedOp {
            name: name.to_string(),
            span: None,
        })?;
        let resolved_name = self.resolve_op_name(name);
        crate::apply_user_op_with_values(self, resolved_name, &def, args, None)
    }
}
