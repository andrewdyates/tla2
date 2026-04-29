// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure values for TLA+ higher-order LAMBDA expressions.
//!
//! `ClosureValue` stores LAMBDA parameters, body, captured environment, and
//! optional TIR body for native TIR-path evaluation. `TirBody` is the opaque
//! trait for bridging to TIR without a crate dependency. Extracted from
//! `lazy_func.rs` as part of #3309.

use super::lazy_func::{deterministic_id_from_span, CapturedChain};
use super::Value;
use std::sync::{Arc, OnceLock};
use tla_core::ast::Expr;
use tla_core::kani_types::HashMap;
use tla_core::Spanned;

/// Trait for opaque TIR body stored in closures.
///
/// Part of #3163: Bridges the tla-value → tla-tir crate boundary so that
/// `ClosureValue` can carry a lowered TIR body without depending on `tla-tir`.
/// Follows the same `CapturedChain` pattern: define trait in tla-value,
/// implement for concrete type in tla-eval (which has both deps).
/// At application time, `tla-eval` downcasts to `Spanned<TirExpr>` and
/// dispatches through `eval_tir` instead of AST `eval`.
pub trait TirBody: std::any::Any + Send + Sync {
    fn clone_box(&self) -> Box<dyn TirBody>;
    fn as_any(&self) -> &dyn std::any::Any;
}

impl Clone for Box<dyn TirBody> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

/// A closure value for higher-order operator arguments.
///
/// Closures are created from LAMBDA expressions passed to operators
/// that take operator parameters (e.g., `ChooseOne(S, P(_))`).
#[derive(Clone)]
pub struct ClosureValue {
    /// Unique identifier for this closure (for hashing/comparison)
    pub(crate) id: u64,
    /// Optional recursive self-binding name.
    ///
    /// Parameterized operators lowered to closures need the same self-binding
    /// contract as LazyFunc when their body recursively references the operator
    /// name. The evaluator pushes this name at application time.
    pub(crate) name: Option<Arc<str>>,
    /// Parameter names from the lambda
    pub(crate) params: Vec<String>,
    /// Lambda body expression
    pub(crate) body: Arc<Spanned<Expr>>,
    /// Captured environment at closure creation time.
    /// Part of #2955: Arc-wrapped for O(1) clone in build_closure_ctx.
    pub(crate) env: Arc<HashMap<Arc<str>, Value>>,
    /// Captured local operators at closure creation time (for LET bindings)
    /// Issue #174: Closures must capture local_ops to access operators from
    /// the enclosing LET scope (e.g., `LET S == {...} InS(y) == y \in S IN ...`)
    pub(crate) local_ops: Option<Arc<tla_core::OpEnv>>,
    /// Part of #2895/#2989: Opaque captured BindingChain from definition time.
    /// At application time, the evaluator restores this chain directly in O(1).
    /// Same pattern as LazyFuncValue::captured_chain.
    pub(crate) captured_chain: Option<Box<dyn CapturedChain>>,
    /// Part of #2895: The binding_depth at definition time (for correct dep tracking).
    pub(crate) captured_chain_depth: usize,
    /// Cached forced value for zero-arg closures (lazy LET thunks).
    /// Part of #607: TLC caches LazyValue results; we do the same via OnceLock.
    /// Arc ensures clones share the same cache.
    pub(crate) cached_value: Arc<OnceLock<Value>>,
    /// Part of #3163: Opaque TIR body for TIR-native closure evaluation.
    /// When present, `apply_closure_with_values` dispatches through `eval_tir`
    /// instead of AST `eval`, keeping the entire evaluation in the TIR path.
    /// `None` for closures created from AST evaluation (legacy path).
    pub(crate) tir_body: Option<Box<dyn TirBody>>,
    /// Part of #3697: Bytecode function index for compiled Lambda bodies.
    /// When present, the bytecode VM can execute the Lambda body via `Call`
    /// instead of falling back to the TIR tree-walker. The index refers to
    /// a function in the `BytecodeChunk` that was active during compilation.
    pub(crate) bytecode_func_idx: Option<u16>,
}

impl ClosureValue {
    /// Create a new closure with a deterministic span-based ID.
    ///
    /// FIX #1989: ID is derived from the body expression span so fingerprints
    /// are stable across runs and parallel workers.
    /// Part of #2955: env parameter is now Arc-wrapped for O(1) sharing.
    pub fn new(
        params: Vec<String>,
        body: Spanned<Expr>,
        env: Arc<HashMap<Arc<str>, Value>>,
        local_ops: Option<Arc<tla_core::OpEnv>>,
    ) -> Self {
        let id = deterministic_id_from_span(&body.span);
        ClosureValue {
            id,
            name: None,
            params,
            body: Arc::new(body),
            env,
            local_ops,
            captured_chain: None,
            captured_chain_depth: 0,
            cached_value: Arc::new(OnceLock::new()),
            tir_body: None,
            bytecode_func_idx: None,
        }
    }

    /// Stable unique identifier used in hashing/fingerprinting contracts.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Borrow the optional recursive self-binding name.
    pub fn name(&self) -> Option<&Arc<str>> {
        self.name.as_ref()
    }

    /// Borrow closure parameter names.
    pub fn params(&self) -> &[String] {
        &self.params
    }

    /// Borrow the closure body expression.
    pub fn body(&self) -> &Spanned<Expr> {
        self.body.as_ref()
    }

    /// Borrow the captured lexical environment.
    pub fn env(&self) -> &HashMap<Arc<str>, Value> {
        &self.env
    }

    /// Borrow the Arc-wrapped captured environment for O(1) sharing.
    /// Part of #2955: Used by `build_closure_ctx` to avoid HashMap clone.
    pub fn env_arc(&self) -> &Arc<HashMap<Arc<str>, Value>> {
        &self.env
    }

    /// Borrow captured local operators, if present.
    pub fn local_ops(&self) -> Option<&Arc<tla_core::OpEnv>> {
        self.local_ops.as_ref()
    }

    /// Return a cached thunk value if already forced.
    pub fn cached_value(&self) -> Option<Value> {
        self.cached_value.get().cloned()
    }

    /// Cache the forced value of a zero-arg thunk.
    ///
    /// If another thread raced and already stored a value, the existing cache
    /// entry is preserved.
    pub fn cache_value(&self, value: Value) {
        let _ = self.cached_value.set(value);
    }

    /// Borrow the captured chain, if present.
    /// Part of #2895: Used by `build_closure_ctx` to restore chain in O(1).
    pub fn captured_chain(&self) -> Option<&dyn CapturedChain> {
        self.captured_chain.as_deref()
    }

    /// The binding_depth at definition time.
    /// Part of #2895: Used to restore correct binding_depth in build_closure_ctx.
    pub fn captured_chain_depth(&self) -> usize {
        self.captured_chain_depth
    }

    /// Set the captured chain for O(1) restore at application time.
    /// Part of #2895: Builder-style setter — call after new() at creation sites
    /// that have access to the BindingChain (in tla-eval).
    pub fn with_captured_chain(mut self, chain: Box<dyn CapturedChain>, depth: usize) -> Self {
        self.captured_chain = Some(chain);
        self.captured_chain_depth = depth;
        self
    }

    /// Set the recursive self-binding name only when it is currently unset.
    pub fn with_name_if_missing(mut self, name: Arc<str>) -> Self {
        if self.name.is_none() {
            self.name = Some(name);
        }
        self
    }

    /// Replace the captured environment.
    /// Part of #3697: Used by the bytecode VM's `MakeClosure` opcode to inject
    /// captured register values into a template closure at runtime.
    pub fn with_env(mut self, env: Arc<HashMap<Arc<str>, Value>>) -> Self {
        self.env = env;
        self
    }

    /// Attach a TIR body for TIR-native closure evaluation.
    /// Part of #3163: Builder-style setter — call at TIR Lambda creation sites
    /// in tla-eval where both the AST body and TIR body are available.
    pub fn with_tir_body(mut self, tir_body: Box<dyn TirBody>) -> Self {
        self.tir_body = Some(tir_body);
        self
    }

    /// Borrow the TIR body, if present.
    /// Part of #3163: Used by `apply_closure_with_values` to dispatch through
    /// `eval_tir` instead of AST `eval` when the closure was created from TIR.
    pub fn tir_body(&self) -> Option<&dyn TirBody> {
        self.tir_body.as_deref()
    }

    /// Attach a compiled bytecode function index for VM-native Lambda execution.
    /// Part of #3697: When set, the bytecode VM executes the Lambda body via
    /// `Call` to this function index instead of falling back to the tree-walker.
    pub fn with_bytecode_func_idx(mut self, idx: u16) -> Self {
        self.bytecode_func_idx = Some(idx);
        self
    }

    /// Return the compiled bytecode function index, if the Lambda body was
    /// compiled to bytecode.
    /// Part of #3697: Used by the VM's `ValueApply` handler to dispatch to
    /// the compiled function instead of tree-walking the closure body.
    pub fn bytecode_func_idx(&self) -> Option<u16> {
        self.bytecode_func_idx
    }
}
