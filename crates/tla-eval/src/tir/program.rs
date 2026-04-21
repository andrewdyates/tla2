// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TirProgram` — lazy-lowering wrapper for TIR evaluation.
//!
//! Owns a `TirLoweringEnv` and caches lowered operators on demand so that the
//! checker hook does not need to eagerly lower entire modules.

use std::cell::RefCell;
use std::sync::Arc;
use rustc_hash::FxHashMap;
use tla_core::ast::{Expr, Module};
use tla_core::{Span, Spanned};
use tla_tir::TirExpr;
use tla_tir::{PreprocessPipeline, TirLoweringEnv, TirOperator};
use tla_value::error::EvalResult;

use super::bytecode_integration::{bytecode_vm_enabled, BytecodeCache};
use super::eval_tir;
use super::preprocess_enabled;
use super::probe::{record_expr_eval, record_named_op_eval, TirExprEvalAttempt};
use super::program_cache::CacheRef;
pub use super::program_cache::TirProgramCaches;
use crate::core::EvalCtx;
use crate::eval_cache_lifecycle::eval_entry_with;
use tla_value::Value;

mod lookup;

#[cfg(test)]
pub(super) use lookup::find_operator;

// Part of #3350: the blanket `expr_contains_unsound_binding_forms` guard has
// been removed. It was a conservative stopgap during #3288 that treated all
// FuncDef/SetFilter/SetBuilder expressions as unsafe and routed them to AST.
// The TIR evaluator now handles all three forms natively via
// `dispatch_bindings.rs`, and the medium-category #3288 closeout
// (reports/2026-03-17-3288-medium-tir-sweep-verification.md) confirmed zero
// remaining correctness regressions under TLA2_TIR_EVAL=all. The #3361 fix
// for TIR \E quantifier cache staleness was the last prerequisite.
//
// Lowering/eval failures still fall back to AST via:
// - `eval_named_op()`: catches lowering errors and eval errors
// - `try_eval_expr_detailed()`: returns Unsupported on lowering failure

/// A TIR program built from AST modules. Operators are lowered lazily on
/// first use and cached by name.
///
/// Also supports expression-level TIR evaluation via `try_eval_expr()`,
/// which lowers individual AST subexpressions on demand and caches by
/// source span (Part of #3194, #3276).
pub struct TirProgram<'a> {
    env: TirLoweringEnv<'a>,
    deps: Vec<&'a Module>,
    root: &'a Module,
    probe_labels: Vec<String>,
    pub(super) cache: CacheRef<'a, FxHashMap<String, TirOperator>>,
    /// Arc-wrapped operator bodies for O(1) clone on cache hit.
    /// Populated alongside `cache` by `get_or_lower`. Part of #4113.
    pub(super) op_body_arc_cache: CacheRef<'a, FxHashMap<String, Arc<Spanned<TirExpr>>>>,
    /// Cache for expression-level lowering: source span → lowered TIR.
    /// `Some(tir)` means lowering succeeded; `None` means lowering failed
    /// and this expression requires AST fallback.
    ///
    /// When constructed via `from_modules_with_cache`, this cache is shared
    /// across `TirProgram` instances (Part of #4113), avoiding redundant
    /// re-lowering of the same expressions across millions of BFS states.
    ///
    /// Keyed by source `Span` (file + byte range) instead of raw pointer so
    /// that temporary expression clones — which the enumerator creates in
    /// `SymbolicAssignment::Expr` and drops between OR branches — do not
    /// alias stale cache entries when the allocator reuses the same heap
    /// address.  Part of #3276 Root Cause B.
    expr_cache: CacheRef<'a, FxHashMap<Span, Option<Spanned<TirExpr>>>>,
    pub(super) bytecode_cache: CacheRef<'a, BytecodeCache>,
}

impl<'a> TirProgram<'a> {
    /// Build a program from a root module and its dependencies.
    #[must_use]
    pub fn from_modules(root: &'a Module, deps: &[&'a Module]) -> Self {
        let mut env = TirLoweringEnv::new(root);
        for dep in deps {
            env.add_module(dep);
        }
        Self {
            env,
            deps: deps.to_vec(),
            root,
            probe_labels: Vec::new(),
            cache: CacheRef::Owned(RefCell::new(FxHashMap::default())),
            op_body_arc_cache: CacheRef::Owned(RefCell::new(FxHashMap::default())),
            expr_cache: CacheRef::Owned(RefCell::new(FxHashMap::default())),
            bytecode_cache: CacheRef::Owned(RefCell::new(BytecodeCache::new())),
        }
    }

    /// Build a program that shares all caches with the caller.
    ///
    /// Lowered named operators and expression-level TIR lowering results
    /// accumulate across calls, avoiding redundant re-lowering when the same
    /// `TirProgram` structure is rebuilt per state during BFS.
    ///
    /// Expression lowering is now shared across program instances (Part of
    /// #4113). TIR lowering is a pure AST-to-TIR syntax transformation that
    /// depends only on source span and module context -- not runtime state.
    /// Sharing the expr_cache avoids re-lowering the same expressions millions
    /// of times during model checking. The init constraint quantifier path
    /// (which substitutes bound variables into the same Span) already calls
    /// `clear_expr_cache()` before each substitution iteration to prevent
    /// stale reuse.
    ///
    /// Part of #3392: per-run cache persistence for the sequential and parallel
    /// model-checker paths.
    #[must_use]
    pub fn from_modules_with_cache(
        root: &'a Module,
        deps: &[&'a Module],
        caches: &'a TirProgramCaches,
    ) -> Self {
        let mut env = TirLoweringEnv::new(root);
        for dep in deps {
            env.add_module(dep);
        }
        Self {
            env,
            deps: deps.to_vec(),
            root,
            probe_labels: Vec::new(),
            cache: CacheRef::Shared(&caches.op_cache),
            op_body_arc_cache: CacheRef::Shared(&caches.op_body_arc_cache),
            expr_cache: CacheRef::Shared(&caches.expr_cache),
            bytecode_cache: CacheRef::Shared(&caches.bytecode_cache),
        }
    }

    /// Clear the expression-level TIR lowering cache.
    ///
    /// Must be called between iterations when the same source-span expressions
    /// are substituted with different bound-variable values (e.g., during `\E`
    /// expansion in init constraint extraction). Without clearing, the cache
    /// returns stale TIR from a prior substitution because the key (source Span)
    /// is identical even though the AST content has changed.
    ///
    /// Part of #3361: TIR \E quantifier cache staleness fix.
    pub fn clear_expr_cache(&self) {
        self.expr_cache.borrow_mut().clear();
    }

    /// Attach a probe label so integration tests can attribute leaf-level TIR
    /// execution to a specific selected operator.
    #[must_use]
    pub fn with_probe_label(mut self, label: impl Into<String>) -> Self {
        self.probe_labels = vec![label.into()];
        self
    }

    /// Attach one or more probe labels so probes can be queried by either the
    /// raw config name or the resolved replacement name.
    #[must_use]
    pub fn with_probe_labels<I, S>(mut self, labels: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.probe_labels = labels.into_iter().map(Into::into).collect();
        self
    }

    /// Probe labels attached by `with_probe_label(s)`.
    #[must_use]
    #[doc(hidden)]
    pub fn probe_labels(&self) -> &[String] {
        &self.probe_labels
    }

    fn record_expr_probe_hits(&self) {
        for label in &self.probe_labels {
            record_expr_eval(label);
        }
    }

    /// Evaluate a named zero-arg operator through the TIR path.
    ///
    /// Lazily lowers the operator on first call, caches the result for
    /// subsequent invocations. Falls back to AST on lowering or eval errors.
    ///
    /// Part of #3350: the blanket `named_op_requires_ast_fallback` pre-check
    /// has been removed. FuncDef/SetFilter/SetBuilder operators are now
    /// attempted via TIR lowering like any other operator, with fallback to
    /// AST driven by actual lowering/eval failures instead of a pre-scan.
    ///
    /// Part of #3391: top-level TIR named-op evaluation runs under the same
    /// cache lifecycle boundary as `EvalCtx::eval_entry()`. The model checker
    /// can reach this path after compiled invariants, which do not call
    /// `eval_entry()`. Without the boundary, per-state caches leaked across
    /// successor states and produced a false `NoDataRaces` violation on
    /// Disruptor_MPMC.
    pub fn eval_named_op(&self, ctx: &EvalCtx, name: &str) -> EvalResult<Value> {
        // Part of #3264: Catch both lowering and eval errors — INSTANCE wrapper
        // modules may not have the operator directly (it's imported), so
        // get_or_lower can fail with "operator not found". Fall back to AST
        // which resolves INSTANCE imports correctly.
        let tir_body = match self.get_or_lower(name) {
            Ok(body) => body,
            Err(_) => return ctx.eval_op(name),
        };
        record_named_op_eval(name);

        // Part of #3583: try bytecode VM execution before tree-walking.
        if bytecode_vm_enabled() {
            match self.try_bytecode_eval(ctx, name, &tir_body) {
                Some(Ok(value)) => return Ok(value),
                Some(Err(e)) => return Err(e),
                None => {}
            }
        }

        // Part of #3392: install this program as the active TIR resolver so that
        // nested user-defined operator references stay in TIR instead of bouncing
        // back to AST through ctx.eval_op().
        let _guard = super::install_tir_program(self);
        // Part of #3276 Root Cause C: Use the caller's original ctx for both
        // TIR eval and AST fallback. The previous approach cloned ctx and called
        // load_modules() on the clone, which created a separate Rc<EvalCtxStable>
        // that lost state-array bindings set by the model checker's RAII guards
        // (bind_state_array_guard). The caller (model checker) already has modules
        // loaded on ctx, so the clone was redundant and actively broke AST fallback
        // when TIR eval failed on parameterized operators with unbound formals.
        let result = eval_entry_with(ctx, || eval_tir(ctx, &tir_body));
        // Part of #3264: Fall back to AST evaluation on any TIR eval error.
        // TIR lowering may inline operator bodies without properly handling
        // parameter bindings or produce type mismatches from incomplete
        // lowering. These are TIR expressiveness gaps — the AST evaluator
        // handles them correctly. If AST also fails, the AST error (which is
        // the canonical one) is returned.
        if result.is_err() {
            return ctx.eval_op(name);
        }
        // Part of #3352: record successful TIR expression evaluation for the
        // named operator. Without this, invariants evaluated via eval_named_op
        // show named_op_evals > 0 but expr_evals == 0, even though TIR evaluation
        // actually ran to completion. This lets callers distinguish "lowered but
        // eval failed (AST fallback)" from "lowered and eval succeeded (real TIR)".
        record_expr_eval(name);
        result
    }

    /// Try to evaluate an AST expression via TIR lowering + eval.
    ///
    /// Returns `Some(Ok(value))` when TIR lowering and evaluation both succeed.
    /// Returns `None` when the expression cannot be lowered to TIR or when the
    /// TIR evaluator reports an error (caller should fall back to AST `eval`).
    ///
    /// Caches lowering results by source `Span` so that temporary expression
    /// clones (created by the enumerator's `SymbolicAssignment::Expr`) do not
    /// alias stale cache entries when the allocator reuses heap addresses.
    ///
    /// Part of #3194, #3276: enables the successor enumerator to evaluate leaf
    /// subexpressions via TIR without rewriting the structural enumeration.
    pub fn try_eval_expr(&self, ctx: &EvalCtx, expr: &Spanned<Expr>) -> Option<EvalResult<Value>> {
        match self.try_eval_expr_detailed(ctx, expr) {
            TirExprEvalAttempt::Unsupported => None,
            TirExprEvalAttempt::Evaluated(Err(_)) => {
                // Part of #4113: do NOT mark the expression as AST-only when
                // TIR eval fails. With the shared expr_cache, overwriting the
                // cached `Some(tir)` lowering result with `None` would
                // permanently disable TIR for this span across all future
                // states, even though the lowering succeeded and eval may
                // succeed for other states with different runtime values.
                // The cached lowered TIR remains valid for re-evaluation.
                None
            }
            TirExprEvalAttempt::Evaluated(Ok(value)) => Some(Ok(value)),
        }
    }

    /// Try to evaluate an AST expression via TIR while preserving eval errors.
    ///
    /// This uses the same lowering cache as `try_eval_expr()`, but returns a
    /// detailed attempt result so callers can compare AST/TIR outcomes before
    /// deciding whether to keep the TIR result or fall back.
    #[doc(hidden)]
    pub fn try_eval_expr_detailed(
        &self,
        ctx: &EvalCtx,
        expr: &Spanned<Expr>,
    ) -> TirExprEvalAttempt {
        // Part of #3392: install this program as the active TIR resolver so that
        // nested user-defined operator references stay in TIR.
        let _guard = super::install_tir_program(self);
        // Part of #3350: the blanket expr_contains_unsound_binding_forms
        // pre-check has been removed. Lowering failures now naturally produce
        // Unsupported via the Err(_) branch below.
        //
        // Part of #3276 Root Cause B: key by source Span, not raw pointer.
        // The enumerator clones AST sub-expressions into SymbolicAssignment::Expr
        // and drops them when an OR branch completes.  The allocator may reuse
        // the same heap address for a different clone in the next branch, causing
        // a stale cache hit that returns the *wrong* lowered TIR.  Source spans
        // are stable across clones and unique per source-level expression.
        let key = expr.span;

        // Skip caching for dummy/generated spans to avoid collisions between
        // unrelated synthetic expressions that share Span::default().
        let cacheable = key != Span::dummy();

        // Check cache first
        if cacheable {
            if let Some(cached) = self.expr_cache.borrow().get(&key) {
                match cached.as_ref() {
                    Some(tir) => {
                        self.record_expr_probe_hits();
                        return TirExprEvalAttempt::Evaluated(eval_tir(ctx, tir));
                    }
                    None => return TirExprEvalAttempt::Unsupported,
                }
            }
        }

        // Try lowering, then apply preprocessing pipeline (NNF, keramelization,
        // constant folding) before evaluation and caching.
        match tla_tir::lower_expr_with_env(&self.env, self.root, expr) {
            Ok(tir) => {
                let tir = if preprocess_enabled() {
                    PreprocessPipeline::new().run(tir)
                } else {
                    tir
                };
                self.record_expr_probe_hits();
                let result = eval_tir(ctx, &tir);
                if cacheable {
                    self.expr_cache.borrow_mut().insert(key, Some(tir));
                }
                TirExprEvalAttempt::Evaluated(result)
            }
            Err(_) => {
                if cacheable {
                    self.expr_cache.borrow_mut().insert(key, None);
                }
                TirExprEvalAttempt::Unsupported
            }
        }
    }

    // try_bytecode_eval() extracted to bytecode_integration.rs (#3593)
}

#[cfg(test)]
#[path = "program_tests/mod.rs"]
mod tests;
