// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared parameter bundles and mutable state types for unified successor
//! enumeration.
//!
//! These types are threaded through all recursive calls of the unified
//! enumerator: `EnumParams` bundles immutable per-enumeration context,
//! `RecState` bundles the recursive-descent mutable state, and `EnumMut`
//! extends `RecState` with conjunct-processing fields.
//!
//! Extracted from unified.rs as part of #2360.

use std::ops::ControlFlow;
use std::rc::Rc;
use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::eval::EvalCtx;
use crate::eval::StackMark;
use crate::state::{ArrayState, DiffSuccessor, UndoEntry};
use crate::var_index::VarRegistry;
use crate::OpEnv;
use crate::Value;
use tla_core::VarIndex;

use super::SymbolicAssignment;

// ─── Successor output abstraction ────────────────────────────────────────────

/// Abstraction for successor output: either a Vec (batch) or a callback (streaming).
///
/// Part of #3027: enables streaming successor processing matching TLC's functor
/// pattern. The batch path uses `Vec<DiffSuccessor>` as the sink (preserving
/// existing behavior). The streaming path uses a `ClosureSink` callback that
/// processes each successor inline during enumeration, enabling early termination.
pub(crate) trait DiffSink {
    /// Push a successor to the sink.
    ///
    /// Returns `Continue(())` to keep enumerating, `Break(())` to stop early.
    fn push(&mut self, diff: DiffSuccessor) -> ControlFlow<()>;

    /// Push a successor with access to the active evaluation context.
    ///
    /// Most sinks do not need `EvalCtx`, so the default implementation
    /// preserves the legacy `push(diff)` behavior. Context-aware sinks can
    /// override this to process successors inline while enumeration still owns
    /// the current `EvalCtx`.
    fn push_with_ctx(&mut self, _ctx: &mut EvalCtx, diff: DiffSuccessor) -> ControlFlow<()> {
        self.push(diff)
    }

    /// Number of successors pushed so far. Used for ENABLED early-exit checks
    /// and debug logging.
    fn count(&self) -> usize;

    /// Whether any successors have been pushed.
    fn has_results(&self) -> bool {
        self.count() > 0
    }

    /// Whether the sink has signaled early termination (Break from push).
    ///
    /// Checked by the enumeration recursion to short-circuit remaining
    /// conjuncts, branches, and quantifier iterations. Default: false
    /// (Vec never stops).
    fn is_stopped(&self) -> bool {
        false
    }
}

/// Batch sink: collects into a Vec. This is the default, preserving existing behavior.
impl DiffSink for Vec<DiffSuccessor> {
    #[inline]
    fn push(&mut self, diff: DiffSuccessor) -> ControlFlow<()> {
        Vec::push(self, diff);
        ControlFlow::Continue(())
    }

    #[inline]
    fn count(&self) -> usize {
        self.len()
    }
}

/// Streaming sink: wraps a closure for per-successor inline processing.
///
/// Part of #3027 Phase 2: This is the TLC `INextStateFunctor` equivalent.
/// Each successor is processed immediately when generated (fingerprint, dedup,
/// invariant check, enqueue) via the callback, rather than being collected into
/// a Vec for batch processing.
///
/// The callback returns `ControlFlow::Break(())` to signal early termination
/// (e.g., on invariant violation), which propagates back through the
/// enumeration recursion via `is_stopped()` checks.
pub(crate) struct ClosureSink<F> {
    callback: F,
    count: usize,
    stopped: bool,
}

impl<F> ClosureSink<F>
where
    F: FnMut(DiffSuccessor) -> ControlFlow<()>,
{
    pub fn new(callback: F) -> Self {
        Self {
            callback,
            count: 0,
            stopped: false,
        }
    }
}

impl<F> DiffSink for ClosureSink<F>
where
    F: FnMut(DiffSuccessor) -> ControlFlow<()>,
{
    #[inline]
    fn push(&mut self, diff: DiffSuccessor) -> ControlFlow<()> {
        if self.stopped {
            return ControlFlow::Break(());
        }
        self.count += 1;
        let result = (self.callback)(diff);
        if result.is_break() {
            self.stopped = true;
        }
        result
    }

    #[inline]
    fn count(&self) -> usize {
        self.count
    }

    #[inline]
    fn is_stopped(&self) -> bool {
        self.stopped
    }
}

// ─── Shared parameter bundles ────────────────────────────────────────────────

/// PlusCal `pc`-based guard hoisting for Or-branch pruning (Part of #3923).
///
/// When a spec follows the PlusCal pattern (`Next == A \/ B \/ C` where each
/// action is guarded by `pc = "label"`), this struct enables the unified
/// enumerator to skip Or branches whose pc guard cannot match the current state.
///
/// The optimization reads `pc` once from the base state and compares it against
/// the guard literal extracted from each Or branch's first conjunct. Branches
/// with a non-matching guard are skipped entirely, avoiding the cost of cloning
/// EvalCtx, resolving operators, and evaluating guards that are guaranteed FALSE.
///
/// Soundness: an Or branch with `pc = "x"` as its first conjunct produces zero
/// successors when `pc != "x"` in the current state. Skipping it changes nothing.
pub(super) struct PcGuardHoist {
    /// The VarIndex of `pc` in the state array.
    #[allow(dead_code)]
    pub pc_var_idx: VarIndex,
    /// The current value of `pc` (read once from the base state at enumeration start).
    pub current_pc: Value,
}

/// Immutable per-enumeration parameters shared across all recursive calls.
///
/// Bundles the parameters that are passed unchanged through every level of
/// the enumeration recursion.
pub(super) struct EnumParams<'a> {
    pub vars: &'a [Arc<str>],
    pub registry: &'a VarRegistry,
    pub base_with_fp: &'a ArrayState,
    pub full_mask: u64,
    /// Optional TIR leaf evaluator for successor generation.
    ///
    /// When `Some`, leaf `eval(ctx, expr)` calls in the unified enumerator
    /// try TIR lowering + evaluation first, falling back to AST `eval` when
    /// the expression cannot be lowered. When `None`, AST `eval` is used
    /// unconditionally (default behavior).
    ///
    /// Part of #3194: moves TIR from invariant-only to the BFS `Next` path.
    pub tir_leaf: Option<&'a tla_eval::tir::TirProgram<'a>>,
    /// PlusCal pc-guard hoisting for Or-branch pruning (Part of #3923).
    ///
    /// When set, Or branches whose first conjunct is `pc = "label"` with a
    /// non-matching label are skipped entirely. This avoids evaluating actions
    /// that are guaranteed to produce zero successors.
    pub pc_guard_hoist: Option<PcGuardHoist>,
}

impl<'a> EnumParams<'a> {
    pub fn new(
        vars: &'a [Arc<str>],
        registry: &'a VarRegistry,
        base_with_fp: &'a ArrayState,
    ) -> Self {
        let num_vars = vars.len();
        let full_mask: u64 = if num_vars > 0 && num_vars < 64 {
            (1u64 << num_vars) - 1
        } else if num_vars == 64 {
            u64::MAX
        } else {
            0 // Disable optimization for 0 or >64 vars
        };
        Self {
            vars,
            registry,
            base_with_fp,
            full_mask,
            tir_leaf: None,
            pc_guard_hoist: None,
        }
    }

    pub fn with_tir_leaf(mut self, tir: Option<&'a tla_eval::tir::TirProgram<'a>>) -> Self {
        self.tir_leaf = tir;
        self
    }

    /// Enable PlusCal pc-guard hoisting for this enumeration.
    ///
    /// Reads the current `pc` value from the base state and stores it
    /// for fast guard comparison during Or-branch dispatch.
    pub fn with_pc_guard_hoist(mut self, pc_var_idx: VarIndex) -> Self {
        let current_pc = self.base_with_fp.get(pc_var_idx);
        self.pc_guard_hoist = Some(PcGuardHoist {
            pc_var_idx,
            current_pc,
        });
        self
    }
}

/// Continuation state: which conjuncts remain and where to resume.
pub(super) struct Cont<'a> {
    pub(super) conjuncts: &'a [&'a Spanned<Expr>],
    pub(super) next_idx: usize,
    /// When set, the base case pops LET/apply bindings and continues with the
    /// parent continuation instead of emitting a successor. This isolates
    /// LET-defined names from leaking into outer continuation conjuncts.
    /// See `conjunct_let` doc comment for the full explanation (fix #804).
    pub(super) scope_restore: Option<Rc<ScopeRestore<'a>>>,
}

/// Saved scope state for restoring after LET/apply body processing.
///
/// When `conjunct_let` or `conjunct_apply` creates an inner `Cont` with a
/// `ScopeRestore`, the base case of `enumerate_conjuncts` will:
/// 1. Pop bindings to `binding_mark`
/// 2. Restore `local_ops` and `skip_prime_validation`
/// 3. Continue enumeration with the parent `Cont`
///
/// Uses `Rc` for parent links instead of `Box` to enable O(1) structural
/// sharing (matching TLC's `Context.cons()`). The restore chain is immutable
/// once created — new scope frames share the parent pointer instead of
/// deep-cloning the entire chain. Part of #3121.
#[allow(clippy::struct_field_names)]
pub(super) struct ScopeRestore<'a> {
    pub(super) parent_conjuncts: &'a [&'a Spanned<Expr>],
    pub(super) parent_next_idx: usize,
    pub(super) parent_scope_restore: Option<Rc<ScopeRestore<'a>>>,
    pub(super) binding_mark: StackMark,
    pub(super) saved_local_ops: Option<Arc<OpEnv>>,
    pub(super) saved_skip_prime: bool,
}

impl<'a> ScopeRestore<'a> {
    /// Reconstruct the parent continuation from this restore point.
    ///
    /// Used by both the normal base case (`enumerate_conjuncts`) and the
    /// allAssigned fast path to avoid duplicating parent Cont assembly.
    /// Part of #3121 Step 2.
    pub(super) fn restored_parent_cont(&self) -> Cont<'a> {
        Cont {
            conjuncts: self.parent_conjuncts,
            next_idx: self.parent_next_idx,
            scope_restore: self.parent_scope_restore.clone(),
        }
    }
}

/// Mutable recursive-descent state threaded through `enumerate_unified_inner`.
///
/// Bundles the 3 heap-allocated mutable collections that every recursive call
/// needs: the scratchpad working state, its undo stack, and the output sink.
/// EvalCtx stays separate because the borrow checker requires independent
/// borrows for ctx vs working/undo.
///
/// Part of #3027: `results` is `&mut dyn DiffSink` instead of
/// `&mut Vec<DiffSuccessor>`, enabling both batch (Vec) and streaming
/// (callback) successor processing.
pub(super) struct RecState<'a> {
    pub working: &'a mut ArrayState,
    pub undo: &'a mut Vec<UndoEntry>,
    pub results: &'a mut dyn DiffSink,
}

/// Mutable per-enumeration state threaded through conjunct processing.
///
/// Extends `RecState` with 3 additional fields for continuation-based conjunct
/// enumeration: symbolic assignment accumulation, the assigned-variable bitmask,
/// and a flag for complex (non-assignment) conjuncts. EvalCtx stays separate
/// because the borrow checker requires independent borrows for ctx vs
/// working/undo.
pub(super) struct EnumMut<'a> {
    pub rec: RecState<'a>,
    pub accumulated: &'a mut Vec<SymbolicAssignment>,
    /// Bitmask of which state variables have been assigned so far.
    pub assigned_mask: u64,
    /// Whether we've encountered complex (non-assignment) conjuncts.
    pub has_complex: bool,
}
