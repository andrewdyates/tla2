// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Persistent caches for `TirProgram` that survive across per-state program
//! instances within a model-checking run.

use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::sync::Arc;
use tla_core::Span;
use tla_tir::{TirExpr, TirOperator};

use super::bytecode_integration::BytecodeCache;
use tla_core::Spanned;

/// Persistent caches for `TirProgram` that survive across per-state program
/// instances within a model-checking run.
///
/// Part of #3392: callers hold this struct and pass it to
/// `TirProgram::from_modules_with_cache` so that named-operator lowering
/// and expression-level lowering work can accumulate across states instead
/// of being discarded each time.
///
/// Part of #4113: expression lowering is now shared across program instances.
/// TIR lowering is a pure AST-to-TIR syntax transformation that depends only
/// on source span and module context, not runtime state. The init constraint
/// quantifier path calls `clear_expr_cache()` before each substitution
/// iteration to handle the special case where the same Span maps to different
/// AST content.
pub struct TirProgramCaches {
    pub(super) op_cache: RefCell<FxHashMap<String, TirOperator>>,
    /// Arc-wrapped operator bodies for O(1) clone on cache hit.
    /// Populated alongside `op_cache` by `get_or_lower`.
    /// Part of #4113.
    pub(super) op_body_arc_cache: RefCell<FxHashMap<String, Arc<Spanned<TirExpr>>>>,
    pub(super) expr_cache: RefCell<FxHashMap<Span, Option<Spanned<TirExpr>>>>,
    pub(super) bytecode_cache: RefCell<BytecodeCache>,
}

impl TirProgramCaches {
    /// Create empty caches.
    #[must_use]
    pub fn new() -> Self {
        Self {
            op_cache: RefCell::new(FxHashMap::default()),
            op_body_arc_cache: RefCell::new(FxHashMap::default()),
            expr_cache: RefCell::new(FxHashMap::default()),
            bytecode_cache: RefCell::new(BytecodeCache::new()),
        }
    }

    /// Reset all caches for a new model-checking run.
    pub fn clear(&self) {
        self.op_cache.borrow_mut().clear();
        self.op_body_arc_cache.borrow_mut().clear();
        self.expr_cache.borrow_mut().clear();
        self.bytecode_cache.borrow_mut().clear();
    }
}

impl Default for TirProgramCaches {
    fn default() -> Self {
        Self::new()
    }
}

/// Cache reference: owned for transient programs, shared for per-run persistence.
///
/// Part of #3392: allows `TirProgram` to hold either local caches (dropped when
/// the program is dropped) or shared caches that accumulate across states within
/// a model-checking run. The two variants expose identical `borrow`/`borrow_mut`
/// semantics so cache-access sites require no changes.
pub(super) enum CacheRef<'a, T> {
    /// Transient: cache lives and dies with this `TirProgram` instance.
    Owned(RefCell<T>),
    /// Shared: cache outlives this `TirProgram`, accumulates across states.
    Shared(&'a RefCell<T>),
}

impl<T> CacheRef<'_, T> {
    pub(super) fn borrow(&self) -> std::cell::Ref<'_, T> {
        match self {
            Self::Owned(rc) => rc.borrow(),
            Self::Shared(rc) => rc.borrow(),
        }
    }

    pub(super) fn borrow_mut(&self) -> std::cell::RefMut<'_, T> {
        match self {
            Self::Owned(rc) => rc.borrow_mut(),
            Self::Shared(rc) => rc.borrow_mut(),
        }
    }
}
