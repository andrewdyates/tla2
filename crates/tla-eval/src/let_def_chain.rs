// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lightweight overlay chain for zero-arg LET operator definitions.
//!
//! Part of #1093: TLC uses `Context.cons(...)` for zero-arg LET defs — one
//! cons-cell per binding, no HashMap clone. TLA2 previously cloned the entire
//! `OpEnv` HashMap for ANY LET containing recursive FuncDefs or InstanceExprs.
//!
//! This module provides a persistent cons-list overlay that `get_op()` checks
//! before `local_ops`, matching TLC's cheap context extension model.
//!
//! # TLC Reference
//!
//! - `Tool.java:1848-1859` — `Context.cons(...)` for zero-arg LET defs
//! - `FcnLambdaValue.java:91-95` — self-binding for recursive functions

use std::sync::Arc;
use tla_core::ast::OperatorDef;
use tla_core::name_intern::{intern_name, NameId};

/// Persistent cons-list of operator definitions for zero-arg LET defs.
///
/// Each node holds one operator definition and a tail pointer.
/// "Cloning" is `Arc::clone` of the head — O(1).
/// Lookup walks the chain comparing names — O(n) in chain length,
/// but LET blocks rarely have more than 5-10 defs.
///
/// Part of #3961: Each node stores a pre-computed NameId for O(1) integer
/// comparison in `get_by_id()`, avoiding string comparison on the hot path.
#[derive(Clone)]
pub(crate) struct LetDefOverlay {
    head: Option<Arc<LetDefNode>>,
}

struct LetDefNode {
    name: Arc<str>,
    /// Pre-interned NameId for integer comparison in `get_by_id()`.
    /// Part of #3961: stored at construction time to avoid re-interning on lookup.
    name_id: NameId,
    def: Arc<OperatorDef>,
    next: Option<Arc<LetDefNode>>,
}

impl LetDefOverlay {
    /// Create an empty overlay (no definitions).
    #[inline]
    pub(crate) fn empty() -> Self {
        LetDefOverlay { head: None }
    }

    /// Prepend one operator definition to the chain — O(1).
    ///
    /// Part of #3961: Interns the name at construction time to store a NameId,
    /// enabling integer comparison in `get_by_id()` instead of string comparison.
    /// `intern_name`'s fast path is a read lock that finds existing entries.
    #[inline]
    pub(crate) fn cons(self, name: Arc<str>, def: Arc<OperatorDef>) -> Self {
        let name_id = intern_name(&name);
        LetDefOverlay {
            head: Some(Arc::new(LetDefNode {
                name,
                name_id,
                def,
                next: self.head,
            })),
        }
    }

    /// Look up an operator definition by name — O(chain length).
    #[inline]
    pub(crate) fn get(&self, name: &str) -> Option<&Arc<OperatorDef>> {
        let mut node = self.head.as_ref();
        while let Some(n) = node {
            if n.name.as_ref() == name {
                return Some(&n.def);
            }
            node = n.next.as_ref();
        }
        None
    }

    /// Look up an operator definition by NameId — O(chain length) with integer comparison.
    ///
    /// Part of #3961: Uses pre-stored NameId for O(1) per-node comparison instead
    /// of string comparison. Called from `check_dynamic_overlays` on the eval_ident
    /// hot path.
    #[inline]
    pub(crate) fn get_by_id(&self, target: NameId) -> Option<&Arc<OperatorDef>> {
        let mut node = self.head.as_ref();
        while let Some(n) = node {
            if n.name_id == target {
                return Some(&n.def);
            }
            node = n.next.as_ref();
        }
        None
    }

    /// Returns true if the overlay is empty (no definitions).
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.head.is_none()
    }
}

impl std::fmt::Debug for LetDefOverlay {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        let mut node = self.head.as_ref();
        while let Some(n) = node {
            list.entry(&n.name.as_ref());
            node = n.next.as_ref();
        }
        list.finish()
    }
}
