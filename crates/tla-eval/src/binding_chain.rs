// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unified binding chain for name resolution — TLC `Context.java` parity (#2364).
//!
//! Replaces the 6-tier identifier lookup in `eval_ident` with a single immutable
//! persistent linked list. All name bindings (INSTANCE substitutions, LET locals,
//! quantifier variables, operator parameters) live in one chain. Lookup walks
//! the chain using [`NameId`] integer equality. Creation prepends one node.
//! "Cloning" is `Arc::clone` of the head pointer.
//!
//! # Arena Dual-Path (#3580 Slice 2)
//!
//! When the thread-local `EvalArena` is active (during BFS successor generation),
//! `cons()` / `cons_local()` / `cons_liveness_local()` allocate nodes from the
//! arena instead of via `Arc`. Arena nodes sit on top of the heap chain:
//! lookup walks arena nodes first, then heap nodes. This saves 16B Arc header +
//! atomic refcount operations per node on the hot path.
//!
//! INSTANCE and Lazy bindings always go to the heap path (they carry heap data
//! that needs proper Drop). When a closure captures a chain, `promote_to_heap()`
//! copies arena nodes to heap so they survive beyond the BFS state boundary.
//!
//! # TLC Reference
//!
//! - `Context.java:34-52` — immutable linked list: `SymbolNode name`, `Object value`, `Context next`
//! - `Context.java:66-68` — `cons()`: allocates one node, returns new head
//! - `Context.java:74-90` — `lookup()`: walks chain with identity comparison

use std::sync::Arc;

use super::OpEvalDeps;
use tla_core::name_intern::NameId;
use tla_value::CompactValue;

mod arena;
mod construction;
mod lazy;
mod lookup;
mod mutation;
use arena::ArenaChainNode;
pub use lazy::BindingValue;
pub(crate) use lazy::LazyBinding;

/// Immutable persistent binding chain — TLC `Context` parity.
///
/// All name bindings (INSTANCE substitutions, LET locals, quantifier
/// variables, operator parameters) live in a single chain. Lookup walks
/// the chain using NameId integer equality. Creation prepends one node.
///
/// # Dual-Path Storage (#3580)
///
/// `arena_head` points to arena-allocated nodes (bump-allocated, no refcount).
/// `heap_head` points to heap-allocated nodes (Arc-wrapped, refcounted).
/// Arena nodes are always newer than heap nodes. Lookup walks arena first,
/// then heap. Clone copies the arena pointer (valid within same BFS state)
/// and Arc-clones the heap head.
///
/// Uses `Arc` (not `Rc`) for Send+Sync (#2955). Made `pub` for liveness
/// subsystem access (#2895).
pub struct BindingChain {
    /// Arena-allocated nodes (newest bindings). Null when no arena bindings.
    /// Valid only within the current BFS state.
    arena_head: *const ArenaChainNode,
    /// Heap-allocated nodes (older bindings). Arc-refcounted.
    heap_head: Option<Arc<BindingNode>>,
}

// SAFETY: BindingChain's arena_head points to thread-local arena memory.
// It is only accessed from the owning thread. The heap_head is Arc (Send+Sync).
// CapturedChain requires Send+Sync; arena chains are promoted to heap before
// escaping the BFS state boundary.
unsafe impl Send for BindingChain {}
unsafe impl Sync for BindingChain {}

impl Clone for BindingChain {
    fn clone(&self) -> Self {
        BindingChain {
            arena_head: self.arena_head,
            heap_head: self.heap_head.clone(),
        }
    }
}

struct BindingNode {
    name: NameId,
    value: BindingValue,
    source: BindingSource,
    next: Option<Arc<BindingNode>>,
}

/// Source-specific metadata attached to each binding in the chain.
///
/// Discriminates how dependency tracking should handle a binding found during lookup.
#[derive(Clone)]
#[allow(private_interfaces)] // OpEvalDeps is pub(crate); external callers use None variant only
pub enum BindingSource {
    /// No dependency info (e.g., test-only bindings, simple cons).
    None,
    /// INSTANCE substitution: carries pre-computed deps for cache correctness.
    /// `propagate_cached_deps` must be called when this binding is used.
    /// Part of #3063: Boxed to reduce BindingSource from ~80B to ~16B.
    Instance(Box<OpEvalDeps>),
    /// Local binding (LET/quantifier): carries the `local_stack` index at the
    /// time of binding.
    Local(usize),
    /// Liveness replay binding: local-like for `Ident`, but distinct so
    /// `Expr::StateVar` can ignore only replayed liveness bindings.
    Liveness(usize),
}

/// Borrowed view of a binding value returned by lookup/iteration.
#[allow(private_interfaces)]
#[derive(Clone, Copy)]
pub enum BindingValueRef<'a> {
    Eager(&'a CompactValue),
    Lazy(&'a LazyBinding),
}

/// Borrowed view of binding metadata returned by lookup/iteration.
#[allow(private_interfaces)]
#[derive(Clone, Copy)]
pub enum BindingSourceRef<'a> {
    None,
    Instance(&'a OpEvalDeps),
    Local(usize),
    Liveness(usize),
}

impl<'a> From<&'a BindingValue> for BindingValueRef<'a> {
    fn from(value: &'a BindingValue) -> Self {
        match value {
            BindingValue::Eager(value) => Self::Eager(value),
            BindingValue::Lazy(lazy) => Self::Lazy(lazy.as_ref()),
        }
    }
}

impl<'a> From<&'a BindingSource> for BindingSourceRef<'a> {
    fn from(source: &'a BindingSource) -> Self {
        match source {
            BindingSource::None => Self::None,
            BindingSource::Instance(deps) => Self::Instance(deps.as_ref()),
            BindingSource::Local(depth) => Self::Local(*depth),
            BindingSource::Liveness(depth) => Self::Liveness(*depth),
        }
    }
}

impl BindingSourceRef<'_> {
    pub(crate) fn to_owned(self) -> BindingSource {
        match self {
            BindingSourceRef::None => BindingSource::None,
            BindingSourceRef::Instance(deps) => BindingSource::Instance(Box::new(deps.clone())),
            BindingSourceRef::Local(depth) => BindingSource::Local(depth),
            BindingSourceRef::Liveness(depth) => BindingSource::Liveness(depth),
        }
    }
}

impl Default for BindingChain {
    fn default() -> Self {
        Self::empty()
    }
}

impl std::fmt::Debug for BindingChain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut entries = Vec::new();
        for (name_id, value, _source) in self.iter() {
            let kind = match value {
                BindingValueRef::Eager(_) => "eager",
                BindingValueRef::Lazy(_) => "lazy",
            };
            entries.push(format!("({:?}, {})", name_id, kind));
        }
        write!(f, "BindingChain[{}]", entries.join(" -> "))
    }
}

/// Part of #3580: `clone_box` promotes arena nodes to heap before cloning,
/// ensuring the captured chain survives beyond the BFS state boundary.
impl tla_value::CapturedChain for BindingChain {
    fn clone_box(&self) -> Box<dyn tla_value::CapturedChain> {
        Box::new(self.promote_all_to_heap())
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn materialize_locals(
        &self,
        env: &mut tla_core::kani_types::HashMap<std::sync::Arc<str>, tla_value::Value>,
    ) {
        self.write_locals_to_env(env);
    }
}

#[cfg(test)]
mod tests;
