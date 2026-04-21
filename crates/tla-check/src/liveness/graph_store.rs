// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Behavior graph topology storage backends.
//!
//! Part of #2732: this module keeps liveness graph topology storage separate
//! from concrete-state caching. The default backend remains an in-memory
//! `FxHashMap`, but Slice E also needs a runtime-selectable disk backend that
//! persists node records and exposes explicit update operations instead of
//! long-lived `&mut NodeInfo` borrows.

use crate::error::{EvalError, EvalResult};
use crate::liveness::behavior_graph::{BehaviorGraphNode, NodeInfo};
use crate::liveness::checker::CheckMask;
use crate::liveness::debug::liveness_inmemory_node_limit;
use crate::liveness::storage::disk_graph::DiskGraphStore;
use crate::state::Fingerprint;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::fmt::Display;
use std::ops::Deref;
use tempfile::TempDir;

/// Invariant violation error for graph store operations.
pub(crate) fn invariant_error(message: String) -> EvalError {
    EvalError::Internal {
        message: format!("behavior graph invariant violated: {message}"),
        span: None,
    }
}

/// Read-only node info access that can be borrowed (in-memory) or owned (disk).
#[derive(Clone)]
pub(crate) enum NodeInfoView<'a> {
    Borrowed(&'a NodeInfo),
    Owned(NodeInfo),
}

impl NodeInfoView<'_> {
    /// Convert to an owned `NodeInfo`, cloning if borrowed.
    #[cfg(test)]
    pub(crate) fn into_owned(self) -> NodeInfo {
        match self {
            Self::Borrowed(info) => info.clone(),
            Self::Owned(info) => info,
        }
    }
}

impl Deref for NodeInfoView<'_> {
    type Target = NodeInfo;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Borrowed(info) => info,
            Self::Owned(info) => info,
        }
    }
}

/// In-memory behavior graph topology store backed by `FxHashMap`.
///
/// This is the current (pre-disk) implementation. The hash map stores one
/// [`NodeInfo`] per `(state_fp, tableau_idx)` pair with successor lists, parent
/// pointers, BFS depth, and precomputed check bitmasks.
#[derive(Debug, Clone)]
pub(crate) struct InMemoryGraphStore {
    pub(crate) nodes: FxHashMap<BehaviorGraphNode, NodeInfo>,
    pub(crate) init_nodes_list: Vec<BehaviorGraphNode>,
    node_limit: Option<usize>,
}

impl InMemoryGraphStore {
    pub(crate) fn new() -> Self {
        Self {
            nodes: FxHashMap::default(),
            init_nodes_list: Vec::new(),
            node_limit: liveness_inmemory_node_limit(),
        }
    }

    fn ensure_capacity_for_new_node(&self, node: BehaviorGraphNode) -> EvalResult<()> {
        if let Some(limit) = self.node_limit {
            if self.nodes.len() >= limit {
                return Err(EvalError::Internal {
                    message: format!(
                        "in-memory liveness graph node limit exceeded: limit={limit}, attempted node {node}; enable disk-backed liveness graph or raise TLA2_LIVENESS_INMEMORY_NODE_LIMIT"
                    ),
                    span: None,
                });
            }
        }
        Ok(())
    }
}

impl Default for InMemoryGraphStore {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
enum GraphStoreBackend {
    InMemory(InMemoryGraphStore),
    Disk {
        store: RefCell<DiskGraphStore>,
        _backing_dir: TempDir,
    },
}

/// Runtime-selectable topology store used by [`super::behavior_graph::BehaviorGraph`].
#[derive(Debug)]
pub(crate) struct RuntimeGraphStore {
    backend: GraphStoreBackend,
}

impl RuntimeGraphStore {
    pub(crate) fn new_in_memory() -> Self {
        Self {
            backend: GraphStoreBackend::InMemory(InMemoryGraphStore::new()),
        }
    }

    pub(crate) fn new_disk_backed(ptr_table_capacity: usize) -> EvalResult<Self> {
        let backing_dir = TempDir::new().map_err(|error| {
            invariant_error(format!(
                "create disk-backed liveness graph tempdir: {error}"
            ))
        })?;
        let store = DiskGraphStore::with_capacity(backing_dir.path(), ptr_table_capacity).map_err(
            |error| {
                invariant_error(format!(
                    "create disk-backed liveness graph store in {}: {error}",
                    backing_dir.path().display()
                ))
            },
        )?;
        Ok(Self {
            backend: GraphStoreBackend::Disk {
                store: RefCell::new(store),
                _backing_dir: backing_dir,
            },
        })
    }

    fn map_disk_error(context: &str, error: impl Display) -> EvalError {
        invariant_error(format!("{context}: {error}"))
    }

    #[cfg(test)]
    pub(crate) fn contains(&self, node: BehaviorGraphNode) -> bool {
        match &self.backend {
            GraphStoreBackend::InMemory(store) => store.nodes.contains_key(&node),
            GraphStoreBackend::Disk { store, .. } => store.borrow().contains(node),
        }
    }

    #[cfg(test)]
    pub(crate) fn is_disk_backed(&self) -> bool {
        matches!(self.backend, GraphStoreBackend::Disk { .. })
    }

    pub(crate) fn add_init_node(&mut self, node: BehaviorGraphNode) -> EvalResult<bool> {
        match &mut self.backend {
            GraphStoreBackend::InMemory(store) => {
                if store.nodes.contains_key(&node) {
                    return Ok(false);
                }
                store.ensure_capacity_for_new_node(node)?;
                store.init_nodes_list.push(node);
                store.nodes.insert(
                    node,
                    NodeInfo {
                        successors: Vec::new(),
                        parent: None,
                        depth: 0,
                        state_check_mask: CheckMask::new(),
                        action_check_masks: Vec::new(),
                    },
                );
                Ok(true)
            }
            GraphStoreBackend::Disk { store, .. } => {
                let mut store = store.borrow_mut();
                if store.contains(node) {
                    return Ok(false);
                }
                let info = NodeInfo {
                    successors: Vec::new(),
                    parent: None,
                    depth: 0,
                    state_check_mask: CheckMask::new(),
                    action_check_masks: Vec::new(),
                };
                store
                    .append_node(node, &info)
                    .map_err(|error| Self::map_disk_error("append initial liveness node", error))?;
                store.mark_init_node(node);
                Ok(true)
            }
        }
    }

    pub(crate) fn add_successor(
        &mut self,
        from: BehaviorGraphNode,
        to: BehaviorGraphNode,
    ) -> EvalResult<bool> {
        match &mut self.backend {
            GraphStoreBackend::InMemory(store) => {
                let from_depth = {
                    let from_info = store.nodes.get_mut(&from).ok_or_else(|| {
                        invariant_error(format!(
                            "cannot add successor edge from {from} to {to}: source node is missing"
                        ))
                    })?;
                    from_info.successors.push(to);
                    from_info.depth
                };
                if store.nodes.contains_key(&to) {
                    return Ok(false);
                }
                store.ensure_capacity_for_new_node(to)?;
                store.nodes.insert(
                    to,
                    NodeInfo {
                        successors: Vec::new(),
                        parent: Some(from),
                        depth: from_depth + 1,
                        state_check_mask: CheckMask::new(),
                        action_check_masks: Vec::new(),
                    },
                );
                Ok(true)
            }
            GraphStoreBackend::Disk { store, .. } => {
                let mut store = store.borrow_mut();
                let mut from_info = store
                    .read_node(from)
                    .map_err(|error| Self::map_disk_error("read source liveness node", error))?
                    .ok_or_else(|| {
                        invariant_error(format!(
                            "cannot add successor edge from {from} to {to}: source node is missing"
                        ))
                    })?;
                let from_depth = from_info.depth;
                from_info.successors.push(to);
                if !store.contains(to) {
                    let to_info = NodeInfo {
                        successors: Vec::new(),
                        parent: Some(from),
                        depth: from_depth + 1,
                        state_check_mask: CheckMask::new(),
                        action_check_masks: Vec::new(),
                    };
                    store.append_node(to, &to_info).map_err(|error| {
                        Self::map_disk_error("append successor liveness node", error)
                    })?;
                    store.update_node(from, &from_info).map_err(|error| {
                        Self::map_disk_error("persist updated source liveness node", error)
                    })?;
                    return Ok(true);
                }
                store.update_node(from, &from_info).map_err(|error| {
                    Self::map_disk_error("persist updated source liveness node", error)
                })?;
                Ok(false)
            }
        }
    }

    pub(crate) fn get_node_info<'a>(
        &'a self,
        node: &BehaviorGraphNode,
    ) -> EvalResult<Option<NodeInfoView<'a>>> {
        match &self.backend {
            GraphStoreBackend::InMemory(store) => {
                Ok(store.nodes.get(node).map(NodeInfoView::Borrowed))
            }
            GraphStoreBackend::Disk { store, .. } => {
                let info = store
                    .borrow_mut()
                    .read_node(*node)
                    .map_err(|error| Self::map_disk_error("read liveness node", error))?;
                Ok(info.map(NodeInfoView::Owned))
            }
        }
    }

    pub(crate) fn update_node_info<R>(
        &mut self,
        node: &BehaviorGraphNode,
        update: impl FnOnce(&mut NodeInfo) -> R,
    ) -> EvalResult<Option<R>> {
        match &mut self.backend {
            GraphStoreBackend::InMemory(store) => Ok(store.nodes.get_mut(node).map(update)),
            GraphStoreBackend::Disk { store, .. } => {
                let mut store = store.borrow_mut();
                let mut info = match store
                    .read_node(*node)
                    .map_err(|error| Self::map_disk_error("read liveness node for update", error))?
                {
                    Some(info) => info,
                    None => return Ok(None),
                };
                let result = update(&mut info);
                store.update_node(*node, &info).map_err(|error| {
                    Self::map_disk_error("persist updated liveness node", error)
                })?;
                Ok(Some(result))
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn get_node_info_mut(&mut self, node: &BehaviorGraphNode) -> Option<&mut NodeInfo> {
        match &mut self.backend {
            GraphStoreBackend::InMemory(store) => store.nodes.get_mut(node),
            GraphStoreBackend::Disk { .. } => None,
        }
    }

    pub(crate) fn reconstruct_fingerprint_trace(
        &self,
        end: BehaviorGraphNode,
    ) -> EvalResult<Vec<(Fingerprint, usize)>> {
        match &self.backend {
            GraphStoreBackend::InMemory(store) => {
                let mut trace = Vec::new();
                let mut current = Some(end);
                while let Some(node) = current {
                    let info = store.nodes.get(&node).ok_or_else(|| {
                        invariant_error(format!(
                            "fingerprint trace reconstruction reached missing node {node}"
                        ))
                    })?;
                    trace.push((node.state_fp, node.tableau_idx));
                    current = info.parent;
                }
                trace.reverse();
                Ok(trace)
            }
            GraphStoreBackend::Disk { store, .. } => {
                let mut trace = Vec::new();
                let mut current = Some(end);
                while let Some(node) = current {
                    let info = store
                        .borrow_mut()
                        .read_node(node)
                        .map_err(|error| {
                            Self::map_disk_error(
                                "read liveness node during fingerprint trace reconstruction",
                                error,
                            )
                        })?
                        .ok_or_else(|| {
                            invariant_error(format!(
                                "fingerprint trace reconstruction reached missing node {node}"
                            ))
                        })?;
                    trace.push((node.state_fp, node.tableau_idx));
                    current = info.parent;
                }
                trace.reverse();
                Ok(trace)
            }
        }
    }

    pub(crate) fn node_keys(&self) -> Vec<BehaviorGraphNode> {
        match &self.backend {
            GraphStoreBackend::InMemory(store) => store.nodes.keys().copied().collect(),
            GraphStoreBackend::Disk { store, .. } => store.borrow().all_nodes().to_vec(),
        }
    }

    #[allow(dead_code)] // Used in tests via BehaviorGraph::len and disk_graph_tests
    pub(crate) fn node_count(&self) -> usize {
        match &self.backend {
            GraphStoreBackend::InMemory(store) => store.nodes.len(),
            GraphStoreBackend::Disk { store, .. } => store.borrow().node_count(),
        }
    }

    #[cfg(test)]
    pub(crate) fn init_nodes(&self) -> Vec<BehaviorGraphNode> {
        match &self.backend {
            GraphStoreBackend::InMemory(store) => store.init_nodes_list.clone(),
            GraphStoreBackend::Disk { store, .. } => store.borrow().init_nodes().to_vec(),
        }
    }
}
