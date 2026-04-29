// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Disk-backed liveness graph storage.
//!
//! Combines the [`NodePtrTable`](super::node_ptr_table::NodePtrTable) (Slice C)
//! with an append-only node record file to provide persistent storage for
//! behavior graph topology. Mirrors TLC's `AbstractDiskGraph` pattern: a
//! pointer table indexes into an append-only record file, with a small
//! direct-mapped cache for reads.
//!
//! # Architecture
//!
//! ```text
//!   NodePtrTable (mmap)          Node Record File (append-only)
//!   ┌──────────────────┐         ┌─────────────────────────┐
//!   │ (fp,tidx) → off  │────────►│ [header][succs][masks]  │ record 0
//!   │ (fp,tidx) → off  │────────►│ [header][succs][masks]  │ record 1
//!   │ ...               │         │ ...                     │
//!   └──────────────────┘         └─────────────────────────┘
//!
//!                     Read Cache (direct-mapped, 64K entries)
//!                     ┌────────────────────────────┐
//!                     │ (fp^tidx) & mask → NodeInfo │
//!                     └────────────────────────────┘
//! ```
//!
//! Part of #2732 Slice D.

use crate::liveness::behavior_graph::{BehaviorGraphNode, NodeInfo};
use crate::liveness::storage::node_ptr_table::{NodePtrError, NodePtrTable};
use crate::liveness::storage::node_record;
use std::fs::{File, OpenOptions};
use std::io::{self, BufWriter, Seek, SeekFrom, Write};
use std::path::Path;

/// Direct-mapped read cache size, matching TLC's `gnodes[65536]`.
const READ_CACHE_SIZE: usize = 1 << 16;

/// Disk-backed liveness graph storage.
///
/// Stores behavior graph nodes in an append-only file, indexed by a
/// [`NodePtrTable`]. Provides a direct-mapped read cache for recently
/// accessed records.
pub(crate) struct DiskGraphStore {
    /// Buffered writer for append-only node records.
    writer: BufWriter<File>,
    /// Separate read handle for random-access reads.
    reader: File,
    /// Current write position (byte offset for next append).
    write_pos: u64,
    /// Node pointer table: (fp, tidx) → byte offset.
    ptr_table: NodePtrTable,
    /// Direct-mapped read cache, indexed by `(fp ^ tidx) & (CACHE_SIZE - 1)`.
    cache: Vec<Option<CacheEntry>>,
    /// Initial nodes in insertion order.
    init_nodes: Vec<BehaviorGraphNode>,
    /// All nodes in append/update insertion order without duplicates.
    all_nodes: Vec<BehaviorGraphNode>,
    /// Total node count.
    node_count: usize,
    /// Whether there are unflushed writes.
    dirty: bool,
}

/// A cached node record.
struct CacheEntry {
    node: BehaviorGraphNode,
    info: NodeInfo,
    offset: u64,
}

impl std::fmt::Debug for DiskGraphStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DiskGraphStore")
            .field("write_pos", &self.write_pos)
            .field("init_nodes", &self.init_nodes)
            .field("all_nodes_len", &self.all_nodes.len())
            .field("node_count", &self.node_count)
            .field("dirty", &self.dirty)
            .finish()
    }
}

impl DiskGraphStore {
    /// Create a new disk graph store with a specific pointer table capacity.
    pub(crate) fn with_capacity(backing_dir: &Path, ptr_table_capacity: usize) -> io::Result<Self> {
        std::fs::create_dir_all(backing_dir)?;

        let node_file_path = backing_dir.join("liveness_nodes.dat");

        let writer = BufWriter::new(
            OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(true)
                .open(&node_file_path)?,
        );
        let reader = OpenOptions::new().read(true).open(&node_file_path)?;

        let ptr_table = NodePtrTable::new(ptr_table_capacity, Some(backing_dir.to_path_buf()))?;

        let cache = (0..READ_CACHE_SIZE).map(|_| None).collect();

        Ok(Self {
            writer,
            reader,
            write_pos: 0,
            ptr_table,
            cache,
            init_nodes: Vec::new(),
            all_nodes: Vec::new(),
            node_count: 0,
            dirty: false,
        })
    }

    fn persist_node(
        &mut self,
        node: BehaviorGraphNode,
        info: &NodeInfo,
    ) -> Result<(u64, bool), DiskGraphError> {
        let offset = self.write_pos;
        let bytes_written = node_record::write_node_record(&mut self.writer, node, info)
            .map_err(DiskGraphError::Io)?;
        self.write_pos += bytes_written as u64;
        self.dirty = true;

        let inserted = self
            .ptr_table
            .insert(node.state_fp, node.tableau_idx, offset)
            .map_err(DiskGraphError::PtrTable)?;

        let cache_idx = Self::cache_index(node);
        self.cache[cache_idx] = Some(CacheEntry {
            node,
            info: info.clone(),
            offset,
        });

        if inserted {
            self.node_count += 1;
            self.all_nodes.push(node);
        }

        Ok((offset, inserted))
    }

    /// Append a node record to disk and index it.
    ///
    /// Returns the byte offset where the record was written.
    pub(crate) fn append_node(
        &mut self,
        node: BehaviorGraphNode,
        info: &NodeInfo,
    ) -> Result<u64, DiskGraphError> {
        if self.contains(node) {
            return Err(DiskGraphError::DuplicateNode(node));
        }
        let (offset, inserted) = self.persist_node(node, info)?;
        debug_assert!(inserted, "append_node should only insert new nodes");
        Ok(offset)
    }

    /// Rewrite an existing node by appending a new version and updating the index.
    pub(crate) fn update_node(
        &mut self,
        node: BehaviorGraphNode,
        info: &NodeInfo,
    ) -> Result<u64, DiskGraphError> {
        if !self.contains(node) {
            return Err(DiskGraphError::MissingNode(node));
        }
        let (offset, inserted) = self.persist_node(node, info)?;
        debug_assert!(!inserted, "update_node should only rewrite existing nodes");
        Ok(offset)
    }

    /// Read a node record. Checks the cache first, falls back to disk.
    ///
    /// Returns `None` if the node is not in the store.
    pub(crate) fn read_node(
        &mut self,
        node: BehaviorGraphNode,
    ) -> Result<Option<NodeInfo>, DiskGraphError> {
        let offset = match self.ptr_table.get(node.state_fp, node.tableau_idx) {
            Some(off) => off,
            None => return Ok(None),
        };

        // Check cache.
        let cache_idx = Self::cache_index(node);
        if let Some(ref entry) = self.cache[cache_idx] {
            if entry.node == node && entry.offset == offset {
                return Ok(Some(entry.info.clone()));
            }
        }

        // Cache miss — flush pending writes, then read from disk.
        if self.dirty {
            self.writer.flush().map_err(DiskGraphError::Io)?;
            self.dirty = false;
        }

        self.reader
            .seek(SeekFrom::Start(offset))
            .map_err(DiskGraphError::Io)?;
        let (read_node, info) =
            node_record::read_node_record(&mut self.reader).map_err(DiskGraphError::Io)?;

        debug_assert_eq!(
            read_node, node,
            "node key mismatch at offset {offset}: expected {node:?}, got {read_node:?}"
        );

        // Populate cache.
        self.cache[cache_idx] = Some(CacheEntry {
            node,
            info: info.clone(),
            offset,
        });

        Ok(Some(info))
    }

    /// Check if a node exists (via pointer table lookup, no disk read).
    pub(crate) fn contains(&self, node: BehaviorGraphNode) -> bool {
        self.ptr_table.contains(node.state_fp, node.tableau_idx)
    }

    /// Record a node as an initial node.
    pub(crate) fn mark_init_node(&mut self, node: BehaviorGraphNode) {
        self.init_nodes.push(node);
    }

    /// Get the initial nodes in insertion order.
    #[cfg(test)]
    pub(crate) fn init_nodes(&self) -> &[BehaviorGraphNode] {
        &self.init_nodes
    }

    /// Get all nodes in insertion order.
    pub(crate) fn all_nodes(&self) -> &[BehaviorGraphNode] {
        &self.all_nodes
    }

    /// Total number of nodes stored.
    #[allow(dead_code)] // Used by GraphStore::node_count and in tests
    pub(crate) fn node_count(&self) -> usize {
        self.node_count
    }

    /// Flush all buffered writes to disk (both record file and pointer table).
    #[cfg(test)]
    pub(crate) fn flush(&mut self) -> Result<(), DiskGraphError> {
        self.writer.flush().map_err(DiskGraphError::Io)?;
        self.dirty = false;
        self.ptr_table.flush().map_err(DiskGraphError::Io)
    }

    /// Cache index for a node (direct-mapped hash).
    #[inline]
    fn cache_index(node: BehaviorGraphNode) -> usize {
        let h = node.state_fp.0 ^ (node.tableau_idx as u64);
        (h as usize) & (READ_CACHE_SIZE - 1)
    }
}

/// Errors from disk graph operations.
#[derive(Debug)]
pub(crate) enum DiskGraphError {
    /// I/O error during file read/write.
    Io(io::Error),
    /// Node pointer table capacity or probe error.
    PtrTable(NodePtrError),
    /// Attempted to append a node that already exists.
    DuplicateNode(BehaviorGraphNode),
    /// Attempted to update a node that does not exist.
    MissingNode(BehaviorGraphNode),
}

impl std::fmt::Display for DiskGraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiskGraphError::Io(e) => write!(f, "disk graph I/O error: {e}"),
            DiskGraphError::PtrTable(e) => {
                write!(f, "disk graph pointer table error: {e}")
            }
            DiskGraphError::DuplicateNode(node) => {
                write!(f, "disk graph node already exists: {node}")
            }
            DiskGraphError::MissingNode(node) => {
                write!(f, "disk graph node missing: {node}")
            }
        }
    }
}

impl std::error::Error for DiskGraphError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DiskGraphError::Io(e) => Some(e),
            DiskGraphError::PtrTable(e) => Some(e),
            DiskGraphError::DuplicateNode(_) | DiskGraphError::MissingNode(_) => None,
        }
    }
}

#[cfg(test)]
#[path = "disk_graph_tests.rs"]
mod tests;
