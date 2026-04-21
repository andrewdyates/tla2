// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Storage infrastructure for disk-backed liveness graphs.
//!
//! Part of #2732: this module provides the mmap-backed storage primitives
//! for the liveness graph. The node pointer table maps `(Fingerprint, tableau_idx)`
//! composite keys to node record offsets, following TLC's `TableauNodePtrTable`
//! pattern.

pub(crate) mod disk_graph;
pub(crate) mod node_ptr_table;
pub(crate) mod node_record;
