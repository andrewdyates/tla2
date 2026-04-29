// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

//! Generic explicit-state model checking traits and reusable algorithms.
//!
//! This crate is the first extraction step for the pnml-tools merger plan:
//! it provides a domain-agnostic transition-system API, exploration observer
//! contracts, a sequential BFS engine, generic fingerprint storage contracts,
//! and iterative Tarjan SCC detection.
//!
//! # Example
//!
//! ```rust
//! use tla_mc_core::{explore_bfs, ExplorationObserver, NoopObserver, TransitionSystem};
//!
//! #[derive(Clone)]
//! struct Counter;
//!
//! impl TransitionSystem for Counter {
//!     type State = u8;
//!     type Action = &'static str;
//!     type Fingerprint = u8;
//!
//!     fn initial_states(&self) -> Vec<Self::State> {
//!         vec![0]
//!     }
//!
//!     fn successors(&self, state: &Self::State) -> Vec<(Self::Action, Self::State)> {
//!         if *state < 2 {
//!             vec![("inc", state + 1)]
//!         } else {
//!             Vec::new()
//!         }
//!     }
//!
//!     fn fingerprint(&self, state: &Self::State) -> Self::Fingerprint {
//!         *state
//!     }
//! }
//!
//! let mut observer = NoopObserver::<Counter>::default();
//! let outcome = explore_bfs(&Counter, &mut observer).unwrap();
//! assert!(outcome.completed);
//! assert_eq!(outcome.states_discovered, 3);
//! ```

mod bfs;
mod cas_fpset;
mod ctl;
pub mod diff_successor;
mod observer;
mod scc;
mod storage;
mod traits;

pub use bfs::{
    explore_bfs, explore_bfs_parallel, explore_bfs_parallel_with_options,
    explore_bfs_parallel_with_storage, explore_bfs_with_options, explore_bfs_with_storage,
    BfsError, BfsOptions, BfsOutcome,
};
pub use cas_fpset::{CasFingerprintSet, PartitionedCasFingerprintSet};
pub use ctl::{
    build_predecessor_adjacency, check_ctl, CtlAtomEvaluator, CtlEdge, CtlEngine, CtlFormula,
    IndexedCtlGraph,
};
pub use diff_successor::{
    finalize_xor, incremental_xor_fingerprint, DiffChanges, DiffSuccessor, DIFF_INLINE_CAPACITY,
};
pub use observer::{
    CompositeObserver, ExplorationObserver, NoopObserver, ParallelObserver, ParallelObserverSummary,
};
pub use scc::{bottom_sccs, tarjan_scc, Scc, TarjanResult};
pub use storage::{
    CapacityStatus, FingerprintSet, InMemoryFingerprintSet, InsertOutcome, LookupOutcome,
    ShardedFingerprintSet, StorageFault, StorageStats,
};
pub use traits::{AtomEvaluator, PorPropertyClass, PorProvider, TransitionSystem};
