// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification assumptions carried by every result.
//!
//! "Verified under these assumptions" is the output, never "verified."

use serde::{Deserialize, Serialize};

/// Assumptions under which verification is performed.
///
/// Every verification result carries these assumptions explicitly.
/// Within these bounds, the checking is exhaustive.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Assumptions {
    /// Maximum number of threads modeled.
    pub thread_bound: usize,
    /// How data values are abstracted.
    pub data_abstraction: DataAbstraction,
    /// Fairness mode for liveness checking.
    pub fairness_mode: FairnessMode,
    /// Memory model assumed for atomic operations.
    pub memory_model: MemoryModel,
    /// State space reductions applied.
    pub reductions: Vec<Reduction>,
    /// Synchronization primitives recognized but not modeled.
    pub unmodeled_primitives: Vec<String>,
    /// Maximum interprocedural call depth analyzed.
    pub interprocedural_depth: usize,
    /// Panic strategy: unwind vs abort.
    pub panic_strategy: PanicStrategy,
    /// Maximum recursion depth (None = unbounded).
    pub recursion_bound: Option<usize>,
    /// Maximum heap allocations modeled (None = unbounded).
    pub heap_bound: Option<usize>,
    /// How dynamic dispatch (dyn Trait) was resolved.
    pub dynamic_dispatch: DynDispatchResolution,
    /// Functions that could not be analyzed (FFI, opaque).
    pub opaque_externals: Vec<String>,
}

impl Default for Assumptions {
    fn default() -> Self {
        Self {
            thread_bound: 0,
            data_abstraction: DataAbstraction::Concrete,
            fairness_mode: FairnessMode::None,
            memory_model: MemoryModel::SequentialConsistency,
            reductions: Vec::new(),
            unmodeled_primitives: Vec::new(),
            interprocedural_depth: 0,
            panic_strategy: PanicStrategy::Unwind,
            recursion_bound: None,
            heap_bound: None,
            dynamic_dispatch: DynDispatchResolution::FullyResolved,
            opaque_externals: Vec::new(),
        }
    }
}

/// How data values are abstracted in the model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DataAbstraction {
    /// Exact concrete values (no abstraction).
    Concrete,
    /// Finite domain abstraction (e.g., integers bounded to small range).
    FiniteDomain,
    /// Predicate abstraction.
    Predicate,
}

/// Fairness mode for liveness properties.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FairnessMode {
    /// Safety only — no fairness constraints.
    None,
    /// Weak fairness (WF) per process action.
    WeakFairness,
    /// Strong fairness (SF) for condvar/channel, WF for others.
    StrongFairness,
}

/// Memory model for atomic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MemoryModel {
    /// All operations appear in a single total order.
    SequentialConsistency,
    /// x86-style total store order.
    TotalStoreOrder,
    /// ARM v8 memory model.
    ArmV8,
    /// RISC-V weak memory ordering (separate from ARM).
    RiscVWmo,
    /// C++11/C11 memory model.
    Rc11,
}

/// State space reduction technique.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Reduction {
    /// Process symmetry: K identical threads → K! reduction.
    Symmetry { group_size: usize },
    /// Partial order reduction.
    PartialOrderReduction,
    /// Preemption bounding (CHESS: 90%+ bugs at K ≤ 2).
    PreemptionBounding { bound: usize },
    /// Context bounding.
    ContextBounding { bound: usize },
}

/// Panic handling strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PanicStrategy {
    /// Stack unwinding with Drop calls.
    Unwind,
    /// Immediate process abort.
    Abort,
}

/// How dynamic dispatch was resolved during extraction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DynDispatchResolution {
    /// All call targets fully resolved.
    FullyResolved,
    /// Some call targets resolved, others opaque.
    Partial,
    /// Dynamic dispatch not analyzed (all opaque).
    Opaque,
}
