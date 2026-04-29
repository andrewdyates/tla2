// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Thread concurrency verification for TLA2.
//!
//! This crate translates a `ConcurrentModel` IR (produced by tRust's MIR
//! extraction) into a TLA+ `Module` AST, feeds it through the TLA2 model
//! checker, and returns structured verification results with source-mapped
//! counterexamples.
//!
//! # Architecture
//!
//! ```text
//! Rust source → tRust MIR extraction → ConcurrentModel (JSON)
//!     → tla-concurrent → TLA+ Module AST → tla-check → CheckResult
//!     → source-mapped counterexample (JSON)
//! ```

pub mod assumptions;
pub mod generate;
pub mod model;
pub mod property;
pub mod source_map;
pub mod sync_kind;
pub mod transition;

#[cfg(feature = "check")]
mod check;
#[cfg(feature = "check")]
mod output;
#[cfg(feature = "check")]
mod trace_mapper;

pub use assumptions::{
    Assumptions, DataAbstraction, DynDispatchResolution, FairnessMode, MemoryModel, PanicStrategy,
    Reduction,
};
#[cfg(feature = "check")]
pub use check::{check_concurrent_model, CheckOptions, ConcurrentCheckResult, ConcurrentError};
pub use model::{
    AccessKind, AccessSite, ConcurrentModel, GuardMode, HeldGuard, LocalVar, Process, ProcessId,
    ProcessKind, SharedVar, StateId, SyncId,
};
#[cfg(feature = "check")]
pub use output::{CheckerStats, VerificationReport, VerificationStatus};
pub use property::Property;
pub use source_map::{MappedStep, MappedTrace, SourceMap, SourceMapEntry, SourceSpan};
pub use sync_kind::{ChannelKind, SyncKind, SyncPrimitive};
pub use transition::{AtomicOp, CasInfo, MemoryOrdering, PanicGuard, Transition, TransitionKind};
