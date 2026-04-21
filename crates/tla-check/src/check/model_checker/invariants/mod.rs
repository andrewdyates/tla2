// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Invariant checking, init-state solving, successor dispatch, and state tracking.
//!
//! Split into concern-focused submodules aligned with TLC boundaries (Part of #2358):
//! - `eval`: Invariant/constraint evaluation (`Tool.isValid()`, `Tool.isInModel()`)
//! - `init_solve`: Init-state predicate solving (`ModelChecker.DoInitFunctor`)
//! - `successor_dispatch`: Successor generation dispatch (`ModelChecker.doNext()`)
//! - `state_tracking`: State storage bookkeeping (`Worker.isSeenState()`, FPSet)

mod constraints;
mod eval;
mod init_solve;
mod state_tracking;
mod successor_dispatch;
#[cfg(test)]
mod tests;

pub(crate) use constraints::check_terminal_array;
pub(crate) use eval::collect_runtime_failing_invariant_bytecode_ops;
pub(crate) use eval::flatten_state_to_i64_selective;
pub(crate) use eval::unflatten_i64_to_array_state;
pub(crate) use eval::unflatten_i64_to_array_state_with_input;
pub(crate) use eval::fingerprint_jit_flat_successor;
pub(crate) use eval::fingerprint_jit_flat_successor_incremental;
#[allow(unused_imports)]
pub(crate) use eval::fingerprint_flat_compiled;
#[allow(unused_imports)]
pub(crate) use eval::fingerprint_flat_compiled_incremental;
pub(crate) use eval::prune_runtime_failing_invariant_bytecode_ops;
pub(in crate::check) use init_solve::BulkInitStates;
