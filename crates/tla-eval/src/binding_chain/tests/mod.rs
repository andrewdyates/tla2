// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for BindingChain — see binding_chain.rs for implementation.
//!
//! Decomposed from a single tests.rs into focused suites (Part of #3389):
//! - core_operations: empty, cons, lookup, shadow, sharing, clone, default, debug
//! - lazy_binding: cache behavior, dual-mode independence, idempotent set
//! - binding_sources: cons_with_deps, cons_local, update_head, instance/local interaction
//! - snapshot_scope: push/pop, nested snapshots, restore, concurrent
//! - iter_tests: iter(), collect_local_bindings consistency, liveness

mod binding_sources;
mod core_operations;
mod iter_tests;
mod lazy_binding;
mod snapshot_scope;
