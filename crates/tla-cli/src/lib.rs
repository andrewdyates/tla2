// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Command-line interface for TLA2, a modern TLA+ verification toolchain.
//!
//! This crate provides the `tla2` binary with subcommands for model checking,
//! parsing, simulation, and related tooling. It is the primary user-facing
//! entry point to the TLA2 ecosystem.
//!
//! # Commands
//!
//! - **`check`** — Model check a TLA+ specification (explicit-state BFS, with
//!   optional BMC, PDR, and parallel workers). Replacement for TLC.
//! - **`parse`** — Parse a TLA+ source file and report syntax errors.
//! - **`ast`** — Parse and lower a spec, then dump the lowered AST.
//! - **`fmt`** — Pretty-print a TLA+ module to stdout.
//! - **`typecheck`** — Type check a TLA+ spec via TIR lowering with `@type:` annotations.
//! - **`simulate`** — Random trace exploration of large state spaces.
//! - **`trace`** — Trace parsing, validation, and visualization tooling.
//! - **`diagnose`** — Regression coverage analysis against TLC baseline results.
//! - **`codegen`** — Generate Rust code from a TLA+ specification.
//! - **`prove`** — Theorem proving (requires Z3, feature-gated).
//! - **`lsp`** — Language Server Protocol server for editor integration.
//!
//! # Crate relationships
//!
//! `tla-cli` delegates to `tla-check` for model checking, `tla-core` for
//! parsing/lowering/resolution, and `tla-eval` for expression evaluation.
//! Output formatting (JSON, JSONL, TLC-tool) is handled here in
//! `check_report` and `cli_schema`.
