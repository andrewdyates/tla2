// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LLVM-based AOT compilation backend for TLA2.
//!
//! Translates TLA+ bytecode to LLVM IR text, enabling full LLVM optimization
//! passes (O2/O3) for aggressive code quality. Unlike the Cranelift JIT which
//! prioritizes compile speed, this backend prioritizes runtime performance
//! for model checking billions of states through the same compiled code.
//!
//! # Architecture
//!
//! ```text
//! BytecodeFunction ──► LLVM IR text (.ll) ──► llc/clang ──► .dylib ──► dlopen
//!                       (pure Rust)          (external)    (native)   (runtime)
//! ```
//!
//! The LLVM IR emitter is pure Rust with no native LLVM dependencies at build
//! time. LLVM tools (`llc`, `clang`) are only needed at runtime for AOT
//! compilation.
//!
//! # ABI Compatibility
//!
//! Uses the same `extern "C"` ABI as `tla-jit`:
//! - Invariant: `fn(out: *mut JitCallOut, state: *const i64, state_len: u32)`
//! - Next-state: `fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32)`

pub mod error;
pub(crate) mod ir;
pub(crate) mod lower;
pub mod compiler;

#[cfg(test)]
mod tests;

pub use compiler::{AotLibrary, LlvmCompiler, OptLevel};
pub use error::LlvmError;
