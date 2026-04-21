// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LLVM2 compilation backend for TLA2.
//!
//! Takes [`tmir::Module`] output from [`tla_tmir`] and compiles it to native
//! code via the LLVM2 verified compiler backend. This crate is the bridge
//! between TLA+-specific IR lowering (tla-tmir) and the language-agnostic
//! LLVM2 compiler.
//!
//! # Architecture
//!
//! ```text
//! TLA+ Spec
//!     |  (tla-core: parse + resolve)
//!     v
//! TIR (typed bytecode)
//!     |  (tla-tmir: TLA+ semantics -> tMIR)
//!     v
//! tmir::Module (SSA IR)
//!     |  (tla-llvm2: THIS CRATE)
//!     v
//! LLVM2 backend (optimize + codegen)
//!     |
//!     v
//! Native code (AArch64/x86)
//! ```
//!
//! # Pipeline
//!
//! 1. **Validate** the tMIR module structure ([`lower::validate_module`])
//! 2. **Lower** tMIR instructions to LLVM2 IR ([`lower::lower_module`])
//! 3. **Compile** to native code via LLVM2 ([`compile::compile_module`])
//!
//! # Optimization Levels
//!
//! - [`OptLevel::O1`]: Fast compilation (~50-200ms). Tier 1 warmup.
//! - [`OptLevel::O3`]: Peak throughput (~0.5-2s). Tier 2 steady-state.
//!
//! # ABI Compatibility
//!
//! Uses the same `extern "C"` ABI as `tla-jit` ([`tla_jit::abi`]):
//! - Invariant: `fn(out: *mut JitCallOut, state: *const i64, state_len: u32)`
//! - Next-state: `fn(out: *mut JitCallOut, state_in: *const i64, state_out: *mut i64, state_len: u32)`
//!
//! # Example
//!
//! ```no_run
//! use tla_llvm2::{compile_module, OptLevel};
//! # fn example(module: &tmir::Module) -> Result<(), tla_llvm2::Llvm2Error> {
//! let compiled = compile_module(module, OptLevel::O1)?;
//! println!("Compiled {} functions ({} instructions, {} helper calls)",
//!     compiled.stats.functions, compiled.stats.instructions,
//!     compiled.stats.helper_calls);
//! # Ok(())
//! # }
//! ```

mod error;
pub(crate) mod emit;
pub mod tir_lower;
#[cfg(test)]
mod validate_ir;
pub mod compile;
pub mod lower;
pub mod runtime;

pub use compile::{
    compile_bfs_step, compile_invariant, compile_module, compile_next_state,
    compile_spec_invariant, compile_spec_next_state, CompiledBfsStep, CompiledModule, OptLevel,
};
pub use error::Llvm2Error;
pub use lower::LoweringStats;
pub use tir_lower::{is_tir_eligible, lower_tir_to_llvm_ir, TirLoweredModule, TirLoweringStats};
