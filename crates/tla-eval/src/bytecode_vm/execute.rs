// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode VM executor — facade module.
//!
//! Owns the `BytecodeVm` struct, `VmError` enum, constructors, and public
//! entry points. Opcode dispatch and handler families live in sibling modules
//! extracted per #3611:
//!
//! - `execute_dispatch.rs` — `execute_with_regs` dispatch loop
//! - `execute_scalar.rs` — scalar/control opcode handlers
//! - `execute_compound.rs` — compound-value opcode handlers
//! - `execute_loops.rs` — quantifier/loop opcode handlers (#3594)
//! - `execute_helpers.rs` — shared helper functions (#3472)

use smallvec::SmallVec;
use thiserror::Error;
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, ConstantPool};
use tla_value::error::EvalError;
use tla_value::Value;

use crate::{core::EvalCtx, note_bytecode_vm_execution, note_bytecode_vm_fallback, StateEnvRef};

/// Errors specific to the bytecode VM (distinct from `EvalError` for eval-time errors).
#[derive(Debug, Error)]
pub enum VmError {
    #[error("unsupported opcode in bytecode VM: {0}")]
    Unsupported(String),

    #[error("bytecode VM evaluation error: {0}")]
    Eval(#[from] EvalError),

    #[error("type error: expected {expected}, got {actual}")]
    TypeError {
        expected: &'static str,
        actual: String,
    },

    #[error("CHOOSE failed: no value satisfies predicate")]
    ChooseFailed,

    #[error("halted")]
    Halted,
}

/// The bytecode virtual machine.
///
/// Executes compiled bytecode functions against state variable arrays.
/// Reuses a register file buffer across invocations to avoid per-execution
/// heap allocation on the invariant-check hot path.
pub struct BytecodeVm<'a> {
    pub(super) chunk: &'a BytecodeChunk,
    /// Current state variable values (indexed by VarIdx).
    pub(super) state: StateEnvRef,
    /// Next (primed) state variable values, if available.
    pub(super) next_state: Option<StateEnvRef>,
    /// Memoized current-state slots materialized during this VM execution.
    pub(super) state_cache: SmallVec<[Option<Value>; 8]>,
    /// Memoized next-state slots materialized during this VM execution.
    pub(super) next_state_cache: Option<SmallVec<[Option<Value>; 8]>>,
    /// Reusable register file buffer. Avoids heap allocation on every
    /// `execute_function` call — significant for invariant checks that
    /// run once per state (millions of times).
    regs_buf: Vec<Value>,
    /// When true, `LoadVar` reads from next-state instead of current state.
    /// Set by `SetPrimeMode` opcode for UNCHANGED general fallback where
    /// `expr = expr'` needs Call targets to use next-state values.
    pub(super) prime_mode: bool,
    /// Caller evaluation context for closure application from bytecode.
    pub(super) eval_ctx: Option<&'a EvalCtx>,
}

impl<'a> BytecodeVm<'a> {
    /// Create a VM bound to a bytecode chunk and state arrays.
    pub fn new(
        chunk: &'a BytecodeChunk,
        state: &'a [Value],
        next_state: Option<&'a [Value]>,
    ) -> Self {
        Self::from_state_env(
            chunk,
            StateEnvRef::from_slice(state),
            next_state.map(StateEnvRef::from_slice),
        )
    }

    /// Create a VM bound directly to borrowed state environments.
    ///
    /// Part of #3579: lets the VM load from compact state arrays on demand
    /// without first materializing the entire state as `Vec<Value>`.
    pub fn from_state_env(
        chunk: &'a BytecodeChunk,
        state: StateEnvRef,
        next_state: Option<StateEnvRef>,
    ) -> Self {
        Self {
            chunk,
            state,
            next_state,
            state_cache: SmallVec::new(),
            next_state_cache: next_state.map(|_| SmallVec::new()),
            regs_buf: Vec::new(),
            prime_mode: false,
            eval_ctx: None,
        }
    }

    /// Attach the caller `EvalCtx` so higher-order closure application can
    /// reuse the existing evaluator semantics from inside the VM.
    #[must_use]
    pub fn with_eval_ctx(mut self, eval_ctx: &'a EvalCtx) -> Self {
        self.eval_ctx = Some(eval_ctx);
        self
    }

    /// Execute a function by index, returning the result value.
    pub fn execute_function(&mut self, func_idx: u16) -> Result<Value, VmError> {
        let func = self.chunk.get_function(func_idx);
        let result = self.execute(func, &self.chunk.constants);
        match &result {
            Ok(_) => note_bytecode_vm_execution(),
            Err(VmError::Unsupported(_)) => note_bytecode_vm_fallback(),
            Err(_) => {}
        }
        result
    }

    /// Execute a bytecode function, reusing the register buffer.
    fn execute(
        &mut self,
        func: &BytecodeFunction,
        constants: &ConstantPool,
    ) -> Result<Value, VmError> {
        let needed = (func.max_register as usize) + 1;
        let mut regs = std::mem::take(&mut self.regs_buf);
        regs.clear();
        regs.resize(needed, Value::Bool(false));
        let result = self.execute_with_regs(func, constants, &mut regs);
        self.regs_buf = regs;
        result
    }
}
