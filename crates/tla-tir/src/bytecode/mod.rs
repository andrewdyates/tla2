// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bytecode representation for TLA+ TIR expressions.
//!
//! This module defines a register-based bytecode instruction set that provides
//! 3-5x speedup over tree-walking interpretation by eliminating:
//! - Recursive function call overhead per AST node
//! - Pointer chasing through `Box<Spanned<TirExpr>>` indirections
//! - Branch misprediction on large `match` arms
//! - Data dependency chains through recursion
//!
//! The bytecode is compiled from TIR in a single O(n) pass at spec load time.
//! A register-based VM executes the flat opcode stream with a stack-allocated
//! register file (256 registers × 8B = 2KB).
//!
//! ## Architecture
//!
//! - **Register-based**: 256 virtual registers (r0-r255), each holds a `CompactValue`
//! - **Constant pool**: Compile-time constants stored in a separate array
//! - **Flat instruction stream**: No recursion, pure linear execution with jumps
//! - **Tiered**: Bytecode is the input format for Cranelift JIT (Phase B2)

pub mod action_transform;
mod chunk;
mod compiler;
mod opcode;
mod opcode_support;

pub use chunk::{specialize_bytecode_function, BytecodeChunk, BytecodeFunction, ConstantPool};
pub use compiler::{BytecodeCompiler, CalleeInfo, CompileError};
pub use opcode::{BuiltinOp, Opcode, Register};
