// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bytecode chunk: a compiled bytecode function with its constant pool.

use super::opcode::{ConstIdx, OpIdx, Opcode};
use tla_value::Value;

/// A pool of constants referenced by bytecode instructions.
///
/// Constants include: string literals, big integers, compound Value constants,
/// record field name IDs, and operator metadata.
#[derive(Debug, Clone, Default)]
pub struct ConstantPool {
    /// Constant values, indexed by `ConstIdx`.
    values: Vec<Value>,
    /// Record field name IDs, stored separately for cache locality.
    /// Indexed by `FieldIdx` in RecordNew/RecordGet instructions.
    field_ids: Vec<u32>,
}

impl ConstantPool {
    /// Create an empty constant pool.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a constant value, returning its index.
    pub fn add_value(&mut self, value: Value) -> ConstIdx {
        let idx = self.values.len();
        assert!(
            idx <= ConstIdx::MAX as usize,
            "constant pool overflow: {idx} > {}",
            ConstIdx::MAX,
        );
        self.values.push(value);
        idx as ConstIdx
    }

    /// Add a field ID, returning its index.
    pub fn add_field_id(&mut self, id: u32) -> u16 {
        let idx = self.field_ids.len();
        assert!(u16::try_from(idx).is_ok(), "field ID pool overflow");
        self.field_ids.push(id);
        idx as u16
    }

    /// Get a constant value by index.
    #[inline]
    #[must_use]
    pub fn get_value(&self, idx: ConstIdx) -> &Value {
        &self.values[idx as usize]
    }

    /// Get a field ID by index.
    #[inline]
    #[must_use]
    pub fn get_field_id(&self, idx: u16) -> u32 {
        self.field_ids[idx as usize]
    }

    /// Number of constant values.
    #[must_use]
    pub fn value_count(&self) -> usize {
        self.values.len()
    }

    /// All field IDs as a slice.
    ///
    /// Used by the JIT compiler to resolve `RecordGet { field_idx }` opcodes
    /// to name IDs at compile time (Part of #3848).
    #[must_use]
    pub fn field_ids(&self) -> &[u32] {
        &self.field_ids
    }
}

/// A single compiled bytecode function.
///
/// Contains the instruction stream for one TLA+ operator or expression,
/// plus metadata for the VM.
#[derive(Debug, Clone)]
pub struct BytecodeFunction {
    /// The operator name (for diagnostics).
    pub name: String,
    /// Number of parameters (for Call instruction validation).
    pub arity: u8,
    /// Maximum register index used (for register file sizing).
    pub max_register: u8,
    /// The instruction stream.
    pub instructions: Vec<Opcode>,
}

impl BytecodeFunction {
    /// Create a new empty bytecode function.
    ///
    /// `max_register` is initialized to `arity - 1` (or 0 when arity is 0)
    /// so the register file is always large enough to hold all parameter
    /// registers. Without this, a function whose body only references
    /// parameter registers (e.g., `LAMBDA x, y: x`) would have
    /// `max_register = 0` and the VM would panic with an index-out-of-bounds
    /// error when copying arguments into the callee register file.
    #[must_use]
    pub fn new(name: String, arity: u8) -> Self {
        Self {
            name,
            arity,
            max_register: arity.saturating_sub(1),
            instructions: Vec::new(),
        }
    }

    /// Emit an instruction, returning its index in the instruction stream.
    pub fn emit(&mut self, op: Opcode) -> usize {
        // Track max register for register file sizing.
        if let Some(rd) = op.dest_register() {
            self.max_register = self.max_register.max(rd);
        }
        // Loop Begin opcodes also write to r_binding during iteration.
        if let Some(rb) = op.binding_register() {
            self.max_register = self.max_register.max(rb);
        }
        // Part of #3802: also track source registers. Defense-in-depth
        // against stale parent-scope binding registers leaking into
        // sub-function opcodes. Without this, a source register beyond
        // the allocated register file causes an index-out-of-bounds panic.
        if let Some(rs) = op.max_source_register() {
            self.max_register = self.max_register.max(rs);
        }
        let idx = self.instructions.len();
        self.instructions.push(op);
        idx
    }

    /// Patch a jump instruction at `idx` to jump to `target`.
    ///
    /// The offset is computed as `target - idx` (relative to the jump instruction).
    pub fn patch_jump(&mut self, idx: usize, target: usize) {
        let offset = (target as i32) - (idx as i32);
        match &mut self.instructions[idx] {
            Opcode::Jump { offset: o } => *o = offset,
            Opcode::JumpTrue { offset: o, .. } => *o = offset,
            Opcode::JumpFalse { offset: o, .. } => *o = offset,
            Opcode::ForallBegin { loop_end, .. } => *loop_end = offset,
            Opcode::ForallNext { loop_begin, .. } => *loop_begin = offset,
            Opcode::ExistsBegin { loop_end, .. } => *loop_end = offset,
            Opcode::ExistsNext { loop_begin, .. } => *loop_begin = offset,
            Opcode::ChooseBegin { loop_end, .. } => *loop_end = offset,
            Opcode::ChooseNext { loop_begin, .. } => *loop_begin = offset,
            Opcode::SetBuilderBegin { loop_end, .. } => *loop_end = offset,
            Opcode::SetFilterBegin { loop_end, .. } => *loop_end = offset,
            Opcode::FuncDefBegin { loop_end, .. } => *loop_end = offset,
            Opcode::LoopNext { loop_begin, .. } => *loop_begin = offset,
            other => panic!("patch_jump on non-jump instruction: {other:?}"),
        }
    }

    /// Current instruction count (next instruction index).
    #[must_use]
    pub fn len(&self) -> usize {
        self.instructions.len()
    }

    /// Whether the function has no instructions.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.instructions.is_empty()
    }
}

/// A complete bytecode compilation unit.
///
/// Contains the constant pool (shared across all functions) and the
/// compiled functions for each operator in the spec.
#[derive(Debug, Clone)]
pub struct BytecodeChunk {
    /// Shared constant pool.
    pub constants: ConstantPool,
    /// Compiled functions, indexed by `OpIdx`.
    pub functions: Vec<BytecodeFunction>,
}

impl BytecodeChunk {
    /// Create an empty bytecode chunk.
    #[must_use]
    pub fn new() -> Self {
        Self {
            constants: ConstantPool::new(),
            functions: Vec::new(),
        }
    }

    /// Add a compiled function, returning its operator index.
    pub fn add_function(&mut self, func: BytecodeFunction) -> OpIdx {
        let idx = self.functions.len();
        assert!(idx <= OpIdx::MAX as usize, "function table overflow");
        self.functions.push(func);
        idx as OpIdx
    }

    /// Get a function by operator index.
    #[inline]
    #[must_use]
    pub fn get_function(&self, idx: OpIdx) -> &BytecodeFunction {
        &self.functions[idx as usize]
    }

    /// Total number of compiled functions.
    #[must_use]
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Total number of instructions across all functions.
    #[must_use]
    pub fn total_instructions(&self) -> usize {
        self.functions.iter().map(|f| f.instructions.len()).sum()
    }
}

impl Default for BytecodeChunk {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::opcode::Opcode;

    #[test]
    fn test_constant_pool() {
        let mut pool = ConstantPool::new();
        let idx0 = pool.add_value(Value::SmallInt(42));
        let idx1 = pool.add_value(Value::Bool(true));
        assert_eq!(idx0, 0);
        assert_eq!(idx1, 1);
        assert_eq!(pool.get_value(0), &Value::SmallInt(42));
        assert_eq!(pool.get_value(1), &Value::Bool(true));
    }

    #[test]
    fn test_bytecode_function_emit() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        assert_eq!(func.len(), 4);
        assert_eq!(func.max_register, 2);
    }

    #[test]
    fn test_patch_jump() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        let jump_idx = func.emit(Opcode::JumpFalse {
            rs: 0,
            offset: 0, // placeholder
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 42 });
        let target = func.len();
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });

        func.patch_jump(jump_idx, target);

        match func.instructions[jump_idx] {
            Opcode::JumpFalse { offset, .. } => {
                assert_eq!(offset, (target as i32) - (jump_idx as i32));
            }
            _ => panic!("expected JumpFalse"),
        }
    }

    #[test]
    fn test_bytecode_chunk() {
        let mut chunk = BytecodeChunk::new();
        let mut f1 = BytecodeFunction::new("Init".to_string(), 0);
        f1.emit(Opcode::LoadBool { rd: 0, value: true });
        f1.emit(Opcode::Ret { rs: 0 });

        let mut f2 = BytecodeFunction::new("Next".to_string(), 0);
        f2.emit(Opcode::LoadImm { rd: 0, value: 1 });
        f2.emit(Opcode::Ret { rs: 0 });

        let idx1 = chunk.add_function(f1);
        let idx2 = chunk.add_function(f2);
        assert_eq!(idx1, 0);
        assert_eq!(idx2, 1);
        assert_eq!(chunk.function_count(), 2);
        assert_eq!(chunk.total_instructions(), 4);
    }

    /// Regression test: loop Begin opcodes must track r_binding in
    /// max_register. Without this, identity-body loops (where the body
    /// is just the bound variable) produce a register file that is too
    /// small, causing an index-out-of-bounds panic at runtime.
    #[test]
    fn test_loop_begin_tracks_binding_register() {
        let mut func = BytecodeFunction::new("test".to_string(), 0);
        // r0 = domain set
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        // FuncDefBegin { rd: 1, r_binding: 2, r_domain: 0 }
        func.emit(Opcode::FuncDefBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 0,
        });
        // Body is just the bound variable — no new register allocated.
        // LoopNext has no dest_register.
        func.emit(Opcode::LoopNext {
            r_binding: 2,
            r_body: 2,
            loop_begin: 0,
        });
        // max_register must be >= 2 (r_binding), not just 1 (rd).
        assert!(
            func.max_register >= 2,
            "max_register must account for r_binding, got {}",
            func.max_register
        );
    }

    /// Regression test: max_register must account for function arity.
    ///
    /// A function with arity=2 whose body only references parameter 0
    /// (e.g., `LAMBDA x, y: x`) must have max_register >= 1 so the
    /// register file is large enough to hold both parameters. Without
    /// this, the VM panics with index-out-of-bounds when copying
    /// arguments into the callee register file.
    ///
    /// Part of #3802.
    #[test]
    fn test_max_register_accounts_for_arity() {
        // Simulate `LAMBDA x, y: x` — body returns r0, no new registers.
        let mut func = BytecodeFunction::new("identity_first".to_string(), 2);
        // Body just returns parameter 0 — only Ret emitted, no Move.
        func.emit(Opcode::Ret { rs: 0 });
        // max_register must be >= 1 (arity - 1) to hold both params.
        assert!(
            func.max_register >= 1,
            "max_register must be >= arity-1 for 2-param function, got {}",
            func.max_register
        );
        // Register file size = max_register + 1 = 2, enough for params r0 and r1.
        assert_eq!((func.max_register as usize) + 1, 2);
    }

    /// Verify zero-arity functions still have max_register = 0.
    #[test]
    fn test_zero_arity_max_register() {
        let func = BytecodeFunction::new("zero_arity".to_string(), 0);
        assert_eq!(func.max_register, 0);
    }

    /// Verify single-arity functions have max_register >= 0.
    #[test]
    fn test_single_arity_max_register() {
        let mut func = BytecodeFunction::new("single_arity".to_string(), 1);
        func.emit(Opcode::Ret { rs: 0 });
        assert_eq!(func.max_register, 0);
    }
}
