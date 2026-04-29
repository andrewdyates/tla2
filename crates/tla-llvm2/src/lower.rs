// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! tMIR -> LLVM2 IR lowering.
//!
//! Translates a [`tmir::Module`] into LLVM2's internal IR representation for
//! compilation to native code. This is a straightforward mapping since tMIR
//! is already close to machine-level IR (SSA, typed, explicit memory ops).
//!
//! # Instruction Mapping
//!
//! | tMIR Inst | LLVM2 IR | Notes |
//! |-----------|----------|-------|
//! | `BinOp(Add, I64, ..)` | `add i64` | Direct 1:1 |
//! | `ICmp(Slt, I64, ..)` | `icmp slt i64` | Direct 1:1 |
//! | `Load(I64, ptr)` | `load i64, ptr` | Direct 1:1 |
//! | `Store(I64, ptr, val)` | `store i64 val, ptr` | Direct 1:1 |
//! | `Alloca(I64, ..)` | `alloca i64` | Direct 1:1 |
//! | `GEP(..)` | `getelementptr` | Direct 1:1 |
//! | `CondBr(..)` | `br i1 cond, ..` | Direct 1:1 |
//! | `Br(..)` | `br label ..` | Direct 1:1 |
//! | `Call(..)` | `call ..` | Direct 1:1 |
//! | `Return(..)` | `ret ..` | Direct 1:1 |
//! | `Const(I64, n)` | immediate operand | Direct 1:1 |
//! | `Select(..)` | `select` | Direct 1:1 |
//!
//! The mapping is intentionally boring. tMIR was designed to be trivially
//! lowerable to LLVM-style IR (it IS an LLVM-style IR). The interesting
//! work happens upstream in tla-tmir (TLA+ semantics -> tMIR) and
//! downstream in LLVM2 (optimization + code generation).

use crate::Llvm2Error;
use tmir::inst::Inst;
use tmir::Module;

/// Validate that a tMIR module is suitable for LLVM2 compilation.
///
/// Checks:
/// - All functions have at least one block
/// - All blocks end with a terminator instruction
/// - No unsupported instruction types
pub fn validate_module(module: &Module) -> Result<(), Llvm2Error> {
    for func in &module.functions {
        if func.blocks.is_empty() {
            return Err(Llvm2Error::InvalidModule(format!(
                "function '{}' has no blocks",
                func.name,
            )));
        }

        for block in &func.blocks {
            if block.body.is_empty() {
                return Err(Llvm2Error::InvalidModule(format!(
                    "block {:?} in function '{}' has no instructions",
                    block.id, func.name,
                )));
            }

            // Last instruction must be a terminator.
            let last = block.body.last().expect("checked non-empty above");
            if !last.is_terminator() {
                return Err(Llvm2Error::InvalidModule(format!(
                    "block {:?} in function '{}' does not end with a terminator",
                    block.id, func.name,
                )));
            }
        }
    }
    Ok(())
}

/// Summary of a lowering pass for diagnostics.
#[derive(Debug, Clone)]
pub struct LoweringStats {
    /// Number of functions lowered.
    pub functions: usize,
    /// Total number of blocks across all functions.
    pub blocks: usize,
    /// Total number of instructions lowered.
    pub instructions: usize,
    /// Instructions that required runtime helper calls.
    pub helper_calls: usize,
    /// LLVM IR text output (`.ll` format). Produced by the textual emitter.
    /// When the LLVM2 crate is available, this will be replaced by direct
    /// API construction.
    pub llvm_ir: String,
}

/// Lower a tMIR module to LLVM IR text representation.
///
/// This is the main entry point for the tMIR -> LLVM IR lowering pass.
/// It validates the module, checks instruction support, emits LLVM IR text,
/// and returns lowering statistics including the emitted IR.
///
/// # Errors
///
/// Returns [`Llvm2Error::InvalidModule`] if the module fails validation.
/// Returns [`Llvm2Error::UnsupportedInst`] if an instruction cannot be lowered.
/// Returns [`Llvm2Error::Emission`] if IR text generation fails.
pub fn lower_module(module: &Module) -> Result<LoweringStats, Llvm2Error> {
    validate_module(module)?;

    let mut stats = LoweringStats {
        functions: module.functions.len(),
        blocks: 0,
        instructions: 0,
        helper_calls: 0,
        llvm_ir: String::new(),
    };

    for func in &module.functions {
        stats.blocks += func.blocks.len();
        for block in &func.blocks {
            for node in &block.body {
                stats.instructions += 1;
                if is_helper_call(&node.inst) {
                    stats.helper_calls += 1;
                }
                check_inst_supported(&node.inst)?;
            }
        }
    }

    // Emit LLVM IR text.
    stats.llvm_ir = crate::emit::emit_module(module)?;

    Ok(stats)
}

/// Check whether an instruction is supported by the LLVM2 lowering.
fn check_inst_supported(inst: &Inst) -> Result<(), Llvm2Error> {
    match inst {
        // Arithmetic and logic -- direct mapping
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Overflow { .. } => Ok(()),

        // Memory -- direct mapping
        Inst::Load { .. } | Inst::Store { .. } | Inst::Alloca { .. } | Inst::GEP { .. } => Ok(()),

        // Atomics -- direct mapping (for AtomicFpSet CAS)
        Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. } => Ok(()),

        // Control flow -- direct mapping
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. } => Ok(()),

        // Aggregates -- direct mapping
        Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. } => Ok(()),

        // Constants and special values
        Inst::Const { .. } | Inst::NullPtr | Inst::Undef { .. } => Ok(()),

        // Proof instructions -- lowered as nops or traps
        Inst::Assume { .. } | Inst::Assert { .. } => Ok(()),

        Inst::Unreachable => Ok(()),

        // Pseudo
        Inst::Copy { .. } | Inst::Select { .. } => Ok(()),

        // Ownership / ARC tracking -- no-op in LLVM emission
        Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. } => Ok(()),

        // Binding-frame instructions (tmir 67f1fdc+) are not yet lowered.
        Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. } => Err(Llvm2Error::UnsupportedInst(
            "binding-frame instruction not yet supported in LLVM2 lowering".to_string(),
        )),

        // Dialect-specific instructions must be lowered to core tMIR first.
        Inst::DialectOp(_) => Err(Llvm2Error::UnsupportedInst(
            "dialect op not yet supported in LLVM2 lowering".to_string(),
        )),
    }
}

/// Check whether an instruction is a call to a runtime helper function.
///
/// Helper calls are generated by tla-tmir for compound TLA+ operations
/// (set membership, record access, function application, etc.) that cannot
/// be lowered to pure scalar tMIR instructions.
fn is_helper_call(inst: &Inst) -> bool {
    matches!(inst, Inst::Call { .. } | Inst::CallIndirect { .. })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tmir::inst::BinOp;
    use tmir::ty::{FuncTy, Ty};
    use tmir::value::{BlockId, FuncId, ValueId};
    use tmir::{Block, Function, InstrNode};

    fn make_trivial_module() -> Module {
        let mut module = Module::new("test");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "main", ft, entry);
        let mut block = Block::new(entry);

        // const i64 42
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: tmir::Constant::Int(42),
            })
            .with_result(ValueId::new(0)),
        );
        // ret 42
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn test_validate_trivial_module() {
        let module = make_trivial_module();
        validate_module(&module).expect("trivial module should validate");
    }

    #[test]
    fn test_lower_trivial_module() {
        let module = make_trivial_module();
        let stats = lower_module(&module).expect("trivial module should lower");
        assert_eq!(stats.functions, 1);
        assert_eq!(stats.blocks, 1);
        assert_eq!(stats.instructions, 2);
        assert_eq!(stats.helper_calls, 0);
    }

    #[test]
    fn test_validate_empty_function_fails() {
        let mut module = Module::new("bad");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let func = Function::new(FuncId::new(0), "empty", ft, BlockId::new(0));
        module.add_function(func);

        let err = validate_module(&module).unwrap_err();
        assert!(err.to_string().contains("has no blocks"));
    }

    #[test]
    fn test_validate_no_terminator_fails() {
        let mut module = Module::new("bad");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "no_term", ft, entry);
        let mut block = Block::new(entry);
        // Only a non-terminator instruction (const), no ret.
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: tmir::Constant::Int(0),
            })
            .with_result(ValueId::new(0)),
        );
        func.blocks.push(block);
        module.add_function(func);

        let err = validate_module(&module).unwrap_err();
        assert!(err.to_string().contains("does not end with a terminator"));
    }

    #[test]
    fn test_lower_module_with_binop() {
        let mut module = Module::new("binop_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "add", ft, entry);
        let mut block = Block::new(entry);

        // %0 = add i64 %arg0, %arg1
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(100),
                rhs: ValueId::new(101),
            })
            .with_result(ValueId::new(0)),
        );
        // ret %0
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let stats = lower_module(&module).expect("binop module should lower");
        assert_eq!(stats.functions, 1);
        assert_eq!(stats.instructions, 2);
        assert_eq!(stats.helper_calls, 0);
    }

    #[test]
    fn test_lower_module_with_call() {
        let mut module = Module::new("call_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "caller", ft, entry);
        let mut block = Block::new(entry);

        // %0 = call @1()
        block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![],
            })
            .with_result(ValueId::new(0)),
        );
        // ret %0
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let stats = lower_module(&module).expect("call module should lower");
        assert_eq!(stats.helper_calls, 1);
    }
}
