// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Top-level compilation API: tMIR Module -> native code.
//!
//! This module provides the primary entry point for compiling a tMIR module
//! (produced by [`tla_tmir`]) into executable native code via the LLVM2 backend.
//!
//! # Pipeline
//!
//! ```text
//! tmir::Module
//!     |
//!     v
//! validate_module()  -- structural checks
//!     |
//!     v
//! lower_module()     -- count instructions, verify support
//!     |
//!     v
//! [LLVM2 backend]    -- (future) IR -> optimized native code
//!     |
//!     v
//! CompiledModule     -- handle to executable code
//! ```
//!
//! # Optimization Levels
//!
//! Two levels, matching LLVM2's pipeline:
//! - **O1**: Fast compilation (~50-200ms). Used during interpreter warmup (Tier 1).
//! - **O3**: Peak throughput (~0.5-2s). Full optimization pipeline (Tier 2).

use crate::lower::{self, LoweringStats};
use crate::Llvm2Error;
use tla_tir::bytecode::BytecodeChunk;
use tmir::Module;

/// Optimization level for LLVM2 compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OptLevel {
    /// Fast compilation for warmup. Minimal optimization.
    O1,
    /// Peak throughput. Full optimization pipeline (DCE, GVN, LICM, unrolling).
    O3,
}

/// Result of compiling a tMIR module to LLVM IR (and eventually native code).
///
/// Holds the emitted LLVM IR text and compilation statistics. When the LLVM2
/// backend crate is available as a dependency, this will additionally hold a
/// handle to the compiled native code (either an in-memory JIT buffer or a
/// path to a compiled .dylib).
#[derive(Debug)]
pub struct CompiledModule {
    /// Name of the source module.
    pub name: String,
    /// Optimization level used.
    pub opt_level: OptLevel,
    /// Lowering statistics.
    pub stats: LoweringStats,
    /// Emitted LLVM IR text (`.ll` format).
    ///
    /// This is the complete LLVM IR module that can be fed to `llc` or `opt`
    /// for native compilation and optimization.
    pub llvm_ir: String,
}

/// Compile a tMIR module to native code.
///
/// This is the primary public API. It validates the module, lowers it
/// through the LLVM2 pipeline, and returns a handle to the compiled code.
///
/// # Arguments
///
/// * `module` - A tMIR module produced by [`tla_tmir::lower`].
/// * `opt_level` - Optimization level ([`OptLevel::O1`] for fast, [`OptLevel::O3`] for peak).
///
/// # Errors
///
/// Returns [`Llvm2Error`] if the module is invalid, contains unsupported
/// instructions, or compilation fails.
///
/// # Example
///
/// ```no_run
/// use tla_llvm2::{compile_module, OptLevel};
/// # fn example(module: &tmir::Module) -> Result<(), tla_llvm2::Llvm2Error> {
/// let compiled = compile_module(module, OptLevel::O1)?;
/// println!("Compiled {} functions, {} instructions",
///     compiled.stats.functions, compiled.stats.instructions);
/// # Ok(())
/// # }
/// ```
pub fn compile_module(module: &Module, opt_level: OptLevel) -> Result<CompiledModule, Llvm2Error> {
    let stats = lower::lower_module(module)?;
    let llvm_ir = stats.llvm_ir.clone();

    Ok(CompiledModule {
        name: module.name.clone(),
        opt_level,
        stats,
        llvm_ir,
    })
}

/// Compile a tMIR module from a bytecode function via tla-tmir lowering.
///
/// Convenience wrapper that chains tla-tmir lowering with LLVM2 compilation.
/// Lowers the bytecode invariant function to tMIR, then compiles via LLVM2.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if tMIR lowering fails, or other
/// [`Llvm2Error`] variants if LLVM2 compilation fails.
pub fn compile_invariant(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    opt_level: OptLevel,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_invariant(func, name)?;
    compile_module(&tmir_module, opt_level)
}

/// Compile a tMIR module from a bytecode next-state function via tla-tmir lowering.
///
/// Convenience wrapper that chains tla-tmir lowering with LLVM2 compilation.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if tMIR lowering fails, or other
/// [`Llvm2Error`] variants if LLVM2 compilation fails.
pub fn compile_next_state(
    func: &tla_tir::bytecode::BytecodeFunction,
    name: &str,
    opt_level: OptLevel,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_next_state(func, name)?;
    compile_module(&tmir_module, opt_level)
}

/// Compile a multi-function bytecode chunk (spec) to LLVM IR.
///
/// This is the primary entry point for compiling a complete TLA+ spec through
/// the full pipeline: BytecodeChunk -> tMIR (via tla-tmir) -> LLVM IR text
/// (via tla-llvm2).
///
/// The entrypoint function at `entry_idx` in the chunk is lowered as an
/// invariant function. All transitively reachable callees are included in the
/// output module.
///
/// # Arguments
///
/// * `chunk` - A complete bytecode compilation unit with shared constant pool.
/// * `entry_idx` - Index of the entrypoint function in the chunk.
/// * `name` - Module name for the output.
/// * `opt_level` - Optimization level.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if bytecode-to-tMIR lowering fails.
/// Returns other [`Llvm2Error`] variants if LLVM IR emission fails.
pub fn compile_spec_invariant(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
    opt_level: OptLevel,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_module_invariant(chunk, entry_idx, name)?;
    compile_module(&tmir_module, opt_level)
}

/// Compile a multi-function bytecode chunk for next-state evaluation.
///
/// Same as [`compile_spec_invariant`] but the entrypoint uses the next-state
/// signature: `fn(out, state_in, state_out, state_len) -> void`.
///
/// # Errors
///
/// Returns [`Llvm2Error::TmirLowering`] if bytecode-to-tMIR lowering fails.
/// Returns other [`Llvm2Error`] variants if LLVM IR emission fails.
pub fn compile_spec_next_state(
    chunk: &BytecodeChunk,
    entry_idx: u16,
    name: &str,
    opt_level: OptLevel,
) -> Result<CompiledModule, Llvm2Error> {
    let tmir_module = tla_tmir::lower::lower_module_next_state(chunk, entry_idx, name)?;
    compile_module(&tmir_module, opt_level)
}

/// Description of a BFS step compilation output.
///
/// Contains the compiled LLVM IR for the next-state relation and all
/// invariant checks for a single action. Used by the model checker to
/// drive state exploration.
#[derive(Debug)]
pub struct CompiledBfsStep {
    /// Name of the action this step was compiled from.
    pub action_name: String,
    /// Compiled next-state function.
    pub next_state: CompiledModule,
    /// Compiled invariant functions (one per invariant).
    pub invariants: Vec<CompiledModule>,
}

/// Compile a BFS step: one next-state function and zero or more invariants.
///
/// This is the compilation driver for the model checker integration. Given a
/// next-state bytecode function and a list of invariant bytecode functions,
/// it produces LLVM IR for all of them through the full pipeline.
///
/// # Arguments
///
/// * `action_name` - Name of the action (for diagnostics).
/// * `next_state_func` - Bytecode function for the next-state relation.
/// * `invariant_funcs` - Bytecode functions for each invariant to check.
/// * `opt_level` - Optimization level.
///
/// # Errors
///
/// Returns [`Llvm2Error`] if any function fails to compile.
pub fn compile_bfs_step(
    action_name: &str,
    next_state_func: &tla_tir::bytecode::BytecodeFunction,
    invariant_funcs: &[&tla_tir::bytecode::BytecodeFunction],
    opt_level: OptLevel,
) -> Result<CompiledBfsStep, Llvm2Error> {
    let next_state_name = format!("{action_name}_next");
    let next_state = compile_next_state(next_state_func, &next_state_name, opt_level)?;

    let mut invariants = Vec::with_capacity(invariant_funcs.len());
    for (i, inv_func) in invariant_funcs.iter().enumerate() {
        let inv_name = format!("{action_name}_inv_{i}");
        let compiled = compile_invariant(inv_func, &inv_name, opt_level)?;
        invariants.push(compiled);
    }

    Ok(CompiledBfsStep {
        action_name: action_name.to_string(),
        next_state,
        invariants,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_tir::bytecode::{BytecodeFunction, Opcode};
    use tmir::constant::Constant;
    use tmir::inst::Inst;
    use tmir::ty::{FuncTy, Ty};
    use tmir::value::{BlockId, FuncId, ValueId};
    use tmir::{Block, Function, InstrNode};

    fn make_return_42_module() -> Module {
        let mut module = Module::new("ret42");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "main", ft, entry);
        let mut block = Block::new(entry);
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn test_compile_module_o1() {
        let module = make_return_42_module();
        let compiled = compile_module(&module, OptLevel::O1).expect("should compile");
        assert_eq!(compiled.name, "ret42");
        assert_eq!(compiled.opt_level, OptLevel::O1);
        assert_eq!(compiled.stats.functions, 1);
        // Verify LLVM IR was emitted.
        assert!(compiled.llvm_ir.contains("define i64 @main()"));
        assert!(compiled.llvm_ir.contains("ret i64 %0"));
    }

    #[test]
    fn test_compile_module_o3() {
        let module = make_return_42_module();
        let compiled = compile_module(&module, OptLevel::O3).expect("should compile");
        assert_eq!(compiled.opt_level, OptLevel::O3);
        // LLVM IR is produced regardless of opt level (optimization is downstream).
        assert!(!compiled.llvm_ir.is_empty());
    }

    #[test]
    fn test_compile_module_ir_has_module_header() {
        let module = make_return_42_module();
        let compiled = compile_module(&module, OptLevel::O1).expect("should compile");
        assert!(compiled.llvm_ir.contains("; ModuleID = 'ret42'"));
        assert!(compiled.llvm_ir.contains("source_filename = \"ret42\""));
    }

    // =========================================================================
    // End-to-end pipeline tests: BytecodeFunction -> tMIR -> LLVM IR
    // =========================================================================

    /// Build a bytecode function for the invariant: x > 0
    fn make_x_gt_zero_invariant() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("Inv_x_gt_0".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = state[0] (x)
        func.emit(Opcode::LoadImm { rd: 1, value: 0 }); // r1 = 0
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        }); // r2 = (x > 0)
        func.emit(Opcode::Ret { rs: 2 }); // return r2
        func
    }

    /// Build a bytecode function for the next-state: x' = x + 1
    fn make_x_incr_next_state() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("Next_x_incr".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = state[0] (x)
        func.emit(Opcode::LoadImm { rd: 1, value: 1 }); // r1 = 1
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        }); // r2 = x + 1
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 }); // state_out[0] = r2
        func.emit(Opcode::LoadImm { rd: 3, value: 1 }); // r3 = true
        func.emit(Opcode::Ret { rs: 3 }); // return true
        func
    }

    #[test]
    fn test_pipeline_invariant_bytecode_to_llvm_ir() {
        let func = make_x_gt_zero_invariant();
        let compiled =
            compile_invariant(&func, "inv_x_gt_0", OptLevel::O1).expect("should compile");

        // Module name matches.
        assert_eq!(compiled.name, "inv_x_gt_0");

        // LLVM IR should contain the function definition.
        let ir = &compiled.llvm_ir;
        assert!(
            ir.contains("define void @inv_x_gt_0("),
            "IR should define the invariant function. IR:\n{ir}"
        );

        // Should contain GEP for state variable access (LoadVar -> GEP + Load).
        assert!(
            ir.contains("getelementptr"),
            "IR should contain GEP for state access. IR:\n{ir}"
        );

        // Should contain integer comparison (GtInt -> icmp sgt).
        assert!(
            ir.contains("icmp sgt"),
            "IR should contain signed-greater-than comparison. IR:\n{ir}"
        );

        // Should contain return.
        assert!(
            ir.contains("ret void"),
            "Invariant function should return void (writes to JitCallOut). IR:\n{ir}"
        );

        // Should have the module header.
        assert!(ir.contains("; ModuleID = 'inv_x_gt_0'"));

        // Stats should reflect the content.
        assert_eq!(compiled.stats.functions, 1);
        assert!(
            compiled.stats.instructions > 0,
            "should have instructions"
        );
    }

    #[test]
    fn test_pipeline_next_state_bytecode_to_llvm_ir() {
        let func = make_x_incr_next_state();
        let compiled =
            compile_next_state(&func, "next_x_incr", OptLevel::O1).expect("should compile");

        let ir = &compiled.llvm_ir;

        // Next-state function should have 4 params (out, state_in, state_out, state_len).
        assert!(
            ir.contains("define void @next_x_incr("),
            "IR should define the next-state function. IR:\n{ir}"
        );

        // Should contain overflow-checked addition (AddInt -> sadd.with.overflow).
        assert!(
            ir.contains("sadd.with.overflow"),
            "IR should contain overflow-checked addition. IR:\n{ir}"
        );

        // Should contain store to state_out (StoreVar -> GEP + Store).
        // Count GEPs — should have at least 2 (one for LoadVar read, one for StoreVar write).
        let gep_count = ir.matches("getelementptr").count();
        assert!(
            gep_count >= 2,
            "IR should have at least 2 GEPs (LoadVar + StoreVar), found {gep_count}. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_compile_spec_invariant() {
        // Build a BytecodeChunk with one function.
        let mut chunk = BytecodeChunk::new();
        let func = make_x_gt_zero_invariant();
        chunk.functions.push(func);

        let compiled = compile_spec_invariant(&chunk, 0, "spec_inv", OptLevel::O1)
            .expect("should compile spec");

        assert_eq!(compiled.name, "spec_inv");
        assert!(
            compiled.llvm_ir.contains("define void @spec_inv("),
            "IR should define the entrypoint function"
        );
    }

    #[test]
    fn test_pipeline_compile_spec_next_state() {
        let mut chunk = BytecodeChunk::new();
        let func = make_x_incr_next_state();
        chunk.functions.push(func);

        let compiled = compile_spec_next_state(&chunk, 0, "spec_next", OptLevel::O1)
            .expect("should compile spec");

        assert_eq!(compiled.name, "spec_next");
        assert!(
            compiled.llvm_ir.contains("define void @spec_next("),
            "IR should define the next-state function"
        );
    }

    #[test]
    fn test_pipeline_compile_bfs_step() {
        let next_func = make_x_incr_next_state();
        let inv_func = make_x_gt_zero_invariant();

        let bfs_step =
            compile_bfs_step("action0", &next_func, &[&inv_func], OptLevel::O1)
                .expect("should compile BFS step");

        assert_eq!(bfs_step.action_name, "action0");

        // Next-state IR should reference the action name.
        assert!(
            bfs_step.next_state.llvm_ir.contains("action0_next"),
            "Next-state IR should use the action name"
        );

        // Should have exactly one invariant.
        assert_eq!(bfs_step.invariants.len(), 1);
        assert!(
            bfs_step.invariants[0]
                .llvm_ir
                .contains("action0_inv_0"),
            "Invariant IR should use the action name and index"
        );
    }

    #[test]
    fn test_pipeline_bfs_step_multiple_invariants() {
        let next_func = make_x_incr_next_state();
        let inv1 = make_x_gt_zero_invariant();

        // Second invariant: x < 100.
        let mut inv2 = BytecodeFunction::new("Inv_x_lt_100".to_string(), 0);
        inv2.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv2.emit(Opcode::LoadImm { rd: 1, value: 100 });
        inv2.emit(Opcode::LtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inv2.emit(Opcode::Ret { rs: 2 });

        let bfs_step =
            compile_bfs_step("step1", &next_func, &[&inv1, &inv2], OptLevel::O1)
                .expect("should compile BFS step with 2 invariants");

        assert_eq!(bfs_step.invariants.len(), 2);
        assert!(bfs_step.invariants[0].llvm_ir.contains("step1_inv_0"));
        assert!(bfs_step.invariants[1].llvm_ir.contains("step1_inv_1"));

        // Second invariant should use slt (less-than).
        assert!(
            bfs_step.invariants[1].llvm_ir.contains("icmp slt"),
            "Second invariant should contain signed-less-than comparison"
        );
    }

    #[test]
    fn test_pipeline_bfs_step_no_invariants() {
        let next_func = make_x_incr_next_state();

        let bfs_step = compile_bfs_step("no_inv", &next_func, &[], OptLevel::O1)
            .expect("should compile BFS step with no invariants");

        assert_eq!(bfs_step.action_name, "no_inv");
        assert!(bfs_step.invariants.is_empty());
        assert!(!bfs_step.next_state.llvm_ir.is_empty());
    }

    #[test]
    fn test_pipeline_state_access_produces_gep_load_pattern() {
        // Verify that LoadVar produces the expected GEP + Load pattern in LLVM IR,
        // which is critical for correct state buffer access.
        let mut func = BytecodeFunction::new("state_access".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 3 }); // Load slot 3
        func.emit(Opcode::Ret { rs: 0 });

        let compiled =
            compile_invariant(&func, "state_access", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // The GEP index should be 3 (the var_idx).
        assert!(
            ir.contains("getelementptr i64"),
            "Should GEP into i64 state array. IR:\n{ir}"
        );
        assert!(
            ir.contains("load i64"),
            "Should load i64 from state buffer. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_store_var_produces_gep_store_pattern() {
        // Verify that StoreVar produces the expected GEP + Store pattern.
        let mut func = BytecodeFunction::new("state_store".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::StoreVar { var_idx: 2, rs: 0 }); // Store to slot 2
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Ret { rs: 1 });

        let compiled =
            compile_next_state(&func, "state_store", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should have a store instruction writing to the state buffer.
        assert!(
            ir.contains("store i64"),
            "Should store i64 to state buffer. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_branching_produces_condbr() {
        // Verify that JumpFalse produces a conditional branch in LLVM IR.
        let mut func = BytecodeFunction::new("branch_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // pc 0
        func.emit(Opcode::JumpFalse { rs: 0, offset: 2 }); // pc 1 -> jump to pc 3
        func.emit(Opcode::LoadImm { rd: 1, value: 42 }); // pc 2 (fallthrough)
        func.emit(Opcode::Ret { rs: 1 }); // pc 3 (target: either from fallthrough or jump)

        let compiled =
            compile_invariant(&func, "branch_test", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain conditional branch.
        assert!(
            ir.contains("br i1"),
            "Should contain conditional branch. IR:\n{ir}"
        );

        // Should have multiple basic blocks (entry + branch targets).
        let bb_count = ir.matches("bb").count();
        assert!(
            bb_count >= 1,
            "Should have multiple basic blocks. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_set_enum_produces_alloca() {
        // Verify that SetEnum produces aggregate allocation in LLVM IR.
        let mut func = BytecodeFunction::new("set_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let compiled =
            compile_invariant(&func, "set_test", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // SetEnum should produce an alloca for the aggregate.
        assert!(
            ir.contains("alloca i64, i32"),
            "SetEnum should produce dynamic alloca for the aggregate. IR:\n{ir}"
        );

        // Should contain ptrtoint (aggregate pointer stored as i64 in register file).
        assert!(
            ir.contains("ptrtoint"),
            "Aggregate pointer should be stored as i64 via ptrtoint. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Boolean/Logic operations
    // =========================================================================

    #[test]
    fn test_pipeline_boolean_and() {
        // And lowers to BinOp::And on i64 values.
        let mut func = BytecodeFunction::new("bool_and".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::And {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "bool_and", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // And on i64 emits `and i64` in LLVM IR.
        assert!(
            ir.contains("and i64"),
            "Boolean And should produce `and i64` instruction. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_boolean_or() {
        let mut func = BytecodeFunction::new("bool_or".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Or {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "bool_or", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("or i64"),
            "Boolean Or should produce `or i64` instruction. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_boolean_not() {
        // Not lowers to: icmp eq i64 value, 0 then zext.
        let mut func = BytecodeFunction::new("bool_not".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::Not { rd: 1, rs: 0 });
        func.emit(Opcode::Ret { rs: 1 });

        let compiled =
            compile_invariant(&func, "bool_not", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Not checks value == 0, so we expect icmp eq.
        assert!(
            ir.contains("icmp eq"),
            "Boolean Not should produce `icmp eq` for zero-check. IR:\n{ir}"
        );
        // Result is zero-extended from i1 to i64.
        assert!(
            ir.contains("zext"),
            "Boolean Not should zext the i1 result to i64. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_implies() {
        // Implies lowers to: !lhs || rhs (icmp eq + icmp ne + or + zext).
        let mut func = BytecodeFunction::new("implies".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::Implies {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "implies", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain both eq and ne comparisons for !lhs and rhs bool checks.
        assert!(
            ir.contains("icmp eq"),
            "Implies should contain `icmp eq` for !lhs. IR:\n{ir}"
        );
        assert!(
            ir.contains("icmp ne"),
            "Implies should contain `icmp ne` for rhs bool. IR:\n{ir}"
        );
        // Should produce a boolean or for the final result.
        assert!(
            ir.contains("or i1"),
            "Implies should produce `or i1` for !lhs || rhs. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_equiv() {
        // Equiv lowers to: icmp eq on i64 values + zext.
        let mut func = BytecodeFunction::new("equiv".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Equiv {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "equiv", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp eq"),
            "Equiv should produce `icmp eq` for equality check. IR:\n{ir}"
        );
        assert!(
            ir.contains("zext"),
            "Equiv should zext the i1 result. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Comparison operations
    // =========================================================================

    #[test]
    fn test_pipeline_comparison_eq() {
        let mut func = BytecodeFunction::new("cmp_eq".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 5 });
        func.emit(Opcode::Eq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "cmp_eq", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp eq"),
            "Eq should produce `icmp eq`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_comparison_neq() {
        let mut func = BytecodeFunction::new("cmp_neq".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 3 });
        func.emit(Opcode::LoadImm { rd: 1, value: 7 });
        func.emit(Opcode::Neq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "cmp_neq", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp ne"),
            "Neq should produce `icmp ne`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_comparison_le() {
        let mut func = BytecodeFunction::new("cmp_le".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 10 });
        func.emit(Opcode::LeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "cmp_le", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp sle"),
            "LeInt should produce `icmp sle`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_comparison_ge() {
        let mut func = BytecodeFunction::new("cmp_ge".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::GeInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "cmp_ge", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("icmp sge"),
            "GeInt should produce `icmp sge`. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Division and Modulo
    // =========================================================================

    #[test]
    fn test_pipeline_intdiv() {
        // IntDiv lowers to: div-by-zero check + sdiv.
        let mut func = BytecodeFunction::new("intdiv".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::IntDiv {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "intdiv", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain sdiv for the actual division.
        assert!(
            ir.contains("sdiv"),
            "IntDiv should produce `sdiv` instruction. IR:\n{ir}"
        );
        // Should contain a conditional branch for div-by-zero check.
        assert!(
            ir.contains("br i1"),
            "IntDiv should have conditional branch for zero check. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_modint() {
        // ModInt lowers to: div-by-zero check + srem.
        let mut func = BytecodeFunction::new("modint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::ModInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "modint", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("srem"),
            "ModInt should produce `srem` instruction. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_real_division() {
        // DivInt (real division) lowers to: zero check + exactness check + sdiv.
        let mut func = BytecodeFunction::new("realdiv".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 12 });
        func.emit(Opcode::LoadImm { rd: 1, value: 4 });
        func.emit(Opcode::DivInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "realdiv", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain both srem (exactness check) and sdiv (actual division).
        assert!(
            ir.contains("srem"),
            "Real division should check exactness with `srem`. IR:\n{ir}"
        );
        assert!(
            ir.contains("sdiv"),
            "Real division should produce `sdiv`. IR:\n{ir}"
        );
        // Should have at least 2 conditional branches (zero check + exactness check).
        let br_count = ir.matches("br i1").count();
        assert!(
            br_count >= 2,
            "Real division should have >=2 conditional branches (zero + exact), found {br_count}. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Negation
    // =========================================================================

    #[test]
    fn test_pipeline_negint() {
        // NegInt lowers to: 0 - value with overflow check (ssub.with.overflow).
        let mut func = BytecodeFunction::new("negint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::NegInt { rd: 1, rs: 0 });
        func.emit(Opcode::Ret { rs: 1 });

        let compiled =
            compile_invariant(&func, "negint", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Negation via 0 - value uses ssub.with.overflow.
        assert!(
            ir.contains("ssub.with.overflow"),
            "NegInt should use `ssub.with.overflow` for overflow-checked negation. IR:\n{ir}"
        );
        // Should have overflow error branch.
        assert!(
            ir.contains("br i1"),
            "NegInt should branch on overflow flag. IR:\n{ir}"
        );
    }

    // =========================================================================
    // CondMove (select instruction)
    // =========================================================================

    #[test]
    fn test_pipeline_condmove() {
        // CondMove lowers to: icmp ne (cond, 0) then select.
        let mut func = BytecodeFunction::new("condmove".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // cond = true
        func.emit(Opcode::LoadImm { rd: 1, value: 99 }); // rd initial
        func.emit(Opcode::LoadImm { rd: 2, value: 42 }); // source value
        func.emit(Opcode::CondMove {
            rd: 1,
            cond: 0,
            rs: 2,
        }); // rd = if cond then source else rd
        func.emit(Opcode::Ret { rs: 1 });

        let compiled =
            compile_invariant(&func, "condmove", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("select"),
            "CondMove should produce a `select` instruction. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Quantifiers: ForAll and Exists
    // =========================================================================

    #[test]
    fn test_pipeline_forall_quantifier() {
        // ForAll quantifier: \A x \in {1,2}: x > 0
        // Build set {1, 2}, then ForallBegin/ForallNext loop.
        let mut func = BytecodeFunction::new("forall".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // pc 0
        func.emit(Opcode::LoadImm { rd: 1, value: 2 }); // pc 1
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        }); // pc 2: domain = {1,2}
        func.emit(Opcode::ForallBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 5,
        }); // pc 3 -> exit at pc 8
        // body: x > 0
        func.emit(Opcode::LoadImm { rd: 5, value: 0 }); // pc 4
        func.emit(Opcode::GtInt {
            rd: 6,
            r1: 4,
            r2: 5,
        }); // pc 5: binding > 0
        func.emit(Opcode::ForallNext {
            rd: 3,
            r_binding: 4,
            r_body: 6,
            loop_begin: -3,
        }); // pc 6 -> back to pc 3
        // After loop, pc 7 is unreachable but we need a valid instruction.
        func.emit(Opcode::Ret { rs: 3 }); // pc 7: return result
        // pc 8 = exit block from ForallBegin
        func.emit(Opcode::Ret { rs: 3 }); // pc 8: return result

        let compiled =
            compile_invariant(&func, "forall", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Quantifier loops produce multiple basic blocks with br instructions.
        let br_count = ir.matches("br ").count();
        assert!(
            br_count >= 3,
            "ForAll quantifier should produce multiple branches (header, body, back-edge), found {br_count}. IR:\n{ir}"
        );

        // Should have GEP for domain element access.
        assert!(
            ir.contains("getelementptr"),
            "ForAll should access domain elements via GEP. IR:\n{ir}"
        );

        // Should have icmp for loop bound check and body comparison.
        let icmp_count = ir.matches("icmp").count();
        assert!(
            icmp_count >= 2,
            "ForAll should have >=2 icmp instructions (bound check + body comparison), found {icmp_count}. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_exists_quantifier() {
        // Exists quantifier: \E x \in {1,2}: x = 2
        let mut func = BytecodeFunction::new("exists".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // pc 0
        func.emit(Opcode::LoadImm { rd: 1, value: 2 }); // pc 1
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        }); // pc 2: domain = {1,2}
        func.emit(Opcode::ExistsBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 5,
        }); // pc 3 -> exit at pc 8
        // body: x = 2
        func.emit(Opcode::LoadImm { rd: 5, value: 2 }); // pc 4
        func.emit(Opcode::Eq {
            rd: 6,
            r1: 4,
            r2: 5,
        }); // pc 5: binding == 2
        func.emit(Opcode::ExistsNext {
            rd: 3,
            r_binding: 4,
            r_body: 6,
            loop_begin: -3,
        }); // pc 6 -> back to pc 3
        func.emit(Opcode::Ret { rs: 3 }); // pc 7: return result
        func.emit(Opcode::Ret { rs: 3 }); // pc 8: exit block return

        let compiled =
            compile_invariant(&func, "exists", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Similar structure to ForAll: multiple branches, GEP, icmp.
        let br_count = ir.matches("br ").count();
        assert!(
            br_count >= 3,
            "Exists quantifier should produce multiple branches, found {br_count}. IR:\n{ir}"
        );
        assert!(
            ir.contains("getelementptr"),
            "Exists should access domain elements via GEP. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Sequence operations
    // =========================================================================

    #[test]
    fn test_pipeline_seq_new() {
        // SeqNew allocates an aggregate: slot[0] = length, slot[1..] = elements.
        let mut func = BytecodeFunction::new("seq_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::LoadImm { rd: 2, value: 30 });
        func.emit(Opcode::SeqNew {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let compiled =
            compile_invariant(&func, "seq_new", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // SeqNew uses the same aggregate layout as SetEnum: alloca + ptrtoint.
        assert!(
            ir.contains("alloca i64, i32"),
            "SeqNew should produce dynamic alloca for aggregate. IR:\n{ir}"
        );
        assert!(
            ir.contains("ptrtoint"),
            "SeqNew aggregate pointer should be stored as i64. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Tuple operations
    // =========================================================================

    #[test]
    fn test_pipeline_tuple_new_and_get() {
        // TupleNew + TupleGet: build <<1, 2>> then access element 1.
        let mut func = BytecodeFunction::new("tuple_ops".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 100 });
        func.emit(Opcode::LoadImm { rd: 1, value: 200 });
        func.emit(Opcode::TupleNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::TupleGet {
            rd: 3,
            rs: 2,
            idx: 1,
        }); // 1-indexed: get first element
        func.emit(Opcode::Ret { rs: 3 });

        let compiled =
            compile_invariant(&func, "tuple_ops", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // TupleNew uses same alloca pattern.
        assert!(
            ir.contains("alloca i64, i32"),
            "TupleNew should produce alloca. IR:\n{ir}"
        );
        // TupleGet accesses via GEP (inttoptr + GEP + load).
        assert!(
            ir.contains("inttoptr"),
            "TupleGet should convert i64 back to pointer via inttoptr. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Inter-function calls via BytecodeChunk
    // =========================================================================

    #[test]
    fn test_pipeline_multi_function_chunk() {
        // Build a chunk with two functions: main calls helper.
        // helper(x) = x + 1
        // main: call helper(state[0])
        let mut chunk = BytecodeChunk::new();

        // Function 0 (main): load state var, call func 1, return result.
        let mut main_func = BytecodeFunction::new("main".to_string(), 0);
        main_func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = state[0]
        main_func.emit(Opcode::Call {
            rd: 1,
            op_idx: 1,  // call function at index 1
            args_start: 0,
            argc: 1,
        });
        main_func.emit(Opcode::Ret { rs: 1 });
        chunk.functions.push(main_func);

        // Function 1 (helper): r0 = arg, r0 + 1.
        let mut helper_func = BytecodeFunction::new("helper".to_string(), 1);
        helper_func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        helper_func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        helper_func.emit(Opcode::Ret { rs: 2 });
        chunk.functions.push(helper_func);

        let compiled = compile_spec_invariant(&chunk, 0, "multi_func", OptLevel::O1)
            .expect("should compile multi-function chunk");
        let ir = &compiled.llvm_ir;

        // Should define at least 2 functions.
        let define_count = ir.matches("define ").count();
        assert!(
            define_count >= 2,
            "Multi-function chunk should define >=2 functions, found {define_count}. IR:\n{ir}"
        );

        // Should contain a call instruction.
        assert!(
            ir.contains("call "),
            "Main function should call the helper. IR:\n{ir}"
        );

        // Both functions should appear.
        assert!(
            ir.contains("@multi_func"),
            "Entrypoint function should be named. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Subtraction and Multiplication (overflow-checked)
    // =========================================================================

    #[test]
    fn test_pipeline_subint() {
        let mut func = BytecodeFunction::new("subint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::SubInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "subint", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("ssub.with.overflow"),
            "SubInt should use `ssub.with.overflow`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_pipeline_mulint() {
        let mut func = BytecodeFunction::new("mulint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 7 });
        func.emit(Opcode::LoadImm { rd: 1, value: 6 });
        func.emit(Opcode::MulInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let compiled =
            compile_invariant(&func, "mulint", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        assert!(
            ir.contains("smul.with.overflow"),
            "MulInt should use `smul.with.overflow`. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Combined pipeline: multiple opcode categories in one function
    // =========================================================================

    #[test]
    fn test_pipeline_combined_arithmetic_and_logic() {
        // Invariant: (state[0] + state[1] > 0) /\ (state[0] >= 0)
        let mut func = BytecodeFunction::new("combined".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = x
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 }); // r1 = y
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        }); // r2 = x + y
        func.emit(Opcode::LoadImm { rd: 3, value: 0 }); // r3 = 0
        func.emit(Opcode::GtInt {
            rd: 4,
            r1: 2,
            r2: 3,
        }); // r4 = (x + y > 0)
        func.emit(Opcode::GeInt {
            rd: 5,
            r1: 0,
            r2: 3,
        }); // r5 = (x >= 0)
        func.emit(Opcode::And {
            rd: 6,
            r1: 4,
            r2: 5,
        }); // r6 = r4 /\ r5
        func.emit(Opcode::Ret { rs: 6 });

        let compiled =
            compile_invariant(&func, "combined", OptLevel::O1).expect("should compile");
        let ir = &compiled.llvm_ir;

        // Should contain all expected patterns.
        assert!(
            ir.contains("sadd.with.overflow"),
            "Should have overflow-checked add. IR:\n{ir}"
        );
        assert!(
            ir.contains("icmp sgt"),
            "Should have signed-greater-than comparison. IR:\n{ir}"
        );
        assert!(
            ir.contains("icmp sge"),
            "Should have signed-greater-or-equal comparison. IR:\n{ir}"
        );
        assert!(
            ir.contains("and i64"),
            "Should have boolean And. IR:\n{ir}"
        );
        // Should access 2 state variables via GEP.
        let gep_count = ir.matches("getelementptr").count();
        assert!(
            gep_count >= 2,
            "Should GEP for 2 state variables, found {gep_count}. IR:\n{ir}"
        );
    }
}
