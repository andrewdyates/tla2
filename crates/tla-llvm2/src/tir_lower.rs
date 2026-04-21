// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct TIR bytecode -> LLVM IR text lowering.
//!
//! This module provides a fast path from TIR bytecode opcodes directly to LLVM
//! IR text, bypassing the intermediate tMIR representation. For scalar
//! operations (arithmetic, comparison, boolean logic), the mapping is
//! straightforward and the extra tMIR layer adds overhead without benefit.
//!
//! # Scope (Phase 1+2+3: Scalar Ops + Control Flow + Set/Seq/Record)
//!
//! Currently handles:
//! - **Value Loading**: LoadImm, LoadBool, LoadConst, Move
//! - **Arithmetic**: AddInt, SubInt, MulInt, IntDiv, ModInt, NegInt (with overflow checks)
//! - **Comparison**: Eq, Neq, LtInt, LeInt, GtInt, GeInt
//! - **Boolean**: And, Or, Not, Implies, Equiv
//! - **Control Flow**: Ret, Jump, JumpTrue, JumpFalse (basic blocks + branches)
//! - **Function Calls**: Call (to user-defined operators, declared as external)
//! - **Set Operations**: SetEnum, SetIn, SetUnion, SetIntersect, SetDiff, Subseteq,
//!   Powerset, BigUnion, Range, KSubset (as runtime function calls)
//! - **Sequence Operations**: SeqNew, Concat (as runtime function calls)
//! - **Tuple Operations**: TupleNew, TupleGet (as runtime function calls)
//! - **Record/Function Ops**: RecordGet, FuncApply, Domain (as runtime function calls)
//! - **Builtins**: CallBuiltin for Len, Head, Tail, Append, SubSeq, Seq,
//!   Cardinality, IsFiniteSet, ToString (as runtime function calls)
//! - **Conditional Move**: CondMove (native LLVM select)
//!
//! Opcodes not in scope (quantifiers, state ops, closures, etc.) return
//! [`Llvm2Error::UnsupportedInst`].
//!
//! # Architecture
//!
//! ```text
//! TIR Opcode stream (BytecodeFunction)
//!     |  (tir_lower: THIS MODULE)
//!     v
//! LLVM IR text (.ll)
//!     |
//!     v
//! llc / opt -> native code
//! ```
//!
//! This is a parallel lowering path to the existing tMIR-based pipeline:
//!
//! ```text
//! TIR -> tMIR -> LLVM IR   (existing: lower.rs + emit.rs)
//! TIR -> LLVM IR            (this module: direct, scalar only)
//! ```
//!
//! # Basic Block Layout (Phase 2)
//!
//! The bytecode instruction stream is analyzed to identify basic block boundaries:
//! 1. Entry point (instruction 0) always starts a block.
//! 2. Jump targets (instruction at `pc + offset`) start new blocks.
//! 3. Instructions immediately following a branch/jump start new blocks
//!    (fall-through targets).
//!
//! Each basic block becomes an LLVM IR labeled block (`bb_N:`). The alloca-based
//! register file (introduced in Phase 1) means we do NOT need phi nodes —
//! LLVM's `mem2reg` pass promotes allocas to SSA form with phi nodes
//! automatically during optimization.
//!
//! # Mapping Reference
//!
//! | TIR Opcode | LLVM IR | Notes |
//! |------------|---------|-------|
//! | `LoadImm(rd, v)` | `%rd = add i64 v, 0` | Materialized constant |
//! | `AddInt(rd,r1,r2)` | `sadd.with.overflow` + br | Overflow checked |
//! | `SubInt(rd,r1,r2)` | `ssub.with.overflow` + br | Overflow checked |
//! | `MulInt(rd,r1,r2)` | `smul.with.overflow` + br | Overflow checked |
//! | `IntDiv(rd,r1,r2)` | `icmp eq` + br + `sdiv` | Zero check + TLC euclidean |
//! | `ModInt(rd,r1,r2)` | `icmp eq` + br + `srem` | Zero check + TLC euclidean |
//! | `NegInt(rd,rs)` | `ssub.with.overflow` | 0 - rs with overflow check |
//! | `Eq(rd,r1,r2)` | `icmp eq` + `zext` | Bool result as i64 |
//! | `Neq(rd,r1,r2)` | `icmp ne` + `zext` | Bool result as i64 |
//! | `LtInt(rd,r1,r2)` | `icmp slt` + `zext` | Signed comparison |
//! | `LeInt(rd,r1,r2)` | `icmp sle` + `zext` | Signed comparison |
//! | `GtInt(rd,r1,r2)` | `icmp sgt` + `zext` | Signed comparison |
//! | `GeInt(rd,r1,r2)` | `icmp sge` + `zext` | Signed comparison |
//! | `And(rd,r1,r2)` | `icmp ne` + `and` + `zext` | Canonicalize to i1 first |
//! | `Or(rd,r1,r2)` | `icmp ne` + `or` + `zext` | Canonicalize to i1 first |
//! | `Not(rd,rs)` | `icmp eq 0` + `zext` | Boolean negation |
//! | `Implies(rd,r1,r2)` | `icmp eq 0` + `icmp ne 0` + `or` | !a \/ b |
//! | `Equiv(rd,r1,r2)` | `icmp ne 0` + `icmp eq` + `zext` | a <=> b |
//! | `Jump(off)` | `br label %bb_N` | Unconditional branch |
//! | `JumpTrue(rs,off)` | `br i1 %c, label %T, label %F` | Conditional branch |
//! | `JumpFalse(rs,off)` | `br i1 %c, label %F, label %T` | Conditional branch |
//! | `Call(rd,op,a,n)` | `call i64 @op_N(i64 %a0, ...)` | External call |
//! | `Ret(rs)` | `ret i64 %rs` | Function return |
//! | `SetEnum(rd,s,n)` | `call i64 @tla_set_enum_N(...)` | Runtime: build set |
//! | `SetIn(rd,e,s)` | `call i64 @tla_set_in(e, s)` | Runtime: membership |
//! | `SetUnion(rd,r1,r2)` | `call i64 @tla_set_union(r1, r2)` | Runtime: union |
//! | `SetIntersect(rd,r1,r2)` | `call i64 @tla_set_intersect(r1, r2)` | Runtime: intersect |
//! | `SetDiff(rd,r1,r2)` | `call i64 @tla_set_diff(r1, r2)` | Runtime: difference |
//! | `Subseteq(rd,r1,r2)` | `call i64 @tla_set_subseteq(r1, r2)` | Runtime: subset check |
//! | `Powerset(rd,rs)` | `call i64 @tla_set_powerset(rs)` | Runtime: SUBSET |
//! | `BigUnion(rd,rs)` | `call i64 @tla_set_big_union(rs)` | Runtime: UNION |
//! | `Range(rd,lo,hi)` | `call i64 @tla_set_range(lo, hi)` | Runtime: lo..hi |
//! | `KSubset(rd,b,k)` | `call i64 @tla_set_ksubset(b, k)` | Runtime: k-subsets |
//! | `SeqNew(rd,s,n)` | `call i64 @tla_seq_new_N(...)` | Runtime: build seq |
//! | `Concat(rd,r1,r2)` | `call i64 @tla_seq_concat(r1, r2)` | Runtime: concatenation |
//! | `TupleNew(rd,s,n)` | `call i64 @tla_tuple_new_N(...)` | Runtime: build tuple |
//! | `TupleGet(rd,rs,i)` | `call i64 @tla_tuple_get(rs, i)` | Runtime: tuple access |
//! | `RecordGet(rd,rs,f)` | `call i64 @tla_record_get(rs, f)` | Runtime: field access |
//! | `FuncApply(rd,f,a)` | `call i64 @tla_func_apply(f, a)` | Runtime: func apply |
//! | `Domain(rd,rs)` | `call i64 @tla_domain(rs)` | Runtime: DOMAIN |
//! | `LoadConst(rd,idx)` | `call i64 @tla_load_const(idx)` | Runtime: constant pool |
//! | `CondMove(rd,c,rs)` | `select i1 %c, i64 %rs, i64 %rd` | Native LLVM select |
//! | `CallBuiltin(rd,b,a,n)` | `call i64 @tla_<builtin>(...)` | Runtime: stdlib op |

use crate::Llvm2Error;
use std::collections::BTreeSet;
use std::fmt::Write;
use tla_tir::bytecode::{BuiltinOp, BytecodeFunction, Opcode};

/// Statistics from a direct TIR-to-LLVM-IR lowering pass.
#[derive(Debug, Clone)]
pub struct TirLoweringStats {
    /// Number of opcodes lowered.
    pub opcodes_lowered: usize,
    /// Number of opcodes skipped (unsupported).
    pub opcodes_skipped: usize,
    /// Number of overflow check branches emitted.
    pub overflow_checks: usize,
    /// Number of division-by-zero check branches emitted.
    pub divzero_checks: usize,
    /// Number of LLVM IR basic blocks emitted (Phase 2).
    pub basic_blocks: usize,
    /// Number of function call instructions emitted (Phase 2).
    pub calls_emitted: usize,
    /// Number of runtime function calls emitted (Phase 3: set/seq/record ops).
    pub runtime_calls: usize,
}

/// Result of lowering a TIR function directly to LLVM IR.
#[derive(Debug, Clone)]
pub struct TirLoweredModule {
    /// The emitted LLVM IR text.
    pub llvm_ir: String,
    /// Lowering statistics.
    pub stats: TirLoweringStats,
}

/// Lower a TIR bytecode function directly to LLVM IR text.
///
/// Produces a standalone LLVM IR module with a single function that takes
/// N i64 parameters (one per register used) and returns i64. This is the
/// scalar fast-path: only integer/boolean operations are supported.
///
/// # Arguments
///
/// * `func` - The bytecode function to lower.
/// * `name` - Name for the emitted LLVM function.
///
/// # Errors
///
/// Returns [`Llvm2Error::UnsupportedInst`] if the function contains opcodes
/// that cannot be lowered (compound values, quantifiers, etc.).
pub fn lower_tir_to_llvm_ir(
    func: &BytecodeFunction,
    name: &str,
) -> Result<TirLoweredModule, Llvm2Error> {
    let mut ctx = TirLowerCtx::new(name);
    ctx.lower_function(func)?;
    Ok(TirLoweredModule {
        llvm_ir: ctx.output,
        stats: ctx.stats,
    })
}

/// Check if a TIR bytecode function is eligible for direct LLVM IR lowering.
///
/// Returns `true` if all opcodes in the function are scalar operations
/// that can be lowered without the tMIR intermediate representation.
pub fn is_tir_eligible(func: &BytecodeFunction) -> bool {
    func.instructions.iter().all(|op| is_scalar_opcode(op))
}

/// Context for TIR-to-LLVM-IR lowering.
struct TirLowerCtx {
    output: String,
    stats: TirLoweringStats,
    /// Counter for generating unique SSA value names.
    next_val: u32,
    /// Counter for generating unique block labels (for internal use by
    /// overflow/divzero checks — basic block labels use `bb_N` scheme).
    next_block: u32,
    /// Name of the function being lowered.
    func_name: String,
    /// Bytecode PC indices that start a new basic block.
    block_starts: BTreeSet<usize>,
    /// Set of `(op_idx, argc)` pairs for called functions that need
    /// external declarations.
    call_targets: BTreeSet<(u16, u8)>,
    /// Set of runtime function declarations needed (Phase 3: set/seq/record).
    /// Each entry is a complete declaration line, e.g. "declare i64 @tla_set_union(i64, i64)".
    runtime_decls: BTreeSet<String>,
}

impl TirLowerCtx {
    fn new(name: &str) -> Self {
        Self {
            output: String::with_capacity(4096),
            stats: TirLoweringStats {
                opcodes_lowered: 0,
                opcodes_skipped: 0,
                overflow_checks: 0,
                divzero_checks: 0,
                basic_blocks: 0,
                calls_emitted: 0,
                runtime_calls: 0,
            },
            next_val: 0,
            next_block: 1, // 0 is reserved for entry
            func_name: name.to_string(),
            block_starts: BTreeSet::new(),
            call_targets: BTreeSet::new(),
            runtime_decls: BTreeSet::new(),
        }
    }

    /// Allocate a fresh SSA value name (%t_N).
    fn fresh_val(&mut self) -> String {
        let id = self.next_val;
        self.next_val += 1;
        format!("%t_{id}")
    }

    /// Allocate a fresh block label.
    fn fresh_block(&mut self, prefix: &str) -> String {
        let id = self.next_block;
        self.next_block += 1;
        format!("{prefix}_{id}")
    }

    /// Analyze the instruction stream to identify basic block boundaries.
    ///
    /// A new basic block starts at:
    /// - Instruction 0 (entry point)
    /// - Any instruction that is the target of a jump
    /// - The instruction immediately following a branch/jump (fall-through)
    fn analyze_blocks(&mut self, func: &BytecodeFunction) {
        let n = func.instructions.len();
        if n == 0 {
            return;
        }
        // Entry is always a block start.
        self.block_starts.insert(0);

        for (pc, op) in func.instructions.iter().enumerate() {
            match *op {
                Opcode::Jump { offset } => {
                    let target = (pc as i64 + offset as i64) as usize;
                    if target < n {
                        self.block_starts.insert(target);
                    }
                    // Fall-through after unconditional jump is dead, but we
                    // still mark it as a block start so the structure is valid.
                    if pc + 1 < n {
                        self.block_starts.insert(pc + 1);
                    }
                }
                Opcode::JumpTrue { offset, .. } | Opcode::JumpFalse { offset, .. } => {
                    let target = (pc as i64 + offset as i64) as usize;
                    if target < n {
                        self.block_starts.insert(target);
                    }
                    // Fall-through (the else branch).
                    if pc + 1 < n {
                        self.block_starts.insert(pc + 1);
                    }
                }
                Opcode::Call {
                    op_idx, argc, ..
                } => {
                    self.call_targets.insert((op_idx, argc));
                }
                // Phase 3: collect runtime function declarations.
                Opcode::SetEnum { count, .. } => {
                    let params = (0..count).map(|_| "i64").collect::<Vec<_>>().join(", ");
                    self.runtime_decls.insert(format!("declare i64 @tla_set_enum_{count}({params})"));
                }
                Opcode::SetIn { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_in(i64, i64)".to_string());
                }
                Opcode::SetUnion { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_union(i64, i64)".to_string());
                }
                Opcode::SetIntersect { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_intersect(i64, i64)".to_string());
                }
                Opcode::SetDiff { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_diff(i64, i64)".to_string());
                }
                Opcode::Subseteq { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_subseteq(i64, i64)".to_string());
                }
                Opcode::Powerset { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_powerset(i64)".to_string());
                }
                Opcode::BigUnion { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_big_union(i64)".to_string());
                }
                Opcode::Range { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_range(i64, i64)".to_string());
                }
                Opcode::KSubset { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_set_ksubset(i64, i64)".to_string());
                }
                Opcode::SeqNew { count, .. } => {
                    let params = (0..count).map(|_| "i64").collect::<Vec<_>>().join(", ");
                    self.runtime_decls.insert(format!("declare i64 @tla_seq_new_{count}({params})"));
                }
                Opcode::Concat { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_seq_concat(i64, i64)".to_string());
                }
                Opcode::TupleNew { count, .. } => {
                    let params = (0..count).map(|_| "i64").collect::<Vec<_>>().join(", ");
                    self.runtime_decls.insert(format!("declare i64 @tla_tuple_new_{count}({params})"));
                }
                Opcode::TupleGet { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_tuple_get(i64, i64)".to_string());
                }
                Opcode::RecordGet { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_record_get(i64, i64)".to_string());
                }
                Opcode::FuncApply { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_func_apply(i64, i64)".to_string());
                }
                Opcode::Domain { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_domain(i64)".to_string());
                }
                Opcode::LoadConst { .. } => {
                    self.runtime_decls.insert("declare i64 @tla_load_const(i64)".to_string());
                }
                Opcode::CondMove { .. } => {
                    // CondMove uses select, no runtime call needed.
                }
                Opcode::CallBuiltin { builtin, .. } => {
                    let decl = match builtin {
                        BuiltinOp::Len => "declare i64 @tla_seq_len(i64)",
                        BuiltinOp::Head => "declare i64 @tla_seq_head(i64)",
                        BuiltinOp::Tail => "declare i64 @tla_seq_tail(i64)",
                        BuiltinOp::Append => "declare i64 @tla_seq_append(i64, i64)",
                        BuiltinOp::SubSeq => "declare i64 @tla_seq_subseq(i64, i64, i64)",
                        BuiltinOp::Seq => "declare i64 @tla_seq_set(i64)",
                        BuiltinOp::Cardinality => "declare i64 @tla_cardinality(i64)",
                        BuiltinOp::IsFiniteSet => "declare i64 @tla_is_finite_set(i64)",
                        BuiltinOp::ToString => "declare i64 @tla_tostring(i64)",
                    };
                    self.runtime_decls.insert(decl.to_string());
                }
                _ => {}
            }
        }
    }

    /// Get the LLVM label for a basic block at the given bytecode PC.
    fn block_label(&self, pc: usize) -> String {
        if pc == 0 {
            "bb_entry".to_string()
        } else {
            format!("bb_{pc}")
        }
    }

    fn lower_function(&mut self, func: &BytecodeFunction) -> Result<(), Llvm2Error> {
        // Phase 2: analyze basic block structure before emitting.
        self.analyze_blocks(func);

        // Module header.
        writeln!(self.output, "; ModuleID = '{}'", self.func_name)
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(
            self.output,
            "source_filename = \"{}\"",
            self.func_name
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(
            self.output,
            "target datalayout = \"e-m:o-i64:64-i128:128-n32:64-S128\""
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output).map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        // Overflow intrinsic declarations.
        writeln!(
            self.output,
            "declare {{ i64, i1 }} @llvm.sadd.with.overflow.i64(i64, i64)"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(
            self.output,
            "declare {{ i64, i1 }} @llvm.ssub.with.overflow.i64(i64, i64)"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(
            self.output,
            "declare {{ i64, i1 }} @llvm.smul.with.overflow.i64(i64, i64)"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "declare void @llvm.trap() noreturn nounwind")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        // Phase 2: declare external functions for Call targets.
        let call_targets: Vec<_> = self.call_targets.iter().copied().collect();
        for (op_idx, argc) in &call_targets {
            let params = (0..*argc)
                .map(|_| "i64".to_string())
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(self.output, "declare i64 @op_{op_idx}({params})")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        }

        // Phase 3: declare runtime functions for set/seq/record operations.
        let runtime_decls: Vec<_> = self.runtime_decls.iter().cloned().collect();
        for decl in &runtime_decls {
            writeln!(self.output, "{decl}")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        }
        writeln!(self.output).map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        // Scan opcodes to determine max register used (for function params).
        let max_reg = func
            .instructions
            .iter()
            .map(|op| max_register_in_opcode(op))
            .max()
            .unwrap_or(0);

        // Function definition: all registers are i64, result is i64.
        write!(
            self.output,
            "define i64 @{}(",
            self.func_name
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, ") {{").map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "entry:").map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        // Allocate register slots (alloca + store 0 for initialization).
        for r in 0..=max_reg {
            writeln!(self.output, "  %r{r}_ptr = alloca i64")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
            writeln!(self.output, "  store i64 0, ptr %r{r}_ptr")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        }

        // If there are basic blocks beyond entry, branch to the first one.
        let has_control_flow = self.block_starts.len() > 1
            || self.block_starts.contains(&0usize);
        if has_control_flow && !func.instructions.is_empty() {
            writeln!(self.output, "  br label %{}", self.block_label(0))
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        }

        // Collect block_starts for iteration (avoid borrow conflict).
        let block_starts: BTreeSet<usize> = self.block_starts.clone();

        // Lower each opcode, inserting block labels at boundaries.
        // Track whether the previous instruction was a terminator (branch/ret/jump).
        let mut prev_was_terminator = has_control_flow;
        for (pc, op) in func.instructions.iter().enumerate() {
            // Emit block label if this PC starts a new basic block.
            if block_starts.contains(&pc) {
                let label = self.block_label(pc);
                writeln!(self.output, "{label}:")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.stats.basic_blocks += 1;
            }

            self.lower_opcode_with_pc(op, pc, func.instructions.len(), &block_starts)?;

            // Track terminators: branches, jumps, and returns all end a block.
            prev_was_terminator = matches!(
                op,
                Opcode::Jump { .. }
                    | Opcode::JumpTrue { .. }
                    | Opcode::JumpFalse { .. }
                    | Opcode::Ret { .. }
                    | Opcode::Halt
            );
        }

        // Safety: if no explicit Ret was emitted, return 0.
        // Only emit if we're not right after a terminator.
        if !prev_was_terminator {
            writeln!(self.output, "  ret i64 0")
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        }
        writeln!(self.output, "}}").map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        Ok(())
    }

    /// Emit a load from a register slot.
    fn emit_load_reg(&mut self, reg: u8) -> Result<String, Llvm2Error> {
        let val = self.fresh_val();
        writeln!(self.output, "  {val} = load i64, ptr %r{reg}_ptr")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        Ok(val)
    }

    /// Emit a store to a register slot.
    fn emit_store_reg(&mut self, reg: u8, val: &str) -> Result<(), Llvm2Error> {
        writeln!(self.output, "  store i64 {val}, ptr %r{reg}_ptr")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        Ok(())
    }

    /// Emit an overflow-checked arithmetic operation.
    ///
    /// Pattern:
    /// ```llvm
    /// %res_ov = call {i64, i1} @llvm.<op>.with.overflow.i64(i64 %a, i64 %b)
    /// %res = extractvalue {i64, i1} %res_ov, 0
    /// %ovf = extractvalue {i64, i1} %res_ov, 1
    /// br i1 %ovf, label %overflow_N, label %continue_N
    /// overflow_N:
    ///   call void @llvm.trap()
    ///   unreachable
    /// continue_N:
    /// ```
    fn emit_overflow_checked_binop(
        &mut self,
        intrinsic: &str,
        lhs: &str,
        rhs: &str,
        rd: u8,
    ) -> Result<(), Llvm2Error> {
        let res_ov = self.fresh_val();
        let res = self.fresh_val();
        let ovf = self.fresh_val();
        let overflow_block = self.fresh_block("overflow");
        let continue_block = self.fresh_block("continue");

        writeln!(
            self.output,
            "  {res_ov} = call {{ i64, i1 }} @{intrinsic}(i64 {lhs}, i64 {rhs})"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(
            self.output,
            "  {res} = extractvalue {{ i64, i1 }} {res_ov}, 0"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(
            self.output,
            "  {ovf} = extractvalue {{ i64, i1 }} {res_ov}, 1"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(
            self.output,
            "  br i1 {ovf}, label %{overflow_block}, label %{continue_block}"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "{overflow_block}:")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "  call void @llvm.trap()")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "  unreachable")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "{continue_block}:")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        self.emit_store_reg(rd, &res)?;
        self.stats.overflow_checks += 1;
        Ok(())
    }

    /// Emit a division-by-zero check followed by the division operation.
    fn emit_divzero_checked(
        &mut self,
        divisor: &str,
    ) -> Result<String, Llvm2Error> {
        let is_zero = self.fresh_val();
        let trap_block = self.fresh_block("divzero");
        let safe_block = self.fresh_block("divsafe");

        writeln!(self.output, "  {is_zero} = icmp eq i64 {divisor}, 0")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(
            self.output,
            "  br i1 {is_zero}, label %{trap_block}, label %{safe_block}"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "{trap_block}:")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "  call void @llvm.trap()")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "  unreachable")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "{safe_block}:")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

        self.stats.divzero_checks += 1;
        Ok(safe_block)
    }

    /// Lower a single opcode with PC context for control flow (Phase 2).
    ///
    /// `pc` is the bytecode program counter of this instruction, used to
    /// compute branch target labels. `n_insts` is the total instruction count.
    /// `block_starts` identifies which PCs begin basic blocks.
    fn lower_opcode_with_pc(
        &mut self,
        op: &Opcode,
        pc: usize,
        _n_insts: usize,
        _block_starts: &BTreeSet<usize>,
    ) -> Result<(), Llvm2Error> {
        match *op {
            // =================================================================
            // Value loading
            // =================================================================
            Opcode::LoadImm { rd, value } => {
                let val = self.fresh_val();
                writeln!(self.output, "  {val} = add i64 {value}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &val)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::LoadBool { rd, value } => {
                let int_val = if value { 1 } else { 0 };
                let val = self.fresh_val();
                writeln!(self.output, "  {val} = add i64 {int_val}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &val)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::Move { rd, rs } => {
                let val = self.emit_load_reg(rs)?;
                self.emit_store_reg(rd, &val)?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Overflow-checked integer arithmetic
            // =================================================================
            Opcode::AddInt { rd, r1, r2 } => {
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;
                self.emit_overflow_checked_binop(
                    "llvm.sadd.with.overflow.i64",
                    &a,
                    &b,
                    rd,
                )?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::SubInt { rd, r1, r2 } => {
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;
                self.emit_overflow_checked_binop(
                    "llvm.ssub.with.overflow.i64",
                    &a,
                    &b,
                    rd,
                )?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::MulInt { rd, r1, r2 } => {
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;
                self.emit_overflow_checked_binop(
                    "llvm.smul.with.overflow.i64",
                    &a,
                    &b,
                    rd,
                )?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::NegInt { rd, rs } => {
                let v = self.emit_load_reg(rs)?;
                let zero = self.fresh_val();
                writeln!(self.output, "  {zero} = add i64 0, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_overflow_checked_binop(
                    "llvm.ssub.with.overflow.i64",
                    &zero,
                    &v,
                    rd,
                )?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Integer division (TLC Euclidean semantics)
            // =================================================================
            Opcode::IntDiv { rd, r1, r2 } => {
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;

                // Division by zero check.
                let _safe = self.emit_divzero_checked(&b)?;

                // Compute q = sdiv, r = srem.
                let q = self.fresh_val();
                let r = self.fresh_val();
                writeln!(self.output, "  {q} = sdiv i64 {a}, {b}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {r} = srem i64 {a}, {b}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                // Euclidean adjustment: if signs differ and remainder != 0, q -= 1.
                let zero = self.fresh_val();
                let one = self.fresh_val();
                let a_xor_b = self.fresh_val();
                let signs_differ = self.fresh_val();
                let r_nonzero = self.fresh_val();
                let need_adjust = self.fresh_val();
                let q_minus_1 = self.fresh_val();
                let result = self.fresh_val();

                writeln!(self.output, "  {zero} = add i64 0, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {one} = add i64 1, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {a_xor_b} = xor i64 {a}, {b}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(
                    self.output,
                    "  {signs_differ} = icmp slt i64 {a_xor_b}, {zero}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {r_nonzero} = icmp ne i64 {r}, {zero}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(
                    self.output,
                    "  {need_adjust} = and i1 {signs_differ}, {r_nonzero}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {q_minus_1} = sub i64 {q}, {one}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(
                    self.output,
                    "  {result} = select i1 {need_adjust}, i64 {q_minus_1}, i64 {q}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::ModInt { rd, r1, r2 } => {
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;

                // Division by zero check.
                let _safe = self.emit_divzero_checked(&b)?;

                // r = srem.
                let r = self.fresh_val();
                writeln!(self.output, "  {r} = srem i64 {a}, {b}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                // Euclidean adjustment: if r < 0, add |b|.
                let zero = self.fresh_val();
                let r_neg = self.fresh_val();
                let b_neg = self.fresh_val();
                let neg_b = self.fresh_val();
                let abs_b = self.fresh_val();
                let r_adjusted = self.fresh_val();
                let result = self.fresh_val();

                writeln!(self.output, "  {zero} = add i64 0, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {r_neg} = icmp slt i64 {r}, {zero}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {b_neg} = icmp slt i64 {b}, {zero}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {neg_b} = sub i64 0, {b}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(
                    self.output,
                    "  {abs_b} = select i1 {b_neg}, i64 {neg_b}, i64 {b}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {r_adjusted} = add i64 {r}, {abs_b}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(
                    self.output,
                    "  {result} = select i1 {r_neg}, i64 {r_adjusted}, i64 {r}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Comparison (result is i64: 0 or 1)
            // =================================================================
            Opcode::Eq { rd, r1, r2 } => {
                self.emit_icmp_zext("eq", r1, r2, rd)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::Neq { rd, r1, r2 } => {
                self.emit_icmp_zext("ne", r1, r2, rd)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::LtInt { rd, r1, r2 } => {
                self.emit_icmp_zext("slt", r1, r2, rd)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::LeInt { rd, r1, r2 } => {
                self.emit_icmp_zext("sle", r1, r2, rd)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::GtInt { rd, r1, r2 } => {
                self.emit_icmp_zext("sgt", r1, r2, rd)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::GeInt { rd, r1, r2 } => {
                self.emit_icmp_zext("sge", r1, r2, rd)?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Boolean operations
            //
            // TLA+ booleans are i64 (0 = false, nonzero = true). We canonicalize
            // to i1 before boolean ops, then zext back to i64.
            // =================================================================
            Opcode::And { rd, r1, r2 } => {
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;
                let a_bool = self.fresh_val();
                let b_bool = self.fresh_val();
                let combined = self.fresh_val();
                let result = self.fresh_val();
                writeln!(self.output, "  {a_bool} = icmp ne i64 {a}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {b_bool} = icmp ne i64 {b}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {combined} = and i1 {a_bool}, {b_bool}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {result} = zext i1 {combined} to i64")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::Or { rd, r1, r2 } => {
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;
                let a_bool = self.fresh_val();
                let b_bool = self.fresh_val();
                let combined = self.fresh_val();
                let result = self.fresh_val();
                writeln!(self.output, "  {a_bool} = icmp ne i64 {a}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {b_bool} = icmp ne i64 {b}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {combined} = or i1 {a_bool}, {b_bool}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {result} = zext i1 {combined} to i64")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::Not { rd, rs } => {
                let v = self.emit_load_reg(rs)?;
                let cmp = self.fresh_val();
                let result = self.fresh_val();
                writeln!(self.output, "  {cmp} = icmp eq i64 {v}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {result} = zext i1 {cmp} to i64")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::Implies { rd, r1, r2 } => {
                // a => b  is equivalent to  !a \/ b.
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;
                let not_a = self.fresh_val();
                let b_bool = self.fresh_val();
                let combined = self.fresh_val();
                let result = self.fresh_val();
                writeln!(self.output, "  {not_a} = icmp eq i64 {a}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {b_bool} = icmp ne i64 {b}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {combined} = or i1 {not_a}, {b_bool}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {result} = zext i1 {combined} to i64")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::Equiv { rd, r1, r2 } => {
                // a <=> b  is equivalent to  (a != 0) == (b != 0).
                let a = self.emit_load_reg(r1)?;
                let b = self.emit_load_reg(r2)?;
                let a_bool = self.fresh_val();
                let b_bool = self.fresh_val();
                let eq = self.fresh_val();
                let result = self.fresh_val();
                writeln!(self.output, "  {a_bool} = icmp ne i64 {a}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {b_bool} = icmp ne i64 {b}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {eq} = icmp eq i1 {a_bool}, {b_bool}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  {result} = zext i1 {eq} to i64")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Control Flow (Phase 2)
            // =================================================================
            Opcode::Jump { offset } => {
                let target_pc = (pc as i64 + offset as i64) as usize;
                let target_label = self.block_label(target_pc);
                writeln!(self.output, "  br label %{target_label}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::JumpTrue { rs, offset } => {
                let val = self.emit_load_reg(rs)?;
                let cond = self.fresh_val();
                writeln!(self.output, "  {cond} = icmp ne i64 {val}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                let target_pc = (pc as i64 + offset as i64) as usize;
                let true_label = self.block_label(target_pc);
                let false_label = self.block_label(pc + 1);
                writeln!(
                    self.output,
                    "  br i1 {cond}, label %{true_label}, label %{false_label}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.stats.opcodes_lowered += 1;
            }
            Opcode::JumpFalse { rs, offset } => {
                let val = self.emit_load_reg(rs)?;
                let cond = self.fresh_val();
                writeln!(self.output, "  {cond} = icmp eq i64 {val}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;

                let target_pc = (pc as i64 + offset as i64) as usize;
                let true_label = self.block_label(target_pc);
                let false_label = self.block_label(pc + 1);
                writeln!(
                    self.output,
                    "  br i1 {cond}, label %{true_label}, label %{false_label}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Function Calls (Phase 2)
            // =================================================================
            Opcode::Call {
                rd,
                op_idx,
                args_start,
                argc,
            } => {
                // Load all arguments from register slots.
                let mut arg_vals = Vec::with_capacity(argc as usize);
                for i in 0..argc {
                    let arg = self.emit_load_reg(args_start + i)?;
                    arg_vals.push(arg);
                }
                let args_str = arg_vals
                    .iter()
                    .map(|v| format!("i64 {v}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @op_{op_idx}({args_str})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.calls_emitted += 1;
            }

            // =================================================================
            // Return
            // =================================================================
            Opcode::Ret { rs } => {
                let val = self.emit_load_reg(rs)?;
                writeln!(self.output, "  ret i64 {val}")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Nop
            // =================================================================
            Opcode::Nop => {
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Halt
            // =================================================================
            Opcode::Halt => {
                writeln!(self.output, "  call void @llvm.trap()")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(self.output, "  unreachable")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Phase 3: Set Operations (runtime function calls)
            // =================================================================
            Opcode::SetEnum { rd, start, count } => {
                let mut arg_vals = Vec::with_capacity(count as usize);
                for i in 0..count {
                    let arg = self.emit_load_reg(start + i)?;
                    arg_vals.push(arg);
                }
                let args_str = arg_vals
                    .iter()
                    .map(|v| format!("i64 {v}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @tla_set_enum_{count}({args_str})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.runtime_calls += 1;
            }
            Opcode::SetIn { rd, elem, set } => {
                let e = self.emit_load_reg(elem)?;
                let s = self.emit_load_reg(set)?;
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @tla_set_in(i64 {e}, i64 {s})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.runtime_calls += 1;
            }
            Opcode::SetUnion { rd, r1, r2 } => {
                self.emit_runtime_binary_op("tla_set_union", r1, r2, rd)?;
            }
            Opcode::SetIntersect { rd, r1, r2 } => {
                self.emit_runtime_binary_op("tla_set_intersect", r1, r2, rd)?;
            }
            Opcode::SetDiff { rd, r1, r2 } => {
                self.emit_runtime_binary_op("tla_set_diff", r1, r2, rd)?;
            }
            Opcode::Subseteq { rd, r1, r2 } => {
                self.emit_runtime_binary_op("tla_set_subseteq", r1, r2, rd)?;
            }
            Opcode::Powerset { rd, rs } => {
                self.emit_runtime_unary_op("tla_set_powerset", rs, rd)?;
            }
            Opcode::BigUnion { rd, rs } => {
                self.emit_runtime_unary_op("tla_set_big_union", rs, rd)?;
            }
            Opcode::Range { rd, lo, hi } => {
                self.emit_runtime_binary_op("tla_set_range", lo, hi, rd)?;
            }
            Opcode::KSubset { rd, base, k } => {
                self.emit_runtime_binary_op("tla_set_ksubset", base, k, rd)?;
            }

            // =================================================================
            // Phase 3: Sequence Operations (runtime function calls)
            // =================================================================
            Opcode::SeqNew { rd, start, count } => {
                let mut arg_vals = Vec::with_capacity(count as usize);
                for i in 0..count {
                    let arg = self.emit_load_reg(start + i)?;
                    arg_vals.push(arg);
                }
                let args_str = arg_vals
                    .iter()
                    .map(|v| format!("i64 {v}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @tla_seq_new_{count}({args_str})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.runtime_calls += 1;
            }
            Opcode::Concat { rd, r1, r2 } => {
                self.emit_runtime_binary_op("tla_seq_concat", r1, r2, rd)?;
            }

            // =================================================================
            // Phase 3: Tuple Operations (runtime function calls)
            // =================================================================
            Opcode::TupleNew { rd, start, count } => {
                let mut arg_vals = Vec::with_capacity(count as usize);
                for i in 0..count {
                    let arg = self.emit_load_reg(start + i)?;
                    arg_vals.push(arg);
                }
                let args_str = arg_vals
                    .iter()
                    .map(|v| format!("i64 {v}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @tla_tuple_new_{count}({args_str})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.runtime_calls += 1;
            }
            Opcode::TupleGet { rd, rs, idx } => {
                let tuple = self.emit_load_reg(rs)?;
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @tla_tuple_get(i64 {tuple}, i64 {idx})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.runtime_calls += 1;
            }

            // =================================================================
            // Phase 3: Record/Function Operations (runtime function calls)
            // =================================================================
            Opcode::RecordGet { rd, rs, field_idx } => {
                let rec = self.emit_load_reg(rs)?;
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @tla_record_get(i64 {rec}, i64 {field_idx})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.runtime_calls += 1;
            }
            Opcode::FuncApply { rd, func, arg } => {
                self.emit_runtime_binary_op("tla_func_apply", func, arg, rd)?;
            }
            Opcode::Domain { rd, rs } => {
                self.emit_runtime_unary_op("tla_domain", rs, rd)?;
            }

            // =================================================================
            // Phase 3: Constant Pool Loading (runtime function call)
            // =================================================================
            Opcode::LoadConst { rd, idx } => {
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @tla_load_const(i64 {idx})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.runtime_calls += 1;
            }

            // =================================================================
            // Phase 3: CondMove (native LLVM select, no runtime call)
            // =================================================================
            Opcode::CondMove { rd, cond, rs } => {
                let c = self.emit_load_reg(cond)?;
                let then_val = self.emit_load_reg(rs)?;
                let else_val = self.emit_load_reg(rd)?;
                let cond_bool = self.fresh_val();
                let result = self.fresh_val();
                writeln!(self.output, "  {cond_bool} = icmp ne i64 {c}, 0")
                    .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                writeln!(
                    self.output,
                    "  {result} = select i1 {cond_bool}, i64 {then_val}, i64 {else_val}"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
            }

            // =================================================================
            // Phase 3: Builtin Standard Library Calls (runtime function calls)
            // =================================================================
            Opcode::CallBuiltin {
                rd,
                builtin,
                args_start,
                argc,
            } => {
                let mut arg_vals = Vec::with_capacity(argc as usize);
                for i in 0..argc {
                    let arg = self.emit_load_reg(args_start + i)?;
                    arg_vals.push(arg);
                }
                let func_name = match builtin {
                    BuiltinOp::Len => "tla_seq_len",
                    BuiltinOp::Head => "tla_seq_head",
                    BuiltinOp::Tail => "tla_seq_tail",
                    BuiltinOp::Append => "tla_seq_append",
                    BuiltinOp::SubSeq => "tla_seq_subseq",
                    BuiltinOp::Seq => "tla_seq_set",
                    BuiltinOp::Cardinality => "tla_cardinality",
                    BuiltinOp::IsFiniteSet => "tla_is_finite_set",
                    BuiltinOp::ToString => "tla_tostring",
                };
                let args_str = arg_vals
                    .iter()
                    .map(|v| format!("i64 {v}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let result = self.fresh_val();
                writeln!(
                    self.output,
                    "  {result} = call i64 @{func_name}({args_str})"
                )
                .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
                self.emit_store_reg(rd, &result)?;
                self.stats.opcodes_lowered += 1;
                self.stats.runtime_calls += 1;
            }

            // =================================================================
            // Unsupported opcodes (quantifiers, state ops, closures, etc.)
            // =================================================================
            _ => {
                self.stats.opcodes_skipped += 1;
                return Err(Llvm2Error::UnsupportedInst(format!(
                    "TIR opcode {:?} not supported in direct LLVM IR lowering",
                    op,
                )));
            }
        }
        Ok(())
    }

    /// Emit an icmp + zext pattern: compare two registers, zero-extend to i64.
    fn emit_icmp_zext(
        &mut self,
        condition: &str,
        r1: u8,
        r2: u8,
        rd: u8,
    ) -> Result<(), Llvm2Error> {
        let a = self.emit_load_reg(r1)?;
        let b = self.emit_load_reg(r2)?;
        let cmp = self.fresh_val();
        let result = self.fresh_val();
        writeln!(self.output, "  {cmp} = icmp {condition} i64 {a}, {b}")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        writeln!(self.output, "  {result} = zext i1 {cmp} to i64")
            .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        self.emit_store_reg(rd, &result)?;
        Ok(())
    }

    /// Emit a unary runtime function call: `rd = @func_name(rs)`.
    fn emit_runtime_unary_op(
        &mut self,
        func_name: &str,
        rs: u8,
        rd: u8,
    ) -> Result<(), Llvm2Error> {
        let v = self.emit_load_reg(rs)?;
        let result = self.fresh_val();
        writeln!(
            self.output,
            "  {result} = call i64 @{func_name}(i64 {v})"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        self.emit_store_reg(rd, &result)?;
        self.stats.opcodes_lowered += 1;
        self.stats.runtime_calls += 1;
        Ok(())
    }

    /// Emit a binary runtime function call: `rd = @func_name(r1, r2)`.
    fn emit_runtime_binary_op(
        &mut self,
        func_name: &str,
        r1: u8,
        r2: u8,
        rd: u8,
    ) -> Result<(), Llvm2Error> {
        let a = self.emit_load_reg(r1)?;
        let b = self.emit_load_reg(r2)?;
        let result = self.fresh_val();
        writeln!(
            self.output,
            "  {result} = call i64 @{func_name}(i64 {a}, i64 {b})"
        )
        .map_err(|e| Llvm2Error::Emission(e.to_string()))?;
        self.emit_store_reg(rd, &result)?;
        self.stats.opcodes_lowered += 1;
        self.stats.runtime_calls += 1;
        Ok(())
    }
}

/// Check if an opcode is supported by the direct TIR-to-LLVM-IR lowering.
///
/// Phase 1: scalar operations (arithmetic, comparison, boolean).
/// Phase 2: control flow (Jump, JumpTrue, JumpFalse) and function calls (Call).
/// Phase 3: set/sequence/record/tuple operations (runtime function calls).
fn is_tir_lowering_eligible(op: &Opcode) -> bool {
    matches!(
        op,
        // Phase 1: scalar
        Opcode::LoadImm { .. }
            | Opcode::LoadBool { .. }
            | Opcode::Move { .. }
            | Opcode::AddInt { .. }
            | Opcode::SubInt { .. }
            | Opcode::MulInt { .. }
            | Opcode::IntDiv { .. }
            | Opcode::ModInt { .. }
            | Opcode::NegInt { .. }
            | Opcode::Eq { .. }
            | Opcode::Neq { .. }
            | Opcode::LtInt { .. }
            | Opcode::LeInt { .. }
            | Opcode::GtInt { .. }
            | Opcode::GeInt { .. }
            | Opcode::And { .. }
            | Opcode::Or { .. }
            | Opcode::Not { .. }
            | Opcode::Implies { .. }
            | Opcode::Equiv { .. }
            // Phase 2: control flow + calls
            | Opcode::Ret { .. }
            | Opcode::Jump { .. }
            | Opcode::JumpTrue { .. }
            | Opcode::JumpFalse { .. }
            | Opcode::Call { .. }
            | Opcode::Halt
            | Opcode::Nop
            // Phase 3: set operations
            | Opcode::SetEnum { .. }
            | Opcode::SetIn { .. }
            | Opcode::SetUnion { .. }
            | Opcode::SetIntersect { .. }
            | Opcode::SetDiff { .. }
            | Opcode::Subseteq { .. }
            | Opcode::Powerset { .. }
            | Opcode::BigUnion { .. }
            | Opcode::Range { .. }
            | Opcode::KSubset { .. }
            // Phase 3: sequence operations
            | Opcode::SeqNew { .. }
            | Opcode::Concat { .. }
            // Phase 3: tuple operations
            | Opcode::TupleNew { .. }
            | Opcode::TupleGet { .. }
            // Phase 3: record/function operations
            | Opcode::RecordGet { .. }
            | Opcode::FuncApply { .. }
            | Opcode::Domain { .. }
            // Phase 3: constant pool + conditional move + builtins
            | Opcode::LoadConst { .. }
            | Opcode::CondMove { .. }
            | Opcode::CallBuiltin { .. }
    )
}

/// Backward-compatible alias for `is_tir_lowering_eligible`.
fn is_scalar_opcode(op: &Opcode) -> bool {
    is_tir_lowering_eligible(op)
}

/// Get the maximum register index referenced by an opcode.
fn max_register_in_opcode(op: &Opcode) -> u8 {
    match *op {
        Opcode::LoadImm { rd, .. } => rd,
        Opcode::LoadBool { rd, .. } => rd,
        Opcode::Move { rd, rs } => rd.max(rs),
        Opcode::AddInt { rd, r1, r2 }
        | Opcode::SubInt { rd, r1, r2 }
        | Opcode::MulInt { rd, r1, r2 }
        | Opcode::IntDiv { rd, r1, r2 }
        | Opcode::ModInt { rd, r1, r2 }
        | Opcode::Eq { rd, r1, r2 }
        | Opcode::Neq { rd, r1, r2 }
        | Opcode::LtInt { rd, r1, r2 }
        | Opcode::LeInt { rd, r1, r2 }
        | Opcode::GtInt { rd, r1, r2 }
        | Opcode::GeInt { rd, r1, r2 }
        | Opcode::And { rd, r1, r2 }
        | Opcode::Or { rd, r1, r2 }
        | Opcode::Implies { rd, r1, r2 }
        | Opcode::Equiv { rd, r1, r2 } => rd.max(r1).max(r2),
        Opcode::NegInt { rd, rs } | Opcode::Not { rd, rs } => rd.max(rs),
        Opcode::Ret { rs } => rs,
        // Phase 2: control flow registers.
        Opcode::JumpTrue { rs, .. } | Opcode::JumpFalse { rs, .. } => rs,
        Opcode::Call {
            rd,
            args_start,
            argc,
            ..
        } => {
            let max_arg = if argc == 0 {
                0
            } else {
                args_start + argc - 1
            };
            rd.max(max_arg)
        }
        Opcode::Jump { .. } | Opcode::Nop | Opcode::Halt => 0,
        // Phase 3: set/sequence/record/tuple operations.
        Opcode::SetEnum { rd, start, count }
        | Opcode::SeqNew { rd, start, count }
        | Opcode::TupleNew { rd, start, count } => {
            let max_elem = if count == 0 { 0 } else { start + count - 1 };
            rd.max(max_elem)
        }
        Opcode::SetIn { rd, elem, set } => rd.max(elem).max(set),
        Opcode::SetUnion { rd, r1, r2 }
        | Opcode::SetIntersect { rd, r1, r2 }
        | Opcode::SetDiff { rd, r1, r2 }
        | Opcode::Subseteq { rd, r1, r2 }
        | Opcode::Range { rd, lo: r1, hi: r2 }
        | Opcode::KSubset { rd, base: r1, k: r2 }
        | Opcode::Concat { rd, r1, r2 } => rd.max(r1).max(r2),
        Opcode::Powerset { rd, rs }
        | Opcode::BigUnion { rd, rs }
        | Opcode::Domain { rd, rs } => rd.max(rs),
        Opcode::TupleGet { rd, rs, .. } | Opcode::RecordGet { rd, rs, .. } => rd.max(rs),
        Opcode::FuncApply { rd, func, arg } => rd.max(func).max(arg),
        Opcode::LoadConst { rd, .. } => rd,
        Opcode::CondMove { rd, cond, rs } => rd.max(cond).max(rs),
        Opcode::CallBuiltin {
            rd,
            args_start,
            argc,
            ..
        } => {
            let max_arg = if argc == 0 { 0 } else { args_start + argc - 1 };
            rd.max(max_arg)
        }
        // For unsupported opcodes, scan all register fields.
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_tir::bytecode::BytecodeFunction;

    // =========================================================================
    // Helper: build simple bytecode functions
    // =========================================================================

    fn make_return_42() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("ret42".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::Ret { rs: 0 });
        func
    }

    fn make_add() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("add".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn make_sub() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("sub".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 30 });
        func.emit(Opcode::LoadImm { rd: 1, value: 7 });
        func.emit(Opcode::SubInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn make_mul() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("mul".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 6 });
        func.emit(Opcode::LoadImm { rd: 1, value: 7 });
        func.emit(Opcode::MulInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn make_neg() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("neg".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::NegInt { rd: 1, rs: 0 });
        func.emit(Opcode::Ret { rs: 1 });
        func
    }

    fn make_intdiv() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("intdiv".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::IntDiv {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn make_modint() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("modint".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::ModInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn make_comparison() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("cmp".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn make_boolean_and() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("bool_and".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::And {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn make_boolean_not() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("bool_not".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::Not { rd: 1, rs: 0 });
        func.emit(Opcode::Ret { rs: 1 });
        func
    }

    fn make_implies() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("implies".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::Implies {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn make_equiv() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("equiv".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Equiv {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    // =========================================================================
    // Eligibility tests
    // =========================================================================

    #[test]
    fn test_eligibility_scalar_function() {
        let func = make_return_42();
        assert!(is_tir_eligible(&func));
    }

    #[test]
    fn test_eligibility_quantifier_ineligible() {
        // Quantifiers are NOT eligible for direct TIR lowering.
        let mut func = BytecodeFunction::new("non_scalar".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::ForallBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 2,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(!is_tir_eligible(&func));
    }

    // =========================================================================
    // Basic lowering tests
    // =========================================================================

    #[test]
    fn test_lower_return_42() {
        let func = make_return_42();
        let result = lower_tir_to_llvm_ir(&func, "ret42").expect("should lower");

        assert!(result.llvm_ir.contains("define i64 @ret42("));
        assert!(result.llvm_ir.contains("ret i64"));
        assert_eq!(result.stats.opcodes_lowered, 2);
        assert_eq!(result.stats.opcodes_skipped, 0);
    }

    #[test]
    fn test_lower_add_has_overflow_check() {
        let func = make_add();
        let result = lower_tir_to_llvm_ir(&func, "add_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("llvm.sadd.with.overflow.i64"),
            "AddInt should use overflow intrinsic. IR:\n{ir}"
        );
        assert!(
            ir.contains("extractvalue"),
            "Should extract overflow flag. IR:\n{ir}"
        );
        assert!(
            ir.contains("llvm.trap"),
            "Should trap on overflow. IR:\n{ir}"
        );
        assert_eq!(result.stats.overflow_checks, 1);
    }

    #[test]
    fn test_lower_sub_has_overflow_check() {
        let func = make_sub();
        let result = lower_tir_to_llvm_ir(&func, "sub_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("llvm.ssub.with.overflow.i64"),
            "SubInt should use overflow intrinsic. IR:\n{ir}"
        );
        assert_eq!(result.stats.overflow_checks, 1);
    }

    #[test]
    fn test_lower_mul_has_overflow_check() {
        let func = make_mul();
        let result = lower_tir_to_llvm_ir(&func, "mul_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("llvm.smul.with.overflow.i64"),
            "MulInt should use overflow intrinsic. IR:\n{ir}"
        );
        assert_eq!(result.stats.overflow_checks, 1);
    }

    #[test]
    fn test_lower_neg_has_overflow_check() {
        let func = make_neg();
        let result = lower_tir_to_llvm_ir(&func, "neg_test").expect("should lower");
        let ir = &result.llvm_ir;

        // Negation is 0 - x, so it uses ssub.with.overflow.
        assert!(
            ir.contains("llvm.ssub.with.overflow.i64"),
            "NegInt should use ssub.with.overflow. IR:\n{ir}"
        );
        assert_eq!(result.stats.overflow_checks, 1);
    }

    #[test]
    fn test_lower_intdiv_has_divzero_check() {
        let func = make_intdiv();
        let result = lower_tir_to_llvm_ir(&func, "intdiv_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("sdiv i64"),
            "IntDiv should contain sdiv. IR:\n{ir}"
        );
        assert!(
            ir.contains("icmp eq"),
            "IntDiv should check for zero. IR:\n{ir}"
        );
        // Euclidean adjustment: xor + icmp slt + select.
        assert!(
            ir.contains("select"),
            "IntDiv should have Euclidean adjustment via select. IR:\n{ir}"
        );
        assert_eq!(result.stats.divzero_checks, 1);
    }

    #[test]
    fn test_lower_modint_has_divzero_check() {
        let func = make_modint();
        let result = lower_tir_to_llvm_ir(&func, "modint_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("srem i64"),
            "ModInt should contain srem. IR:\n{ir}"
        );
        assert!(
            ir.contains("select"),
            "ModInt should have Euclidean adjustment via select. IR:\n{ir}"
        );
        assert_eq!(result.stats.divzero_checks, 1);
    }

    // =========================================================================
    // Comparison tests
    // =========================================================================

    #[test]
    fn test_lower_gt_comparison() {
        let func = make_comparison();
        let result = lower_tir_to_llvm_ir(&func, "cmp_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("icmp sgt"),
            "GtInt should produce icmp sgt. IR:\n{ir}"
        );
        assert!(
            ir.contains("zext i1"),
            "Comparison result should be zero-extended to i64. IR:\n{ir}"
        );
    }

    #[test]
    fn test_lower_all_comparisons() {
        // Test that all six comparison opcodes produce the right icmp condition.
        let cases: Vec<(Opcode, &str)> = vec![
            (
                Opcode::Eq {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "icmp eq",
            ),
            (
                Opcode::Neq {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "icmp ne",
            ),
            (
                Opcode::LtInt {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "icmp slt",
            ),
            (
                Opcode::LeInt {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "icmp sle",
            ),
            (
                Opcode::GtInt {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "icmp sgt",
            ),
            (
                Opcode::GeInt {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "icmp sge",
            ),
        ];

        for (opcode, expected_cmp) in cases {
            let mut func = BytecodeFunction::new("cmp_all".to_string(), 0);
            func.emit(Opcode::LoadImm { rd: 0, value: 5 });
            func.emit(Opcode::LoadImm { rd: 1, value: 3 });
            func.emit(opcode);
            func.emit(Opcode::Ret { rs: 2 });

            let result = lower_tir_to_llvm_ir(&func, "cmp_all").expect("should lower");
            assert!(
                result.llvm_ir.contains(expected_cmp),
                "Opcode {:?} should produce {}. IR:\n{}",
                opcode,
                expected_cmp,
                result.llvm_ir
            );
        }
    }

    // =========================================================================
    // Boolean operation tests
    // =========================================================================

    #[test]
    fn test_lower_boolean_and() {
        let func = make_boolean_and();
        let result = lower_tir_to_llvm_ir(&func, "and_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("and i1"),
            "And should produce i1 `and`. IR:\n{ir}"
        );
        assert!(
            ir.contains("zext i1"),
            "And should zext to i64. IR:\n{ir}"
        );
    }

    #[test]
    fn test_lower_boolean_or() {
        let mut func = BytecodeFunction::new("bool_or".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Or {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "or_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("or i1"),
            "Or should produce i1 `or`. IR:\n{ir}"
        );
    }

    #[test]
    fn test_lower_boolean_not() {
        let func = make_boolean_not();
        let result = lower_tir_to_llvm_ir(&func, "not_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("icmp eq i64"),
            "Not should produce icmp eq (zero-check). IR:\n{ir}"
        );
    }

    #[test]
    fn test_lower_implies() {
        let func = make_implies();
        let result = lower_tir_to_llvm_ir(&func, "implies_test").expect("should lower");
        let ir = &result.llvm_ir;

        // Implies is !a || b: icmp eq (for !a) + icmp ne (for b) + or.
        assert!(
            ir.contains("icmp eq"),
            "Implies should have icmp eq for !a. IR:\n{ir}"
        );
        assert!(
            ir.contains("or i1"),
            "Implies should have or for !a || b. IR:\n{ir}"
        );
    }

    #[test]
    fn test_lower_equiv() {
        let func = make_equiv();
        let result = lower_tir_to_llvm_ir(&func, "equiv_test").expect("should lower");
        let ir = &result.llvm_ir;

        // Equiv is (a != 0) == (b != 0).
        assert!(
            ir.contains("icmp eq i1"),
            "Equiv should compare i1 booleans for equality. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Module structure tests
    // =========================================================================

    #[test]
    fn test_module_header_present() {
        let func = make_return_42();
        let result = lower_tir_to_llvm_ir(&func, "header_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("; ModuleID = 'header_test'"),
            "IR should have module ID. IR:\n{ir}"
        );
        assert!(
            ir.contains("source_filename"),
            "IR should have source_filename. IR:\n{ir}"
        );
        assert!(
            ir.contains("target datalayout"),
            "IR should have target datalayout. IR:\n{ir}"
        );
    }

    #[test]
    fn test_overflow_intrinsics_declared() {
        let func = make_add();
        let result = lower_tir_to_llvm_ir(&func, "decl_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("declare { i64, i1 } @llvm.sadd.with.overflow.i64"),
            "sadd intrinsic should be declared. IR:\n{ir}"
        );
        assert!(
            ir.contains("declare { i64, i1 } @llvm.ssub.with.overflow.i64"),
            "ssub intrinsic should be declared. IR:\n{ir}"
        );
        assert!(
            ir.contains("declare { i64, i1 } @llvm.smul.with.overflow.i64"),
            "smul intrinsic should be declared. IR:\n{ir}"
        );
    }

    #[test]
    fn test_register_allocation_with_alloca() {
        let func = make_return_42();
        let result = lower_tir_to_llvm_ir(&func, "alloca_test").expect("should lower");
        let ir = &result.llvm_ir;

        // Register r0 should have an alloca.
        assert!(
            ir.contains("%r0_ptr = alloca i64"),
            "Register r0 should have alloca. IR:\n{ir}"
        );
    }

    // =========================================================================
    // Error handling tests
    // =========================================================================

    #[test]
    fn test_unsupported_opcode_error() {
        // ForallBegin is a quantifier opcode — NOT supported by direct lowering.
        let mut func = BytecodeFunction::new("unsupported".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::ForallBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 2,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let err = lower_tir_to_llvm_ir(&func, "bad").unwrap_err();
        assert!(
            err.to_string().contains("unsupported"),
            "Error should mention unsupported: {err}"
        );
    }

    // =========================================================================
    // Combined operation tests
    // =========================================================================

    #[test]
    fn test_lower_combined_arithmetic_and_comparison() {
        // (a + b) > 0
        let mut func = BytecodeFunction::new("combined".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 0 });
        func.emit(Opcode::GtInt {
            rd: 4,
            r1: 2,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let result = lower_tir_to_llvm_ir(&func, "combined").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(ir.contains("sadd.with.overflow"));
        assert!(ir.contains("icmp sgt"));
        assert_eq!(result.stats.opcodes_lowered, 6);
    }

    #[test]
    fn test_lower_combined_logic_chain() {
        // (a > 0) /\ (b > 0) => (a + b > 0)
        let mut func = BytecodeFunction::new("logic_chain".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });  // a
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });  // b
        func.emit(Opcode::LoadImm { rd: 2, value: 0 });  // zero

        func.emit(Opcode::GtInt {
            rd: 3,
            r1: 0,
            r2: 2,
        }); // a > 0
        func.emit(Opcode::GtInt {
            rd: 4,
            r1: 1,
            r2: 2,
        }); // b > 0
        func.emit(Opcode::And {
            rd: 5,
            r1: 3,
            r2: 4,
        }); // (a > 0) /\ (b > 0)

        func.emit(Opcode::AddInt {
            rd: 6,
            r1: 0,
            r2: 1,
        }); // a + b
        func.emit(Opcode::GtInt {
            rd: 7,
            r1: 6,
            r2: 2,
        }); // a + b > 0

        func.emit(Opcode::Implies {
            rd: 8,
            r1: 5,
            r2: 7,
        }); // antecedent => consequent
        func.emit(Opcode::Ret { rs: 8 });

        let result = lower_tir_to_llvm_ir(&func, "logic_chain").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(ir.contains("icmp sgt"));
        assert!(ir.contains("and i1"));
        assert!(ir.contains("sadd.with.overflow"));
        assert!(ir.contains("or i1")); // implies uses or
        assert_eq!(result.stats.opcodes_lowered, 10);
    }

    // =========================================================================
    // Comparison: tMIR-based pipeline vs direct TIR lowering
    // =========================================================================

    #[test]
    fn test_tir_direct_vs_tmir_pipeline_both_produce_ir() {
        // Both paths should produce valid LLVM IR for the same function.
        let func = make_add();

        // Direct TIR lowering path.
        let tir_result = lower_tir_to_llvm_ir(&func, "add_tir").expect("TIR should lower");

        // tMIR pipeline path.
        let tmir_result = crate::compile_invariant(&func, "add_tmir", crate::OptLevel::O1)
            .expect("tMIR should compile");

        // Both should contain function definitions.
        assert!(
            tir_result.llvm_ir.contains("define"),
            "TIR IR should have function definition"
        );
        assert!(
            tmir_result.llvm_ir.contains("define"),
            "tMIR IR should have function definition"
        );

        // Both should contain overflow-checked addition.
        assert!(
            tir_result.llvm_ir.contains("sadd.with.overflow")
                || tir_result.llvm_ir.contains("sadd"),
            "TIR IR should have add. IR:\n{}",
            tir_result.llvm_ir
        );
        assert!(
            tmir_result.llvm_ir.contains("sadd.with.overflow"),
            "tMIR IR should have overflow-checked add. IR:\n{}",
            tmir_result.llvm_ir
        );
    }

    #[test]
    fn test_tir_direct_vs_tmir_pipeline_comparisons() {
        let func = make_comparison();

        let tir_result = lower_tir_to_llvm_ir(&func, "cmp_tir").expect("TIR should lower");
        let tmir_result = crate::compile_invariant(&func, "cmp_tmir", crate::OptLevel::O1)
            .expect("tMIR should compile");

        // Both should contain signed greater-than comparison.
        assert!(
            tir_result.llvm_ir.contains("icmp sgt"),
            "TIR IR should have icmp sgt"
        );
        assert!(
            tmir_result.llvm_ir.contains("icmp sgt"),
            "tMIR IR should have icmp sgt"
        );
    }

    #[test]
    fn test_tir_direct_vs_tmir_pipeline_boolean_ops() {
        let func = make_boolean_and();

        let tir_result = lower_tir_to_llvm_ir(&func, "and_tir").expect("TIR should lower");
        let tmir_result = crate::compile_invariant(&func, "and_tmir", crate::OptLevel::O1)
            .expect("tMIR should compile");

        // Both should contain boolean and operation.
        assert!(
            tir_result.llvm_ir.contains("and i"),
            "TIR IR should have `and`. IR:\n{}",
            tir_result.llvm_ir
        );
        assert!(
            tmir_result.llvm_ir.contains("and i64"),
            "tMIR IR should have `and i64`. IR:\n{}",
            tmir_result.llvm_ir
        );
    }

    // =========================================================================
    // Phase 2: Control flow tests
    // =========================================================================

    /// Build a function with an unconditional jump: Jump over one instruction.
    fn make_unconditional_jump() -> BytecodeFunction {
        // r0 = 10
        // Jump +2  (skip the r0=99 instruction, land on Ret)
        // r0 = 99  (dead code)
        // Ret r0
        let mut func = BytecodeFunction::new("jump_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // pc=0
        func.emit(Opcode::Jump { offset: 2 });             // pc=1, target=3
        func.emit(Opcode::LoadImm { rd: 0, value: 99 });   // pc=2 (dead)
        func.emit(Opcode::Ret { rs: 0 });                  // pc=3
        func
    }

    #[test]
    fn test_lower_unconditional_jump() {
        let func = make_unconditional_jump();
        let result = lower_tir_to_llvm_ir(&func, "jump_test").expect("should lower");
        let ir = &result.llvm_ir;

        // Should have an unconditional branch.
        assert!(
            ir.contains("br label %"),
            "Jump should produce br label. IR:\n{ir}"
        );
        // Should have basic block labels.
        assert!(
            ir.contains("bb_"),
            "Should have basic block labels. IR:\n{ir}"
        );
        assert_eq!(result.stats.opcodes_lowered, 4);
        assert!(
            result.stats.basic_blocks >= 2,
            "Should have at least 2 basic blocks, got {}. IR:\n{ir}",
            result.stats.basic_blocks
        );
    }

    /// Build a function with a conditional branch (JumpFalse for if-then-else).
    fn make_conditional_branch() -> BytecodeFunction {
        // r0 = cond (1 = true)
        // JumpFalse r0 +2  -> skip to else
        // r1 = 42           (then branch)
        // Jump +2           (skip else)
        // r1 = 0            (else branch)
        // Ret r1
        let mut func = BytecodeFunction::new("cond_test".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true }); // pc=0
        func.emit(Opcode::JumpFalse {                       // pc=1, target=3
            rs: 0,
            offset: 2,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 42 });    // pc=2 (then)
        func.emit(Opcode::Jump { offset: 2 });               // pc=3, target=5
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });     // pc=4 (else)
        func.emit(Opcode::Ret { rs: 1 });                   // pc=5
        func
    }

    #[test]
    fn test_lower_conditional_branch() {
        let func = make_conditional_branch();
        let result = lower_tir_to_llvm_ir(&func, "cond_test").expect("should lower");
        let ir = &result.llvm_ir;

        // Should have conditional branch (JumpFalse -> br i1 with icmp eq).
        assert!(
            ir.contains("br i1"),
            "JumpFalse should produce conditional br. IR:\n{ir}"
        );
        // Should have at least 3 basic blocks (entry-cond, then, else/merge).
        assert!(
            result.stats.basic_blocks >= 3,
            "Should have at least 3 basic blocks, got {}. IR:\n{ir}",
            result.stats.basic_blocks
        );
        assert_eq!(result.stats.opcodes_lowered, 6);
    }

    /// Build a function with JumpTrue (short-circuit evaluation).
    fn make_jump_true_branch() -> BytecodeFunction {
        // r0 = 1 (true)
        // JumpTrue r0 +2  -> skip to end
        // r0 = 0            (false path)
        // Ret r0
        let mut func = BytecodeFunction::new("jump_true_test".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true }); // pc=0
        func.emit(Opcode::JumpTrue {                        // pc=1, target=3
            rs: 0,
            offset: 2,
        });
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });     // pc=2 (false path)
        func.emit(Opcode::Ret { rs: 0 });                   // pc=3
        func
    }

    #[test]
    fn test_lower_jump_true() {
        let func = make_jump_true_branch();
        let result = lower_tir_to_llvm_ir(&func, "jump_true_test").expect("should lower");
        let ir = &result.llvm_ir;

        // JumpTrue checks icmp ne (nonzero = true).
        assert!(
            ir.contains("icmp ne i64"),
            "JumpTrue should check icmp ne for truth. IR:\n{ir}"
        );
        assert!(
            ir.contains("br i1"),
            "JumpTrue should produce conditional br. IR:\n{ir}"
        );
        assert_eq!(result.stats.opcodes_lowered, 4);
    }

    // =========================================================================
    // Phase 2: Function call tests
    // =========================================================================

    /// Build a function with a Call instruction.
    fn make_call() -> BytecodeFunction {
        // r0 = 10
        // r1 = 20
        // r2 = call @op_0(r0, r1)
        // Ret r2
        let mut func = BytecodeFunction::new("call_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::Call {
            rd: 2,
            op_idx: 0,
            args_start: 0,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    #[test]
    fn test_lower_call() {
        let func = make_call();
        let result = lower_tir_to_llvm_ir(&func, "call_test").expect("should lower");
        let ir = &result.llvm_ir;

        // Should declare the external function.
        assert!(
            ir.contains("declare i64 @op_0(i64, i64)"),
            "Should declare external function op_0. IR:\n{ir}"
        );
        // Should emit a call instruction.
        assert!(
            ir.contains("call i64 @op_0("),
            "Should emit call to op_0. IR:\n{ir}"
        );
        assert_eq!(result.stats.calls_emitted, 1);
        assert_eq!(result.stats.opcodes_lowered, 4);
    }

    /// Build a function with a zero-arg Call instruction.
    fn make_call_zero_args() -> BytecodeFunction {
        // r0 = call @op_5()
        // Ret r0
        let mut func = BytecodeFunction::new("call_zero".to_string(), 0);
        func.emit(Opcode::Call {
            rd: 0,
            op_idx: 5,
            args_start: 0,
            argc: 0,
        });
        func.emit(Opcode::Ret { rs: 0 });
        func
    }

    #[test]
    fn test_lower_call_zero_args() {
        let func = make_call_zero_args();
        let result = lower_tir_to_llvm_ir(&func, "call_zero").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("declare i64 @op_5()"),
            "Should declare zero-arg function. IR:\n{ir}"
        );
        assert!(
            ir.contains("call i64 @op_5()"),
            "Should emit zero-arg call. IR:\n{ir}"
        );
        assert_eq!(result.stats.calls_emitted, 1);
    }

    // =========================================================================
    // Phase 2: Eligibility tests
    // =========================================================================

    #[test]
    fn test_eligibility_with_control_flow() {
        let func = make_conditional_branch();
        assert!(
            is_tir_eligible(&func),
            "Function with Jump/JumpFalse should be eligible"
        );
    }

    #[test]
    fn test_eligibility_with_call() {
        let func = make_call();
        assert!(
            is_tir_eligible(&func),
            "Function with Call should be eligible"
        );
    }

    // =========================================================================
    // Phase 2: Combined control flow + arithmetic
    // =========================================================================

    #[test]
    fn test_lower_if_then_else_with_arithmetic() {
        // IF r0 > 0 THEN r0 + 10 ELSE r0 - 5
        let mut func = BytecodeFunction::new("if_arith".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 3 });     // pc=0: r0 = 3
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });     // pc=1: r1 = 0
        func.emit(Opcode::GtInt {                            // pc=2: r2 = r0 > 0
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::JumpFalse {                        // pc=3: if !r2, goto pc=7
            rs: 2,
            offset: 4,
        });
        // Then branch: r3 = r0 + 10
        func.emit(Opcode::LoadImm { rd: 1, value: 10 });    // pc=4
        func.emit(Opcode::AddInt {                           // pc=5: r3 = r0 + 10
            rd: 3,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Jump { offset: 3 });               // pc=6: goto pc=9
        // Else branch: r3 = r0 - 5
        func.emit(Opcode::LoadImm { rd: 1, value: 5 });     // pc=7
        func.emit(Opcode::SubInt {                           // pc=8: r3 = r0 - 5
            rd: 3,
            r1: 0,
            r2: 1,
        });
        // Merge point
        func.emit(Opcode::Ret { rs: 3 });                   // pc=9

        let result = lower_tir_to_llvm_ir(&func, "if_arith").expect("should lower");
        let ir = &result.llvm_ir;

        // Should have both overflow-checked add and sub.
        assert!(ir.contains("sadd.with.overflow"), "IR:\n{ir}");
        assert!(ir.contains("ssub.with.overflow"), "IR:\n{ir}");
        // Should have conditional branch.
        assert!(ir.contains("br i1"), "IR:\n{ir}");
        // Should have basic blocks for then, else, and merge paths.
        assert!(
            result.stats.basic_blocks >= 3,
            "Should have at least 3 blocks, got {}. IR:\n{ir}",
            result.stats.basic_blocks
        );
        assert_eq!(result.stats.opcodes_lowered, 10);
    }

    #[test]
    fn test_lower_call_with_branch() {
        // Call a function, then branch on the result.
        let mut func = BytecodeFunction::new("call_branch".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });    // pc=0
        func.emit(Opcode::Call {                              // pc=1: r1 = op_3(r0)
            rd: 1,
            op_idx: 3,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::JumpTrue {                          // pc=2: if r1, goto 4
            rs: 1,
            offset: 2,
        });
        func.emit(Opcode::LoadImm { rd: 2, value: 0 });     // pc=3: false path
        func.emit(Opcode::Ret { rs: 2 });                   // pc=4

        let result = lower_tir_to_llvm_ir(&func, "call_branch").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("declare i64 @op_3(i64)"),
            "Should declare op_3. IR:\n{ir}"
        );
        assert!(
            ir.contains("call i64 @op_3("),
            "Should call op_3. IR:\n{ir}"
        );
        assert!(
            ir.contains("br i1"),
            "Should have conditional branch. IR:\n{ir}"
        );
        assert_eq!(result.stats.calls_emitted, 1);
    }

    // =========================================================================
    // Phase 2: Block structure validation
    // =========================================================================

    #[test]
    fn test_block_labels_present() {
        let func = make_conditional_branch();
        let result = lower_tir_to_llvm_ir(&func, "block_test").expect("should lower");
        let ir = &result.llvm_ir;

        // Should have entry block.
        assert!(
            ir.contains("bb_entry:"),
            "Should have bb_entry label. IR:\n{ir}"
        );
        // Target of JumpFalse at pc=1 with offset=2 -> pc=3
        assert!(
            ir.contains("bb_3:"),
            "Should have bb_3 label (JumpFalse target). IR:\n{ir}"
        );
    }

    #[test]
    fn test_halt_opcode() {
        let mut func = BytecodeFunction::new("halt_test".to_string(), 0);
        func.emit(Opcode::Halt);

        let result = lower_tir_to_llvm_ir(&func, "halt_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("call void @llvm.trap()"),
            "Halt should produce trap. IR:\n{ir}"
        );
        assert!(
            ir.contains("unreachable"),
            "Halt should produce unreachable. IR:\n{ir}"
        );
        assert_eq!(result.stats.opcodes_lowered, 1);
    }

    #[test]
    fn test_stats_basic_blocks_counted() {
        // A function with no branches should still have 1 basic block (entry).
        let func = make_return_42();
        let result = lower_tir_to_llvm_ir(&func, "simple").expect("should lower");
        assert!(
            result.stats.basic_blocks >= 1,
            "Even a straight-line function should have at least 1 basic block"
        );
    }

    // =========================================================================
    // Phase 3: Set operation tests
    // =========================================================================

    #[test]
    fn test_lower_set_enum() {
        let mut func = BytecodeFunction::new("set_enum".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let result = lower_tir_to_llvm_ir(&func, "set_enum_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_set_enum_3"),
            "SetEnum should call @tla_set_enum_3. IR:\n{ir}"
        );
        assert!(
            ir.contains("declare i64 @tla_set_enum_3(i64, i64, i64)"),
            "Should declare @tla_set_enum_3 with 3 params. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
        assert_eq!(result.stats.opcodes_lowered, 5);
    }

    #[test]
    fn test_lower_set_in() {
        let mut func = BytecodeFunction::new("set_in".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 }); // elem
        func.emit(Opcode::LoadImm { rd: 1, value: 99 }); // set (opaque)
        func.emit(Opcode::SetIn {
            rd: 2,
            elem: 0,
            set: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "set_in_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_set_in"),
            "SetIn should call @tla_set_in. IR:\n{ir}"
        );
        assert!(
            ir.contains("declare i64 @tla_set_in(i64, i64)"),
            "Should declare @tla_set_in. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_set_binary_ops() {
        let ops_and_funcs: Vec<(Opcode, &str)> = vec![
            (
                Opcode::SetUnion {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "tla_set_union",
            ),
            (
                Opcode::SetIntersect {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "tla_set_intersect",
            ),
            (
                Opcode::SetDiff {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "tla_set_diff",
            ),
            (
                Opcode::Subseteq {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                "tla_set_subseteq",
            ),
        ];

        for (opcode, func_name) in ops_and_funcs {
            let mut func = BytecodeFunction::new("set_bin".to_string(), 0);
            func.emit(Opcode::LoadImm { rd: 0, value: 10 });
            func.emit(Opcode::LoadImm { rd: 1, value: 20 });
            func.emit(opcode);
            func.emit(Opcode::Ret { rs: 2 });

            let result = lower_tir_to_llvm_ir(&func, "set_bin").expect("should lower");
            let ir = &result.llvm_ir;

            assert!(
                ir.contains(&format!("@{func_name}")),
                "Opcode should call @{func_name}. IR:\n{ir}"
            );
            assert!(
                ir.contains(&format!("declare i64 @{func_name}(i64, i64)")),
                "Should declare @{func_name}. IR:\n{ir}"
            );
            assert_eq!(result.stats.runtime_calls, 1, "for {func_name}");
        }
    }

    #[test]
    fn test_lower_set_unary_ops() {
        let ops_and_funcs: Vec<(Opcode, &str)> = vec![
            (Opcode::Powerset { rd: 1, rs: 0 }, "tla_set_powerset"),
            (Opcode::BigUnion { rd: 1, rs: 0 }, "tla_set_big_union"),
        ];

        for (opcode, func_name) in ops_and_funcs {
            let mut func = BytecodeFunction::new("set_unary".to_string(), 0);
            func.emit(Opcode::LoadImm { rd: 0, value: 10 });
            func.emit(opcode);
            func.emit(Opcode::Ret { rs: 1 });

            let result = lower_tir_to_llvm_ir(&func, "set_unary").expect("should lower");
            let ir = &result.llvm_ir;

            assert!(
                ir.contains(&format!("@{func_name}")),
                "Opcode should call @{func_name}. IR:\n{ir}"
            );
            assert_eq!(result.stats.runtime_calls, 1, "for {func_name}");
        }
    }

    #[test]
    fn test_lower_range() {
        let mut func = BytecodeFunction::new("range".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 10 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "range_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_set_range"),
            "Range should call @tla_set_range. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_ksubset() {
        let mut func = BytecodeFunction::new("ksubset".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // base set
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });  // k
        func.emit(Opcode::KSubset {
            rd: 2,
            base: 0,
            k: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "ksubset_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_set_ksubset"),
            "KSubset should call @tla_set_ksubset. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    // =========================================================================
    // Phase 3: Sequence operation tests
    // =========================================================================

    #[test]
    fn test_lower_seq_new() {
        let mut func = BytecodeFunction::new("seq_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "seq_new_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_seq_new_2"),
            "SeqNew should call @tla_seq_new_2. IR:\n{ir}"
        );
        assert!(
            ir.contains("declare i64 @tla_seq_new_2(i64, i64)"),
            "Should declare @tla_seq_new_2. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_concat() {
        let mut func = BytecodeFunction::new("concat".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::Concat {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "concat_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_seq_concat"),
            "Concat should call @tla_seq_concat. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    // =========================================================================
    // Phase 3: Tuple operation tests
    // =========================================================================

    #[test]
    fn test_lower_tuple_new() {
        let mut func = BytecodeFunction::new("tuple_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::TupleNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "tuple_new_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_tuple_new_2"),
            "TupleNew should call @tla_tuple_new_2. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_tuple_get() {
        let mut func = BytecodeFunction::new("tuple_get".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 99 }); // tuple handle
        func.emit(Opcode::TupleGet {
            rd: 1,
            rs: 0,
            idx: 2,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let result = lower_tir_to_llvm_ir(&func, "tuple_get_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_tuple_get"),
            "TupleGet should call @tla_tuple_get. IR:\n{ir}"
        );
        // idx=2 should be passed as immediate
        assert!(
            ir.contains("i64 2)"),
            "TupleGet should pass idx as i64 immediate. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    // =========================================================================
    // Phase 3: Record/Function operation tests
    // =========================================================================

    #[test]
    fn test_lower_record_get() {
        let mut func = BytecodeFunction::new("record_get".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 99 }); // record handle
        func.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: 5,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let result = lower_tir_to_llvm_ir(&func, "record_get_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_record_get"),
            "RecordGet should call @tla_record_get. IR:\n{ir}"
        );
        assert!(
            ir.contains("i64 5)"),
            "RecordGet should pass field_idx as i64 immediate. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_func_apply() {
        let mut func = BytecodeFunction::new("func_apply".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // func handle
        func.emit(Opcode::LoadImm { rd: 1, value: 42 }); // arg
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "func_apply_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_func_apply"),
            "FuncApply should call @tla_func_apply. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_domain() {
        let mut func = BytecodeFunction::new("domain".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // func handle
        func.emit(Opcode::Domain { rd: 1, rs: 0 });
        func.emit(Opcode::Ret { rs: 1 });

        let result = lower_tir_to_llvm_ir(&func, "domain_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_domain"),
            "Domain should call @tla_domain. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    // =========================================================================
    // Phase 3: LoadConst and CondMove tests
    // =========================================================================

    #[test]
    fn test_lower_load_const() {
        let mut func = BytecodeFunction::new("load_const".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx: 7 });
        func.emit(Opcode::Ret { rs: 0 });

        let result = lower_tir_to_llvm_ir(&func, "load_const_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_load_const"),
            "LoadConst should call @tla_load_const. IR:\n{ir}"
        );
        assert!(
            ir.contains("i64 7)"),
            "LoadConst should pass idx=7. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_cond_move() {
        let mut func = BytecodeFunction::new("cond_move".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 99 });  // else value (rd)
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });   // cond (true)
        func.emit(Opcode::LoadImm { rd: 2, value: 42 });  // then value (rs)
        func.emit(Opcode::CondMove {
            rd: 0,
            cond: 1,
            rs: 2,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let result = lower_tir_to_llvm_ir(&func, "cond_move_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("select i1"),
            "CondMove should produce LLVM select. IR:\n{ir}"
        );
        // No runtime call for CondMove.
        assert_eq!(result.stats.runtime_calls, 0);
        assert_eq!(result.stats.opcodes_lowered, 5);
    }

    // =========================================================================
    // Phase 3: CallBuiltin tests
    // =========================================================================

    #[test]
    fn test_lower_call_builtin_len() {
        let mut func = BytecodeFunction::new("builtin_len".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // seq handle
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Len,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let result = lower_tir_to_llvm_ir(&func, "builtin_len_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_seq_len"),
            "CallBuiltin(Len) should call @tla_seq_len. IR:\n{ir}"
        );
        assert!(
            ir.contains("declare i64 @tla_seq_len(i64)"),
            "Should declare @tla_seq_len. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_call_builtin_append() {
        let mut func = BytecodeFunction::new("builtin_append".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // seq handle
        func.emit(Opcode::LoadImm { rd: 1, value: 42 }); // element
        func.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::Append,
            args_start: 0,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let result = lower_tir_to_llvm_ir(&func, "builtin_append_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_seq_append"),
            "CallBuiltin(Append) should call @tla_seq_append. IR:\n{ir}"
        );
        assert!(
            ir.contains("declare i64 @tla_seq_append(i64, i64)"),
            "Should declare @tla_seq_append. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_call_builtin_subseq() {
        let mut func = BytecodeFunction::new("builtin_subseq".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // seq
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });  // lo
        func.emit(Opcode::LoadImm { rd: 2, value: 5 });  // hi
        func.emit(Opcode::CallBuiltin {
            rd: 3,
            builtin: BuiltinOp::SubSeq,
            args_start: 0,
            argc: 3,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let result = lower_tir_to_llvm_ir(&func, "builtin_subseq_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_seq_subseq"),
            "CallBuiltin(SubSeq) should call @tla_seq_subseq. IR:\n{ir}"
        );
        assert!(
            ir.contains("declare i64 @tla_seq_subseq(i64, i64, i64)"),
            "Should declare @tla_seq_subseq. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_call_builtin_cardinality() {
        let mut func = BytecodeFunction::new("builtin_card".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // set handle
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Cardinality,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let result = lower_tir_to_llvm_ir(&func, "builtin_card_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(
            ir.contains("@tla_cardinality"),
            "CallBuiltin(Cardinality) should call @tla_cardinality. IR:\n{ir}"
        );
        assert_eq!(result.stats.runtime_calls, 1);
    }

    #[test]
    fn test_lower_all_builtins() {
        // Test that all BuiltinOp variants produce the expected function name.
        let cases: Vec<(BuiltinOp, u8, &str)> = vec![
            (BuiltinOp::Len, 1, "tla_seq_len"),
            (BuiltinOp::Head, 1, "tla_seq_head"),
            (BuiltinOp::Tail, 1, "tla_seq_tail"),
            (BuiltinOp::Append, 2, "tla_seq_append"),
            (BuiltinOp::SubSeq, 3, "tla_seq_subseq"),
            (BuiltinOp::Seq, 1, "tla_seq_set"),
            (BuiltinOp::Cardinality, 1, "tla_cardinality"),
            (BuiltinOp::IsFiniteSet, 1, "tla_is_finite_set"),
            (BuiltinOp::ToString, 1, "tla_tostring"),
        ];

        for (builtin, argc, expected_fn) in cases {
            let mut func = BytecodeFunction::new("builtin_all".to_string(), 0);
            for i in 0..argc {
                func.emit(Opcode::LoadImm {
                    rd: i,
                    value: (i + 1) as i64,
                });
            }
            func.emit(Opcode::CallBuiltin {
                rd: argc,
                builtin,
                args_start: 0,
                argc,
            });
            func.emit(Opcode::Ret { rs: argc });

            let result = lower_tir_to_llvm_ir(&func, "builtin_all").expect("should lower");
            assert!(
                result.llvm_ir.contains(&format!("@{expected_fn}")),
                "BuiltinOp::{builtin:?} should call @{expected_fn}. IR:\n{}",
                result.llvm_ir,
            );
        }
    }

    // =========================================================================
    // Phase 3: Eligibility tests
    // =========================================================================

    #[test]
    fn test_eligibility_set_enum() {
        let mut func = BytecodeFunction::new("elig_set".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            is_tir_eligible(&func),
            "Functions with SetEnum should now be eligible"
        );
    }

    #[test]
    fn test_eligibility_call_builtin() {
        let mut func = BytecodeFunction::new("elig_builtin".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Len,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            is_tir_eligible(&func),
            "Functions with CallBuiltin should be eligible"
        );
    }

    #[test]
    fn test_eligibility_quantifier_still_ineligible() {
        let mut func = BytecodeFunction::new("elig_quant".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::ForallBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 2,
        });
        func.emit(Opcode::Ret { rs: 1 });
        assert!(
            !is_tir_eligible(&func),
            "Functions with quantifiers should still be ineligible"
        );
    }

    // =========================================================================
    // Phase 3: Combined tests
    // =========================================================================

    #[test]
    fn test_lower_set_membership_in_branch() {
        // if (elem \in set) then 1 else 0
        let mut func = BytecodeFunction::new("set_in_branch".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });   // pc=0: elem
        func.emit(Opcode::LoadImm { rd: 1, value: 99 });   // pc=1: set
        func.emit(Opcode::SetIn {                           // pc=2: r2 = elem \in set
            rd: 2,
            elem: 0,
            set: 1,
        });
        func.emit(Opcode::JumpFalse {                       // pc=3: if !r2, goto 6
            rs: 2,
            offset: 3,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });    // pc=4: then
        func.emit(Opcode::Jump { offset: 2 });              // pc=5: goto 7
        func.emit(Opcode::LoadImm { rd: 3, value: 0 });    // pc=6: else
        func.emit(Opcode::Ret { rs: 3 });                   // pc=7

        let result =
            lower_tir_to_llvm_ir(&func, "set_in_branch_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(ir.contains("@tla_set_in"), "IR:\n{ir}");
        assert!(ir.contains("br i1"), "Should have conditional branch. IR:\n{ir}");
        assert_eq!(result.stats.runtime_calls, 1);
        assert_eq!(result.stats.opcodes_lowered, 8);
    }

    #[test]
    fn test_lower_combined_set_and_cardinality() {
        // Build a set, take its cardinality.
        let mut func = BytecodeFunction::new("set_card".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 3,
            builtin: BuiltinOp::Cardinality,
            args_start: 2,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let result = lower_tir_to_llvm_ir(&func, "set_card_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(ir.contains("@tla_set_enum_2"), "IR:\n{ir}");
        assert!(ir.contains("@tla_cardinality"), "IR:\n{ir}");
        assert_eq!(result.stats.runtime_calls, 2);
    }

    #[test]
    fn test_lower_seq_and_len() {
        // Build a sequence, take its length.
        let mut func = BytecodeFunction::new("seq_len".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::LoadImm { rd: 2, value: 30 });
        func.emit(Opcode::SeqNew {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Len,
            args_start: 3,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let result = lower_tir_to_llvm_ir(&func, "seq_len_test").expect("should lower");
        let ir = &result.llvm_ir;

        assert!(ir.contains("@tla_seq_new_3"), "IR:\n{ir}");
        assert!(ir.contains("@tla_seq_len"), "IR:\n{ir}");
        assert_eq!(result.stats.runtime_calls, 2);
    }
}
