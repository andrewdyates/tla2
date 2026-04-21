// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LLVM IR text emission from tMIR modules.
//!
//! Produces LLVM-compatible `.ll` text IR from a [`tmir::Module`]. This is
//! the bridge layer: tMIR is already close to LLVM IR (SSA, typed, explicit
//! memory ops), so the translation is mostly syntactic.
//!
//! When the LLVM2 crate becomes available as a workspace dependency, this
//! textual emitter can be replaced by direct LLVM2 API calls. For now, the
//! text format is the integration point: it can be fed to `llc` or `opt`
//! for native compilation and optimization.
//!
//! # LLVM IR Format Reference
//!
//! The emitted IR follows LLVM 18+ text format conventions:
//! - Opaque pointers (`ptr` instead of typed pointers)
//! - SSA values as `%N` (numbered), functions as `@name`
//! - Type syntax: `i8`, `i16`, `i32`, `i64`, `i128`, `float`, `double`, `ptr`, `void`

use crate::Llvm2Error;
use std::collections::HashMap;
use std::fmt::Write;
use tmir::constant::Constant;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::value::BlockId;
use tmir::{Block, Function, Module};

/// Helper macro to reduce `.map_err(|e| Llvm2Error::Emission(e.to_string()))`
/// boilerplate on every `write!`/`writeln!` call.
macro_rules! emit {
    ($dst:expr, $($arg:tt)*) => {
        write!($dst, $($arg)*).map_err(|e| Llvm2Error::Emission(e.to_string()))
    };
}

macro_rules! emitln {
    ($dst:expr) => {
        writeln!($dst).map_err(|e| Llvm2Error::Emission(e.to_string()))
    };
    ($dst:expr, $($arg:tt)*) => {
        writeln!($dst, $($arg)*).map_err(|e| Llvm2Error::Emission(e.to_string()))
    };
}

/// Emit LLVM IR text for an entire tMIR module.
///
/// Returns the complete `.ll` file content as a string.
///
/// # Errors
///
/// Returns [`Llvm2Error::Emission`] if any instruction cannot be translated.
pub(crate) fn emit_module(module: &Module) -> Result<String, Llvm2Error> {
    let mut ctx = EmitCtx::new(module);
    ctx.emit_module()?;
    Ok(ctx.output)
}

/// Emission context holding output buffer and module-level state.
struct EmitCtx<'m> {
    module: &'m Module,
    output: String,
    /// Map from FuncId to function name for call resolution.
    func_names: HashMap<u32, String>,
    /// Map from FuncId index to FuncTyId index for O(1) callee type lookups.
    /// Replaces linear scan through module.functions for every Call instruction.
    func_ty_ids: HashMap<u32, usize>,
    /// Counter for generating unique assert failure block labels.
    assert_counter: u32,
    /// Counter for generating unique temporary register names (%_tmp_N).
    /// Used by lowered instruction patterns that need intermediate values
    /// (e.g., ExtractElement/InsertElement lowered to GEP+load/store).
    temp_counter: u32,
    /// Current function's return type string, set during emit_function.
    /// Used by Return instruction to emit the correct return type.
    current_return_ty: String,
    /// Current function's per-return-value types (set in emit_function).
    /// Used by multi-value Return to emit correct per-element types
    /// instead of hardcoded i64.
    current_return_element_tys: Vec<String>,
    /// SSA value type map for the current function. Populated when instructions
    /// produce results (Const, BinOp, Cast, etc.), used by GEP to emit the
    /// correct index type.
    value_types: HashMap<u32, Ty>,
}

impl<'m> EmitCtx<'m> {
    fn new(module: &'m Module) -> Self {
        let mut func_names = HashMap::new();
        let mut func_ty_ids = HashMap::new();
        for func in &module.functions {
            func_names.insert(func.id.index(), func.name.clone());
            func_ty_ids.insert(func.id.index(), func.ty.as_usize());
        }
        Self {
            module,
            output: String::with_capacity(4096),
            func_names,
            func_ty_ids,
            assert_counter: 0,
            temp_counter: 0,
            current_return_ty: String::new(),
            current_return_element_tys: Vec::new(),
            value_types: HashMap::new(),
        }
    }

    /// Resolve a tMIR type to its LLVM IR text representation.
    ///
    /// Unlike the old free-function `llvm_ty`, this method has access to the
    /// module's struct definitions, type table, and func_types, so it can
    /// produce proper LLVM aggregate types instead of collapsing everything
    /// to `ptr`.
    fn llvm_type(&self, ty: &Ty) -> String {
        match ty {
            Ty::I8 => "i8".to_string(),
            Ty::I16 => "i16".to_string(),
            Ty::I32 => "i32".to_string(),
            Ty::I64 => "i64".to_string(),
            Ty::I128 => "i128".to_string(),
            Ty::F32 => "float".to_string(),
            Ty::F64 => "double".to_string(),
            Ty::Bool => "i1".to_string(),
            Ty::Ptr => "ptr".to_string(),
            Ty::Unit => "void".to_string(),
            Ty::Struct(sid) => {
                // Emit named struct reference %struct.Name if we have the def.
                if let Some(sd) = self.module.structs.iter().find(|s| s.id == *sid) {
                    format!("%struct.{}", sd.name)
                } else {
                    // Fallback: unnamed struct reference by index.
                    format!("%struct.{}", sid.index())
                }
            }
            Ty::Array(elem_ty_id, len) => {
                // Resolve element type from the module's type table.
                let elem_ty = self
                    .module
                    .types
                    .get(elem_ty_id.as_usize())
                    .cloned()
                    .unwrap_or(Ty::I64);
                format!("[{} x {}]", len, self.llvm_type(&elem_ty))
            }
            Ty::Func(fty_id) => {
                // Emit LLVM function pointer type.
                if let Some(ft) = self.module.func_types.get(fty_id.as_usize()) {
                    let ret = self.format_return_type(ft);
                    let params: Vec<String> =
                        ft.params.iter().map(|t| self.llvm_type(t)).collect();
                    format!("ptr ; {} ({})", ret, params.join(", "))
                } else {
                    "ptr".to_string()
                }
            }
            // Unsigned integers map to same LLVM iN types as signed.
            Ty::U8 => "i8".to_string(),
            Ty::U16 => "i16".to_string(),
            Ty::U32 => "i32".to_string(),
            Ty::U64 => "i64".to_string(),
            Ty::U128 => "i128".to_string(),
            // Never type maps to void in LLVM.
            Ty::Never => "void".to_string(),
            // Tuple types are not directly representable; use opaque ptr.
            Ty::Tuple(_) => "ptr".to_string(),
            // Enum types are not directly representable; use opaque ptr.
            Ty::Enum(_) => "ptr".to_string(),
            // Reference types all lower to ptr in LLVM IR.
            Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) => {
                "ptr".to_string()
            }
            // Compound TLA+ types (Set/Sequence/Record/Closure) lower to opaque
            // ptr in LLVM IR; their layout is managed by the runtime.
            Ty::Set(_, _) | Ty::Sequence(_) | Ty::Record(_) | Ty::Closure(_) => {
                "ptr".to_string()
            }
        }
    }

    /// Format a FuncTy's return type as an LLVM IR type string.
    ///
    /// Deduplicates the `ft.returns.as_slice()` match pattern that previously
    /// appeared in emit_function, Call, and CallIndirect.
    fn format_return_type(&self, ft: &tmir::ty::FuncTy) -> String {
        match ft.returns.as_slice() {
            [] => "void".to_string(),
            [ty] => self.llvm_type(ty),
            tys => {
                let parts: Vec<String> = tys.iter().map(|t| self.llvm_type(t)).collect();
                format!("{{ {} }}", parts.join(", "))
            }
        }
    }

    fn emit_module(&mut self) -> Result<(), Llvm2Error> {
        // Module header.
        emitln!(self.output, "; ModuleID = '{}'", self.module.name)?;
        emitln!(
            self.output,
            "source_filename = \"{}\"",
            self.module.name
        )?;
        emitln!(
            self.output,
            "target datalayout = \"e-m:o-i64:64-i128:128-n32:64-S128\""
        )?;
        emitln!(self.output)?;

        // Struct type definitions.
        for sd in &self.module.structs {
            emit!(self.output, "%struct.{} = type {{ ", sd.name)?;
            for (i, field) in sd.fields.iter().enumerate() {
                if i > 0 {
                    emit!(self.output, ", ")?;
                }
                let ty_str = self.llvm_type(&field.ty);
                emit!(self.output, "{}", ty_str)?;
            }
            emitln!(self.output, " }}")?;
        }

        // Global declarations.
        for global in &self.module.globals {
            let mutability = if global.mutable { "global" } else { "constant" };
            let ty_str = self.llvm_type(&global.ty);
            let init = match &global.initializer {
                Some(c) => self.format_constant(c, &global.ty),
                None => llvm_zero_init(&global.ty),
            };
            emitln!(
                self.output,
                "@{} = {} {} {}",
                global.name,
                mutability,
                ty_str,
                init,
            )?;
        }

        // Intrinsic declarations for assert/assume lowering.
        emitln!(self.output, "declare void @llvm.trap() noreturn nounwind")?;
        emitln!(self.output, "declare void @llvm.assume(i1) nounwind")?;

        // Runtime helper declarations (external functions referenced by Call).
        self.emit_runtime_declarations()?;

        // Function definitions.
        for func in &self.module.functions {
            emitln!(self.output)?;
            self.emit_function(func)?;
        }

        Ok(())
    }

    fn emit_runtime_declarations(&mut self) -> Result<(), Llvm2Error> {
        // Emit external declarations for runtime helpers.
        for helper in crate::runtime::RUNTIME_HELPERS {
            let ret_str = llvm_ty_static(&helper.ret);
            emit!(self.output, "declare {} @{}(", ret_str, helper.symbol)?;
            for (i, param_ty) in helper.params.iter().enumerate() {
                if i > 0 {
                    emit!(self.output, ", ")?;
                }
                emit!(self.output, "{}", llvm_ty_static(param_ty))?;
            }
            emitln!(self.output, ")")?;
        }
        Ok(())
    }

    fn emit_function(&mut self, func: &Function) -> Result<(), Llvm2Error> {
        // Clear per-function state.
        self.value_types.clear();

        let ft_idx = func.ty.index() as usize;
        let func_ty = self.module.func_types.get(ft_idx).ok_or_else(|| {
            Llvm2Error::Emission(format!(
                "function '{}' references func type index {} but module has {} func types",
                func.name,
                ft_idx,
                self.module.func_types.len(),
            ))
        })?;

        // Function signature.
        let ret_ty = self.format_return_type(func_ty);

        // Store return type for use by Return instructions in this function.
        self.current_return_ty = ret_ty.clone();

        // Store per-element return types for multi-value returns so we
        // emit correct per-element types instead of hardcoded i64.
        self.current_return_element_tys = func_ty
            .returns
            .iter()
            .map(|t| self.llvm_type(t))
            .collect();

        emit!(self.output, "define {} @{}(", ret_ty, func.name)?;

        // Parameters are taken from the entry block's params.
        let entry_block = func.blocks.first().ok_or_else(|| {
            Llvm2Error::Emission(format!("function '{}' has no blocks", func.name))
        })?;

        for (i, (val_id, ty)) in entry_block.params.iter().enumerate() {
            if i > 0 {
                emit!(self.output, ", ")?;
            }
            let ty_str = self.llvm_type(ty);
            emit!(self.output, "{} %{}", ty_str, val_id.index())?;
        }

        emitln!(self.output, ") {{")?;

        // Emit blocks.
        for (block_idx, block) in func.blocks.iter().enumerate() {
            self.emit_block(block, block_idx == 0)?;
        }

        emitln!(self.output, "}}")?;

        Ok(())
    }

    fn emit_block(&mut self, block: &Block, is_entry: bool) -> Result<(), Llvm2Error> {
        // Record parameter types for GEP index type resolution.
        for (val, ty) in &block.params {
            self.value_types.insert(val.index(), ty.clone());
        }

        if is_entry {
            emitln!(self.output, "entry:")?;
        } else {
            emit!(self.output, "bb{}:", block.id.index())?;

            if !block.params.is_empty() {
                emit!(self.output, "  ; params:")?;
                for (val, ty) in &block.params {
                    let ty_str = self.llvm_type(ty);
                    emit!(self.output, " %{}:{}", val.index(), ty_str)?;
                }
            }
            emitln!(self.output)?;
        }

        // Emit instructions.
        for node in &block.body {
            self.emit_instruction(node)?;
        }

        Ok(())
    }

    fn emit_instruction(&mut self, node: &tmir::InstrNode) -> Result<(), Llvm2Error> {
        emit!(self.output, "  ")?;

        // If the instruction produces a result, emit the assignment.
        let result = node.results.first().copied();

        match &node.inst {
            Inst::BinOp { op, ty, lhs, rhs } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("BinOp has no result".to_string())
                })?;
                self.value_types.insert(r.index(), ty.clone());
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = {} {} %{}, %{}",
                    r.index(),
                    llvm_binop(op),
                    ty_str,
                    lhs.index(),
                    rhs.index(),
                )?;
            }
            Inst::UnOp { op, ty, operand } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("UnOp has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                match op {
                    UnOp::Neg => emitln!(
                        self.output,
                        "%{} = sub {} 0, %{}",
                        r.index(),
                        ty_str,
                        operand.index(),
                    )?,
                    UnOp::FNeg => emitln!(
                        self.output,
                        "%{} = fneg {} %{}",
                        r.index(),
                        ty_str,
                        operand.index(),
                    )?,
                    UnOp::Not => emitln!(
                        self.output,
                        "%{} = xor {} %{}, -1",
                        r.index(),
                        ty_str,
                        operand.index(),
                    )?,
                }
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("Overflow has no result".to_string())
                })?;
                let intrinsic = llvm_overflow_intrinsic(op, ty);
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = call {{ {}, i1 }} @{}({} %{}, {} %{})",
                    r.index(),
                    ty_str,
                    intrinsic,
                    ty_str,
                    lhs.index(),
                    ty_str,
                    rhs.index(),
                )?;
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("ICmp has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = icmp {} {} %{}, %{}",
                    r.index(),
                    llvm_icmp(op),
                    ty_str,
                    lhs.index(),
                    rhs.index(),
                )?;
            }
            Inst::FCmp { op, ty, lhs, rhs } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("FCmp has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = fcmp {} {} %{}, %{}",
                    r.index(),
                    llvm_fcmp(op),
                    ty_str,
                    lhs.index(),
                    rhs.index(),
                )?;
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("Cast has no result".to_string())
                })?;
                // Record the destination type for GEP index resolution.
                self.value_types.insert(r.index(), dst_ty.clone());
                let src = self.llvm_type(src_ty);
                let dst = self.llvm_type(dst_ty);
                emitln!(
                    self.output,
                    "%{} = {} {} %{} to {}",
                    r.index(),
                    llvm_cast(op),
                    src,
                    operand.index(),
                    dst,
                )?;
            }
            Inst::Load { ty, ptr, .. } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("Load has no result".to_string())
                })?;
                self.value_types.insert(r.index(), ty.clone());
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = load {}, ptr %{}",
                    r.index(),
                    ty_str,
                    ptr.index(),
                )?;
            }
            Inst::Store { ty, ptr, value, .. } => {
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "store {} %{}, ptr %{}",
                    ty_str,
                    value.index(),
                    ptr.index(),
                )?;
            }
            Inst::Alloca { ty, count, .. } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("Alloca has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                match count {
                    Some(c) => emitln!(
                        self.output,
                        "%{} = alloca {}, i32 %{}",
                        r.index(),
                        ty_str,
                        c.index(),
                    )?,
                    None => emitln!(
                        self.output,
                        "%{} = alloca {}",
                        r.index(),
                        ty_str,
                    )?,
                }
            }
            Inst::GEP {
                pointee_ty,
                base,
                indices,
            } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("GEP has no result".to_string())
                })?;
                let ty_str = self.llvm_type(pointee_ty);
                emit!(
                    self.output,
                    "%{} = getelementptr {}, ptr %{}",
                    r.index(),
                    ty_str,
                    base.index(),
                )?;
                for idx in indices {
                    // GEP index type must match the SSA value type. Look up the
                    // type from the value_types map (populated by Const, Cast,
                    // block params, etc.). Fall back to i64 if unknown.
                    let idx_ty = self.value_types.get(&idx.index())
                        .map(|t| self.llvm_type(t))
                        .unwrap_or_else(|| "i64".to_string());
                    emit!(self.output, ", {} %{}", idx_ty, idx.index())?;
                }
                emitln!(self.output)?;
            }
            Inst::AtomicLoad { ty, ptr, ordering } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("AtomicLoad has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = load atomic {}, ptr %{} {}",
                    r.index(),
                    ty_str,
                    ptr.index(),
                    llvm_ordering(ordering),
                )?;
            }
            Inst::AtomicStore {
                ty,
                ptr,
                value,
                ordering,
            } => {
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "store atomic {} %{}, ptr %{} {}",
                    ty_str,
                    value.index(),
                    ptr.index(),
                    llvm_ordering(ordering),
                )?;
            }
            Inst::AtomicRMW {
                op,
                ty,
                ptr,
                value,
                ordering,
            } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("AtomicRMW has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = atomicrmw {} ptr %{}, {} %{} {}",
                    r.index(),
                    llvm_rmw(op),
                    ptr.index(),
                    ty_str,
                    value.index(),
                    llvm_ordering(ordering),
                )?;
            }
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                success,
                failure,
            } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("CmpXchg has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = cmpxchg ptr %{}, {} %{}, {} %{} {} {}",
                    r.index(),
                    ptr.index(),
                    ty_str,
                    expected.index(),
                    ty_str,
                    desired.index(),
                    llvm_ordering(success),
                    llvm_ordering(failure),
                )?;
            }
            Inst::Fence { ordering } => {
                emitln!(self.output, "fence {}", llvm_ordering(ordering))?;
            }
            Inst::Br { target, args: _ } => {
                emitln!(self.output, "br label %{}", block_label(*target))?;
            }
            Inst::CondBr {
                cond,
                then_target,
                then_args: _,
                else_target,
                else_args: _,
            } => {
                emitln!(
                    self.output,
                    "br i1 %{}, label %{}, label %{}",
                    cond.index(),
                    block_label(*then_target),
                    block_label(*else_target),
                )?;
            }
            Inst::Switch {
                value,
                default,
                default_args: _,
                cases,
            } => {
                emit!(
                    self.output,
                    "switch i64 %{}, label %{} [",
                    value.index(),
                    block_label(*default),
                )?;
                for case in cases {
                    let case_val = match &case.value {
                        Constant::Int(v) => *v,
                        _ => {
                            return Err(Llvm2Error::Emission(
                                "switch case must be integer constant".to_string(),
                            ));
                        }
                    };
                    emit!(
                        self.output,
                        " i64 {}, label %{}",
                        case_val,
                        block_label(case.target),
                    )?;
                }
                emitln!(self.output, " ]")?;
            }
            Inst::Call { callee, args } => {
                let callee_name = self
                    .func_names
                    .get(&callee.index())
                    .cloned()
                    .unwrap_or_else(|| format!("func.{}", callee.index()));

                // Look up callee's FuncTy for proper return/param types.
                // Use pre-built func_ty_ids map for O(1) lookup instead of
                // linear scan through module.functions.
                let callee_func_ty = self
                    .func_ty_ids
                    .get(&callee.index())
                    .and_then(|&ft_idx| self.module.func_types.get(ft_idx));

                if let Some(r) = result {
                    let ret_str = callee_func_ty
                        .map(|ft| self.format_return_type(ft))
                        .unwrap_or_else(|| "i64".to_string());
                    emit!(
                        self.output,
                        "%{} = call {} @{}(",
                        r.index(),
                        ret_str,
                        callee_name,
                    )?;
                } else {
                    emit!(self.output, "call void @{}(", callee_name)?;
                }
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        emit!(self.output, ", ")?;
                    }
                    // Use parameter types from callee signature when available.
                    let param_ty_str = callee_func_ty
                        .and_then(|ft| ft.params.get(i))
                        .map(|ty| self.llvm_type(ty))
                        .unwrap_or_else(|| "i64".to_string());
                    emit!(self.output, "{} %{}", param_ty_str, arg.index())?;
                }
                emitln!(self.output, ")")?;
            }
            Inst::CallIndirect {
                callee,
                sig,
                args,
            } => {
                // Resolve indirect call signature from the module's func_types.
                let sig_ty = self.module.func_types.get(sig.as_usize());

                if let Some(r) = result {
                    let ret_str = sig_ty
                        .map(|ft| self.format_return_type(ft))
                        .unwrap_or_else(|| "i64".to_string());
                    emit!(
                        self.output,
                        "%{} = call {} %{}(",
                        r.index(),
                        ret_str,
                        callee.index(),
                    )?;
                } else {
                    emit!(self.output, "call void %{}(", callee.index())?;
                }
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        emit!(self.output, ", ")?;
                    }
                    let param_ty_str = sig_ty
                        .and_then(|ft| ft.params.get(i))
                        .map(|ty| self.llvm_type(ty))
                        .unwrap_or_else(|| "i64".to_string());
                    emit!(self.output, "{} %{}", param_ty_str, arg.index())?;
                }
                emitln!(self.output, ")")?;
            }
            Inst::Return { values } => {
                // Use the current function's return type (set in emit_function)
                // instead of hardcoding i64.
                let ret_ty = &self.current_return_ty;
                match values.as_slice() {
                    [] => emitln!(self.output, "ret void")?,
                    [v] => emitln!(self.output, "ret {} %{}", ret_ty, v.index())?,
                    vals => {
                        // Multiple return values: pack into struct.
                        // ret_ty is already the full struct type string.
                        emit!(self.output, "ret {} {{ ", ret_ty)?;
                        for (i, v) in vals.iter().enumerate() {
                            if i > 0 {
                                emit!(self.output, ", ")?;
                            }
                            // Use per-element return types from the function
                            // signature instead of hardcoded i64.
                            let elem_ty = self
                                .current_return_element_tys
                                .get(i)
                                .cloned()
                                .unwrap_or_else(|| "i64".to_string());
                            emit!(self.output, "{} %{}", elem_ty, v.index())?;
                        }
                        emitln!(self.output, " }}")?;
                    }
                }
            }
            Inst::ExtractField { ty, aggregate, field } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("ExtractField has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = extractvalue {} %{}, {}",
                    r.index(),
                    ty_str,
                    aggregate.index(),
                    field,
                )?;
            }
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("InsertField has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                // Resolve the field type for the inserted value.
                let field_ty_str = self.resolve_struct_field_ty(ty, *field);
                emitln!(
                    self.output,
                    "%{} = insertvalue {} %{}, {} %{}, {}",
                    r.index(),
                    ty_str,
                    aggregate.index(),
                    field_ty_str,
                    value.index(),
                    field,
                )?;
            }
            Inst::ExtractElement { ty, array, index } => {
                // Dynamic array indexing requires GEP+load (extractvalue only
                // accepts constant indices in LLVM IR).
                //
                // Lower to:
                //   %_tmp_N   = alloca <array_ty>
                //   store <array_ty> %array, ptr %_tmp_N
                //   %_tmp_N+1 = getelementptr <array_ty>, ptr %_tmp_N, i64 0, i64 %index
                //   %result   = load <elem_ty>, ptr %_tmp_N+1
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("ExtractElement has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                let elem_ty_str = self.resolve_array_elem_ty(ty);
                let tmp_alloca = self.temp_counter;
                let tmp_gep = self.temp_counter + 1;
                self.temp_counter += 2;
                emitln!(
                    self.output,
                    "%_tmp_{} = alloca {}",
                    tmp_alloca,
                    ty_str,
                )?;
                emitln!(
                    self.output,
                    "  store {} %{}, ptr %_tmp_{}",
                    ty_str,
                    array.index(),
                    tmp_alloca,
                )?;
                emitln!(
                    self.output,
                    "  %_tmp_{} = getelementptr {}, ptr %_tmp_{}, i64 0, i64 %{}",
                    tmp_gep,
                    ty_str,
                    tmp_alloca,
                    index.index(),
                )?;
                emitln!(
                    self.output,
                    "  %{} = load {}, ptr %_tmp_{}",
                    r.index(),
                    elem_ty_str,
                    tmp_gep,
                )?;
            }
            Inst::InsertElement {
                ty,
                array,
                index,
                value,
            } => {
                // Dynamic array insert requires alloca+store+GEP+store+load
                // (insertvalue only accepts constant indices in LLVM IR).
                //
                // Lower to:
                //   %_tmp_N   = alloca <array_ty>
                //   store <array_ty> %array, ptr %_tmp_N
                //   %_tmp_N+1 = getelementptr <array_ty>, ptr %_tmp_N, i64 0, i64 %index
                //   store <elem_ty> %value, ptr %_tmp_N+1
                //   %result   = load <array_ty>, ptr %_tmp_N
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("InsertElement has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                let elem_ty_str = self.resolve_array_elem_ty(ty);
                let tmp_alloca = self.temp_counter;
                let tmp_gep = self.temp_counter + 1;
                self.temp_counter += 2;
                emitln!(
                    self.output,
                    "%_tmp_{} = alloca {}",
                    tmp_alloca,
                    ty_str,
                )?;
                emitln!(
                    self.output,
                    "  store {} %{}, ptr %_tmp_{}",
                    ty_str,
                    array.index(),
                    tmp_alloca,
                )?;
                emitln!(
                    self.output,
                    "  %_tmp_{} = getelementptr {}, ptr %_tmp_{}, i64 0, i64 %{}",
                    tmp_gep,
                    ty_str,
                    tmp_alloca,
                    index.index(),
                )?;
                emitln!(
                    self.output,
                    "  store {} %{}, ptr %_tmp_{}",
                    elem_ty_str,
                    value.index(),
                    tmp_gep,
                )?;
                emitln!(
                    self.output,
                    "  %{} = load {}, ptr %_tmp_{}",
                    r.index(),
                    ty_str,
                    tmp_alloca,
                )?;
            }
            Inst::Const { ty, value } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("Const has no result".to_string())
                })?;
                // Record the type for GEP index resolution.
                self.value_types.insert(r.index(), ty.clone());
                let val_str = self.format_constant(value, ty);
                let ty_str = self.llvm_type(ty);
                match ty {
                    Ty::Ptr => {
                        emitln!(
                            self.output,
                            "%{} = inttoptr i64 {} to ptr",
                            r.index(),
                            val_str,
                        )?;
                    }
                    Ty::F32 | Ty::F64 => {
                        emitln!(
                            self.output,
                            "%{} = fadd {} {}, 0.0",
                            r.index(),
                            ty_str,
                            val_str,
                        )?;
                    }
                    Ty::Bool => {
                        emitln!(
                            self.output,
                            "%{} = add i1 {}, 0",
                            r.index(),
                            val_str,
                        )?;
                    }
                    _ => {
                        emitln!(
                            self.output,
                            "%{} = add {} {}, 0",
                            r.index(),
                            ty_str,
                            val_str,
                        )?;
                    }
                }
            }
            Inst::NullPtr => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("NullPtr has no result".to_string())
                })?;
                emitln!(self.output, "%{} = inttoptr i64 0 to ptr", r.index())?;
            }
            Inst::Undef { ty } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("Undef has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = freeze {} undef",
                    r.index(),
                    ty_str,
                )?;
            }
            Inst::Assume { cond } => {
                emitln!(
                    self.output,
                    "call void @llvm.assume(i1 %{})",
                    cond.index(),
                )?;
            }
            Inst::Assert { cond } => {
                // Lower assertions as conditional branch to trap:
                //   br i1 %cond, label %assert_ok_N, label %assert_fail_N
                //   assert_fail_N:
                //     call void @llvm.trap()
                //     unreachable
                //   assert_ok_N:
                let id = self.assert_counter;
                self.assert_counter += 1;
                emitln!(
                    self.output,
                    "br i1 %{}, label %assert_ok_{}, label %assert_fail_{}",
                    cond.index(),
                    id,
                    id,
                )?;
                emitln!(self.output, "assert_fail_{}:", id)?;
                emitln!(self.output, "  call void @llvm.trap()")?;
                emitln!(self.output, "  unreachable")?;
                emitln!(self.output, "assert_ok_{}:", id)?;
            }
            Inst::Unreachable => {
                emitln!(self.output, "unreachable")?;
            }
            Inst::Copy { ty, operand } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("Copy has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                match ty {
                    Ty::Ptr
                    | Ty::Ref(_)
                    | Ty::RefMut(_)
                    | Ty::PtrConst(_)
                    | Ty::PtrMut(_)
                    | Ty::Rc(_) => emitln!(
                        self.output,
                        "%{} = bitcast ptr %{} to ptr",
                        r.index(),
                        operand.index(),
                    )?,
                    Ty::F32 | Ty::F64 => emitln!(
                        self.output,
                        "%{} = fadd {} %{}, 0.0",
                        r.index(),
                        ty_str,
                        operand.index(),
                    )?,
                    // Aggregate types (struct, array, tuple, enum) cannot use
                    // `add`; lower to alloca+store+load for a correct copy.
                    Ty::Struct(_)
                    | Ty::Array(_, _)
                    | Ty::Tuple(_)
                    | Ty::Enum(_) => {
                        let tmp = self.temp_counter;
                        self.temp_counter += 1;
                        emitln!(
                            self.output,
                            "%_tmp_{} = alloca {}",
                            tmp,
                            ty_str,
                        )?;
                        emitln!(
                            self.output,
                            "  store {} %{}, ptr %_tmp_{}",
                            ty_str,
                            operand.index(),
                            tmp,
                        )?;
                        emitln!(
                            self.output,
                            "  %{} = load {}, ptr %_tmp_{}",
                            r.index(),
                            ty_str,
                            tmp,
                        )?;
                    }
                    _ => emitln!(
                        self.output,
                        "%{} = add {} %{}, 0",
                        r.index(),
                        ty_str,
                        operand.index(),
                    )?,
                }
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                let r = result.ok_or_else(|| {
                    Llvm2Error::Emission("Select has no result".to_string())
                })?;
                let ty_str = self.llvm_type(ty);
                emitln!(
                    self.output,
                    "%{} = select i1 %{}, {} %{}, {} %{}",
                    r.index(),
                    cond.index(),
                    ty_str,
                    then_val.index(),
                    ty_str,
                    else_val.index(),
                )?;
            }
            // Borrow/Retain/Release instructions are not emitted to LLVM IR;
            // they are higher-level tMIR constructs for ownership tracking.
            Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. } => {
                // No-op in LLVM emission — these are ownership annotations.
            }
            // Binding-frame instructions (tmir 67f1fdc+) track SSA binding
            // scopes. They are not lowered to LLVM IR today — callers relying
            // on binding frames must resolve them before reaching emission.
            Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. } => {
                return Err(Llvm2Error::UnsupportedInst(
                    "binding-frame instruction not yet supported in LLVM2 emission".to_string(),
                ));
            }
            // Dialect-specific instructions carry opaque payloads and must be
            // lowered to core tMIR before reaching LLVM emission.
            Inst::DialectOp(_) => {
                return Err(Llvm2Error::UnsupportedInst(
                    "dialect op not yet supported in LLVM2 emission".to_string(),
                ));
            }
        }

        Ok(())
    }

    /// Resolve a struct field type for InsertField emission.
    fn resolve_struct_field_ty(&self, ty: &Ty, field: u32) -> String {
        if let Ty::Struct(sid) = ty {
            if let Some(sd) = self.module.structs.iter().find(|s| s.id == *sid) {
                if let Some(f) = sd.fields.get(field as usize) {
                    return self.llvm_type(&f.ty);
                }
            }
        }
        // Fallback for non-struct or unresolvable field.
        "i64".to_string()
    }

    /// Resolve an array element type for InsertElement emission.
    fn resolve_array_elem_ty(&self, ty: &Ty) -> String {
        if let Ty::Array(elem_ty_id, _) = ty {
            if let Some(elem_ty) = self.module.types.get(elem_ty_id.as_usize()) {
                return self.llvm_type(elem_ty);
            }
        }
        // Fallback for non-array or unresolvable element.
        "i64".to_string()
    }

    /// Format a constant value as an LLVM IR literal.
    ///
    /// Unlike the free function `llvm_constant`, this method has access to
    /// the module's struct definitions and type table, so it can emit
    /// correct per-element types for aggregate constants instead of
    /// defaulting everything to i64.
    fn format_constant(&self, c: &Constant, ty: &Ty) -> String {
        match c {
            Constant::Int(v) => format!("{v}"),
            Constant::Float(v) => format!("{v:e}"),
            Constant::Bool(b) => {
                if *b {
                    "1".to_string()
                } else {
                    "0".to_string()
                }
            }
            Constant::Aggregate(elems) => {
                let parts: Vec<String> = match ty {
                    Ty::Struct(sid) => {
                        // Use struct field types for each element.
                        let fields = self
                            .module
                            .structs
                            .iter()
                            .find(|s| s.id == *sid)
                            .map(|sd| &sd.fields[..]);
                        elems
                            .iter()
                            .enumerate()
                            .map(|(i, e)| {
                                let field_ty = fields
                                    .and_then(|fs| fs.get(i))
                                    .map(|f| &f.ty);
                                let ty_str = field_ty
                                    .map(|t| self.llvm_type(t))
                                    .unwrap_or_else(|| "i64".to_string());
                                let val = field_ty
                                    .map(|t| self.format_constant(e, t))
                                    .unwrap_or_else(|| self.format_constant(e, &Ty::I64));
                                format!("{} {}", ty_str, val)
                            })
                            .collect()
                    }
                    Ty::Array(elem_ty_id, _) => {
                        // Use array element type for all elements.
                        let elem_ty = self
                            .module
                            .types
                            .get(elem_ty_id.as_usize())
                            .cloned()
                            .unwrap_or(Ty::I64);
                        let ty_str = self.llvm_type(&elem_ty);
                        elems
                            .iter()
                            .map(|e| {
                                format!(
                                    "{} {}",
                                    ty_str,
                                    self.format_constant(e, &elem_ty),
                                )
                            })
                            .collect()
                    }
                    _ => {
                        // Unknown aggregate type; fall back to i64 per element.
                        elems
                            .iter()
                            .map(|e| {
                                format!("i64 {}", self.format_constant(e, &Ty::I64))
                            })
                            .collect()
                    }
                };
                format!("{{ {} }}", parts.join(", "))
            }
            // Compound TLA+ constants (Sequence/Set/Record/Closure) are not
            // representable as LLVM IR literals; callers should lift them to
            // runtime-constructed values before emission. Fall back to null.
            Constant::Sequence(_)
            | Constant::Set(_)
            | Constant::Record(_)
            | Constant::Closure { .. } => "null".to_string(),
        }
    }
}

// =============================================================================
// Helpers
// =============================================================================

fn block_label(id: BlockId) -> String {
    if id.index() == 0 {
        "entry".to_string()
    } else {
        format!("bb{}", id.index())
    }
}

/// Static type mapping for primitive types only (used by runtime declarations
/// where module context is not needed).
fn llvm_ty_static(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "i8",
        Ty::I16 => "i16",
        Ty::I32 => "i32",
        Ty::I64 => "i64",
        Ty::I128 => "i128",
        Ty::F32 => "float",
        Ty::F64 => "double",
        Ty::Bool => "i1",
        Ty::Ptr => "ptr",
        Ty::Unit => "void",
        Ty::Struct(_) | Ty::Array(_, _) | Ty::Func(_) => "ptr",
        Ty::U8 => "i8",
        Ty::U16 => "i16",
        Ty::U32 => "i32",
        Ty::U64 => "i64",
        Ty::U128 => "i128",
        Ty::Never => "void",
        Ty::Tuple(_) | Ty::Enum(_) => "ptr",
        Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) => "ptr",
        // Compound TLA+ types lower to opaque ptr in LLVM IR.
        Ty::Set(_, _) | Ty::Sequence(_) | Ty::Record(_) | Ty::Closure(_) => "ptr",
    }
}

fn llvm_binop(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::UDiv => "udiv",
        BinOp::SDiv => "sdiv",
        BinOp::URem => "urem",
        BinOp::SRem => "srem",
        BinOp::FAdd => "fadd",
        BinOp::FSub => "fsub",
        BinOp::FMul => "fmul",
        BinOp::FDiv => "fdiv",
        BinOp::FRem => "frem",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Xor => "xor",
        BinOp::Shl => "shl",
        BinOp::LShr => "lshr",
        BinOp::AShr => "ashr",
    }
}

fn llvm_icmp(op: &ICmpOp) -> &'static str {
    match op {
        ICmpOp::Eq => "eq",
        ICmpOp::Ne => "ne",
        ICmpOp::Ult => "ult",
        ICmpOp::Ule => "ule",
        ICmpOp::Ugt => "ugt",
        ICmpOp::Uge => "uge",
        ICmpOp::Slt => "slt",
        ICmpOp::Sle => "sle",
        ICmpOp::Sgt => "sgt",
        ICmpOp::Sge => "sge",
    }
}

fn llvm_fcmp(op: &FCmpOp) -> &'static str {
    match op {
        FCmpOp::OEq => "oeq",
        FCmpOp::ONe => "one",
        FCmpOp::OLt => "olt",
        FCmpOp::OLe => "ole",
        FCmpOp::OGt => "ogt",
        FCmpOp::OGe => "oge",
        FCmpOp::UEq => "ueq",
        FCmpOp::UNe => "une",
        FCmpOp::ULt => "ult",
        FCmpOp::ULe => "ule",
        FCmpOp::UGt => "ugt",
        FCmpOp::UGe => "uge",
    }
}

fn llvm_cast(op: &CastOp) -> &'static str {
    match op {
        CastOp::Trunc => "trunc",
        CastOp::ZExt => "zext",
        CastOp::SExt => "sext",
        CastOp::FPTrunc => "fptrunc",
        CastOp::FPExt => "fpext",
        CastOp::FPToUI => "fptoui",
        CastOp::FPToSI => "fptosi",
        CastOp::UIToFP => "uitofp",
        CastOp::SIToFP => "sitofp",
        CastOp::PtrToInt => "ptrtoint",
        CastOp::IntToPtr => "inttoptr",
        CastOp::Bitcast => "bitcast",
    }
}

fn llvm_ordering(ord: &Ordering) -> &'static str {
    match ord {
        Ordering::Relaxed => "monotonic",
        Ordering::Acquire => "acquire",
        Ordering::Release => "release",
        Ordering::AcqRel => "acq_rel",
        Ordering::SeqCst => "seq_cst",
    }
}

fn llvm_rmw(op: &AtomicRMWOp) -> &'static str {
    match op {
        AtomicRMWOp::Xchg => "xchg",
        AtomicRMWOp::Add => "add",
        AtomicRMWOp::Sub => "sub",
        AtomicRMWOp::And => "and",
        AtomicRMWOp::Or => "or",
        AtomicRMWOp::Xor => "xor",
        AtomicRMWOp::Max => "max",
        AtomicRMWOp::Min => "min",
        AtomicRMWOp::UMax => "umax",
        AtomicRMWOp::UMin => "umin",
    }
}

fn llvm_overflow_intrinsic(op: &OverflowOp, ty: &Ty) -> String {
    let op_name = match op {
        OverflowOp::AddOverflow => "sadd",
        OverflowOp::SubOverflow => "ssub",
        OverflowOp::MulOverflow => "smul",
    };
    format!("llvm.{}.with.overflow.{}", op_name, llvm_ty_static(ty))
}


fn llvm_zero_init(ty: &Ty) -> String {
    match ty {
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 => "0".to_string(),
        Ty::F32 | Ty::F64 => "0.0".to_string(),
        Ty::Bool => "0".to_string(),
        Ty::Ptr => "null".to_string(),
        Ty::Unit => "void".to_string(),
        _ => "zeroinitializer".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tmir::ty::{FieldDef, FuncTy, StructDef};
    use tmir::value::{FuncId, StructId, TyId, ValueId};
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
    fn test_emit_return_42() {
        let module = make_return_42_module();
        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("define i64 @main()"));
        assert!(ir.contains("add i64 42, 0"));
        assert!(ir.contains("ret i64 %0"));
    }

    #[test]
    fn test_emit_module_header() {
        let module = Module::new("test_header");
        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("; ModuleID = 'test_header'"));
        assert!(ir.contains("source_filename = \"test_header\""));
    }

    #[test]
    fn test_emit_binop() {
        let mut module = Module::new("binop");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "add_fn", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::I64)
            .with_param(ValueId::new(11), Ty::I64);
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(10),
                rhs: ValueId::new(11),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("define i64 @add_fn(i64 %10, i64 %11)"));
        assert!(ir.contains("%0 = add i64 %10, %11"));
        assert!(ir.contains("ret i64 %0"));
    }

    #[test]
    fn test_emit_branch() {
        let mut module = Module::new("branch");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let then_bb = BlockId::new(1);
        let else_bb = BlockId::new(2);

        let mut func = Function::new(FuncId::new(0), "branch_fn", ft, entry);

        // Entry: condbr
        let mut entry_block =
            Block::new(entry).with_param(ValueId::new(10), Ty::I64);
        entry_block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I64,
                lhs: ValueId::new(10),
                rhs: ValueId::new(10),
            })
            .with_result(ValueId::new(0)),
        );
        entry_block.body.push(InstrNode::new(Inst::CondBr {
            cond: ValueId::new(0),
            then_target: then_bb,
            then_args: vec![],
            else_target: else_bb,
            else_args: vec![],
        }));
        func.blocks.push(entry_block);

        // Then: return 1
        let mut then_block = Block::new(then_bb);
        then_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(1)),
        );
        then_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        func.blocks.push(then_block);

        // Else: return 0
        let mut else_block = Block::new(else_bb);
        else_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(2)),
        );
        else_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }));
        func.blocks.push(else_block);

        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("br i1 %0, label %bb1, label %bb2"));
        assert!(ir.contains("bb1:"));
        assert!(ir.contains("bb2:"));
    }

    #[test]
    fn test_emit_alloca_load_store() {
        let mut module = Module::new("mem");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "mem_fn", ft, entry);
        let mut block = Block::new(entry);

        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(99),
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            align: None,
            volatile: false,
        }));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                align: None,
                volatile: false,
            })
            .with_result(ValueId::new(2)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }));

        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("%0 = alloca i64"));
        assert!(ir.contains("store i64 %1, ptr %0"));
        assert!(ir.contains("%2 = load i64, ptr %0"));
        assert!(ir.contains("ret i64 %2"));
    }

    #[test]
    fn test_emit_gep() {
        let mut module = Module::new("gep");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "gep_fn", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::Ptr)
            .with_param(ValueId::new(11), Ty::I32);
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(10),
                indices: vec![ValueId::new(11)],
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                align: None,
                volatile: false,
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        // ValueId 11 has Ty::I32 from block params, so the GEP index is i32.
        assert!(ir.contains("getelementptr i64, ptr %10, i32 %11"));
    }

    #[test]
    fn test_emit_select() {
        let mut module = Module::new("sel");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "sel_fn", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::Bool)
            .with_param(ValueId::new(11), Ty::I64)
            .with_param(ValueId::new(12), Ty::I64);
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: ValueId::new(10),
                then_val: ValueId::new(11),
                else_val: ValueId::new(12),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("select i1 %10, i64 %11, i64 %12"));
    }

    #[test]
    fn test_emit_cast() {
        let mut module = Module::new("cast");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "cast_fn", ft, entry);
        let mut block =
            Block::new(entry).with_param(ValueId::new(10), Ty::I32);
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: ValueId::new(10),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("sext i32 %10 to i64"));
    }

    #[test]
    fn test_emit_void_return() {
        let mut module = Module::new("void_ret");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "void_fn", ft, entry);
        let mut block = Block::new(entry);
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("define void @void_fn()"));
        assert!(ir.contains("ret void"));
    }

    #[test]
    fn test_emit_runtime_helpers_declared() {
        let module = Module::new("helpers");
        let ir = emit_module(&module).expect("should emit");
        assert!(ir.contains("declare i64 @jit_pow_i64(i64, i64)"));
        assert!(ir.contains("declare i64 @jit_set_contains_i64(ptr, i64)"));
    }

    #[test]
    fn test_emit_assert_lowers_to_trap() {
        let mut module = Module::new("assert_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "assert_fn", ft, entry);
        let mut block =
            Block::new(entry).with_param(ValueId::new(10), Ty::Bool);
        block.body.push(InstrNode::new(Inst::Assert {
            cond: ValueId::new(10),
        }));
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        // Must NOT contain llvm.assume for assertions.
        assert!(
            !ir.contains("llvm.assume(i1 %10)  ; assert"),
            "Assert must not lower to llvm.assume"
        );
        // Must contain conditional branch to trap.
        assert!(
            ir.contains("br i1 %10, label %assert_ok_0, label %assert_fail_0"),
            "Assert must emit conditional branch"
        );
        assert!(
            ir.contains("assert_fail_0:"),
            "Assert must emit failure block"
        );
        assert!(
            ir.contains("call void @llvm.trap()"),
            "Assert must call llvm.trap on failure"
        );
        assert!(
            ir.contains("unreachable"),
            "Assert failure block must end with unreachable"
        );
        assert!(
            ir.contains("assert_ok_0:"),
            "Assert must emit continuation block"
        );
        // The trap intrinsic must be declared.
        assert!(
            ir.contains("declare void @llvm.trap() noreturn nounwind"),
            "Module must declare llvm.trap"
        );
    }

    #[test]
    fn test_emit_assume_still_uses_llvm_assume() {
        let mut module = Module::new("assume_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "assume_fn", ft, entry);
        let mut block =
            Block::new(entry).with_param(ValueId::new(10), Ty::Bool);
        block.body.push(InstrNode::new(Inst::Assume {
            cond: ValueId::new(10),
        }));
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(
            ir.contains("call void @llvm.assume(i1 %10)"),
            "Assume should still use llvm.assume"
        );
        // The llvm.assume intrinsic must be declared.
        assert!(
            ir.contains("declare void @llvm.assume(i1) nounwind"),
            "Module must declare llvm.assume"
        );
    }

    #[test]
    fn test_emit_struct_type_resolved() {
        let mut module = Module::new("struct_test");
        let sid = StructId::new(0);
        module.add_struct(StructDef {
            id: sid,
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::I64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::I64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),
        });

        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "struct_fn", ft, entry);
        let mut block = Block::new(entry);

        // Alloca a struct.
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::Struct(sid),
                count: None,
                align: None,
            })
            .with_result(ValueId::new(0)),
        );

        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));

        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        // Struct type definition should be present.
        assert!(
            ir.contains("%struct.Point = type { i64, i64 }"),
            "Struct type definition should be emitted"
        );
        // Alloca should use named struct type.
        assert!(
            ir.contains("%0 = alloca %struct.Point"),
            "Alloca should reference named struct type, not ptr"
        );
    }

    #[test]
    fn test_emit_extractfield_uses_struct_type() {
        let mut module = Module::new("extract_test");
        let sid = StructId::new(0);
        module.add_struct(StructDef {
            id: sid,
            name: "Pair".to_string(),
            fields: vec![
                FieldDef {
                    name: "a".to_string(),
                    ty: Ty::I32,
                    offset: Some(0),
                },
                FieldDef {
                    name: "b".to_string(),
                    ty: Ty::I64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),
        });

        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Struct(sid)],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "extract_fn", ft, entry);
        let mut block =
            Block::new(entry).with_param(ValueId::new(10), Ty::Struct(sid));

        block.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Struct(sid),
                aggregate: ValueId::new(10),
                field: 0,
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));

        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(
            ir.contains("extractvalue %struct.Pair %10, 0"),
            "ExtractField should use named struct type, not {{}}. IR:\n{}",
            ir
        );
    }

    #[test]
    fn test_emit_array_type_resolved() {
        let mut module = Module::new("array_test");
        // Register element type.
        let elem_ty_id = module.add_type(Ty::I32);

        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "array_fn", ft, entry);
        let mut block = Block::new(entry);

        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::Array(elem_ty_id, 10),
                count: None,
                align: None,
            })
            .with_result(ValueId::new(0)),
        );

        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));

        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(
            ir.contains("%0 = alloca [10 x i32]"),
            "Array alloca should use [N x T] syntax, not ptr. IR:\n{}",
            ir
        );
    }

    #[test]
    fn test_emit_call_uses_callee_types() {
        let mut module = Module::new("call_types");

        // Callee: takes (i32, ptr) returns i32.
        let callee_ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let callee_entry = BlockId::new(0);
        let mut callee_func =
            Function::new(FuncId::new(0), "helper", callee_ft, callee_entry);
        let mut callee_block = Block::new(callee_entry)
            .with_param(ValueId::new(10), Ty::I32)
            .with_param(ValueId::new(11), Ty::Ptr);
        callee_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(10)],
        }));
        callee_func.blocks.push(callee_block);
        module.add_function(callee_func);

        // Caller: calls helper.
        let caller_ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let caller_entry = BlockId::new(0);
        let mut caller_func =
            Function::new(FuncId::new(1), "caller", caller_ft, caller_entry);
        let mut caller_block = Block::new(caller_entry)
            .with_param(ValueId::new(20), Ty::I32)
            .with_param(ValueId::new(21), Ty::Ptr);
        caller_block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(20), ValueId::new(21)],
            })
            .with_result(ValueId::new(0)),
        );
        caller_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        caller_func.blocks.push(caller_block);
        module.add_function(caller_func);

        let ir = emit_module(&module).expect("should emit");
        // Call should use i32 return and (i32, ptr) params, not i64 everywhere.
        assert!(
            ir.contains("call i32 @helper(i32 %20, ptr %21)"),
            "Call should use callee's actual types, not hardcoded i64. IR:\n{}",
            ir
        );
    }

    #[test]
    fn test_emit_return_uses_function_return_type() {
        // Verify that `ret` uses the function's declared return type, not
        // hardcoded i64. Function returns i32 -> ret should be `ret i32 %N`.
        let mut module = Module::new("ret_type_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func = Function::new(FuncId::new(0), "ret_i32", ft, entry);
        let mut block =
            Block::new(entry).with_param(ValueId::new(10), Ty::I32);
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(10)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        assert!(
            ir.contains("ret i32 %10"),
            "Return should use function's return type (i32), not hardcoded i64. IR:\n{}",
            ir
        );
        assert!(
            !ir.contains("ret i64"),
            "Return should NOT contain i64 for an i32-returning function. IR:\n{}",
            ir
        );
    }

    #[test]
    fn test_emit_extract_element_uses_gep() {
        // Verify ExtractElement with dynamic index lowers to GEP+load
        // instead of invalid `extractvalue` with dynamic index.
        let mut module = Module::new("extract_elem_test");
        let elem_ty_id = module.add_type(Ty::I32);
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Array(elem_ty_id, 4), Ty::I64],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func =
            Function::new(FuncId::new(0), "extract_elem", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::Array(elem_ty_id, 4))
            .with_param(ValueId::new(11), Ty::I64);
        block.body.push(
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::Array(elem_ty_id, 4),
                array: ValueId::new(10),
                index: ValueId::new(11),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        // Should NOT contain extractvalue with dynamic index.
        assert!(
            !ir.contains("extractvalue"),
            "ExtractElement should NOT use extractvalue (requires constant index). IR:\n{}",
            ir
        );
        // Should contain GEP for dynamic indexing.
        assert!(
            ir.contains("getelementptr [4 x i32]"),
            "ExtractElement should lower to GEP for dynamic array access. IR:\n{}",
            ir
        );
        // Should contain load for the element.
        assert!(
            ir.contains("load i32"),
            "ExtractElement should load the element type (i32). IR:\n{}",
            ir
        );
    }

    #[test]
    fn test_emit_insert_element_uses_gep() {
        // Verify InsertElement with dynamic index lowers to GEP+store
        // instead of invalid `insertvalue` with dynamic index.
        let mut module = Module::new("insert_elem_test");
        let elem_ty_id = module.add_type(Ty::I64);
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Array(elem_ty_id, 8), Ty::I64, Ty::I64],
            returns: vec![Ty::Array(elem_ty_id, 8)],
            is_vararg: false,
        });
        let entry = BlockId::new(0);
        let mut func =
            Function::new(FuncId::new(0), "insert_elem", ft, entry);
        let mut block = Block::new(entry)
            .with_param(ValueId::new(10), Ty::Array(elem_ty_id, 8))
            .with_param(ValueId::new(11), Ty::I64)
            .with_param(ValueId::new(12), Ty::I64);
        block.body.push(
            InstrNode::new(Inst::InsertElement {
                ty: Ty::Array(elem_ty_id, 8),
                array: ValueId::new(10),
                index: ValueId::new(11),
                value: ValueId::new(12),
            })
            .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let ir = emit_module(&module).expect("should emit");
        // Should NOT contain insertvalue with dynamic index.
        assert!(
            !ir.contains("insertvalue"),
            "InsertElement should NOT use insertvalue (requires constant index). IR:\n{}",
            ir
        );
        // Should contain GEP for dynamic indexing.
        assert!(
            ir.contains("getelementptr [8 x i64]"),
            "InsertElement should lower to GEP for dynamic array access. IR:\n{}",
            ir
        );
        // Should contain both store (to set element) and load (to read back array).
        assert!(
            ir.contains("store i64"),
            "InsertElement should store element at GEP'd location. IR:\n{}",
            ir
        );
    }
}
