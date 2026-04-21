// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cranelift JIT compiler for TLA+ expressions.
//!
//! This module provides the core JIT compilation infrastructure using Cranelift.
//! The compiler translates TLA+ AST nodes to Cranelift IR, which is then compiled
//! to native machine code.
//!
//! # Submodules
//!
//! - [`preflight`]: Compile-time constant evaluation and overflow detection
//! - [`lower`]: Cranelift IR code generation from TLA+ AST

mod lower;
mod lower_func;
mod lower_quantifier;
mod lower_record;
mod lower_set;
mod preflight;
mod preflight_funcdef;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_semantics;

use crate::error::JitError;
use crate::jit_native::{JITModule, Linkage, Module};
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, UserFuncName};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use std::alloc::Layout;
use std::mem;
use tla_core::ast::Expr;
use tla_core::span::Spanned;

use lower::compile_expr_inner;
use preflight::{preflight_const_value, PreflightValue};

/// JIT compilation context.
///
/// Manages Cranelift JIT module and provides methods to compile TLA+ expressions.
pub struct JitContext {
    /// Cranelift JIT module
    module: JITModule,
    /// Context for building functions
    ctx: Context,
    /// Function builder context (reusable)
    builder_ctx: FunctionBuilderContext,
    /// Counter for generating unique function names
    func_counter: u32,
    /// Heap allocations leaked via Box::into_raw for JIT code data sections.
    /// Reclaimed in Drop.
    leaked_allocs: Vec<(*mut u8, Layout)>,
}

impl JitContext {
    /// Create a new JIT context.
    pub fn new() -> Result<Self, JitError> {
        let module = crate::create_jit_module()?;
        let ctx = module.make_context();

        Ok(JitContext {
            module,
            ctx,
            builder_ctx: FunctionBuilderContext::new(),
            func_counter: 0,
            leaked_allocs: Vec::new(),
        })
    }

    /// Compile a TLA+ expression to a native function that returns an i64.
    ///
    /// The expression must be a constant expression (no free variables).
    /// Returns a function pointer that can be called to evaluate the expression.
    ///
    /// # ABI Note
    ///
    /// Cranelift compiles with the platform's default calling convention (SystemV
    /// on x86_64-linux, AppleAarch64 on aarch64-apple-darwin). For zero-argument
    /// functions returning a single integer, this is ABI-compatible with Rust's
    /// `fn() -> i64`. For the explicitly-typed `extern "C"` variant, see
    /// [`JitExprFn`](crate::abi::JitExprFn).
    pub fn compile_expr(&mut self, expr: &Spanned<Expr>) -> Result<fn() -> i64, JitError> {
        // Cranelift integer ops wrap on overflow. TLA+ integers are unbounded, so overflow
        // would silently diverge from TLC semantics. Preflight ensures all executed integer
        // operations are in-range for i64, or we fail compilation so the caller can fall back.
        //
        // Set-typed expressions (SetEnum, Range) are not directly compilable to an i64 result,
        // but they can appear as subexpressions of In/NotIn/Forall/Exists. At the top level,
        // they are caught here as a type error before reaching compile_expr_inner.
        let preflight_val = preflight_const_value(&expr.node)?;
        match &preflight_val {
            PreflightValue::Set(_)
            | PreflightValue::Function(_)
            | PreflightValue::Record(_)
            | PreflightValue::RecordFunction(_) => {
                return Err(JitError::TypeMismatch {
                    expected: "scalar (integer or boolean)".to_string(),
                    actual: preflight_val.ty_name().to_string(),
                });
            }
            PreflightValue::Bool(_) | PreflightValue::Int(_) => {}
        }

        // Create function signature: () -> i64
        let mut sig = self.module.make_signature();
        sig.returns.push(AbiParam::new(types::I64));

        // Declare the function
        let func_name = format!("expr_{}", self.func_counter);
        self.func_counter += 1;
        let func_id = self
            .module
            .declare_function(&func_name, Linkage::Local, &sig)?;

        // Build the function body
        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);
            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            // Compile the expression (preserving spans through lowering)
            let value = compile_expr_inner(&mut builder, expr)?;

            // Return the result
            builder.ins().return_(&[value]);
            builder.finalize();
        }

        // Drain any heap allocations registered during lowering.
        lower::LEAKED_ALLOCS.with(|allocs| {
            self.leaked_allocs.append(&mut allocs.borrow_mut());
        });

        // Compile to machine code
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| JitError::CompileError(e.to_string()))?;

        self.module.clear_context(&mut self.ctx);
        self.module
            .finalize_definitions()
            .map_err(|e| JitError::CompileError(format!("Failed to finalize: {e}")))?;

        // Get the function pointer
        let code_ptr = self.module.get_finalized_function(func_id);
        // SAFETY: The transmute from `*const u8` to `fn() -> i64` is sound because:
        // 1. Calling convention: Cranelift uses `isa().default_call_conv()` which is
        //    the platform's C ABI (SystemV on x86_64-linux, AppleAarch64 on aarch64-
        //    apple-darwin). For a zero-argument function returning a single integer,
        //    the C ABI and Rust ABI produce identical machine code (return value in
        //    the integer return register, no stack args).
        // 2. Signature: The Cranelift IR function has no params and returns one I64,
        //    matching the Rust fn pointer's `() -> i64` signature exactly.
        // 3. Lifetime: The code buffer is owned by `self.module` (a JITModule) which
        //    outlives the returned function pointer (both stored in JitContext).
        // 4. Validity: `get_finalized_function` returns a non-null pointer to
        //    executable memory only after `finalize_definitions()` succeeds.
        debug_assert!(
            !code_ptr.is_null(),
            "JIT code pointer is null after finalization"
        );
        let func: fn() -> i64 = unsafe { mem::transmute(code_ptr) };

        Ok(func)
    }

    /// Compile a TLA+ expression intended to be used in "predicate position" (must be boolean).
    pub fn compile_predicate(&mut self, expr: &Spanned<Expr>) -> Result<fn() -> i64, JitError> {
        let v = preflight_const_value(&expr.node)?;
        if !matches!(v, PreflightValue::Bool(_)) {
            return Err(JitError::TypeMismatch {
                expected: "boolean".to_string(),
                actual: v.ty_name().to_string(),
            });
        }
        self.compile_expr(expr)
    }
}

impl Drop for JitContext {
    fn drop(&mut self) {
        for &(ptr, layout) in &self.leaked_allocs {
            if !ptr.is_null() && layout.size() > 0 {
                // SAFETY: Each pointer was obtained from Box::into_raw during
                // JIT compilation and has not been deallocated elsewhere.
                // The layout matches the original Box<[i64]> allocation.
                unsafe {
                    std::alloc::dealloc(ptr, layout);
                }
            }
        }
    }
}
