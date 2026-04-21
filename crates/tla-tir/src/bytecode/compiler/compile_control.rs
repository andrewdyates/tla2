// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Control flow, constant, LET/CASE, and operator-call compilation helpers.

use super::super::opcode::{BuiltinOp, Opcode, Register};
use super::{CompileError, FnCompileState};
use crate::nodes::{
    PreservedAstBody, StoredTirBody, TirBoolOp, TirExpr, TirNameKind, TirOperatorRef,
};
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{free_vars, Span, Spanned};
use tla_value::{ClosureValue, Value};

impl<'a> FnCompileState<'a> {
    /// Compile a constant value.
    pub(super) fn compile_const(&mut self, value: &Value) -> Result<Register, CompileError> {
        let rd = self.alloc_reg()?;
        match value {
            Value::Bool(b) => {
                self.func.emit(Opcode::LoadBool { rd, value: *b });
            }
            Value::SmallInt(n) => {
                self.func.emit(Opcode::LoadImm { rd, value: *n });
            }
            _ => {
                let idx = self.add_const(value.clone())?;
                self.func.emit(Opcode::LoadConst { rd, idx });
            }
        }
        Ok(rd)
    }

    /// Compile boolean binary operations with short-circuit semantics.
    pub(super) fn compile_bool_binop(
        &mut self,
        left: &Spanned<TirExpr>,
        op: TirBoolOp,
        right: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        match op {
            TirBoolOp::And => {
                // Short-circuit: if left is FALSE, skip right.
                let r1 = self.compile_expr(left)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Move { rd, rs: r1 });
                let jump_idx = self.func.emit(Opcode::JumpFalse {
                    rs: rd,
                    offset: 0, // patched
                });
                let r2 = self.compile_expr(right)?;
                self.func.emit(Opcode::Move { rd, rs: r2 });
                let end = self.func.len();
                self.func.patch_jump(jump_idx, end);
                Ok(rd)
            }
            TirBoolOp::Or => {
                // Short-circuit: if left is TRUE, skip right.
                let r1 = self.compile_expr(left)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Move { rd, rs: r1 });
                let jump_idx = self.func.emit(Opcode::JumpTrue {
                    rs: rd,
                    offset: 0, // patched
                });
                let r2 = self.compile_expr(right)?;
                self.func.emit(Opcode::Move { rd, rs: r2 });
                let end = self.func.len();
                self.func.patch_jump(jump_idx, end);
                Ok(rd)
            }
            TirBoolOp::Implies => {
                // a => b  ≡  ~a \/ b
                // Short-circuit: if left is FALSE, result is TRUE.
                let r1 = self.compile_expr(left)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::LoadBool { rd, value: true });
                let jump_idx = self.func.emit(Opcode::JumpFalse {
                    rs: r1,
                    offset: 0, // patched
                });
                let r2 = self.compile_expr(right)?;
                self.func.emit(Opcode::Move { rd, rs: r2 });
                let end = self.func.len();
                self.func.patch_jump(jump_idx, end);
                Ok(rd)
            }
            TirBoolOp::Equiv => {
                let r1 = self.compile_expr(left)?;
                let r2 = self.compile_expr(right)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Equiv { rd, r1, r2 });
                Ok(rd)
            }
        }
    }

    /// Compile IF-THEN-ELSE.
    pub(super) fn compile_if(
        &mut self,
        cond: &Spanned<TirExpr>,
        then_: &Spanned<TirExpr>,
        else_: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        let r_cond = self.compile_expr(cond)?;
        let rd = self.alloc_reg()?;

        // Jump to else branch if FALSE.
        let jump_to_else = self.func.emit(Opcode::JumpFalse {
            rs: r_cond,
            offset: 0,
        });

        // Then branch.
        let r_then = self.compile_expr(then_)?;
        self.func.emit(Opcode::Move { rd, rs: r_then });
        let jump_to_end = self.func.emit(Opcode::Jump { offset: 0 });

        // Else branch.
        let else_start = self.func.len();
        self.func.patch_jump(jump_to_else, else_start);
        let r_else = self.compile_expr(else_)?;
        self.func.emit(Opcode::Move { rd, rs: r_else });

        let end = self.func.len();
        self.func.patch_jump(jump_to_end, end);

        Ok(rd)
    }

    /// Compile LET/IN block.
    pub(super) fn compile_let(
        &mut self,
        defs: &[crate::nodes::TirLetDef],
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        let saved_bindings = self.bindings.len();
        let saved_local_ops: std::collections::HashSet<String> =
            self.local_op_indices.keys().cloned().collect();

        for def in defs {
            if def.params.is_empty() {
                // Zero-arg LET — bind result to a register.
                let r_val = self.compile_expr(&def.body)?;
                self.bindings.push((def.name.clone(), r_val));
            } else {
                // Parameterized LET — compile as a sub-function.
                self.compile_let_as_function(&def.name, &def.params, &def.body)?;
            }
        }

        let result = self.compile_expr(body)?;

        // Pop all LET bindings and local op_indices added by this LET block.
        self.bindings.truncate(saved_bindings);
        self.local_op_indices
            .retain(|k, _| saved_local_ops.contains(k));

        Ok(result)
    }

    /// Compile a parameterized LET def as a sub-function.
    ///
    /// Temporarily swaps out the parent function state to compile the LET
    /// body with fresh registers and parameter bindings. On success, the
    /// sub-function is pushed to `sub_functions` and its name registered
    /// in `local_op_indices`. On error, parent state is fully restored.
    fn compile_let_as_function(
        &mut self,
        name: &str,
        params: &[String],
        body: &Spanned<TirExpr>,
    ) -> Result<(), CompileError> {
        let arity = params.len() as u8;

        let sub_func = super::BytecodeFunction::new(name.to_string(), arity);

        // Save parent state and swap in the sub-function context.
        let saved_func = std::mem::replace(&mut self.func, sub_func);
        let saved_next_reg = self.next_reg;
        let saved_local_ops: std::collections::HashSet<String> =
            self.local_op_indices.keys().cloned().collect();

        // Part of #3802: CLEAR parent bindings before compiling the LET body.
        // Parameterized LET defs are compiled as separate BytecodeFunctions
        // with their own register files. If parent bindings remain visible,
        // lookup_binding() can return a register index from the parent's
        // register space that exceeds the sub-function's max_register, causing
        // an index-out-of-bounds panic at runtime.
        let saved_bindings: Vec<(String, u8)> = self.bindings.drain(..).collect();

        // Bind parameters to registers 0..arity.
        self.next_reg = 0;
        for (i, param) in params.iter().enumerate() {
            self.bindings.push((param.clone(), i as u8));
        }
        self.next_reg = arity;

        let compile_result = self.compile_expr(body);

        // Restore parent state regardless of success/failure.
        let compiled_sub_func = std::mem::replace(&mut self.func, saved_func);
        self.next_reg = saved_next_reg;
        self.bindings.clear();
        self.bindings.extend(saved_bindings);
        self.local_op_indices
            .retain(|k, _| saved_local_ops.contains(k));

        // Propagate error after state is restored.
        let result_reg = compile_result?;

        // Finalize the sub-function: add Move+Ret epilogue.
        let mut finalized = compiled_sub_func;
        if result_reg != 0 {
            finalized.emit(Opcode::Move {
                rd: 0,
                rs: result_reg,
            });
        }
        finalized.emit(Opcode::Ret { rs: 0 });

        // Compute func_idx AFTER body compilation because compile_expr may
        // add sub-functions (via nested on-demand compilation or inner LET defs),
        // growing self.sub_functions. Computing before would produce a stale index
        // that collides with sub-functions added during body compilation.
        // Part of #3802.
        let func_idx = self.next_func_idx + self.sub_functions.len() as u16;
        self.sub_functions.push(finalized);
        self.local_op_indices.insert(name.to_string(), func_idx);

        Ok(())
    }

    /// Compile CASE expression.
    pub(super) fn compile_case(
        &mut self,
        arms: &[crate::nodes::TirCaseArm],
        other: Option<&Spanned<TirExpr>>,
    ) -> Result<Register, CompileError> {
        let rd = self.alloc_reg()?;
        let mut end_jumps = Vec::new();

        for arm in arms {
            let r_guard = self.compile_expr(&arm.guard)?;
            let skip_idx = self.func.emit(Opcode::JumpFalse {
                rs: r_guard,
                offset: 0,
            });

            let r_body = self.compile_expr(&arm.body)?;
            self.func.emit(Opcode::Move { rd, rs: r_body });
            end_jumps.push(self.func.emit(Opcode::Jump { offset: 0 }));

            let next = self.func.len();
            self.func.patch_jump(skip_idx, next);
        }

        // OTHER branch or halt.
        if let Some(other_expr) = other {
            let r_other = self.compile_expr(other_expr)?;
            self.func.emit(Opcode::Move { rd, rs: r_other });
        } else {
            self.func.emit(Opcode::Halt);
        }

        // Patch all end jumps.
        let end = self.func.len();
        for j in end_jumps {
            self.func.patch_jump(j, end);
        }

        Ok(rd)
    }

    /// Compile an `Apply { op, args }` node to a `Call` opcode.
    ///
    /// Handles `Apply(Name(Ident), args)` where the callee is a pre-compiled
    /// operator. Higher-order cases lower to `ValueApply`, which dispatches
    /// closures and single-arg function-like values at runtime.
    pub(super) fn compile_apply(
        &mut self,
        op: &Spanned<TirExpr>,
        args: &[Spanned<TirExpr>],
    ) -> Result<Register, CompileError> {
        match &op.node {
            TirExpr::Name(name_ref)
                if matches!(name_ref.kind, TirNameKind::Ident)
                    && self.lookup_binding(&name_ref.name).is_none() =>
            {
                if let Some(result) = self.try_compile_builtin_call(&name_ref.name, args)? {
                    return Ok(result);
                }
                if let Ok(result) = self.resolve_and_emit_call(&name_ref.name, args) {
                    return Ok(result);
                }
                // Part of #3789: when the callee is in callee_bodies but not
                // yet compiled (e.g., cross-module INSTANCE import), compile
                // it on-demand instead of emitting CallExternal.
                let resolved_name = self.resolve_op_name(&name_ref.name).to_string();
                if let Some(callee_bodies) = self.callee_bodies {
                    if let Some(info) = callee_bodies.get(&resolved_name) {
                        let info_clone = info.clone();
                        match self.compile_callee_on_demand(&resolved_name, &info_clone) {
                            Ok(func_idx) => {
                                return self.emit_call(func_idx, args);
                            }
                            Err(_) => {
                                // On-demand compilation failed; fall back to
                                // CallExternal for runtime resolution.
                                let name_idx =
                                    self.add_const(Value::string(resolved_name.clone()))?;
                                let args_start =
                                    self.compile_exprs_into_consecutive(args.iter())?;
                                let rd = self.alloc_reg()?;
                                self.func.emit(Opcode::CallExternal {
                                    rd,
                                    name_idx,
                                    args_start,
                                    argc: args.len() as u8,
                                });
                                return Ok(rd);
                            }
                        }
                    }
                }
                self.compile_value_apply(op, args)
            }
            _ => self.compile_value_apply(op, args),
        }
    }

    fn compile_value_apply(
        &mut self,
        op: &Spanned<TirExpr>,
        args: &[Spanned<TirExpr>],
    ) -> Result<Register, CompileError> {
        let r_func = self.compile_expr(op)?;
        let args_start = self.compile_exprs_into_consecutive(args.iter())?;
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::ValueApply {
            rd,
            func: r_func,
            args_start,
            argc: args.len() as u8,
        });
        Ok(rd)
    }

    /// Compile an `OperatorRef` node.
    ///
    /// OperatorRef carries a module path and operator name. Module-qualified
    /// refs (non-empty path) should have been inlined by the TIR lowerer;
    /// plain refs are resolved the same way as `Apply(Name(Ident), args)`.
    ///
    /// Part of #3693: full INSTANCE-imported operator support:
    /// - Module-qualified OperatorRef resolves by the operator's simple name
    ///   when it was pre-compiled as a callee during the seeding phase.
    /// - Zero-arg OperatorRef on a parameterized operator produces a closure
    ///   value (same as `compile_name_expr` for `Name(Ident)`).
    /// - OperatorRef with args falls through to ValueApply when the callee
    ///   is not pre-compiled (e.g., higher-order INSTANCE-imported operators).
    pub(super) fn compile_operator_ref(
        &mut self,
        op_ref: &TirOperatorRef,
    ) -> Result<Register, CompileError> {
        let op_name = &op_ref.operator;
        let resolved_name = self.resolve_op_name(op_name).to_string();

        // Check callee_bodies FIRST for parameterized operator-as-value
        // (zero args but the operator itself has params → emit closure).
        // This must precede Call resolution because the fixed-point loop
        // may have compiled the callee, but a zero-arg OperatorRef to a
        // parameterized operator means "use it as a first-class value"
        // rather than "call it with zero arguments".
        if op_ref.args.is_empty() {
            if let Some(callee_bodies) = self.callee_bodies {
                if let Some(info) = callee_bodies
                    .get(&resolved_name)
                    .or_else(|| callee_bodies.get(op_name))
                {
                    if !info.params.is_empty() {
                        let ast_body = info.ast_body.as_ref().ok_or_else(|| {
                            CompileError::Unsupported(format!(
                                "parameterized OperatorRef '{}' is missing an AST body",
                                op_name
                            ))
                        })?;
                        return self.compile_closure_const(
                            info.params.clone(),
                            (*ast_body.0).clone(),
                            Some(&*info.body),
                        );
                    }
                }
            }
        }

        // Normal path: callee already compiled — emit a Call opcode.
        if let Ok(result) = self.resolve_and_emit_call(op_name, &op_ref.args) {
            return Ok(result);
        }

        // Part of #3789: try on-demand compilation for unresolved OperatorRef
        // before falling back to CallExternal.
        if let Some(callee_bodies) = self.callee_bodies {
            if let Some(info) = callee_bodies
                .get(&resolved_name)
                .or_else(|| callee_bodies.get(op_name))
            {
                let info_clone = info.clone();
                let compile_name = if callee_bodies.contains_key(&resolved_name) {
                    &resolved_name
                } else {
                    op_name
                };
                if let Ok(func_idx) = self.compile_callee_on_demand(compile_name, &info_clone) {
                    return self.emit_call(func_idx, &op_ref.args);
                }
            }
        }

        // Fallback: OperatorRef where on-demand compilation failed.
        // Emit CallExternal so the VM resolves via the TIR tree-walker.
        let name_idx = self.add_const(Value::string(op_name.to_string()))?;
        if !op_ref.args.is_empty() {
            let args_start = self.compile_exprs_into_consecutive(op_ref.args.iter())?;
            let rd = self.alloc_reg()?;
            self.func.emit(Opcode::CallExternal {
                rd,
                name_idx,
                args_start,
                argc: op_ref.args.len() as u8,
            });
            return Ok(rd);
        }
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::CallExternal {
            rd,
            name_idx,
            args_start: 0,
            argc: 0,
        });
        Ok(rd)
    }

    /// Resolve an operator name to a function index and emit a Call opcode.
    ///
    /// Shared by `compile_apply` (Name case) and `compile_operator_ref`.
    fn resolve_and_emit_call(
        &mut self,
        op_name: &str,
        args: &[Spanned<TirExpr>],
    ) -> Result<Register, CompileError> {
        let op_idx = self.resolve_callee_idx(op_name)?;
        self.emit_call(op_idx, args)
    }

    pub(super) fn compile_lambda_expr(
        &mut self,
        params: &[String],
        body: &Spanned<TirExpr>,
        ast_body: &PreservedAstBody,
    ) -> Result<Register, CompileError> {
        // Lambda bodies can reference LET-scoped operators via the inherited
        // `local_op_indices` map. The sub-function compilation context preserves
        // the parent's local_op_indices, so `Call` opcodes resolve normally.
        // Only register-bound variables (not local operators) need to be captured
        // at runtime via MakeClosure. Part of #3776.
        let captures = self.lambda_captured_bindings(params, ast_body);
        if captures.is_empty() {
            // Non-capturing: compile body as sub-function and embed as closure constant.
            return self.compile_lambda_with_sub_function(params, body, ast_body, &[]);
        }
        self.compile_capturing_lambda(params, body, ast_body, &captures)
    }

    pub(super) fn compile_op_ref_expr(
        &mut self,
        op: &str,
        span: Span,
    ) -> Result<Register, CompileError> {
        self.compile_closure_const(
            vec!["x".to_string(), "y".to_string()],
            Spanned {
                node: Expr::OpRef(op.to_string()),
                span,
            },
            None,
        )
    }

    pub(super) fn compile_closure_const(
        &mut self,
        params: Vec<String>,
        body: Spanned<Expr>,
        tir_body: Option<&Spanned<TirExpr>>,
    ) -> Result<Register, CompileError> {
        let mut closure = ClosureValue::new(params, body, Arc::new(Default::default()), None);
        if let Some(tir_body) = tir_body {
            closure = closure.with_tir_body(Box::new(StoredTirBody::new(tir_body.clone())));
        }
        self.compile_const(&Value::Closure(Arc::new(closure)))
    }

    /// Compile a Lambda body as a bytecode sub-function, then embed the result
    /// as a closure constant with a `bytecode_func_idx` so the VM can execute
    /// it natively instead of falling back to the TIR tree-walker.
    ///
    /// `capture_names` lists captured variable names that become extra parameters
    /// (appended after the Lambda's own params) in the compiled sub-function.
    /// For non-capturing lambdas, pass an empty slice.
    ///
    /// Part of #3697: compile Lambda expressions in bytecode VM.
    fn compile_lambda_with_sub_function(
        &mut self,
        params: &[String],
        body: &Spanned<TirExpr>,
        ast_body: &PreservedAstBody,
        capture_names: &[String],
    ) -> Result<Register, CompileError> {
        let bytecode_func_idx = self.try_compile_lambda_sub_function(params, body, capture_names);

        // Build the closure constant, attaching the bytecode func idx if
        // compilation succeeded. If it failed, the closure still works via
        // the TIR tree-walker fallback path.
        let mut closure = ClosureValue::new(
            params.to_vec(),
            (*ast_body.0).clone(),
            Arc::new(Default::default()),
            None,
        )
        .with_tir_body(Box::new(StoredTirBody::new(body.clone())));
        if let Some(idx) = bytecode_func_idx {
            closure = closure.with_bytecode_func_idx(idx);
        }
        self.compile_const(&Value::Closure(Arc::new(closure)))
    }

    /// Return the (name, register) pairs for free variables captured from
    /// local bindings. Empty if the lambda is non-capturing or only captures
    /// from outer (non-local) scope.
    fn lambda_captured_bindings(
        &self,
        params: &[String],
        ast_body: &PreservedAstBody,
    ) -> Vec<(String, Register)> {
        let mut free = free_vars(&ast_body.0.node);
        for param in params {
            free.remove(param);
        }
        let mut captures = Vec::new();
        for (name, reg) in self.bindings.iter().rev() {
            if free.remove(name) {
                captures.push((name.clone(), *reg));
            }
        }
        // Sort captures by name so that the compile-time parameter order is
        // deterministic and matches the sorted order used by the VM at runtime
        // when extracting capture values from the closure's HashMap env.
        // Part of #3697: HashMap iteration order is unspecified, so both sides
        // must agree on a canonical (alphabetical) ordering.
        captures.sort_by(|(a, _), (b, _)| a.cmp(b));
        captures
    }

    /// Try to compile a Lambda body as a bytecode sub-function.
    ///
    /// Returns `Some(func_idx)` on success, `None` if the body contains
    /// unsupported expressions. The sub-function receives `params` followed
    /// by `capture_names` as its parameter list.
    ///
    /// Part of #3697: Shared by both non-capturing and capturing Lambda paths.
    fn try_compile_lambda_sub_function(
        &mut self,
        params: &[String],
        body: &Spanned<TirExpr>,
        capture_names: &[String],
    ) -> Option<u16> {
        let full_params: Vec<String> = params.iter().chain(capture_names.iter()).cloned().collect();
        let arity = full_params.len() as u8;

        // Use a placeholder name; the actual func_idx is computed after body
        // compilation to account for sub-functions added during compilation.
        let sub_func = super::BytecodeFunction::new("<lambda>".to_string(), arity);

        // Save parent state and swap in the sub-function context.
        let saved_func = std::mem::replace(&mut self.func, sub_func);
        let saved_next_reg = self.next_reg;
        let saved_local_ops: std::collections::HashSet<String> =
            self.local_op_indices.keys().cloned().collect();

        // Part of #3802: CLEAR parent bindings before compiling the Lambda body.
        // Lambda sub-functions have their own register files. Parent bindings
        // that are NOT in the capture list would resolve to parent register
        // indices that don't exist in the sub-function's register file. The
        // Lambda's own params and captures (bound below) are the only valid
        // bindings. Non-captured parent names that are referenced will fail
        // compilation and fall back to the tree-walker via the Option return.
        let saved_bindings: Vec<(String, u8)> = self.bindings.drain(..).collect();

        // Bind all parameters to registers 0..arity.
        self.next_reg = 0;
        for (i, param) in full_params.iter().enumerate() {
            self.bindings.push((param.clone(), i as u8));
        }
        self.next_reg = arity;

        let compile_result = self.compile_expr(body);

        // Restore parent state regardless of success/failure.
        let compiled_sub_func = std::mem::replace(&mut self.func, saved_func);
        self.next_reg = saved_next_reg;
        self.bindings.clear();
        self.bindings.extend(saved_bindings);
        self.local_op_indices
            .retain(|k, _| saved_local_ops.contains(k));

        let result_reg = compile_result.ok()?;

        // Finalize the sub-function: add Move+Ret epilogue.
        let mut finalized = compiled_sub_func;
        if result_reg != 0 {
            finalized.emit(Opcode::Move {
                rd: 0,
                rs: result_reg,
            });
        }
        finalized.emit(Opcode::Ret { rs: 0 });

        // Compute func_idx AFTER body compilation because compile_expr may
        // add sub-functions, growing self.sub_functions. Part of #3802.
        let func_idx = self.next_func_idx + self.sub_functions.len() as u16;
        finalized.name = format!("<lambda@{func_idx}>");
        self.sub_functions.push(finalized);
        Some(func_idx)
    }

    /// Compile a capturing Lambda to a `MakeClosure` opcode.
    ///
    /// Emits a template closure constant, capture-name string constants,
    /// packs captured register values into consecutive registers, and
    /// emits `MakeClosure` to build the closure at runtime.
    ///
    /// Part of #3697: Also compiles the Lambda body as a sub-function with
    /// captures as extra parameters, attaching the `bytecode_func_idx` to the
    /// template closure so the VM can execute it natively.
    fn compile_capturing_lambda(
        &mut self,
        params: &[String],
        body: &Spanned<TirExpr>,
        ast_body: &PreservedAstBody,
        captures: &[(String, Register)],
    ) -> Result<Register, CompileError> {
        // Try to compile the Lambda body as a sub-function first.
        // Captures become extra parameters appended after the real params.
        let capture_names: Vec<String> = captures.iter().map(|(n, _)| n.clone()).collect();
        let bytecode_func_idx = self.try_compile_lambda_sub_function(params, body, &capture_names);

        // 1. Build and store the template closure (empty env).
        let mut closure = ClosureValue::new(
            params.to_vec(),
            (*ast_body.0).clone(),
            Arc::new(Default::default()),
            None,
        );
        closure = closure.with_tir_body(Box::new(StoredTirBody::new(body.clone())));
        if let Some(idx) = bytecode_func_idx {
            closure = closure.with_bytecode_func_idx(idx);
        }
        let template_idx = self.add_const(Value::Closure(Arc::new(closure)))?;

        // 2. Store capture names as string constants immediately after the template.
        for (name, _) in captures {
            self.add_const(Value::string(name.clone()))?;
        }

        // 3. Pack captured register values into consecutive registers.
        let captures_start = self.alloc_consecutive_regs(captures.len())?;
        for (i, (_, src_reg)) in captures.iter().enumerate() {
            let dst = captures_start + i as u8;
            if *src_reg != dst {
                self.func.emit(Opcode::Move {
                    rd: dst,
                    rs: *src_reg,
                });
            }
        }

        // 4. Emit MakeClosure opcode.
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::MakeClosure {
            rd,
            template_idx,
            captures_start,
            capture_count: captures.len() as u8,
        });
        Ok(rd)
    }

    /// Resolve an operator name to its function index.
    ///
    /// Checks local (LET) scope first, then global op_indices with
    /// operator replacement (e.g., `.cfg` `CONSTANT Foo <- Bar`).
    fn resolve_callee_idx(&self, op_name: &str) -> Result<u16, CompileError> {
        if let Some(&idx) = self.local_op_indices.get(op_name) {
            return Ok(idx);
        }
        match self.op_indices {
            Some(indices) => {
                let resolved_name = self.resolve_op_name(op_name);
                match indices.get(resolved_name) {
                    Some(&idx) => Ok(idx),
                    None => Err(CompileError::Unsupported(format!(
                        "callee '{}' not compiled",
                        op_name
                    ))),
                }
            }
            None => Err(CompileError::Unsupported(format!(
                "no op_indices for '{}'",
                op_name
            ))),
        }
    }

    /// Compile a callee body on-demand as a sub-function.
    ///
    /// When the bytecode compiler encounters a cross-module identifier that is
    /// present in `callee_bodies` but was not compiled during the fixed-point
    /// loop (e.g., an INSTANCE-imported operator whose TIR body references
    /// other operators), this method compiles it inline as a sub-function and
    /// registers it in `local_op_indices` so subsequent references resolve via
    /// `Call` instead of falling back to `CallExternal`.
    ///
    /// Part of #3789: cross-module identifier resolution in bytecode VM.
    pub(super) fn compile_callee_on_demand(
        &mut self,
        name: &str,
        info: &super::CalleeInfo,
    ) -> Result<u16, CompileError> {
        // Recursion guard: if we're already compiling this callee, bail out.
        if !self.on_demand_compiling.insert(name.to_string()) {
            return Err(CompileError::Unsupported(format!(
                "recursive on-demand compilation of '{name}'"
            )));
        }

        let arity = info.params.len() as u8;
        let sub_func = super::BytecodeFunction::new(name.to_string(), arity);

        // Save parent state and swap in the sub-function context.
        let saved_func = std::mem::replace(&mut self.func, sub_func);
        let saved_next_reg = self.next_reg;
        let saved_local_ops: std::collections::HashSet<String> =
            self.local_op_indices.keys().cloned().collect();

        // Part of #3802: CLEAR parent bindings before compiling the callee body.
        // On-demand compiled callees are separate operators — their bodies must
        // not see the parent scope's quantifier/LET bindings. Without this,
        // lookup_binding() can return a register index from the parent's register
        // space, but the callee's register file is sized only by its own
        // max_register, causing an index-out-of-bounds panic at runtime.
        //
        // Unlike compile_let_as_function and try_compile_lambda_sub_function
        // (which compile LET bodies and Lambda bodies that intentionally capture
        // enclosing scope), on-demand callees are independent operator definitions.
        let saved_bindings: Vec<(String, u8)> = self.bindings.drain(..).collect();

        // Bind parameters to registers 0..arity.
        self.next_reg = 0;
        for (i, param) in info.params.iter().enumerate() {
            self.bindings.push((param.clone(), i as u8));
        }
        self.next_reg = arity;

        let compile_result = self.compile_expr(&*info.body);

        // Restore parent state regardless of success/failure.
        let compiled_sub_func = std::mem::replace(&mut self.func, saved_func);
        self.next_reg = saved_next_reg;
        self.bindings.clear();
        self.bindings.extend(saved_bindings);
        self.local_op_indices
            .retain(|k, _| saved_local_ops.contains(k));
        self.on_demand_compiling.remove(name);

        // Propagate error after state is restored.
        let result_reg = compile_result?;

        // Finalize the sub-function: add Move+Ret epilogue.
        let mut finalized = compiled_sub_func;
        if result_reg != 0 {
            finalized.emit(Opcode::Move {
                rd: 0,
                rs: result_reg,
            });
        }
        finalized.emit(Opcode::Ret { rs: 0 });

        // Compute func_idx AFTER body compilation because compile_expr may
        // add sub-functions (via nested on-demand compilation), growing
        // self.sub_functions. Computing before would produce a stale index
        // that collides with sub-functions added during body compilation.
        // Part of #3802.
        let func_idx = self.next_func_idx + self.sub_functions.len() as u16;
        self.sub_functions.push(finalized);
        self.local_op_indices.insert(name.to_string(), func_idx);

        Ok(func_idx)
    }

    pub(super) fn try_compile_builtin_call(
        &mut self,
        name: &str,
        args: &[Spanned<TirExpr>],
    ) -> Result<Option<Register>, CompileError> {
        // Sequence/string concatenation: \o and \circ map to Concat (polymorphic).
        // Fixes #3820: StrConcat only handles strings; Concat handles both
        // sequences and strings via execute_concat dispatch.
        if (name == "\\o" || name == "\\circ") && args.len() == 2 {
            let r1 = self.compile_expr(&args[0])?;
            let r2 = self.compile_expr(&args[1])?;
            let rd = self.alloc_reg()?;
            self.func.emit(Opcode::Concat { rd, r1, r2 });
            return Ok(Some(rd));
        }

        // Map stdlib operator names to CallBuiltin opcodes.
        // Part of #3824: wire the compiler to emit CallBuiltin for operators
        // from EXTENDS modules (Sequences, FiniteSets, TLC) instead of falling
        // through to Call/CallExternal.
        let (builtin, expected_argc) = match name {
            // Sequences module
            "Len" => (BuiltinOp::Len, 1),
            "Head" => (BuiltinOp::Head, 1),
            "Tail" => (BuiltinOp::Tail, 1),
            "Append" => (BuiltinOp::Append, 2),
            "SubSeq" => (BuiltinOp::SubSeq, 3),
            "Seq" => (BuiltinOp::Seq, 1),
            // FiniteSets module
            "Cardinality" => (BuiltinOp::Cardinality, 1),
            "IsFiniteSet" => (BuiltinOp::IsFiniteSet, 1),
            // TLC module
            "ToString" => (BuiltinOp::ToString, 1),
            _ => return Ok(None),
        };

        if args.len() != expected_argc {
            return Ok(None);
        }

        let args_start = self.compile_exprs_into_consecutive(args.iter())?;
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::CallBuiltin {
            rd,
            builtin,
            args_start,
            argc: expected_argc as u8,
        });
        Ok(Some(rd))
    }

    /// Compile arguments into consecutive registers and emit a Call opcode.
    fn emit_call(
        &mut self,
        op_idx: u16,
        args: &[Spanned<TirExpr>],
    ) -> Result<Register, CompileError> {
        let args_start = self.next_reg;
        let argc = args.len() as u8;
        // Reserve consecutive slots for arguments up front.
        for _ in 0..argc {
            self.alloc_reg()?;
        }
        // Each arg may use multiple intermediate registers (e.g., `1+2` uses 3 regs),
        // so we Move each result to its expected slot after compilation.
        for (i, arg) in args.iter().enumerate() {
            let r_result = self.compile_expr(arg)?;
            let expected = args_start + i as u8;
            if r_result != expected {
                self.func.emit(Opcode::Move {
                    rd: expected,
                    rs: r_result,
                });
            }
        }

        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::Call {
            rd,
            op_idx,
            args_start,
            argc,
        });
        Ok(rd)
    }
}
