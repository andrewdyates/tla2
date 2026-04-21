// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Support helpers for `compile_expr` — name resolution, EXCEPT/record lowering,
//! and Prime/UNCHANGED special-case compilation.

use super::super::opcode::{Opcode, Register};
use super::{CompileError, FnCompileState};
use crate::nodes::{TirExceptPathElement, TirExpr, TirNameKind, TirNameRef};
use tla_core::Spanned;
use tla_value::Value;

impl<'a> FnCompileState<'a> {
    pub(super) fn compile_name_expr(
        &mut self,
        name_ref: &TirNameRef,
    ) -> Result<Register, CompileError> {
        // Check for bound variable first.
        if let Some(reg) = self.lookup_binding(&name_ref.name) {
            return Ok(reg);
        }
        match &name_ref.kind {
            TirNameKind::StateVar { index } => {
                let rd = self.alloc_reg()?;
                if self.in_prime_context {
                    self.func.emit(Opcode::LoadPrime {
                        rd,
                        var_idx: *index,
                    });
                } else {
                    self.func.emit(Opcode::LoadVar {
                        rd,
                        var_idx: *index,
                    });
                }
                Ok(rd)
            }
            TirNameKind::Ident => {
                if let Some(resolved_constants) = self.resolved_constants {
                    let lookup_id = if name_ref.name_id != tla_core::NameId::INVALID {
                        Some(name_ref.name_id)
                    } else {
                        tla_core::name_intern::lookup_name_id(&name_ref.name)
                    };
                    if let Some(lookup_id) = lookup_id {
                        if let Some(value) = resolved_constants.get(&lookup_id) {
                            return self.compile_const(value);
                        }
                    }
                }
                // Own the resolved name so it doesn't borrow `self`.
                let resolved_name = self.resolve_op_name(&name_ref.name).to_string();
                if let Some(callee_bodies) = self.callee_bodies {
                    if let Some(info) = callee_bodies.get(&resolved_name) {
                        if !info.params.is_empty() {
                            let ast_body = info.ast_body.as_ref().ok_or_else(|| {
                                CompileError::Unsupported(format!(
                                    "parameterized operator reference '{}' is missing an AST body",
                                    resolved_name
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
                // Try to resolve as a zero-arg operator call.
                // Check local (LET) scope first, then global op_indices.
                if let Some(&op_idx) = self.local_op_indices.get(&name_ref.name) {
                    let rd = self.alloc_reg()?;
                    self.func.emit(Opcode::Call {
                        rd,
                        op_idx,
                        args_start: 0,
                        argc: 0,
                    });
                    return Ok(rd);
                }
                if let Some(op_indices) = self.op_indices {
                    if let Some(&op_idx) = op_indices.get(resolved_name.as_str()) {
                        let rd = self.alloc_reg()?;
                        self.func.emit(Opcode::Call {
                            rd,
                            op_idx,
                            args_start: 0,
                            argc: 0,
                        });
                        return Ok(rd);
                    }
                }
                // Check if this Ident is actually a state variable (unresolved
                // because the Module AST wasn't state-var-resolved before TIR lowering).
                if let Some(state_vars) = self.state_vars {
                    if let Some(&var_idx) = state_vars.get(&name_ref.name) {
                        let rd = self.alloc_reg()?;
                        if self.in_prime_context {
                            self.func.emit(Opcode::LoadPrime { rd, var_idx });
                        } else {
                            self.func.emit(Opcode::LoadVar { rd, var_idx });
                        }
                        return Ok(rd);
                    }
                }
                // Part of #3789: compile cross-module callee on-demand when
                // it wasn't pre-compiled during the fixed-point loop. This
                // avoids CallExternal fallback which requires EvalCtx at runtime.
                if let Some(callee_bodies) = self.callee_bodies {
                    if let Some(info) = callee_bodies.get(&resolved_name) {
                        if info.params.is_empty() {
                            let info_clone = info.clone();
                            match self.compile_callee_on_demand(&resolved_name, &info_clone) {
                                Ok(func_idx) => {
                                    let rd = self.alloc_reg()?;
                                    self.func.emit(Opcode::Call {
                                        rd,
                                        op_idx: func_idx,
                                        args_start: 0,
                                        argc: 0,
                                    });
                                    return Ok(rd);
                                }
                                Err(_) => {
                                    // On-demand compilation failed (e.g., recursive or
                                    // unsupported sub-expression). Fall back to CallExternal.
                                    let name_idx =
                                        self.add_const(Value::string(resolved_name.clone()))?;
                                    let rd = self.alloc_reg()?;
                                    self.func.emit(Opcode::CallExternal {
                                        rd,
                                        name_idx,
                                        args_start: 0,
                                        argc: 0,
                                    });
                                    return Ok(rd);
                                }
                            }
                        }
                    }
                }
                Err(CompileError::Unsupported(format!(
                    "unresolved identifier '{}'",
                    name_ref.name
                )))
            }
        }
    }

    pub(super) fn compile_except_expr(
        &mut self,
        base: &Spanned<TirExpr>,
        specs: &[crate::nodes::TirExceptSpec],
    ) -> Result<Register, CompileError> {
        let mut r_func = self.compile_expr(base)?;
        for spec in specs {
            // For single-path EXCEPT, emit FuncExcept directly.
            if spec.path.len() == 1 {
                match &spec.path[0] {
                    TirExceptPathElement::Index(idx_expr) => {
                        let r_path = self.compile_expr(idx_expr)?;
                        // Compute @ = base[key] for ExceptAt references in value.
                        let r_at = self.alloc_reg()?;
                        self.func.emit(Opcode::FuncApply {
                            rd: r_at,
                            func: r_func,
                            arg: r_path,
                        });
                        let prev_at = self.except_at_register.replace(r_at);
                        let r_val = self.compile_expr(&spec.value)?;
                        self.except_at_register = prev_at;
                        let rd = self.alloc_reg()?;
                        self.func.emit(Opcode::FuncExcept {
                            rd,
                            func: r_func,
                            path: r_path,
                            val: r_val,
                        });
                        r_func = rd;
                    }
                    TirExceptPathElement::Field(field) => {
                        let field_idx = self.constants.add_field_id(field.field_id.0);
                        let r_path = self.alloc_reg()?;
                        let idx = self.add_const(Value::String(field.name.clone().into()))?;
                        self.func.emit(Opcode::LoadConst { rd: r_path, idx });
                        // Compute @ = base[key] for ExceptAt references in value.
                        let r_at = self.alloc_reg()?;
                        self.func.emit(Opcode::FuncApply {
                            rd: r_at,
                            func: r_func,
                            arg: r_path,
                        });
                        let prev_at = self.except_at_register.replace(r_at);
                        let r_val = self.compile_expr(&spec.value)?;
                        self.except_at_register = prev_at;
                        let rd = self.alloc_reg()?;
                        self.func.emit(Opcode::FuncExcept {
                            rd,
                            func: r_func,
                            path: r_path,
                            val: r_val,
                        });
                        let _ = field_idx; // Used for future optimization
                        r_func = rd;
                    }
                }
            } else {
                // Multi-level EXCEPT: desugar to nested single-level.
                // [f EXCEPT ![a][b] = c] → [f EXCEPT ![a] = [f[a] EXCEPT ![b] = c]]
                r_func = self.compile_multi_level_except(r_func, &spec.path, &spec.value)?;
            }
        }
        Ok(r_func)
    }

    /// Compile a multi-level EXCEPT path by recursive desugaring.
    ///
    /// `[f EXCEPT ![a][b] = c]` → `[f EXCEPT ![a] = [f[a] EXCEPT ![b] = c]]`
    ///
    /// The recursion peels one path element at a time. When only one element
    /// remains, we emit a single FuncExcept directly.
    fn compile_multi_level_except(
        &mut self,
        r_func: Register,
        path: &[TirExceptPathElement],
        value: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        debug_assert!(path.len() >= 2);

        // Compile the first path element as a key.
        let r_key = self.compile_except_key(&path[0])?;

        // Get the inner value: f[a]
        let r_inner = self.alloc_reg()?;
        self.func.emit(Opcode::FuncApply {
            rd: r_inner,
            func: r_func,
            arg: r_key,
        });

        // Recursively compile the inner EXCEPT on remaining path elements.
        let r_inner_result = if path.len() == 2 {
            // Base case: single remaining element → direct FuncExcept.
            let r_inner_key = self.compile_except_key(&path[1])?;
            // Compute @ = inner[key] for ExceptAt references in value.
            let r_at = self.alloc_reg()?;
            self.func.emit(Opcode::FuncApply {
                rd: r_at,
                func: r_inner,
                arg: r_inner_key,
            });
            let prev_at = self.except_at_register.replace(r_at);
            let r_val = self.compile_expr(value)?;
            self.except_at_register = prev_at;
            let rd = self.alloc_reg()?;
            self.func.emit(Opcode::FuncExcept {
                rd,
                func: r_inner,
                path: r_inner_key,
                val: r_val,
            });
            rd
        } else {
            // Recursive case: more path elements remain.
            self.compile_multi_level_except(r_inner, &path[1..], value)?
        };

        // Outer EXCEPT: [f EXCEPT ![a] = inner_result]
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::FuncExcept {
            rd,
            func: r_func,
            path: r_key,
            val: r_inner_result,
        });
        Ok(rd)
    }

    /// Compile a single EXCEPT path element (Index or Field) into a register.
    fn compile_except_key(
        &mut self,
        element: &TirExceptPathElement,
    ) -> Result<Register, CompileError> {
        match element {
            TirExceptPathElement::Index(idx_expr) => self.compile_expr(idx_expr),
            TirExceptPathElement::Field(field) => {
                let _field_idx = self.constants.add_field_id(field.field_id.0);
                let rd = self.alloc_reg()?;
                let idx = self.add_const(Value::String(field.name.clone().into()))?;
                self.func.emit(Opcode::LoadConst { rd, idx });
                Ok(rd)
            }
        }
    }

    pub(super) fn compile_record_expr(
        &mut self,
        fields: &[(crate::nodes::TirFieldName, Spanned<TirExpr>)],
    ) -> Result<Register, CompileError> {
        if fields.is_empty() {
            let rd = self.alloc_reg()?;
            self.func.emit(Opcode::RecordNew {
                rd,
                fields_start: 0,
                values_start: 0,
                count: 0,
            });
            return Ok(rd);
        }

        // Add field IDs to constant pool.
        let fields_start = self.constants.value_count() as u16;
        for (field_name, _) in fields {
            self.add_const(Value::String(field_name.name.clone().into()))?;
        }

        let values_start =
            self.compile_exprs_into_consecutive(fields.iter().map(|(_, expr)| expr))?;

        let count = fields.len().min(255) as u8;
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::RecordNew {
            rd,
            fields_start,
            values_start,
            count,
        });
        Ok(rd)
    }

    pub(super) fn compile_record_access_expr(
        &mut self,
        record: &Spanned<TirExpr>,
        field: &crate::nodes::TirFieldName,
    ) -> Result<Register, CompileError> {
        let rs = self.compile_expr(record)?;
        let field_idx = self.constants.add_field_id(field.field_id.0);
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::RecordGet { rd, rs, field_idx });
        Ok(rd)
    }

    pub(super) fn compile_record_set_expr(
        &mut self,
        fields: &[(crate::nodes::TirFieldName, Spanned<TirExpr>)],
    ) -> Result<Register, CompileError> {
        let fields_start = self.constants.value_count() as u16;
        for (field_name, _) in fields {
            self.add_const(Value::String(field_name.name.clone().into()))?;
        }
        let values_start =
            self.compile_exprs_into_consecutive(fields.iter().map(|(_, expr)| expr))?;
        let count = fields.len().min(255) as u8;
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::RecordSet {
            rd,
            fields_start,
            values_start,
            count,
        });
        Ok(rd)
    }

    pub(super) fn compile_prime_expr(
        &mut self,
        inner: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        // If inner is a state variable name, use LoadPrime directly.
        if let TirExpr::Name(name_ref) = &inner.node {
            match &name_ref.kind {
                TirNameKind::StateVar { index } => {
                    let rd = self.alloc_reg()?;
                    self.func.emit(Opcode::LoadPrime {
                        rd,
                        var_idx: *index,
                    });
                    return Ok(rd);
                }
                TirNameKind::Ident => {
                    // Unresolved Ident — check if it's a state variable.
                    if let Some(state_vars) = self.state_vars {
                        if let Some(&var_idx) = state_vars.get(&name_ref.name) {
                            let rd = self.alloc_reg()?;
                            self.func.emit(Opcode::LoadPrime { rd, var_idx });
                            return Ok(rd);
                        }
                    }
                }
            }
        }
        // General case: compile inner expression in prime context so that
        // all state variable loads use LoadPrime (next-state) instead of LoadVar.
        // SetPrimeMode also needed for Call targets whose LoadVar opcodes are
        // resolved at runtime.
        self.func.emit(Opcode::SetPrimeMode { enable: true });
        let was_prime = self.in_prime_context;
        self.in_prime_context = true;
        let result = self.compile_expr(inner);
        self.in_prime_context = was_prime;
        self.func.emit(Opcode::SetPrimeMode { enable: false });
        result
    }

    pub(super) fn compile_unchanged_expr(
        &mut self,
        inner: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        // Fast path: extract state variable indices directly and emit a
        // single Unchanged opcode that compares current vs next state slots.
        if let Ok(var_indices) = extract_unchanged_var_indices(inner, self.state_vars) {
            let count = var_indices.len();
            if count > 0 && count <= 255 {
                let start = self.add_const(Value::SmallInt(var_indices[0] as i64))?;
                for &idx in &var_indices[1..] {
                    self.add_const(Value::SmallInt(idx as i64))?;
                }
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Unchanged {
                    rd,
                    start,
                    count: count as u8,
                });
                return Ok(rd);
            }
        }

        // General fallback: UNCHANGED expr ≡ (expr = expr').
        // Compile inner in normal context (current state), then in prime
        // context (next state), and compare with Eq. Handles operator-defined
        // variable tuples like `UNCHANGED vars` where `vars == <<x, y>>`.
        //
        // Both compile-time (in_prime_context) and runtime (SetPrimeMode)
        // flags are used: in_prime_context redirects direct LoadVar→LoadPrime
        // at compile time, while SetPrimeMode causes the VM to redirect
        // LoadVar→next-state for calls to pre-compiled functions that use
        // LoadVar opcodes.
        let r_current = self.compile_expr(inner)?;
        self.func.emit(Opcode::SetPrimeMode { enable: true });
        let was_prime = self.in_prime_context;
        self.in_prime_context = true;
        let r_prime = self.compile_expr(inner)?;
        self.in_prime_context = was_prime;
        self.func.emit(Opcode::SetPrimeMode { enable: false });
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::Eq {
            rd,
            r1: r_current,
            r2: r_prime,
        });
        Ok(rd)
    }
}

/// Extract state variable indices from an UNCHANGED inner expression.
///
/// Supports:
/// - Single state variable: `UNCHANGED x` → `[idx]`
/// - Tuple of state variables: `UNCHANGED <<x, y>>` → `[idx_x, idx_y]`
///
/// When `state_vars` is provided, unresolved `Ident` names are checked
/// against the state variable map as a fallback (for TIR bodies lowered
/// from raw Module AST without prior state-var resolution).
///
/// Returns `Err(Unsupported)` for complex inner expressions.
fn extract_unchanged_var_indices(
    inner: &Spanned<TirExpr>,
    state_vars: Option<&std::collections::HashMap<String, u16>>,
) -> Result<Vec<u16>, CompileError> {
    match &inner.node {
        TirExpr::Name(name_ref) => match &name_ref.kind {
            TirNameKind::StateVar { index } => Ok(vec![*index]),
            TirNameKind::Ident => {
                if let Some(sv) = state_vars {
                    if let Some(&var_idx) = sv.get(&name_ref.name) {
                        return Ok(vec![var_idx]);
                    }
                }
                Err(CompileError::Unsupported(
                    "UNCHANGED on non-state-variable identifier".to_string(),
                ))
            }
        },
        TirExpr::Tuple(elems) => {
            let mut indices = Vec::with_capacity(elems.len());
            for elem in elems {
                match &elem.node {
                    TirExpr::Name(name_ref) => match &name_ref.kind {
                        TirNameKind::StateVar { index } => indices.push(*index),
                        TirNameKind::Ident => {
                            if let Some(sv) = state_vars {
                                if let Some(&var_idx) = sv.get(&name_ref.name) {
                                    indices.push(var_idx);
                                    continue;
                                }
                            }
                            return Err(CompileError::Unsupported(
                                "UNCHANGED tuple element is not a state variable".to_string(),
                            ));
                        }
                    },
                    _ => {
                        return Err(CompileError::Unsupported(
                            "UNCHANGED tuple element is not a simple variable".to_string(),
                        ));
                    }
                }
            }
            Ok(indices)
        }
        _ => Err(CompileError::Unsupported(
            "UNCHANGED on complex expression".to_string(),
        )),
    }
}
