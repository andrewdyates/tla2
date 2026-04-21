// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier and set comprehension compilation helpers.

use super::super::opcode::{Opcode, Register};
use super::{CompileError, FnCompileState};
use crate::nodes::{TirBoundVar, TirExpr};
use tla_core::Spanned;

impl<'a> FnCompileState<'a> {
    /// Compile FORALL quantifier.
    ///
    /// Multi-variable `\A x \in S, y \in T: P(x, y)` is desugared to
    /// `\A x \in S: (\A y \in T: P(x, y))` via recursive nesting.
    pub(super) fn compile_forall(
        &mut self,
        vars: &[TirBoundVar],
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        self.compile_forall_nested(vars, body)
    }

    fn compile_forall_nested(
        &mut self,
        vars: &[TirBoundVar],
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        let var = &vars[0];
        let domain_expr = var
            .domain
            .as_ref()
            .ok_or_else(|| CompileError::Unsupported("FORALL without domain".to_string()))?;

        let r_domain = self.compile_expr(domain_expr)?;
        let rd = self.alloc_reg()?;
        let r_binding = self.alloc_reg()?;

        let begin_idx = self.func.emit(Opcode::ForallBegin {
            rd,
            r_binding,
            r_domain,
            loop_end: 0, // patched
        });

        // Push binding for this variable.
        self.bindings.push((var.name.clone(), r_binding));
        // If more variables remain, nest; otherwise compile the body.
        let r_body = if vars.len() > 1 {
            self.compile_forall_nested(&vars[1..], body)?
        } else {
            self.compile_expr(body)?
        };
        self.bindings.pop();

        let next_idx = self.func.emit(Opcode::ForallNext {
            rd,
            r_binding,
            r_body,
            loop_begin: 0, // patched
        });

        let end = self.func.len();
        self.func.patch_jump(begin_idx, end);
        self.func.patch_jump(next_idx, begin_idx + 1);

        Ok(rd)
    }

    /// Compile EXISTS quantifier.
    ///
    /// Multi-variable `\E x \in S, y \in T: P(x, y)` is desugared to
    /// `\E x \in S: (\E y \in T: P(x, y))` via recursive nesting.
    pub(super) fn compile_exists(
        &mut self,
        vars: &[TirBoundVar],
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        self.compile_exists_nested(vars, body)
    }

    fn compile_exists_nested(
        &mut self,
        vars: &[TirBoundVar],
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        let var = &vars[0];
        let domain_expr = var
            .domain
            .as_ref()
            .ok_or_else(|| CompileError::Unsupported("EXISTS without domain".to_string()))?;

        let r_domain = self.compile_expr(domain_expr)?;
        let rd = self.alloc_reg()?;
        let r_binding = self.alloc_reg()?;

        let begin_idx = self.func.emit(Opcode::ExistsBegin {
            rd,
            r_binding,
            r_domain,
            loop_end: 0, // patched
        });

        self.bindings.push((var.name.clone(), r_binding));
        let r_body = if vars.len() > 1 {
            self.compile_exists_nested(&vars[1..], body)?
        } else {
            self.compile_expr(body)?
        };
        self.bindings.pop();

        let next_idx = self.func.emit(Opcode::ExistsNext {
            rd,
            r_binding,
            r_body,
            loop_begin: 0, // patched
        });

        let end = self.func.len();
        self.func.patch_jump(begin_idx, end);
        self.func.patch_jump(next_idx, begin_idx + 1);

        Ok(rd)
    }

    /// Compile CHOOSE expression: `CHOOSE x \in S : P(x)`.
    ///
    /// Iterates the domain, evaluates the predicate for each element,
    /// and returns the first element where the predicate is TRUE.
    /// If no element satisfies P, halts (TLA+ runtime error).
    pub(super) fn compile_choose(
        &mut self,
        var: &TirBoundVar,
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        let domain_expr = var
            .domain
            .as_ref()
            .ok_or_else(|| CompileError::Unsupported("CHOOSE without domain".to_string()))?;

        let r_domain = self.compile_expr(domain_expr)?;
        let rd = self.alloc_reg()?;
        let r_binding = self.alloc_reg()?;

        let begin_idx = self.func.emit(Opcode::ChooseBegin {
            rd,
            r_binding,
            r_domain,
            loop_end: 0, // patched
        });

        self.bindings.push((var.name.clone(), r_binding));
        let r_body = self.compile_expr(body)?;
        self.bindings.pop();

        let next_idx = self.func.emit(Opcode::ChooseNext {
            rd,
            r_binding,
            r_body,
            loop_begin: 0, // patched
        });

        let end = self.func.len();
        self.func.patch_jump(begin_idx, end);
        self.func.patch_jump(next_idx, begin_idx + 1);

        Ok(rd)
    }

    /// Compile set filter: `{x \in S : P(x)}`.
    pub(super) fn compile_set_filter(
        &mut self,
        var: &TirBoundVar,
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        let domain_expr = var
            .domain
            .as_ref()
            .ok_or_else(|| CompileError::Unsupported("SetFilter without domain".to_string()))?;

        let r_domain = self.compile_expr(domain_expr)?;
        let rd = self.alloc_reg()?;
        let r_binding = self.alloc_reg()?;

        let begin_idx = self.func.emit(Opcode::SetFilterBegin {
            rd,
            r_binding,
            r_domain,
            loop_end: 0,
        });

        self.bindings.push((var.name.clone(), r_binding));
        let r_body = self.compile_expr(body)?;
        self.bindings.pop();

        let next_idx = self.func.emit(Opcode::LoopNext {
            r_binding,
            r_body,
            loop_begin: 0,
        });

        let end = self.func.len();
        self.func.patch_jump(begin_idx, end);
        self.func.patch_jump(next_idx, begin_idx + 1);

        Ok(rd)
    }

    /// Compile set builder: `{e : x \in S}` or `{e : x \in S, y \in T}`.
    ///
    /// Multi-variable SetBuilder is desugared via UNION (BigUnion) to flatten
    /// nested iteration into a flat set:
    /// `{e : x \in S, y \in T}` → `UNION {{e : y \in T} : x \in S}`
    pub(super) fn compile_set_builder(
        &mut self,
        body: &Spanned<TirExpr>,
        vars: &[TirBoundVar],
    ) -> Result<Register, CompileError> {
        if vars.len() == 1 {
            return self.compile_set_builder_single(body, &vars[0]);
        }
        // Multi-variable: peel first var, recurse on rest, flatten with BigUnion.
        // Outer set builder iterates x ∈ S, body = {e : y ∈ T, ...}
        let var = &vars[0];
        let domain_expr = var
            .domain
            .as_ref()
            .ok_or_else(|| CompileError::Unsupported("SetBuilder without domain".to_string()))?;

        let r_domain = self.compile_expr(domain_expr)?;
        let r_outer = self.alloc_reg()?;
        let r_binding = self.alloc_reg()?;

        let begin_idx = self.func.emit(Opcode::SetBuilderBegin {
            rd: r_outer,
            r_binding,
            r_domain,
            loop_end: 0,
        });

        self.bindings.push((var.name.clone(), r_binding));
        // Inner set builder produces {e : remaining vars}
        let r_inner_set = self.compile_set_builder(body, &vars[1..])?;
        self.bindings.pop();

        let next_idx = self.func.emit(Opcode::LoopNext {
            r_binding,
            r_body: r_inner_set,
            loop_begin: 0,
        });

        let end = self.func.len();
        self.func.patch_jump(begin_idx, end);
        self.func.patch_jump(next_idx, begin_idx + 1);

        // Flatten: UNION { {e : y ∈ T, ...} : x ∈ S }
        let rd = self.alloc_reg()?;
        self.func.emit(Opcode::BigUnion { rd, rs: r_outer });
        Ok(rd)
    }

    /// Compile a single-variable set builder: `{e : x \in S}`.
    fn compile_set_builder_single(
        &mut self,
        body: &Spanned<TirExpr>,
        var: &TirBoundVar,
    ) -> Result<Register, CompileError> {
        let domain_expr = var
            .domain
            .as_ref()
            .ok_or_else(|| CompileError::Unsupported("SetBuilder without domain".to_string()))?;

        let r_domain = self.compile_expr(domain_expr)?;
        let rd = self.alloc_reg()?;
        let r_binding = self.alloc_reg()?;

        let begin_idx = self.func.emit(Opcode::SetBuilderBegin {
            rd,
            r_binding,
            r_domain,
            loop_end: 0,
        });

        self.bindings.push((var.name.clone(), r_binding));
        let r_body = self.compile_expr(body)?;
        self.bindings.pop();

        let next_idx = self.func.emit(Opcode::LoopNext {
            r_binding,
            r_body,
            loop_begin: 0,
        });

        let end = self.func.len();
        self.func.patch_jump(begin_idx, end);
        self.func.patch_jump(next_idx, begin_idx + 1);

        Ok(rd)
    }

    /// Compile function definition: `[x \in S |-> e]` or `[x \in S, y \in T |-> e]`.
    ///
    /// Multi-variable FuncDef is desugared to a tuple-domain function:
    /// `[x \in S, y \in T |-> e]` → `[t \in S \X T |-> LET x == t[1], y == t[2] IN e]`
    pub(super) fn compile_func_def(
        &mut self,
        vars: &[TirBoundVar],
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        if vars.len() == 1 {
            return self.compile_func_def_single(&vars[0], body);
        }

        // Multi-variable: compute cross-product domain S × T × ...
        let mut domain_regs = Vec::with_capacity(vars.len());
        for var in vars {
            let domain_expr = var
                .domain
                .as_ref()
                .ok_or_else(|| CompileError::Unsupported("FuncDef without domain".to_string()))?;
            domain_regs.push(self.compile_expr(domain_expr)?);
        }

        // Emit Times to compute the cross product.
        let times_start = self.next_reg;
        let count = vars.len().min(255) as u8;
        for &r in &domain_regs {
            let slot = self.alloc_reg()?;
            if r != slot {
                self.func.emit(Opcode::Move { rd: slot, rs: r });
            }
        }
        let r_domain = self.alloc_reg()?;
        self.func.emit(Opcode::Times {
            rd: r_domain,
            start: times_start,
            count,
        });

        // Iterate over the cross-product domain.
        let rd = self.alloc_reg()?;
        let r_binding = self.alloc_reg()?;

        let begin_idx = self.func.emit(Opcode::FuncDefBegin {
            rd,
            r_binding,
            r_domain,
            loop_end: 0,
        });

        // Destructure tuple: bind x = t[1], y = t[2], etc.
        let saved_bindings = self.bindings.len();
        for (i, var) in vars.iter().enumerate() {
            let r_idx = self.alloc_reg()?;
            // TLA+ tuples are 1-indexed.
            self.func.emit(Opcode::LoadImm {
                rd: r_idx,
                value: (i as i64) + 1,
            });
            let r_elem = self.alloc_reg()?;
            self.func.emit(Opcode::FuncApply {
                rd: r_elem,
                func: r_binding,
                arg: r_idx,
            });
            self.bindings.push((var.name.clone(), r_elem));
        }

        let r_body = self.compile_expr(body)?;

        // Pop all tuple-destructuring bindings.
        self.bindings.truncate(saved_bindings);

        let next_idx = self.func.emit(Opcode::LoopNext {
            r_binding,
            r_body,
            loop_begin: 0,
        });

        let end = self.func.len();
        self.func.patch_jump(begin_idx, end);
        self.func.patch_jump(next_idx, begin_idx + 1);

        Ok(rd)
    }

    /// Compile a single-variable function definition: `[x \in S |-> e]`.
    fn compile_func_def_single(
        &mut self,
        var: &TirBoundVar,
        body: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        let domain_expr = var
            .domain
            .as_ref()
            .ok_or_else(|| CompileError::Unsupported("FuncDef without domain".to_string()))?;

        let r_domain = self.compile_expr(domain_expr)?;
        let rd = self.alloc_reg()?;
        let r_binding = self.alloc_reg()?;

        let begin_idx = self.func.emit(Opcode::FuncDefBegin {
            rd,
            r_binding,
            r_domain,
            loop_end: 0,
        });

        self.bindings.push((var.name.clone(), r_binding));
        let r_body = self.compile_expr(body)?;
        self.bindings.pop();

        let next_idx = self.func.emit(Opcode::LoopNext {
            r_binding,
            r_body,
            loop_begin: 0,
        });

        let end = self.func.len();
        self.func.patch_jump(begin_idx, end);
        self.func.patch_jump(next_idx, begin_idx + 1);

        Ok(rd)
    }
}
