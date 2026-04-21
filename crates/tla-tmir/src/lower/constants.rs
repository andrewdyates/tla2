// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constant and frame condition lowering: LoadConst, FuncSet, Unchanged.

use crate::TmirError;
use tla_value::Value;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::value::ValueId;

use super::{Ctx, LoweringMode};

impl<'cp> Ctx<'cp> {
    // =====================================================================
    // LoadConst: load a compile-time constant from the constant pool
    // =====================================================================

    /// Lower `LoadConst { rd, idx }`.
    ///
    /// Resolves the constant pool entry at compile time and emits the
    /// appropriate immediate load. Supports `SmallInt` (→ `LoadImm i64`)
    /// and `Bool` (→ `LoadImm 0/1`). Compound values (sets, strings, etc.)
    /// cannot be represented as i64 scalars and produce an error.
    pub(super) fn lower_load_const(
        &mut self,
        block_idx: usize,
        rd: u8,
        idx: u16,
    ) -> Result<Option<usize>, TmirError> {
        let pool = self.require_const_pool()?;
        let value = pool.get_value(idx);
        match value {
            Value::SmallInt(n) => {
                self.store_reg_imm(block_idx, rd, *n)?;
                Ok(Some(block_idx))
            }
            Value::Bool(b) => {
                self.store_reg_imm(block_idx, rd, i64::from(*b))?;
                Ok(Some(block_idx))
            }
            other => Err(TmirError::UnsupportedOpcode(format!(
                "LoadConst: compound constant pool value not representable as i64: {other:?}"
            ))),
        }
    }

    // =====================================================================
    // FuncSet: [S -> T] — the set of all functions from S to T
    // =====================================================================

    /// Lower `FuncSet { rd, domain, range }`.
    ///
    /// A function set `[S -> T]` is represented as a 2-slot aggregate containing
    /// the domain set pointer and the codomain set pointer:
    ///
    ///   `[domain_ptr_as_i64, codomain_ptr_as_i64]`
    ///
    /// This is a lazy representation — the function set is not materialized into
    /// all |T|^|S| functions. The aggregate stores enough information for
    /// downstream operations (membership testing, iteration) to reconstruct the
    /// semantics.
    pub(super) fn lower_func_set(
        &mut self,
        block_idx: usize,
        rd: u8,
        domain_reg: u8,
        range_reg: u8,
    ) -> Result<(), TmirError> {
        // Load the domain and range set pointers from their registers.
        let domain_val = self.load_reg(block_idx, domain_reg)?;
        let range_val = self.load_reg(block_idx, range_reg)?;

        // Allocate a 2-slot aggregate: [domain_ptr, codomain_ptr].
        let agg_ptr = self.alloc_aggregate(block_idx, 2);

        // Store domain set pointer at slot 0.
        self.store_at_offset(block_idx, agg_ptr, 0, domain_val);

        // Store codomain set pointer at slot 1.
        self.store_at_offset(block_idx, agg_ptr, 1, range_val);

        // Store the aggregate pointer into rd.
        self.store_reg_ptr(block_idx, rd, agg_ptr)
    }

    // =====================================================================
    // Unchanged: frame condition (next' = current for listed vars)
    // =====================================================================

    /// Lower `Unchanged { rd, start, count }`.
    ///
    /// Iterates over `count` entries in the constant pool starting at `start`.
    /// Each entry must be `SmallInt(var_idx)`. For each, loads
    /// `state_in[var_idx]` and `state_out[var_idx]`, compares equality, and
    /// ANDs the results. Stores `1` (TRUE) or `0` (FALSE) into `rd`.
    ///
    /// Requires `NextState` mode (needs both `state_in` and `state_out`).
    pub(super) fn lower_unchanged(
        &mut self,
        block_idx: usize,
        rd: u8,
        start: u16,
        count: u8,
    ) -> Result<Option<usize>, TmirError> {
        if self.mode != LoweringMode::NextState {
            return Err(TmirError::NotEligible {
                reason: "Unchanged requires next-state lowering".to_owned(),
            });
        }
        let state_out = self.state_out_ptr.ok_or_else(|| {
            TmirError::Emission(
                "missing state_out parameter for Unchanged in next-state lowering".to_owned(),
            )
        })?;
        let pool = self.require_const_pool()?;

        // Resolve all var indices at compile time.
        let mut var_indices = Vec::with_capacity(count as usize);
        for i in 0..(count as u16) {
            let val = pool.get_value(start + i);
            match val {
                Value::SmallInt(idx) => var_indices.push(*idx as u16),
                other => {
                    return Err(TmirError::Emission(format!(
                        "Unchanged: constant pool entry at {} is not SmallInt: {other:?}",
                        start + i
                    )));
                }
            }
        }

        if var_indices.is_empty() {
            // UNCHANGED <<>> is vacuously true.
            self.store_reg_imm(block_idx, rd, 1)?;
            return Ok(Some(block_idx));
        }

        let state_in = self.state_in_ptr;

        // For a single variable, just compare directly.
        // For multiple, AND the comparisons together.
        //
        // Emit: for each var_idx:
        //   cur = load state_in[var_idx]
        //   nxt = load state_out[var_idx]
        //   eq_i = icmp eq cur, nxt
        //   eq_i_i64 = zext eq_i to i64
        // Then AND all eq_i_i64 values together.

        let mut result_val: Option<ValueId> = None;

        for &var_idx in &var_indices {
            // Load current state value.
            let cur_ptr = self.emit_state_slot_ptr(block_idx, state_in, var_idx);
            let cur = self.emit_with_result(block_idx, Inst::Load { ty: Ty::I64, ptr: cur_ptr });

            // Load next state value.
            let nxt_ptr = self.emit_state_slot_ptr(block_idx, state_out, var_idx);
            let nxt = self.emit_with_result(block_idx, Inst::Load { ty: Ty::I64, ptr: nxt_ptr });

            // Compare.
            let eq = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: cur,
                    rhs: nxt,
                },
            );
            let eq_i64 = self.emit_with_result(
                block_idx,
                Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: Ty::I64,
                    operand: eq,
                },
            );

            result_val = Some(match result_val {
                None => eq_i64,
                Some(prev) => self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: prev,
                        rhs: eq_i64,
                    },
                ),
            });
        }

        // Store the final result into rd.
        self.store_reg_value(block_idx, rd, result_val.expect("non-empty var_indices"))?;

        Ok(Some(block_idx))
    }
}
