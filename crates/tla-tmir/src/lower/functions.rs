// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Function operation lowering: FuncApply, Domain, FuncExcept, FuncDefBegin,
//! LoopNext (FuncDef).

use crate::TmirError;
use tla_jit_abi::JitRuntimeErrorKind;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::value::ValueId;
use tmir::Constant;
use tmir::InstrNode;

use super::{Ctx, LoopNextKind, LoopNextState, QuantifierLoopState};

impl<'cp> Ctx<'cp> {
    // =====================================================================
    // Function operations
    // =====================================================================
    //
    // TLA+ functions are total mappings from domain keys to values.
    // Aggregate layout: slot[0] = pair_count, then interleaved key-value pairs:
    //   slot[1] = key1, slot[2] = val1, slot[3] = key2, slot[4] = val2, ...
    //
    // For a function with N pairs, total slots = 1 + 2*N.
    // Key at index i (0-based): slot[1 + 2*i]
    // Value at index i (0-based): slot[2 + 2*i]

    pub(super) fn copy_compact_slots_from_dynamic_base(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        source_base_slot: ValueId,
        slot_count: u32,
    ) -> ValueId {
        let result_ptr = self.alloc_aggregate(block_idx, slot_count);
        for slot in 0..slot_count {
            let slot_offset = self.emit_i64_const(block_idx, i64::from(slot));
            let source_slot = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: source_base_slot,
                    rhs: slot_offset,
                },
            );
            let value = self.load_at_dynamic_offset(block_idx, source_ptr, source_slot);
            self.store_at_offset(block_idx, result_ptr, slot, value);
        }
        result_ptr
    }

    pub(super) fn store_compact_aggregate_result(
        &mut self,
        block_idx: usize,
        rd: u8,
        source_ptr: ValueId,
        shape: super::AggregateShape,
    ) -> Result<(), TmirError> {
        self.store_reg_ptr(block_idx, rd, source_ptr)?;
        self.compact_state_slots.insert(
            rd,
            super::CompactStateSlot::pointer_backed_in_block(source_ptr, 0, block_idx),
        );
        if let Some(len) = shape.tracked_len() {
            self.const_set_sizes.insert(rd, len);
        } else {
            self.const_set_sizes.remove(&rd);
        }
        self.aggregate_shapes.insert(rd, shape);
        self.const_scalar_values.remove(&rd);
        Ok(())
    }

    pub(super) fn store_single_slot_compact_result(
        &mut self,
        block_idx: usize,
        rd: u8,
        value: ValueId,
        source_slot: super::CompactStateSlot,
        shape: super::AggregateShape,
    ) -> Result<(), TmirError> {
        self.store_reg_value(block_idx, rd, value)?;
        if let Some(len) = shape.tracked_len() {
            self.const_set_sizes.insert(rd, len);
        } else {
            self.const_set_sizes.remove(&rd);
        }
        self.compact_state_slots
            .insert(rd, source_slot.as_raw_slot());
        self.aggregate_shapes.insert(rd, shape);
        self.const_scalar_values.remove(&rd);
        Ok(())
    }

    fn store_compact_identity_result(
        &mut self,
        block_idx: usize,
        rd: u8,
        source_slot: super::CompactStateSlot,
        shape: super::AggregateShape,
    ) -> Result<(), TmirError> {
        let slot_count = shape.compact_slot_count().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "compact identity result requires fixed-width shape for r{rd}, got {shape:?}"
            ))
        })?;
        if slot_count == 1 {
            let value = self.load_at_offset(block_idx, source_slot.source_ptr, source_slot.offset);
            self.store_single_slot_compact_result(block_idx, rd, value, source_slot, shape)
        } else {
            let result_ptr = self.alloc_aggregate(block_idx, slot_count);
            for slot in 0..slot_count {
                let value = self.load_at_offset(
                    block_idx,
                    source_slot.source_ptr,
                    source_slot.offset + slot,
                );
                self.store_at_offset(block_idx, result_ptr, slot, value);
            }
            self.store_compact_aggregate_result(block_idx, rd, result_ptr, shape)
        }
    }

    fn compact_record_field_from_scalar_key(
        shape: &super::AggregateShape,
        key: i64,
        mode: super::RecordSelectorMode,
    ) -> Option<(tla_core::NameId, u32, Option<super::AggregateShape>)> {
        let super::AggregateShape::Record { fields } = shape else {
            return None;
        };

        let target_idx = match mode {
            super::RecordSelectorMode::FieldName => {
                let field = tla_core::NameId(u32::try_from(key).ok()?);
                fields.iter().position(|(name, _)| *name == field)
            }
            super::RecordSelectorMode::Positional => {
                let positional = if let Ok(idx) = usize::try_from(key) {
                    (idx < fields.len()).then_some(idx)
                } else {
                    None
                };
                positional.or_else(|| {
                    let field = tla_core::NameId(u32::try_from(key).ok()?);
                    fields.iter().position(|(name, _)| *name == field)
                })
            }
        }?;

        let mut compact_offset = 0_u32;
        for (_, field_shape) in &fields[..target_idx] {
            compact_offset =
                compact_offset.checked_add(field_shape.as_deref()?.compact_slot_count()?)?;
        }
        let (field_name, field_shape) = &fields[target_idx];
        Some((*field_name, compact_offset, field_shape.as_deref().cloned()))
    }

    fn compact_value_source_for_reg(
        &mut self,
        block_idx: usize,
        reg: u8,
        expected_shape: &super::AggregateShape,
    ) -> Result<super::CompactMaterializationResult, TmirError> {
        self.materialize_reg_as_compact_source(block_idx, reg, expected_shape)
    }

    fn fold_sum_operand_is_function_like(shape: Option<&super::AggregateShape>) -> bool {
        matches!(
            shape,
            Some(super::AggregateShape::Function { .. } | super::AggregateShape::StateValue) | None
        )
    }

    fn fold_sum_should_swap_operands(
        first_shape: Option<&super::AggregateShape>,
        second_shape: Option<&super::AggregateShape>,
    ) -> bool {
        let first_is_set = first_shape.is_some_and(super::AggregateShape::is_finite_set_shape);
        let second_is_set = second_shape.is_some_and(super::AggregateShape::is_finite_set_shape);
        if second_is_set {
            return false;
        }
        if first_is_set && Self::fold_sum_operand_is_function_like(second_shape) {
            return true;
        }
        first_shape.is_none()
            && matches!(second_shape, Some(super::AggregateShape::Function { .. }))
    }

    fn contiguous_int_domain_lo(shape: Option<&super::AggregateShape>, len: u32) -> Option<i64> {
        super::dense_ordered_int_domain_lo(shape?, len)
    }

    fn resolve_fold_sum_set_shape(
        set_reg: u8,
        set_shape: Option<&super::AggregateShape>,
        func_shape: Option<&super::AggregateShape>,
    ) -> Result<Option<super::AggregateShape>, TmirError> {
        if let Some(shape) = set_shape {
            if !shape.is_finite_set_shape() {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "FoldFunctionOnSetSum: set argument r{set_reg} must be a tracked finite set, got {shape:?}"
                )));
            }
        }

        let function_domain_shape =
            func_shape.and_then(super::AggregateShape::function_domain_shape);
        match (set_shape, function_domain_shape.as_ref()) {
            (Some(set_shape), Some(function_domain_shape)) => {
                if let (
                    super::AggregateShape::Interval {
                        lo: set_lo,
                        hi: set_hi,
                    },
                    super::AggregateShape::Interval {
                        lo: domain_lo,
                        hi: domain_hi,
                    },
                ) = (set_shape, function_domain_shape)
                {
                    let set_is_empty = *set_hi < *set_lo;
                    if !set_is_empty && (*set_lo < *domain_lo || *set_hi > *domain_hi) {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "FoldFunctionOnSetSum: set argument r{set_reg} is incompatible with function domain: set={set_shape:?}, domain={function_domain_shape:?}"
                        )));
                    }
                    return Ok(Some(set_shape.clone()));
                }

                super::merge_compatible_shapes(Some(set_shape), Some(function_domain_shape))
                    .ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "FoldFunctionOnSetSum: set argument r{set_reg} is incompatible with function domain: set={set_shape:?}, domain={function_domain_shape:?}"
                        ))
                    })
                    .map(Some)
            }
            (Some(set_shape), None) => Ok(Some(set_shape.clone())),
            (None, Some(function_domain_shape)) => Ok(Some(function_domain_shape.clone())),
            (None, None) => Ok(None),
        }
    }

    /// Lower FoldFunctionOnSet(+, 0, f, S): sum `f[x]` for every `x` in `S`.
    ///
    /// This builtin is deliberately narrow: TIR only emits it for the
    /// recognized `FoldFunctionOnSet(+, 0, f, S)` shape, and this lowering
    /// uses tracked finite shapes when they are available. Generic user
    /// operators such as `Sum(f, S)` may lower this builtin from inside an
    /// arity-positive callee where formal parameter shapes are unknown; those
    /// loops still lower with dynamic lengths and are marked unbounded.
    pub(super) fn lower_fold_function_on_set_sum(
        &mut self,
        block_idx: usize,
        rd: u8,
        mut func_reg: u8,
        mut set_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        let first_shape = self.aggregate_shapes.get(&func_reg).cloned();
        let second_shape = self.aggregate_shapes.get(&set_reg).cloned();
        let swapped_set_first =
            Self::fold_sum_should_swap_operands(first_shape.as_ref(), second_shape.as_ref());
        if swapped_set_first {
            std::mem::swap(&mut func_reg, &mut set_reg);
        }

        let set_shape = self.aggregate_shapes.get(&set_reg).cloned();
        let func_shape = self.aggregate_shapes.get(&func_reg).cloned();
        let resolved_set_shape =
            Self::resolve_fold_sum_set_shape(set_reg, set_shape.as_ref(), func_shape.as_ref())?;
        let set_exact_len = resolved_set_shape
            .as_ref()
            .and_then(super::AggregateShape::tracked_len);
        if let Some(shape) = resolved_set_shape.clone() {
            if let Some(len) = shape.tracked_len().or_else(|| shape.finite_set_len_bound()) {
                self.const_set_sizes.insert(set_reg, len);
            } else {
                self.const_set_sizes.remove(&set_reg);
            }
            self.aggregate_shapes.insert(set_reg, shape);
        } else {
            self.const_set_sizes.remove(&set_reg);
        }

        let value = match &func_shape {
            Some(super::AggregateShape::Function { value, .. }) => value.clone(),
            Some(super::AggregateShape::StateValue) | None => {
                let value = Some(Box::new(super::AggregateShape::Scalar(
                    super::ScalarShape::Int,
                )));
                if let Some(len) = set_exact_len {
                    self.const_set_sizes.insert(func_reg, len);
                    self.aggregate_shapes.insert(
                        func_reg,
                        super::AggregateShape::Function {
                            len,
                            domain_lo: None,
                            value: value.clone(),
                        },
                    );
                } else {
                    self.const_set_sizes.remove(&func_reg);
                    self.aggregate_shapes.remove(&func_reg);
                }
                value
            }
            Some(other) => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "FoldFunctionOnSetSum: first argument r{func_reg} must be a tracked finite function, got {other:?}"
                )));
            }
        };
        if let Some(value_shape) = value.as_deref() {
            if !value_shape.is_numeric_scalar_shape() {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "FoldFunctionOnSetSum: function values must be Int, got {value_shape:?}"
                )));
            }
        }

        let func_ptr = self.load_reg_as_ptr_or_materialize_raw_compact(
            block_idx,
            func_reg,
            "FoldFunctionOnSetSum function",
        )?;
        let set_ptr = self.load_reg_as_ptr_or_materialize_raw_compact(
            block_idx,
            set_reg,
            "FoldFunctionOnSetSum set",
        )?;
        let set_len = self.load_at_offset(block_idx, set_ptr, 0);
        let pair_count = self.load_at_offset(block_idx, func_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);

        let set_idx_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: set_idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let func_idx_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: func_idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let acc_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: acc_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let set_header = self.new_aux_block("fold_sum_set_header");
        let set_body = self.new_aux_block("fold_sum_set_body");
        let func_header = self.new_aux_block("fold_sum_func_header");
        let func_body = self.new_aux_block("fold_sum_func_body");
        let func_inc = self.new_aux_block("fold_sum_func_inc");
        let func_found = self.new_aux_block("fold_sum_func_found");
        let add_overflow = self.new_aux_block("fold_sum_overflow");
        let add_ok = self.new_aux_block("fold_sum_add_ok");
        let func_missing = self.new_aux_block("fold_sum_missing");
        let done = self.new_aux_block("fold_sum_done");

        let set_header_id = self.block_id_of(set_header);
        let set_body_id = self.block_id_of(set_body);
        let func_header_id = self.block_id_of(func_header);
        let func_body_id = self.block_id_of(func_body);
        let func_inc_id = self.block_id_of(func_inc);
        let func_found_id = self.block_id_of(func_found);
        let add_overflow_id = self.block_id_of(add_overflow);
        let add_ok_id = self.block_id_of(add_ok);
        let func_missing_id = self.block_id_of(func_missing);
        let done_id = self.block_id_of(done);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: set_header_id,
                args: vec![],
            }),
        );

        let set_idx = self.emit_with_result(
            set_header,
            Inst::Load {
                ty: Ty::I64,
                ptr: set_idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let set_in_bounds = self.emit_with_result(
            set_header,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: set_idx,
                rhs: set_len,
            },
        );
        self.emit(
            set_header,
            InstrNode::new(Inst::CondBr {
                cond: set_in_bounds,
                then_target: set_body_id,
                then_args: vec![],
                else_target: done_id,
                else_args: vec![],
            }),
        );
        if !self.annotate_loop_bound(set_header, set_reg) {
            self.mark_unbounded_loop();
        }

        let one = self.emit_i64_const(set_body, 1);
        let set_idx_for_load = self.emit_with_result(
            set_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: set_idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let set_slot = self.emit_with_result(
            set_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: set_idx_for_load,
                rhs: one,
            },
        );
        let set_elem = self.load_at_dynamic_offset(set_body, set_ptr, set_slot);
        let zero_for_func_idx = self.emit_i64_const(set_body, 0);
        self.emit(
            set_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: func_idx_alloca,
                value: zero_for_func_idx,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            set_body,
            InstrNode::new(Inst::Br {
                target: func_header_id,
                args: vec![],
            }),
        );

        let func_idx = self.emit_with_result(
            func_header,
            Inst::Load {
                ty: Ty::I64,
                ptr: func_idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let func_in_bounds = self.emit_with_result(
            func_header,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: func_idx,
                rhs: pair_count,
            },
        );
        self.emit(
            func_header,
            InstrNode::new(Inst::CondBr {
                cond: func_in_bounds,
                then_target: func_body_id,
                then_args: vec![],
                else_target: func_missing_id,
                else_args: vec![],
            }),
        );
        if !self.annotate_loop_bound(func_header, func_reg) {
            self.mark_unbounded_loop();
        }

        let two = self.emit_i64_const(func_body, 2);
        let one_for_key = self.emit_i64_const(func_body, 1);
        let func_idx_for_key = self.emit_with_result(
            func_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: func_idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let key_offset = self.emit_with_result(
            func_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: func_idx_for_key,
                rhs: two,
            },
        );
        let key_slot = self.emit_with_result(
            func_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: key_offset,
                rhs: one_for_key,
            },
        );
        let key = self.load_at_dynamic_offset(func_body, func_ptr, key_slot);
        let key_matches = self.emit_with_result(
            func_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: key,
                rhs: set_elem,
            },
        );
        self.emit(
            func_body,
            InstrNode::new(Inst::CondBr {
                cond: key_matches,
                then_target: func_found_id,
                then_args: vec![],
                else_target: func_inc_id,
                else_args: vec![],
            }),
        );

        let func_idx_for_inc = self.emit_with_result(
            func_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: func_idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one_for_inc = self.emit_i64_const(func_inc, 1);
        let next_func_idx = self.emit_with_result(
            func_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: func_idx_for_inc,
                rhs: one_for_inc,
            },
        );
        self.emit(
            func_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: func_idx_alloca,
                value: next_func_idx,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            func_inc,
            InstrNode::new(Inst::Br {
                target: func_header_id,
                args: vec![],
            }),
        );

        let two_for_value = self.emit_i64_const(func_found, 2);
        let func_idx_for_value = self.emit_with_result(
            func_found,
            Inst::Load {
                ty: Ty::I64,
                ptr: func_idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let value_offset = self.emit_with_result(
            func_found,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: func_idx_for_value,
                rhs: two_for_value,
            },
        );
        let value_slot = self.emit_with_result(
            func_found,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: value_offset,
                rhs: two_for_value,
            },
        );
        let func_value = self.load_at_dynamic_offset(func_found, func_ptr, value_slot);
        let acc = self.emit_with_result(
            func_found,
            Inst::Load {
                ty: Ty::I64,
                ptr: acc_alloca,
                align: None,
                volatile: false,
            },
        );
        let add_result = self.alloc_value();
        let overflow_flag = self.alloc_value();
        self.emit(
            func_found,
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: Ty::I64,
                lhs: acc,
                rhs: func_value,
            })
            .with_result(add_result)
            .with_result(overflow_flag),
        );
        self.emit(
            func_found,
            InstrNode::new(Inst::CondBr {
                cond: overflow_flag,
                then_target: add_overflow_id,
                then_args: vec![],
                else_target: add_ok_id,
                else_args: vec![],
            }),
        );

        self.emit_runtime_error_and_return(add_overflow, JitRuntimeErrorKind::ArithmeticOverflow);
        self.emit_runtime_error_and_return(func_missing, JitRuntimeErrorKind::TypeMismatch);

        self.emit(
            add_ok,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: acc_alloca,
                value: add_result,
                align: None,
                volatile: false,
            }),
        );
        let set_idx_for_inc = self.emit_with_result(
            add_ok,
            Inst::Load {
                ty: Ty::I64,
                ptr: set_idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one_for_set_inc = self.emit_i64_const(add_ok, 1);
        let next_set_idx = self.emit_with_result(
            add_ok,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: set_idx_for_inc,
                rhs: one_for_set_inc,
            },
        );
        self.emit(
            add_ok,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: set_idx_alloca,
                value: next_set_idx,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            add_ok,
            InstrNode::new(Inst::Br {
                target: set_header_id,
                args: vec![],
            }),
        );

        let result = self.emit_with_result(
            done,
            Inst::Load {
                ty: Ty::I64,
                ptr: acc_alloca,
                align: None,
                volatile: false,
            },
        );
        self.store_reg_value(done, rd, result)?;
        self.compact_state_slots.remove(&rd);
        self.aggregate_shapes
            .insert(rd, super::AggregateShape::Scalar(super::ScalarShape::Int));
        self.const_set_sizes.remove(&rd);
        self.const_scalar_values.remove(&rd);

        Ok(Some(done))
    }

    /// Lower FuncApply { rd, func, arg }: function application f[x].
    ///
    /// Linear scan: for each key in the function, compare with arg.
    /// If found, return the corresponding value. If not found, runtime error.
    ///
    /// CFG:
    ///   entry -> header
    ///   header -> body (if i < len) | not_found (if i >= len)
    ///   body -> found (if key == arg) | inc (if key != arg)
    ///   inc -> header
    ///   found -> merge (rd = value)
    ///   not_found -> runtime_error
    pub(super) fn lower_func_apply(
        &mut self,
        block_idx: usize,
        rd: u8,
        func_reg: u8,
        arg_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let Some(path_raw) = self.scalar_of(arg_reg) {
            let selector_mode = self.scalar_record_selector_mode(arg_reg);
            if let (Some(source_slot), Some(record_shape)) = (
                self.compact_state_slot_for_use(block_idx, func_reg)?,
                self.aggregate_shapes.get(&func_reg).cloned(),
            ) {
                if let Some((_field_name, field_offset, field_shape)) =
                    Self::compact_record_field_from_scalar_key(
                        &record_shape,
                        path_raw,
                        selector_mode,
                    )
                {
                    let Some(field_shape) = field_shape else {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "FuncApply: compact record field r{func_reg}[{path_raw}] has no tracked shape"
                        )));
                    };
                    let field_stride = field_shape.compact_slot_count().ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "FuncApply: compact record field r{func_reg}[{path_raw}] requires fixed-width shape, got {field_shape:?}"
                        ))
                    })?;
                    if field_stride == 1 {
                        let result_val = self.load_at_offset(
                            block_idx,
                            source_slot.source_ptr,
                            source_slot.offset + field_offset,
                        );
                        self.store_single_slot_compact_result(
                            block_idx,
                            rd,
                            result_val,
                            super::CompactStateSlot::raw(
                                source_slot.source_ptr,
                                source_slot.offset + field_offset,
                            ),
                            field_shape,
                        )?;
                    } else {
                        let source_base = self.emit_i64_const(
                            block_idx,
                            i64::from(source_slot.offset + field_offset),
                        );
                        let result_ptr = self.copy_compact_slots_from_dynamic_base(
                            block_idx,
                            source_slot.source_ptr,
                            source_base,
                            field_stride,
                        );
                        self.store_compact_aggregate_result(
                            block_idx,
                            rd,
                            result_ptr,
                            field_shape,
                        )?;
                    }
                    return Ok(Some(block_idx));
                }
            }

            if let Some((_field_name, field_idx, field_shape)) = self
                .aggregate_shapes
                .get(&func_reg)
                .and_then(|shape| shape.record_field_from_scalar_key(path_raw, selector_mode))
            {
                self.reject_raw_compact_pointer_fallback(func_reg, "FuncApply")?;
                let rec_ptr = self.load_reg_as_ptr(block_idx, func_reg)?;
                let result_val = self.load_at_offset(block_idx, rec_ptr, field_idx);
                self.store_reg_value(block_idx, rd, result_val)?;
                self.compact_state_slots.remove(&rd);
                if let Some(shape) = field_shape {
                    if let Some(len) = shape.tracked_len() {
                        self.const_set_sizes.insert(rd, len);
                    } else {
                        self.const_set_sizes.remove(&rd);
                    }
                    self.aggregate_shapes.insert(rd, shape);
                } else {
                    self.aggregate_shapes.remove(&rd);
                    self.const_set_sizes.remove(&rd);
                }
                self.const_scalar_values.remove(&rd);
                return Ok(Some(block_idx));
            }
        }

        if let (
            Some(source_slot),
            Some(super::AggregateShape::Function {
                len,
                domain_lo: Some(domain_lo),
                value,
            }),
        ) = (
            self.compact_state_slot_for_use(block_idx, func_reg)?,
            self.aggregate_shapes.get(&func_reg).cloned(),
        ) {
            let value_shape = value.as_deref().cloned();
            let value_stride = value_shape
                .as_ref()
                .and_then(super::AggregateShape::compact_slot_count)
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "FuncApply: compact function r{func_reg} requires fixed-width value shape, got {value_shape:?}"
                    ))
                })?;

            let arg_val = self.load_reg(block_idx, arg_reg)?;
            let lo_val = self.emit_i64_const(block_idx, domain_lo);
            let hi_val = self.emit_i64_const(block_idx, domain_lo + i64::from(len) - 1);
            let ge_lo = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    lhs: arg_val,
                    rhs: lo_val,
                },
            );
            let check_hi_blk = self.new_aux_block("compact_fapply_check_hi");
            let found_blk = self.new_aux_block("compact_fapply_found");
            let not_found_blk = self.new_aux_block("compact_fapply_not_found");
            let merge_blk = self.new_aux_block("compact_fapply_merge");
            let check_hi_id = self.block_id_of(check_hi_blk);
            let found_id = self.block_id_of(found_blk);
            let not_found_id = self.block_id_of(not_found_blk);
            let merge_id = self.block_id_of(merge_blk);
            self.emit(
                block_idx,
                InstrNode::new(Inst::CondBr {
                    cond: ge_lo,
                    then_target: check_hi_id,
                    then_args: vec![],
                    else_target: not_found_id,
                    else_args: vec![],
                }),
            );

            let le_hi = self.emit_with_result(
                check_hi_blk,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: arg_val,
                    rhs: hi_val,
                },
            );
            self.emit(
                check_hi_blk,
                InstrNode::new(Inst::CondBr {
                    cond: le_hi,
                    then_target: found_id,
                    then_args: vec![],
                    else_target: not_found_id,
                    else_args: vec![],
                }),
            );

            let rel_idx = self.emit_with_result(
                found_blk,
                Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: arg_val,
                    rhs: lo_val,
                },
            );
            let base = self.emit_i64_const(found_blk, i64::from(source_slot.offset));
            let value_slot = if value_stride == 1 {
                self.emit_with_result(
                    found_blk,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: base,
                        rhs: rel_idx,
                    },
                )
            } else {
                let stride = self.emit_i64_const(found_blk, i64::from(value_stride));
                let offset = self.emit_with_result(
                    found_blk,
                    Inst::BinOp {
                        op: BinOp::Mul,
                        ty: Ty::I64,
                        lhs: rel_idx,
                        rhs: stride,
                    },
                );
                self.emit_with_result(
                    found_blk,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: base,
                        rhs: offset,
                    },
                )
            };
            if value_stride == 1 {
                let result_val =
                    self.load_at_dynamic_offset(found_blk, source_slot.source_ptr, value_slot);
                if let Some(shape) = value_shape.clone() {
                    if matches!(&shape, super::AggregateShape::Scalar(_)) {
                        let result_ptr = self.alloc_aggregate(found_blk, 1);
                        self.store_at_offset(found_blk, result_ptr, 0, result_val);
                        self.store_single_slot_compact_result(
                            found_blk,
                            rd,
                            result_val,
                            super::CompactStateSlot::raw(result_ptr, 0),
                            shape,
                        )?;
                    } else {
                        let result_ptr = self.copy_compact_slots_from_dynamic_base(
                            found_blk,
                            source_slot.source_ptr,
                            value_slot,
                            value_stride,
                        );
                        let stored_val = self.load_at_offset(found_blk, result_ptr, 0);
                        self.store_single_slot_compact_result(
                            found_blk,
                            rd,
                            stored_val,
                            super::CompactStateSlot::raw(result_ptr, 0),
                            shape,
                        )?;
                    }
                } else {
                    self.store_reg_value(found_blk, rd, result_val)?;
                    self.aggregate_shapes.remove(&rd);
                    self.const_set_sizes.remove(&rd);
                    self.compact_state_slots.remove(&rd);
                    self.const_scalar_values.remove(&rd);
                }
            } else {
                let result_ptr = self.copy_compact_slots_from_dynamic_base(
                    found_blk,
                    source_slot.source_ptr,
                    value_slot,
                    value_stride,
                );
                if let Some(shape) = value_shape.clone() {
                    self.store_compact_aggregate_result(found_blk, rd, result_ptr, shape)?;
                } else {
                    self.store_reg_ptr(found_blk, rd, result_ptr)?;
                    self.compact_state_slots.insert(
                        rd,
                        super::CompactStateSlot::pointer_backed_in_block(result_ptr, 0, found_blk),
                    );
                    self.aggregate_shapes.remove(&rd);
                    self.const_set_sizes.remove(&rd);
                    self.const_scalar_values.remove(&rd);
                }
            }
            self.emit(
                found_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );
            self.emit_runtime_error_and_return(not_found_blk, JitRuntimeErrorKind::TypeMismatch);

            return Ok(Some(merge_blk));
        }

        if let Some(super::AggregateShape::Sequence { extent, element }) =
            self.aggregate_shapes.get(&func_reg).cloned()
        {
            let seq_shape = super::AggregateShape::Sequence {
                extent,
                element: element.clone(),
            };
            let seq_capacity = extent.capacity();
            let element_shape = element.as_deref().cloned();
            let element_stride = element_shape
                .as_ref()
                .and_then(super::AggregateShape::compact_slot_count)
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "FuncApply: compact sequence r{func_reg} requires fixed-width element shape, got {element_shape:?}"
                    ))
                })?;
            let (block_idx, source_slot) =
                if let Some(source_slot) = self.compact_state_slot_for_use(block_idx, func_reg)? {
                    (block_idx, source_slot)
                } else {
                    let source =
                        self.materialize_reg_as_compact_source(block_idx, func_reg, &seq_shape)?;
                    (source.block_idx, source.slot)
                };

            let arg_val = self.load_reg(block_idx, arg_reg)?;
            let seq_len =
                self.load_at_offset(block_idx, source_slot.source_ptr, source_slot.offset);
            let one = self.emit_i64_const(block_idx, 1);
            let ge_one = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    lhs: arg_val,
                    rhs: one,
                },
            );
            let check_capacity_blk = self.new_aux_block("compact_seq_apply_check_capacity");
            let check_hi_blk = self.new_aux_block("compact_seq_apply_check_hi");
            let found_blk = self.new_aux_block("compact_seq_apply_found");
            let not_found_blk = self.new_aux_block("compact_seq_apply_not_found");
            let merge_blk = self.new_aux_block("compact_seq_apply_merge");
            let check_capacity_id = self.block_id_of(check_capacity_blk);
            let check_hi_id = self.block_id_of(check_hi_blk);
            let found_id = self.block_id_of(found_blk);
            let not_found_id = self.block_id_of(not_found_blk);
            let merge_id = self.block_id_of(merge_blk);
            self.emit(
                block_idx,
                InstrNode::new(Inst::CondBr {
                    cond: ge_one,
                    then_target: check_capacity_id,
                    then_args: vec![],
                    else_target: not_found_id,
                    else_args: vec![],
                }),
            );

            let capacity_val = self.emit_i64_const(check_capacity_blk, i64::from(seq_capacity));
            let within_capacity = self.emit_with_result(
                check_capacity_blk,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: seq_len,
                    rhs: capacity_val,
                },
            );
            self.emit(
                check_capacity_blk,
                InstrNode::new(Inst::CondBr {
                    cond: within_capacity,
                    then_target: check_hi_id,
                    then_args: vec![],
                    else_target: not_found_id,
                    else_args: vec![],
                }),
            );

            let le_len = self.emit_with_result(
                check_hi_blk,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: arg_val,
                    rhs: seq_len,
                },
            );
            self.emit(
                check_hi_blk,
                InstrNode::new(Inst::CondBr {
                    cond: le_len,
                    then_target: found_id,
                    then_args: vec![],
                    else_target: not_found_id,
                    else_args: vec![],
                }),
            );

            let rel_idx = self.emit_with_result(
                found_blk,
                Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: arg_val,
                    rhs: one,
                },
            );
            let first_elem_slot = source_slot.offset.checked_add(1).ok_or_else(|| {
                TmirError::UnsupportedOpcode(
                    "FuncApply: compact sequence first element slot overflows".to_owned(),
                )
            })?;
            let first_elem = self.emit_i64_const(found_blk, i64::from(first_elem_slot));
            let elem_slot = if element_stride == 1 {
                self.emit_with_result(
                    found_blk,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: first_elem,
                        rhs: rel_idx,
                    },
                )
            } else {
                let stride = self.emit_i64_const(found_blk, i64::from(element_stride));
                let offset = self.emit_with_result(
                    found_blk,
                    Inst::BinOp {
                        op: BinOp::Mul,
                        ty: Ty::I64,
                        lhs: rel_idx,
                        rhs: stride,
                    },
                );
                self.emit_with_result(
                    found_blk,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: first_elem,
                        rhs: offset,
                    },
                )
            };
            if element_stride == 1 {
                let result_val =
                    self.load_at_dynamic_offset(found_blk, source_slot.source_ptr, elem_slot);
                if let Some(shape) = element_shape {
                    if matches!(&shape, super::AggregateShape::Scalar(_)) {
                        let result_ptr = self.alloc_aggregate(found_blk, 1);
                        self.store_at_offset(found_blk, result_ptr, 0, result_val);
                        self.store_single_slot_compact_result(
                            found_blk,
                            rd,
                            result_val,
                            super::CompactStateSlot::raw(result_ptr, 0),
                            shape,
                        )?;
                    } else {
                        let result_ptr = self.copy_compact_slots_from_dynamic_base(
                            found_blk,
                            source_slot.source_ptr,
                            elem_slot,
                            element_stride,
                        );
                        let stored_val = self.load_at_offset(found_blk, result_ptr, 0);
                        self.store_single_slot_compact_result(
                            found_blk,
                            rd,
                            stored_val,
                            super::CompactStateSlot::raw(result_ptr, 0),
                            shape,
                        )?;
                    }
                } else {
                    self.store_reg_value(found_blk, rd, result_val)?;
                    self.aggregate_shapes.remove(&rd);
                    self.const_set_sizes.remove(&rd);
                    self.compact_state_slots.remove(&rd);
                    self.const_scalar_values.remove(&rd);
                }
            } else {
                let result_ptr = self.copy_compact_slots_from_dynamic_base(
                    found_blk,
                    source_slot.source_ptr,
                    elem_slot,
                    element_stride,
                );
                if let Some(shape) = element_shape {
                    self.store_compact_aggregate_result(found_blk, rd, result_ptr, shape)?;
                } else {
                    self.store_reg_ptr(found_blk, rd, result_ptr)?;
                    self.compact_state_slots.insert(
                        rd,
                        super::CompactStateSlot::pointer_backed_in_block(result_ptr, 0, found_blk),
                    );
                    self.aggregate_shapes.remove(&rd);
                    self.const_set_sizes.remove(&rd);
                    self.const_scalar_values.remove(&rd);
                }
            }
            self.emit(
                found_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );
            self.emit_runtime_error_and_return(not_found_blk, JitRuntimeErrorKind::TypeMismatch);

            return Ok(Some(merge_blk));
        }

        self.reject_raw_compact_pointer_fallback(func_reg, "FuncApply")?;
        let arg_val = self.load_reg(block_idx, arg_reg)?;
        let func_ptr = self.load_reg_as_ptr(block_idx, func_reg)?;
        let pair_count = self.load_at_offset(block_idx, func_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let two = self.emit_i64_const(block_idx, 2);

        let idx_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let loop_header = self.new_aux_block("fapply_header");
        let loop_body = self.new_aux_block("fapply_body");
        let loop_inc = self.new_aux_block("fapply_inc");
        let found_blk = self.new_aux_block("fapply_found");
        let not_found_blk = self.new_aux_block("fapply_not_found");
        let merge_blk = self.new_aux_block("fapply_merge");

        let header_id = self.block_id_of(loop_header);
        let body_id = self.block_id_of(loop_body);
        let inc_id = self.block_id_of(loop_inc);
        let found_id = self.block_id_of(found_blk);
        let not_found_id = self.block_id_of(not_found_blk);
        let merge_id = self.block_id_of(merge_blk);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

        // Header: i < pair_count?
        let cur_idx = self.emit_with_result(
            loop_header,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp = self.emit_with_result(
            loop_header,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: cur_idx,
                rhs: pair_count,
            },
        );
        self.emit(
            loop_header,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: body_id,
                then_args: vec![],
                else_target: not_found_id,
                else_args: vec![],
            }),
        );

        // Body: load key at slot[1 + 2*i], compare with arg
        let cur_idx2 = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let key_offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: cur_idx2,
                rhs: two,
            },
        );
        let key_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: key_offset,
                rhs: one,
            },
        );
        let key_val = self.load_at_dynamic_offset(loop_body, func_ptr, key_slot);
        let eq = self.emit_with_result(
            loop_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: key_val,
                rhs: arg_val,
            },
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::CondBr {
                cond: eq,
                then_target: found_id,
                then_args: vec![],
                else_target: inc_id,
                else_args: vec![],
            }),
        );

        // Increment: i++, goto header
        let cur_idx3 = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_idx = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cur_idx3,
                rhs: one,
            },
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_idx,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

        // Found: load value at slot[2 + 2*i], store to rd
        let cur_idx4 = self.emit_with_result(
            found_blk,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let val_offset = self.emit_with_result(
            found_blk,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: cur_idx4,
                rhs: two,
            },
        );
        let val_slot = self.emit_with_result(
            found_blk,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: val_offset,
                rhs: two,
            },
        );
        let result_val = self.load_at_dynamic_offset(found_blk, func_ptr, val_slot);
        self.store_reg_value(found_blk, rd, result_val)?;
        self.compact_state_slots.remove(&rd);
        self.emit(
            found_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        // Not found: runtime error (function applied to value not in domain)
        self.emit_runtime_error_and_return(not_found_blk, JitRuntimeErrorKind::TypeMismatch);

        if let Some(shape) = self
            .aggregate_shapes
            .get(&func_reg)
            .and_then(|shape| shape.function_value_shape())
        {
            if let Some(len) = shape.tracked_len() {
                self.const_set_sizes.insert(rd, len);
            } else {
                self.const_set_sizes.remove(&rd);
            }
            self.aggregate_shapes.insert(rd, shape);
        } else {
            self.aggregate_shapes.remove(&rd);
            self.const_set_sizes.remove(&rd);
        }
        self.const_scalar_values.remove(&rd);

        Ok(Some(merge_blk))
    }

    /// Lower Domain { rd, rs }: extract domain set from function.
    ///
    /// Reads the function aggregate at rs and builds a new set containing
    /// all keys. Function layout: [pair_count, k1, v1, k2, v2, ...].
    /// Result set layout: [pair_count, k1, k2, ...].
    pub(super) fn lower_domain(
        &mut self,
        block_idx: usize,
        rd: u8,
        rs: u8,
    ) -> Result<Option<usize>, TmirError> {
        let domain_shape = self
            .aggregate_shapes
            .get(&rs)
            .and_then(super::AggregateShape::function_domain_shape);
        if self
            .compact_state_slots
            .get(&rs)
            .copied()
            .is_some_and(super::CompactStateSlot::is_raw_compact_slot)
        {
            if let Some(super::AggregateShape::Function {
                len,
                domain_lo: Some(domain_lo),
                ..
            }) = self.aggregate_shapes.get(&rs).cloned()
            {
                let total_slots = len.checked_add(1).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "Domain: raw compact function r{rs} domain slot count overflows"
                    ))
                })?;
                let result_ptr = self.alloc_aggregate(block_idx, total_slots);
                let len_value = self.emit_i64_const(block_idx, i64::from(len));
                self.store_at_offset(block_idx, result_ptr, 0, len_value);

                for idx in 0..len {
                    let key = domain_lo.checked_add(i64::from(idx)).ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "Domain: raw compact function r{rs} domain key overflows"
                        ))
                    })?;
                    let key_value = self.emit_i64_const(block_idx, key);
                    self.store_at_offset(block_idx, result_ptr, idx + 1, key_value);
                }

                self.store_reg_ptr(block_idx, rd, result_ptr)?;
                self.compact_state_slots.remove(&rd);
                self.aggregate_shapes.insert(
                    rd,
                    domain_shape
                        .clone()
                        .unwrap_or(super::AggregateShape::Set { len, element: None }),
                );
                self.record_set_size(rd, len);
                self.const_scalar_values.remove(&rd);
                return Ok(Some(block_idx));
            }
        }

        let func_ptr = self.load_reg_as_ptr_or_materialize_raw_compact(block_idx, rs, "Domain")?;
        let pair_count = self.load_at_offset(block_idx, func_ptr, 0);

        let one = self.emit_i64_const(block_idx, 1);
        let two = self.emit_i64_const(block_idx, 2);
        let zero = self.emit_i64_const(block_idx, 0);

        // Allocate result set: pair_count + 1 slots (length header + keys)
        let total = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: pair_count,
                rhs: one,
            },
        );
        let result_ptr = if let Some(len) = self.const_set_sizes.get(&rs).copied() {
            self.alloc_aggregate(block_idx, len + 1)
        } else {
            self.alloc_dynamic_i64_slots(block_idx, total)
        };

        // Store length = pair_count
        self.store_at_offset(block_idx, result_ptr, 0, pair_count);

        // Loop: for i in 0..pair_count, result[i+1] = func[1 + 2*i]
        let i_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let loop_hdr = self.new_aux_block("domain_hdr");
        let loop_body = self.new_aux_block("domain_body");
        let loop_done = self.new_aux_block("domain_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Header: i < pair_count?
        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: pair_count,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: body_id,
                then_args: vec![],
                else_target: done_id,
                else_args: vec![],
            }),
        );

        // Body: result[i+1] = func[1 + 2*i]
        let i_val2 = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let key_offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: two,
            },
        );
        let key_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: key_offset,
                rhs: one,
            },
        );
        let key_val = self.load_at_dynamic_offset(loop_body, func_ptr, key_slot);

        let dst_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        self.store_at_dynamic_offset(loop_body, result_ptr, dst_slot, key_val);

        let next_i = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Done
        self.store_reg_ptr(loop_done, rd, result_ptr)?;
        self.compact_state_slots.remove(&rd);
        if let Some(n) = self.const_set_sizes.get(&rs).copied() {
            self.aggregate_shapes.insert(
                rd,
                domain_shape.unwrap_or(super::AggregateShape::Set {
                    len: n,
                    element: None,
                }),
            );
            self.record_set_size(rd, n);
        } else {
            self.aggregate_shapes.remove(&rd);
            self.const_set_sizes.remove(&rd);
        }
        self.const_scalar_values.remove(&rd);

        Ok(Some(loop_done))
    }

    /// Lower FuncExcept { rd, func, path, val }: [f EXCEPT ![x] = y].
    ///
    /// Creates a new function identical to func but with the value at key `path`
    /// replaced by `val`. If the key does not exist, the original function is
    /// returned unchanged (TLA+ semantics: EXCEPT on non-existent key is identity).
    ///
    /// Implementation: allocate new function aggregate of same size, copy all pairs,
    /// but when key matches `path`, store `val` instead of the original value.
    pub(super) fn lower_func_except(
        &mut self,
        block_idx: usize,
        rd: u8,
        func_reg: u8,
        path_reg: u8,
        val_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let Some(path_raw) = self.scalar_of(path_reg) {
            let selector_mode = self.scalar_record_selector_mode(path_reg);
            if let (Some(source_slot), Some(record_shape)) = (
                self.compact_state_slot_for_use(block_idx, func_reg)?,
                self.aggregate_shapes.get(&func_reg).cloned(),
            ) {
                if let Some((field_name, field_offset, field_shape)) =
                    Self::compact_record_field_from_scalar_key(
                        &record_shape,
                        path_raw,
                        selector_mode,
                    )
                {
                    let Some(field_shape) = field_shape else {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "FuncExcept: compact record field r{func_reg}[{path_raw}] has no tracked shape"
                        )));
                    };
                    let field_stride = field_shape.compact_slot_count().ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "FuncExcept: compact record field r{func_reg}[{path_raw}] requires fixed-width shape, got {field_shape:?}"
                        ))
                    })?;
                    let total_slots = record_shape.compact_slot_count().ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "FuncExcept: compact record r{func_reg} requires fixed-width shape, got {record_shape:?}"
                        ))
                    })?;
                    let result_ptr = self.alloc_aggregate(block_idx, total_slots);
                    let new_scalar_val = if field_stride == 1
                        && Self::is_single_slot_flat_aggregate_value(&field_shape)
                    {
                        Some(self.load_reg_as_compatible_single_slot_value(
                            block_idx,
                            val_reg,
                            &field_shape,
                            "FuncExcept compact record replacement",
                        )?)
                    } else {
                        None
                    };
                    let new_compact_source = if new_scalar_val.is_none() {
                        let materialized =
                            self.compact_value_source_for_reg(block_idx, val_reg, &field_shape)?;
                        let block_idx = materialized.block_idx;
                        Some((materialized.slot, block_idx))
                    } else {
                        None
                    };
                    let block_idx = new_compact_source
                        .map_or(block_idx, |(_, materialized_block)| materialized_block);
                    let new_compact_source =
                        new_compact_source.map(|(slot, _materialized_block)| slot);

                    for slot in 0..total_slots {
                        let old_val = self.load_at_offset(
                            block_idx,
                            source_slot.source_ptr,
                            source_slot.offset + slot,
                        );
                        let in_replaced_field =
                            slot >= field_offset && slot < field_offset + field_stride;
                        let value = if in_replaced_field {
                            if let Some(new_scalar_val) = new_scalar_val {
                                new_scalar_val
                            } else {
                                let new_compact_source = new_compact_source
                                    .expect("compact record replacement source was checked above");
                                self.load_at_offset(
                                    block_idx,
                                    new_compact_source.source_ptr,
                                    new_compact_source.offset + slot - field_offset,
                                )
                            }
                        } else {
                            old_val
                        };
                        self.store_at_offset(block_idx, result_ptr, slot, value);
                    }

                    let updated_shape = record_shape.with_record_field_shape(
                        field_name,
                        self.aggregate_shapes.get(&val_reg).cloned(),
                    );
                    if total_slots == 1 {
                        let first = self.load_at_offset(block_idx, result_ptr, 0);
                        self.store_single_slot_compact_result(
                            block_idx,
                            rd,
                            first,
                            super::CompactStateSlot::raw(result_ptr, 0),
                            updated_shape,
                        )?;
                    } else {
                        self.store_compact_aggregate_result(
                            block_idx,
                            rd,
                            result_ptr,
                            updated_shape,
                        )?;
                    }
                    return Ok(Some(block_idx));
                } else if matches!(&record_shape, super::AggregateShape::Record { .. }) {
                    self.store_compact_identity_result(block_idx, rd, source_slot, record_shape)?;
                    return Ok(Some(block_idx));
                }
            }

            if let Some(record_shape) = self.aggregate_shapes.get(&func_reg).cloned() {
                if let Some((field_name, field_idx, _)) =
                    record_shape.record_field_from_scalar_key(path_raw, selector_mode)
                {
                    self.reject_raw_compact_pointer_fallback(func_reg, "FuncExcept")?;
                    let rec_ptr = self.load_reg_as_ptr(block_idx, func_reg)?;
                    let new_val = self.load_reg(block_idx, val_reg)?;
                    let super::AggregateShape::Record { fields } = &record_shape else {
                        unreachable!("record_field returned Some only for record shapes");
                    };
                    let result_ptr = self.alloc_aggregate(
                        block_idx,
                        u32::try_from(fields.len()).expect("record field count must fit in u32"),
                    );
                    for slot in 0..fields.len() {
                        let slot_u32 =
                            u32::try_from(slot).expect("record field index must fit in u32");
                        let src_val = self.load_at_offset(block_idx, rec_ptr, slot_u32);
                        self.store_at_offset(
                            block_idx,
                            result_ptr,
                            slot_u32,
                            if slot_u32 == field_idx {
                                new_val
                            } else {
                                src_val
                            },
                        );
                    }
                    self.store_reg_ptr(block_idx, rd, result_ptr)?;
                    self.compact_state_slots.remove(&rd);
                    self.aggregate_shapes.insert(
                        rd,
                        record_shape.with_record_field_shape(
                            field_name,
                            self.aggregate_shapes.get(&val_reg).cloned(),
                        ),
                    );
                    self.const_set_sizes.remove(&rd);
                    self.const_scalar_values.remove(&rd);
                    return Ok(Some(block_idx));
                }
            }
        } else if let (Some(_source_slot), Some(super::AggregateShape::Record { .. })) = (
            self.compact_state_slots.get(&func_reg).copied(),
            self.aggregate_shapes.get(&func_reg).cloned(),
        ) {
            return Err(TmirError::UnsupportedOpcode(format!(
                "FuncExcept: dynamic compact record path r{path_reg} for r{func_reg} is not supported"
            )));
        }

        if let (
            Some(source_slot),
            Some(
                ref shape @ super::AggregateShape::Function {
                    len,
                    domain_lo: Some(domain_lo),
                    value: Some(ref value_shape),
                },
            ),
        ) = (
            self.compact_state_slot_for_use(block_idx, func_reg)?,
            self.aggregate_shapes.get(&func_reg).cloned(),
        ) {
            let value_stride = value_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "FuncExcept: compact function r{func_reg} requires fixed-width value shape, got {value_shape:?}"
                ))
            })?;
            let total_slots = len.checked_mul(value_stride).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "FuncExcept: compact function slot count overflows: {len} * {value_stride}"
                ))
            })?;

            if let Some(path_raw) = self.scalar_of(path_reg) {
                let replace_idx = path_raw
                    .checked_sub(domain_lo)
                    .and_then(|relative_key| u32::try_from(relative_key).ok());
                let Some(replace_idx) = replace_idx else {
                    self.store_compact_identity_result(block_idx, rd, source_slot, shape.clone())?;
                    return Ok(Some(block_idx));
                };
                if replace_idx >= len {
                    self.store_compact_identity_result(block_idx, rd, source_slot, shape.clone())?;
                    return Ok(Some(block_idx));
                }

                let (result_shape, replacement_shape, result_slots) = if len == 1 {
                    let replacement_shape = value_shape.as_ref().clone();
                    let replacement_slots = value_stride;
                    (
                        super::AggregateShape::Function {
                            len,
                            domain_lo: Some(domain_lo),
                            value: Some(Box::new(replacement_shape.clone())),
                        },
                        replacement_shape,
                        replacement_slots,
                    )
                } else {
                    (shape.clone(), value_shape.as_ref().clone(), total_slots)
                };
                let replacement_stride = replacement_shape.compact_slot_count().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "FuncExcept: compact function replacement requires fixed-width value shape, got {replacement_shape:?}"
                    ))
                })?;
                let replacement =
                    self.compact_value_source_for_reg(block_idx, val_reg, &replacement_shape)?;
                let block_idx = replacement.block_idx;
                let replacement_source = replacement.slot;
                let result_ptr = self.alloc_aggregate(block_idx, result_slots);
                if len > 1 {
                    for slot in 0..total_slots {
                        let old_val = self.load_at_offset(
                            block_idx,
                            source_slot.source_ptr,
                            source_slot.offset + slot,
                        );
                        self.store_at_offset(block_idx, result_ptr, slot, old_val);
                    }
                }
                let replace_base = replace_idx.checked_mul(replacement_stride).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "FuncExcept: compact function replacement slot overflows: {replace_idx} * {replacement_stride}"
                    ))
                })?;
                for value_offset in 0..replacement_stride {
                    let new_val = self.load_at_offset(
                        block_idx,
                        replacement_source.source_ptr,
                        replacement_source.offset + value_offset,
                    );
                    self.store_at_offset(
                        block_idx,
                        result_ptr,
                        replace_base + value_offset,
                        new_val,
                    );
                }
                if result_slots == 1 {
                    let first = self.load_at_offset(block_idx, result_ptr, 0);
                    self.store_single_slot_compact_result(
                        block_idx,
                        rd,
                        first,
                        super::CompactStateSlot::raw(result_ptr, 0),
                        result_shape,
                    )?;
                } else {
                    self.store_compact_aggregate_result(block_idx, rd, result_ptr, result_shape)?;
                }
                return Ok(Some(block_idx));
            }

            let result_ptr = self.alloc_aggregate(block_idx, total_slots);
            let path_val = self.load_reg(block_idx, path_reg)?;
            let new_scalar_val = if value_stride == 1
                && Self::is_single_slot_flat_aggregate_value(value_shape.as_ref())
            {
                Some(self.load_reg_as_compatible_single_slot_value(
                    block_idx,
                    val_reg,
                    value_shape,
                    "FuncExcept compact function replacement",
                )?)
            } else {
                None
            };
            let new_compact_source = if new_scalar_val.is_none() {
                let materialized =
                    self.compact_value_source_for_reg(block_idx, val_reg, value_shape)?;
                let block_idx = materialized.block_idx;
                Some((materialized.slot, block_idx))
            } else {
                None
            };
            let block_idx =
                new_compact_source.map_or(block_idx, |(_, materialized_block)| materialized_block);
            let new_compact_source = new_compact_source.map(|(slot, _materialized_block)| slot);

            for idx in 0..len {
                let key_val = self.emit_i64_const(block_idx, domain_lo + i64::from(idx));
                let key_match = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        lhs: path_val,
                        rhs: key_val,
                    },
                );
                for value_offset in 0..value_stride {
                    let source_offset = source_slot.offset + idx * value_stride + value_offset;
                    let src_ptr = self.emit_state_slot_ptr_at_slot(
                        block_idx,
                        source_slot.source_ptr,
                        source_offset,
                    );
                    let old_val = self.emit_with_result(
                        block_idx,
                        Inst::Load {
                            ty: Ty::I64,
                            ptr: src_ptr,
                            align: None,
                            volatile: false,
                        },
                    );
                    let new_val = if let Some(new_scalar_val) = new_scalar_val {
                        new_scalar_val
                    } else {
                        let new_compact_source = new_compact_source
                            .expect("multi-slot compact update source was checked above");
                        let new_ptr = self.emit_state_slot_ptr_at_slot(
                            block_idx,
                            new_compact_source.source_ptr,
                            new_compact_source.offset + value_offset,
                        );
                        self.emit_with_result(
                            block_idx,
                            Inst::Load {
                                ty: Ty::I64,
                                ptr: new_ptr,
                                align: None,
                                volatile: false,
                            },
                        )
                    };
                    let selected_val = self.emit_with_result(
                        block_idx,
                        Inst::Select {
                            ty: Ty::I64,
                            cond: key_match,
                            then_val: new_val,
                            else_val: old_val,
                        },
                    );
                    self.store_at_offset(
                        block_idx,
                        result_ptr,
                        idx * value_stride + value_offset,
                        selected_val,
                    );
                }
            }

            if total_slots == 1 {
                let first = self.load_at_offset(block_idx, result_ptr, 0);
                self.store_single_slot_compact_result(
                    block_idx,
                    rd,
                    first,
                    super::CompactStateSlot::raw(result_ptr, 0),
                    shape.clone(),
                )?;
            } else {
                self.store_compact_aggregate_result(block_idx, rd, result_ptr, shape.clone())?;
            }
            return Ok(Some(block_idx));
        }

        if let Some(super::AggregateShape::Sequence { extent, element }) =
            self.aggregate_shapes.get(&func_reg).cloned()
        {
            let seq_shape = super::AggregateShape::Sequence {
                extent,
                element: element.clone(),
            };
            let seq_capacity = extent.capacity();
            let Some(element_shape) = element.as_deref() else {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "FuncExcept: compact sequence r{func_reg} requires tracked element shape"
                )));
            };
            let element_stride = element_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "FuncExcept: compact sequence r{func_reg} requires fixed-width element shape, got {element_shape:?}"
                ))
            })?;
            let total_slots = seq_shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "FuncExcept: compact sequence r{func_reg} requires fixed-width shape, got {seq_shape:?}"
                ))
            })?;
            let source = self.materialize_reg_as_compact_source(block_idx, func_reg, &seq_shape)?;
            let block_idx = source.block_idx;
            let source_slot = source.slot;
            if let Some(path_raw) = self.scalar_of(path_reg) {
                let replace_idx = path_raw
                    .checked_sub(1)
                    .and_then(|relative_key| u32::try_from(relative_key).ok());
                if match replace_idx {
                    Some(idx) => idx >= seq_capacity,
                    None => true,
                } {
                    self.store_compact_identity_result(block_idx, rd, source_slot, seq_shape)?;
                    return Ok(Some(block_idx));
                }
            }
            let replacement =
                self.compact_value_source_for_reg(block_idx, val_reg, element_shape)?;
            let block_idx = replacement.block_idx;
            let replacement_source = replacement.slot;
            let result_ptr = self.alloc_aggregate(block_idx, total_slots);
            for slot in 0..total_slots {
                let old_val = self.load_at_offset(
                    block_idx,
                    source_slot.source_ptr,
                    source_slot.offset + slot,
                );
                self.store_at_offset(block_idx, result_ptr, slot, old_val);
            }

            let runtime_len =
                self.load_at_offset(block_idx, source_slot.source_ptr, source_slot.offset);
            let path_val = if let Some(path_raw) = self.scalar_of(path_reg) {
                self.emit_i64_const(block_idx, path_raw)
            } else {
                self.load_reg(block_idx, path_reg)?
            };
            let zero = self.emit_i64_const(block_idx, 0);
            let one = self.emit_i64_const(block_idx, 1);
            let capacity = self.emit_i64_const(block_idx, i64::from(seq_capacity));

            let len_nonnegative = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    lhs: runtime_len,
                    rhs: zero,
                },
            );

            let check_capacity_blk = self.new_aux_block("compact_seq_except_check_capacity");
            let check_path_lo_blk = self.new_aux_block("compact_seq_except_check_path_lo");
            let check_path_hi_blk = self.new_aux_block("compact_seq_except_check_path_hi");
            let update_blk = self.new_aux_block("compact_seq_except_update");
            let merge_blk = self.new_aux_block("compact_seq_except_merge");
            let check_capacity_id = self.block_id_of(check_capacity_blk);
            let check_path_lo_id = self.block_id_of(check_path_lo_blk);
            let check_path_hi_id = self.block_id_of(check_path_hi_blk);
            let update_id = self.block_id_of(update_blk);
            let merge_id = self.block_id_of(merge_blk);

            self.emit(
                block_idx,
                InstrNode::new(Inst::CondBr {
                    cond: len_nonnegative,
                    then_target: check_capacity_id,
                    then_args: vec![],
                    else_target: merge_id,
                    else_args: vec![],
                }),
            );

            let len_within_capacity = self.emit_with_result(
                check_capacity_blk,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: runtime_len,
                    rhs: capacity,
                },
            );
            self.emit(
                check_capacity_blk,
                InstrNode::new(Inst::CondBr {
                    cond: len_within_capacity,
                    then_target: check_path_lo_id,
                    then_args: vec![],
                    else_target: merge_id,
                    else_args: vec![],
                }),
            );

            let path_ge_one = self.emit_with_result(
                check_path_lo_blk,
                Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    lhs: path_val,
                    rhs: one,
                },
            );
            self.emit(
                check_path_lo_blk,
                InstrNode::new(Inst::CondBr {
                    cond: path_ge_one,
                    then_target: check_path_hi_id,
                    then_args: vec![],
                    else_target: merge_id,
                    else_args: vec![],
                }),
            );

            let path_le_len = self.emit_with_result(
                check_path_hi_blk,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: path_val,
                    rhs: runtime_len,
                },
            );
            self.emit(
                check_path_hi_blk,
                InstrNode::new(Inst::CondBr {
                    cond: path_le_len,
                    then_target: update_id,
                    then_args: vec![],
                    else_target: merge_id,
                    else_args: vec![],
                }),
            );

            let rel_idx = self.emit_with_result(
                update_blk,
                Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: path_val,
                    rhs: one,
                },
            );
            let first_elem = self.emit_i64_const(update_blk, 1);
            let elem_offset = if element_stride == 1 {
                rel_idx
            } else {
                let stride = self.emit_i64_const(update_blk, i64::from(element_stride));
                self.emit_with_result(
                    update_blk,
                    Inst::BinOp {
                        op: BinOp::Mul,
                        ty: Ty::I64,
                        lhs: rel_idx,
                        rhs: stride,
                    },
                )
            };
            let elem_base_slot = self.emit_with_result(
                update_blk,
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: first_elem,
                    rhs: elem_offset,
                },
            );
            for value_offset in 0..element_stride {
                let new_val = self.load_at_offset(
                    update_blk,
                    replacement_source.source_ptr,
                    replacement_source.offset + value_offset,
                );
                let target_slot = if value_offset == 0 {
                    elem_base_slot
                } else {
                    let offset = self.emit_i64_const(update_blk, i64::from(value_offset));
                    self.emit_with_result(
                        update_blk,
                        Inst::BinOp {
                            op: BinOp::Add,
                            ty: Ty::I64,
                            lhs: elem_base_slot,
                            rhs: offset,
                        },
                    )
                };
                self.store_at_dynamic_offset(update_blk, result_ptr, target_slot, new_val);
            }
            self.emit(
                update_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );

            self.store_compact_aggregate_result(merge_blk, rd, result_ptr, seq_shape)?;
            return Ok(Some(merge_blk));
        }

        self.reject_raw_compact_pointer_fallback(func_reg, "FuncExcept")?;
        let path_val = self.load_reg(block_idx, path_reg)?;
        let new_val = self.load_reg(block_idx, val_reg)?;
        let func_ptr = self.load_reg_as_ptr(block_idx, func_reg)?;
        let pair_count = self.load_at_offset(block_idx, func_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let two = self.emit_i64_const(block_idx, 2);

        // Allocate new function: 1 + 2*pair_count slots
        let pairs_x2 = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: pair_count,
                rhs: two,
            },
        );
        let total = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: pairs_x2,
                rhs: one,
            },
        );
        let result_ptr = if let Some(pair_count_u32) = self.const_set_sizes.get(&func_reg).copied()
        {
            self.alloc_aggregate(block_idx, 1 + (2 * pair_count_u32))
        } else {
            self.alloc_dynamic_i64_slots(block_idx, total)
        };

        // Store pair_count in new function
        self.store_at_offset(block_idx, result_ptr, 0, pair_count);

        // Loop: for i in 0..pair_count, copy key, conditionally replace value
        let i_alloca = self.emit_with_result(
            block_idx,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let loop_hdr = self.new_aux_block("fexcept_hdr");
        let loop_body = self.new_aux_block("fexcept_body");
        let loop_done = self.new_aux_block("fexcept_done");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let done_id = self.block_id_of(loop_done);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Header: i < pair_count?
        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: pair_count,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: body_id,
                then_args: vec![],
                else_target: done_id,
                else_args: vec![],
            }),
        );

        // Body: copy key, select value based on key match
        let i_val2 = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );

        // Source key slot: 1 + 2*i
        let src_key_offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: two,
            },
        );
        let src_key_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: src_key_offset,
                rhs: one,
            },
        );
        let key = self.load_at_dynamic_offset(loop_body, func_ptr, src_key_slot);

        // Source value slot: 2 + 2*i
        let src_val_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: src_key_offset,
                rhs: two,
            },
        );
        let orig_val = self.load_at_dynamic_offset(loop_body, func_ptr, src_val_slot);

        // Select: if key == path then new_val else orig_val
        let key_match = self.emit_with_result(
            loop_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: key,
                rhs: path_val,
            },
        );
        let selected_val = self.emit_with_result(
            loop_body,
            Inst::Select {
                ty: Ty::I64,
                cond: key_match,
                then_val: new_val,
                else_val: orig_val,
            },
        );

        // Store key and selected value in result
        self.store_at_dynamic_offset(loop_body, result_ptr, src_key_slot, key);
        self.store_at_dynamic_offset(loop_body, result_ptr, src_val_slot, selected_val);

        // Increment
        let next_i = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Done
        self.store_reg_ptr(loop_done, rd, result_ptr)?;
        self.compact_state_slots.remove(&rd);
        self.mark_flat_funcdef_pair_list(rd);
        if let Some(shape) = self.aggregate_shapes.get(&func_reg).cloned() {
            self.aggregate_shapes.insert(rd, shape);
        } else {
            self.aggregate_shapes.remove(&rd);
        }
        if let Some(n) = self.const_set_sizes.get(&func_reg).copied() {
            self.record_set_size(rd, n);
        } else {
            self.const_set_sizes.remove(&rd);
        }
        self.const_scalar_values.remove(&rd);

        Ok(Some(loop_done))
    }

    /// Lower FuncDefBegin: initialize function builder, iterate domain.
    ///
    /// Allocates a function aggregate sized for the domain, then iterates
    /// over domain elements. For each element, the body evaluates the
    /// mapping expression, and LoopNext stores the (key, value) pair.
    ///
    /// Function layout: [pair_count, key1, val1, key2, val2, ...]
    ///
    /// CFG produced:
    ///   current_block -> header
    ///   header -> body_block (if i < len) | exit_block (if i >= len)
    pub(super) fn lower_func_def_begin(
        &mut self,
        pc: usize,
        block: usize,
        rd: u8,
        r_binding: u8,
        r_domain: u8,
        loop_end: i32,
    ) -> Result<Option<usize>, TmirError> {
        let exit_pc = self.resolve_forward_target(pc, loop_end, "FuncDefBegin")?;
        let body_pc = pc + 1;
        let exit_block = self.block_index_for_pc(exit_pc)?;
        let body_block = self.block_index_for_pc(body_pc)?;

        // Load domain pointer and length.
        self.reject_compact_set_bitmask_powerset_iteration(r_domain, "FuncDefBegin")?;
        let binding_shape = self
            .aggregate_shapes
            .get(&r_domain)
            .and_then(super::binding_shape_from_domain);
        let domain_ptr =
            self.load_reg_as_ptr_or_materialize_raw_compact(block, r_domain, "FuncDefBegin")?;
        let domain_len = self.load_at_offset(block, domain_ptr, 0);

        let zero = self.emit_i64_const(block, 0);
        let one = self.emit_i64_const(block, 1);
        let two = self.emit_i64_const(block, 2);

        // Allocate function aggregate: 1 + 2*domain_len slots
        let pairs_x2 = self.emit_with_result(
            block,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: domain_len,
                rhs: two,
            },
        );
        let total = self.emit_with_result(
            block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: pairs_x2,
                rhs: one,
            },
        );
        let static_domain_capacity = self.const_set_sizes.get(&r_domain).copied().or_else(|| {
            self.aggregate_shapes
                .get(&r_domain)
                .and_then(super::AggregateShape::finite_set_len_bound)
        });
        let func_ptr = if let Some(domain_len_u32) = static_domain_capacity {
            self.alloc_aggregate(block, 1 + (2 * domain_len_u32))
        } else {
            self.alloc_dynamic_i64_slots(block, total)
        };

        // Store pair_count = domain_len
        self.store_at_offset(block, func_ptr, 0, domain_len);

        // Store function pointer in rd now (so LoopNext can access it).
        self.store_reg_ptr(block, rd, func_ptr)?;
        self.compact_state_slots.remove(&rd);
        self.mark_flat_funcdef_pair_list(rd);

        // Allocate index counter, initialize to 0.
        let idx_alloca = self.emit_with_result(
            block,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            block,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        // Create loop header block.
        let header_block = self.new_aux_block("funcdef_header");
        let header_id = self.block_id_of(header_block);
        let body_id = self.block_id_of(body_block);
        let exit_id = self.block_id_of(exit_block);

        // Branch to header.
        self.emit(
            block,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

        // Header: check i < domain_len.
        let cur_idx = self.emit_with_result(
            header_block,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let in_bounds = self.emit_with_result(
            header_block,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: cur_idx,
                rhs: domain_len,
            },
        );

        let load_block = self.new_aux_block("funcdef_load");
        let load_id = self.block_id_of(load_block);

        self.emit(
            header_block,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: load_id,
                then_args: vec![],
                else_target: exit_id,
                else_args: vec![],
            }),
        );

        // Load element: r_binding = domain[i+1] (skip length header).
        let cur_idx2 = self.emit_with_result(
            load_block,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot_idx = self.emit_with_result(
            load_block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cur_idx2,
                rhs: one,
            },
        );
        let elem = self.load_at_dynamic_offset(load_block, domain_ptr, slot_idx);
        self.store_reg_value(load_block, r_binding, elem)?;
        self.invalidate_reg_tracking(r_binding);
        if let Some(binding_shape) = binding_shape {
            self.aggregate_shapes.insert(r_binding, binding_shape);
        }

        // Also store the key into the function aggregate at slot[1 + 2*i].
        let func_ptr_reload = self.load_reg_as_ptr(load_block, rd)?;
        let key_offset = self.emit_with_result(
            load_block,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: cur_idx2,
                rhs: two,
            },
        );
        let key_slot = self.emit_with_result(
            load_block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: key_offset,
                rhs: one,
            },
        );
        self.store_at_dynamic_offset(load_block, func_ptr_reload, key_slot, elem);

        // Branch to the body block.
        self.emit(
            load_block,
            InstrNode::new(Inst::Br {
                target: body_id,
                args: vec![],
            }),
        );

        // Save loop state for LoopNext (use the shared builder-loop stack,
        // not quantifier_loops, because LoopNext does not carry rd or kind).
        self.loop_next_stack.push(LoopNextState {
            rd,
            kind: LoopNextKind::FuncDef,
            loop_state: QuantifierLoopState {
                idx_alloca,
                header_block,
                exit_block,
            },
            funcdef_capture: Some(super::FuncDefCaptureState {
                preheader_block: block,
                domain_len,
                static_domain_capacity,
            }),
        });

        // FuncDef's per-key body writes to a distinct slot (slot 2+2*i in
        // the function aggregate) and reads only from its own binding
        // register. Iterations are independent → mark the loop header as
        // a `tmir.parallel_map` candidate.
        self.annotate_parallel_map(header_block);

        // If the domain size is compile-time known, also emit
        // `tmir.bounded_loop(n)`. If not, mark the function as unbounded
        // so Terminates is suppressed.
        if !self.annotate_loop_bound(header_block, r_domain) {
            self.mark_unbounded_loop();
        }

        // The function-aggregate value lives in rd; its cardinality equals
        // the domain size.
        if let Some(&n) = self.const_set_sizes.get(&r_domain) {
            let domain_lo = Self::contiguous_int_domain_lo(self.aggregate_shapes.get(&r_domain), n);
            self.aggregate_shapes.insert(
                rd,
                super::AggregateShape::Function {
                    len: n,
                    domain_lo,
                    value: None,
                },
            );
            self.record_set_size(rd, n);
        } else {
            self.aggregate_shapes.remove(&rd);
            self.const_set_sizes.remove(&rd);
        }
        self.const_scalar_values.remove(&rd);

        // Body block is the next PC's block — return None to let lower_body
        // transition to it naturally.
        Ok(None)
    }

    pub(super) fn lower_loop_next(
        &mut self,
        _pc: usize,
        block: usize,
        r_binding: u8,
        r_body: u8,
    ) -> Result<Option<usize>, TmirError> {
        let state = self
            .loop_next_stack
            .pop()
            .ok_or_else(|| TmirError::Emission("LoopNext without matching Begin".to_owned()))?;

        match state.kind {
            LoopNextKind::FuncDef => {
                let capture = state.funcdef_capture.ok_or_else(|| {
                    TmirError::Emission("FuncDef LoopNext missing capture state".to_owned())
                })?;
                self.lower_loop_next_func_def(block, r_body, state.rd, state.loop_state, capture)
            }
            LoopNextKind::SetFilter => self.lower_loop_next_set_filter(
                block,
                r_binding,
                r_body,
                state.rd,
                state.loop_state,
            ),
        }
    }

    fn insert_preheader_with_result(&mut self, block_idx: usize, inst: Inst) -> ValueId {
        let result = self.alloc_value();
        let node = InstrNode::new(inst).with_result(result);
        let func = &mut self.module.functions[self.func_idx];
        let body = &mut func.blocks[block_idx].body;
        let insert_idx = body
            .iter()
            .rposition(|node| node.is_terminator())
            .unwrap_or(body.len());
        body.insert(insert_idx, node);
        result
    }

    fn alloc_funcdef_capture_backing(
        &mut self,
        capture_state: super::FuncDefCaptureState,
        value_slots: u32,
    ) -> Result<ValueId, TmirError> {
        let count = if let Some(domain_capacity) = capture_state.static_domain_capacity {
            let total_slots = domain_capacity.checked_mul(value_slots).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "FuncDef compact capture backing overflows: {domain_capacity} * {value_slots}"
                ))
            })?;
            self.insert_preheader_with_result(
                capture_state.preheader_block,
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(i128::from(total_slots)),
                },
            )
        } else {
            let value_slots = self.insert_preheader_with_result(
                capture_state.preheader_block,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(i128::from(value_slots)),
                },
            );
            let total_slots = self.insert_preheader_with_result(
                capture_state.preheader_block,
                Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: capture_state.domain_len,
                    rhs: value_slots,
                },
            );
            self.insert_preheader_with_result(
                capture_state.preheader_block,
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I64,
                    dst_ty: Ty::I32,
                    operand: total_slots,
                },
            )
        };

        Ok(self.insert_preheader_with_result(
            capture_state.preheader_block,
            Inst::Alloca {
                ty: Ty::I64,
                count: Some(count),
                align: None,
            },
        ))
    }

    /// Lower LoopNext for FuncDef: store body result as value, advance iterator.
    ///
    /// Stores the body result (r_body) as the value for the current key in the
    /// function aggregate, then increments the index and branches back to the header.
    fn lower_loop_next_func_def(
        &mut self,
        block: usize,
        r_body: u8,
        rd: u8,
        loop_state: QuantifierLoopState,
        capture_state: super::FuncDefCaptureState,
    ) -> Result<Option<usize>, TmirError> {
        let mut block = block;
        let body_shape = self.aggregate_shapes.get(&r_body).cloned();
        let body_val = if let Some(shape) = body_shape
            .as_ref()
            .filter(|shape| Self::is_compact_compound_aggregate(shape))
        {
            let materialized = self.materialize_reg_as_compact_source(block, r_body, shape)?;
            block = materialized.block_idx;
            let slot_count = shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "FuncDef LoopNext compact body r{r_body} requires fixed-width shape, got {shape:?}"
                ))
            })?;
            let cur_idx = self.emit_with_result(
                block,
                Inst::Load {
                    ty: Ty::I64,
                    ptr: loop_state.idx_alloca,
                    align: None,
                    volatile: false,
                },
            );
            let backing_ptr = self.alloc_funcdef_capture_backing(capture_state, slot_count)?;
            let slot_count_value = self.emit_i64_const(block, i64::from(slot_count));
            let capture_offset = self.emit_with_result(
                block,
                Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: cur_idx,
                    rhs: slot_count_value,
                },
            );
            let capture_offset_i32 = self.emit_with_result(
                block,
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I64,
                    dst_ty: Ty::I32,
                    operand: capture_offset,
                },
            );
            let capture_ptr = self.emit_with_result(
                block,
                Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: backing_ptr,
                    indices: vec![capture_offset_i32],
                },
            );
            for offset in 0..slot_count {
                let value = self.load_at_offset(
                    block,
                    materialized.slot.source_ptr,
                    materialized.slot.offset + offset,
                );
                self.store_at_offset(block, capture_ptr, offset, value);
            }
            self.ptr_to_i64(block, capture_ptr)
        } else {
            self.load_reg(block, r_body)?
        };
        let two = self.emit_i64_const(block, 2);
        let one = self.emit_i64_const(block, 1);

        // Store value at slot[2 + 2*i] in the function aggregate.
        let func_ptr = self.load_reg_as_ptr(block, rd)?;
        let cur_idx = self.emit_with_result(
            block,
            Inst::Load {
                ty: Ty::I64,
                ptr: loop_state.idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let val_offset = self.emit_with_result(
            block,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: cur_idx,
                rhs: two,
            },
        );
        let val_slot = self.emit_with_result(
            block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: val_offset,
                rhs: two,
            },
        );
        self.store_at_dynamic_offset(block, func_ptr, val_slot, body_val);
        if let Some(shape) = self.aggregate_shapes.get(&r_body).cloned() {
            if let Some(super::AggregateShape::Function { len, domain_lo, .. }) =
                self.aggregate_shapes.get(&rd)
            {
                self.aggregate_shapes.insert(
                    rd,
                    super::AggregateShape::Function {
                        len: *len,
                        domain_lo: *domain_lo,
                        value: Some(Box::new(shape)),
                    },
                );
            }
        }

        // Advance: increment index, branch to header.
        let next_idx = self.emit_with_result(
            block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cur_idx,
                rhs: one,
            },
        );
        self.emit(
            block,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: loop_state.idx_alloca,
                value: next_idx,
                align: None,
                volatile: false,
            }),
        );

        let header_id = self.block_id_of(loop_state.header_block);
        self.emit(
            block,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

        // Return None — the exit block is the next PC's block, lower_body handles it.
        Ok(None)
    }
}
