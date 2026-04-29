// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set operation lowering: SetEnum, SetIn, SetUnion, SetIntersect, SetDiff,
//! SubsetEq, Range.

use crate::TmirError;
use tla_jit_abi::JitRuntimeErrorKind;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::value::{BlockId, ValueId};
use tmir::InstrNode;

use super::{Ctx, LoopNextKind, LoopNextState, QuantifierLoopState};

impl<'cp> Ctx<'cp> {
    /// Lower Powerset { rd, rs }: build a lazy representation of SUBSET(rs).
    ///
    /// The register stores the base set pointer unchanged. Shape tracking marks
    /// the value as a powerset so SetIn can lower `x \in SUBSET S` as
    /// `x \subseteq S` without enumerating subsets.
    pub(super) fn lower_powerset(
        &mut self,
        block_idx: usize,
        rd: u8,
        rs: u8,
    ) -> Result<(), TmirError> {
        let base_shape = self.aggregate_shapes.get(&rs).cloned().ok_or_else(|| {
            TmirError::UnsupportedOpcode(
                "Powerset: base must have a tracked finite shape".to_owned(),
            )
        })?;
        base_shape.validate_powerset_base("Powerset")?;

        let base_value = self.load_reg(block_idx, rs)?;
        self.store_reg_value(block_idx, rd, base_value)?;
        self.compact_state_slots.remove(&rd);
        self.aggregate_shapes.insert(
            rd,
            super::AggregateShape::Powerset {
                base: Box::new(base_shape),
            },
        );
        self.const_set_sizes.remove(&rd);
        self.const_scalar_values.remove(&rd);
        Ok(())
    }

    /// Lower SetEnum { rd, start, count }: build a set from consecutive registers.
    ///
    /// Layout: alloca[0] = count, alloca[1..=count] = elements from registers.
    pub(super) fn lower_set_enum(
        &mut self,
        block_idx: usize,
        rd: u8,
        start: u8,
        count: u8,
    ) -> Result<(), TmirError> {
        if let Some((universe_len, universe)) =
            self.set_enum_scalar_int_domain_universe_from_registers(start, count)
        {
            let mut mask = self.emit_i64_const(block_idx, 0);
            for i in 0..count {
                let elem = self.load_reg(block_idx, start + i)?;
                let bit = self.emit_set_bitmask_universe_bit_i64(
                    block_idx,
                    elem,
                    universe_len,
                    &universe,
                    "SetEnum",
                )?;
                mask = self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::Or,
                        ty: Ty::I64,
                        lhs: mask,
                        rhs: bit,
                    },
                );
            }
            self.store_reg_value(block_idx, rd, mask)?;
            self.compact_state_slots.remove(&rd);
            return Ok(());
        }

        let total_slots = u32::from(count) + 1; // length header + elements
        let agg_ptr = self.alloc_aggregate(block_idx, total_slots);

        // Store length
        let len_val = self.emit_i64_const(block_idx, i64::from(count));
        self.store_at_offset(block_idx, agg_ptr, 0, len_val);

        // Store each element
        for i in 0..count {
            let elem = self.load_reg(block_idx, start + i)?;
            self.store_at_offset(block_idx, agg_ptr, u32::from(i) + 1, elem);
        }

        self.store_reg_ptr(block_idx, rd, agg_ptr)?;
        self.compact_state_slots.remove(&rd);
        Ok(())
    }

    /// Lower SetFilterBegin: build `{x \in S : P(x)}` as a bounded set.
    ///
    /// The result aggregate is allocated up front with capacity `|S| + 1`
    /// slots and length initialized to zero. Each matching LoopNext appends
    /// the current binding and increments slot 0.
    pub(super) fn lower_set_filter_begin(
        &mut self,
        pc: usize,
        block_idx: usize,
        rd: u8,
        r_binding: u8,
        r_domain: u8,
        loop_end: i32,
    ) -> Result<Option<usize>, TmirError> {
        let exit_pc = self.resolve_forward_target(pc, loop_end, "SetFilterBegin")?;
        let body_pc = pc + 1;
        let exit_block = self.block_index_for_pc(exit_pc)?;
        let body_block = self.block_index_for_pc(body_pc)?;

        let domain_max_len = self.finite_set_len_bound_of(r_domain);
        if let Some(super::AggregateShape::SetBitmask {
            universe_len,
            universe,
        }) = self.aggregate_shapes.get(&r_domain).cloned()
        {
            match &universe {
                super::SetBitmaskUniverse::IntRange { .. }
                | super::SetBitmaskUniverse::ExplicitInt(_) => {}
                super::SetBitmaskUniverse::Exact(_) => {
                    return Err(TmirError::UnsupportedOpcode(
                        "SetFilterBegin: compact SetBitmask iteration requires exact universe metadata with integer elements"
                            .to_owned(),
                    ));
                }
                super::SetBitmaskUniverse::Unknown => {
                    return Err(TmirError::UnsupportedOpcode(
                        "SetFilterBegin: compact SetBitmask domain requires exact universe metadata"
                            .to_owned(),
                    ));
                }
            }
            Self::compact_set_bitmask_valid_mask(universe_len, "SetFilterBegin")?;
            let total_slots = universe_len.checked_add(1).ok_or_else(|| {
                TmirError::UnsupportedOpcode(
                    "SetFilterBegin: compact SetBitmask result capacity overflows u32".to_owned(),
                )
            })?;
            let result_ptr = self.alloc_aggregate(block_idx, total_slots);
            let zero = self.emit_i64_const(block_idx, 0);
            self.store_at_offset(block_idx, result_ptr, 0, zero);
            self.store_reg_ptr(block_idx, rd, result_ptr)?;
            self.compact_state_slots.remove(&rd);

            let frame = self.emit_compact_set_bitmask_binding_frame_prelude(
                pc,
                block_idx,
                r_binding,
                r_domain,
                loop_end,
                "setfilter_header",
                "setfilter_load",
                "SetFilterBegin",
                universe_len,
                &universe,
                None,
            )?;
            self.loop_next_stack.push(LoopNextState {
                rd,
                kind: LoopNextKind::SetFilter,
                loop_state: QuantifierLoopState {
                    idx_alloca: frame.idx_alloca,
                    header_block: frame.header_block,
                    exit_block: frame.exit_block,
                },
                funcdef_capture: None,
            });
            if !self.annotate_loop_bound(frame.header_block, r_domain) {
                self.mark_unbounded_loop();
            }
            self.aggregate_shapes.insert(
                rd,
                super::AggregateShape::BoundedSet {
                    max_len: universe_len,
                    element: super::binding_shape_from_domain(&super::AggregateShape::SetBitmask {
                        universe_len,
                        universe: universe.clone(),
                    })
                    .map(Box::new),
                },
            );
            self.const_set_sizes.remove(&rd);
            self.const_scalar_values.remove(&rd);
            return Ok(None);
        }
        self.reject_compact_set_bitmask_powerset_iteration(r_domain, "SetFilterBegin")?;
        let binding_shape = self
            .aggregate_shapes
            .get(&r_domain)
            .and_then(super::binding_shape_from_domain);
        let domain_ptr = self.load_reg_as_ptr(block_idx, r_domain)?;
        let domain_len = self.load_at_offset(block_idx, domain_ptr, 0);
        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        let total_slots = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: domain_len,
                rhs: one,
            },
        );
        let result_ptr = match domain_max_len.and_then(|max_len| max_len.checked_add(1)) {
            Some(static_slots) => self.alloc_aggregate(block_idx, static_slots),
            None => self.alloc_dynamic_i64_slots(block_idx, total_slots),
        };

        self.store_at_offset(block_idx, result_ptr, 0, zero);
        self.store_reg_ptr(block_idx, rd, result_ptr)?;
        self.compact_state_slots.remove(&rd);

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

        let header_block = self.new_aux_block("setfilter_header");
        let load_block = self.new_aux_block("setfilter_load");
        let header_id = self.block_id_of(header_block);
        let load_id = self.block_id_of(load_block);
        let body_id = self.block_id_of(body_block);
        let exit_id = self.block_id_of(exit_block);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

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

        let load_idx = self.emit_with_result(
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
                lhs: load_idx,
                rhs: one,
            },
        );
        let elem = self.load_at_dynamic_offset(load_block, domain_ptr, slot_idx);
        self.store_reg_value(load_block, r_binding, elem)?;
        self.invalidate_reg_tracking(r_binding);
        if let Some(binding_shape) = binding_shape.clone() {
            self.aggregate_shapes.insert(r_binding, binding_shape);
        }
        self.emit(
            load_block,
            InstrNode::new(Inst::Br {
                target: body_id,
                args: vec![],
            }),
        );

        self.loop_next_stack.push(LoopNextState {
            rd,
            kind: LoopNextKind::SetFilter,
            loop_state: QuantifierLoopState {
                idx_alloca,
                header_block,
                exit_block,
            },
            funcdef_capture: None,
        });

        if !self.annotate_loop_bound(header_block, r_domain) {
            self.mark_unbounded_loop();
        }

        if let Some(max_len) = domain_max_len {
            self.aggregate_shapes.insert(
                rd,
                super::AggregateShape::BoundedSet {
                    max_len,
                    element: binding_shape.map(Box::new),
                },
            );
        } else if self
            .aggregate_shapes
            .get(&r_domain)
            .is_some_and(super::AggregateShape::is_finite_set_shape)
        {
            self.aggregate_shapes
                .insert(rd, super::AggregateShape::FiniteSet);
        } else {
            self.aggregate_shapes.remove(&rd);
        }
        self.const_set_sizes.remove(&rd);
        self.const_scalar_values.remove(&rd);

        Ok(None)
    }

    /// Lower LoopNext for SetFilter: append the current binding when the
    /// predicate is true, then advance the iterator.
    pub(super) fn lower_loop_next_set_filter(
        &mut self,
        block_idx: usize,
        r_binding: u8,
        r_body: u8,
        rd: u8,
        loop_state: QuantifierLoopState,
    ) -> Result<Option<usize>, TmirError> {
        let body_val = self.load_reg(block_idx, r_body)?;
        let zero = self.emit_i64_const(block_idx, 0);
        let predicate_true = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: body_val,
                rhs: zero,
            },
        );

        let append_block = self.new_aux_block("setfilter_append");
        let advance_block = self.new_aux_block("setfilter_advance");
        let append_id = self.block_id_of(append_block);
        let advance_id = self.block_id_of(advance_block);
        let header_id = self.block_id_of(loop_state.header_block);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: predicate_true,
                then_target: append_id,
                then_args: vec![],
                else_target: advance_id,
                else_args: vec![],
            }),
        );

        let result_ptr = self.load_reg_as_ptr(append_block, rd)?;
        let current_len = self.load_at_offset(append_block, result_ptr, 0);
        let one_for_slot = self.emit_i64_const(append_block, 1);
        let slot_idx = self.emit_with_result(
            append_block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: current_len,
                rhs: one_for_slot,
            },
        );
        let binding_val = self.load_reg(append_block, r_binding)?;
        self.store_at_dynamic_offset(append_block, result_ptr, slot_idx, binding_val);
        let new_len = self.emit_with_result(
            append_block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: current_len,
                rhs: one_for_slot,
            },
        );
        self.store_at_offset(append_block, result_ptr, 0, new_len);
        self.emit(
            append_block,
            InstrNode::new(Inst::Br {
                target: advance_id,
                args: vec![],
            }),
        );

        let cur_idx = self.emit_with_result(
            advance_block,
            Inst::Load {
                ty: Ty::I64,
                ptr: loop_state.idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one_for_inc = self.emit_i64_const(advance_block, 1);
        let next_idx = self.emit_with_result(
            advance_block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cur_idx,
                rhs: one_for_inc,
            },
        );
        self.emit(
            advance_block,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: loop_state.idx_alloca,
                value: next_idx,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            advance_block,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

        Ok(None)
    }

    /// Lower SetIn { rd, elem, set }: set membership test.
    ///
    /// Emits a linear scan loop: for each element in the set, compare with elem.
    /// Result is 1 (found) or 0 (not found).
    ///
    /// CFG:
    ///   entry -> header
    ///   header -> body (if i < len) | not_found (if i >= len)
    ///   body -> found (if equal) | inc (if not equal)
    ///   inc -> header
    ///   found -> merge (rd = 1)
    ///   not_found -> merge (rd = 0)
    pub(super) fn lower_set_in(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_reg: u8,
        set_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let Some(shape) = self.aggregate_shapes.get(&set_reg).cloned() {
            match shape {
                super::AggregateShape::Interval { lo, hi } => {
                    let elem_val = self.load_reg(block_idx, elem_reg)?;
                    self.lower_interval_membership_value(block_idx, rd, elem_val, lo, hi)?;
                    return Ok(Some(block_idx));
                }
                super::AggregateShape::RecordSet { fields } => {
                    return self
                        .lower_record_set_membership(block_idx, rd, elem_reg, set_reg, fields);
                }
                super::AggregateShape::Powerset { base } => {
                    return self.lower_powerset_membership(block_idx, rd, elem_reg, set_reg, *base);
                }
                super::AggregateShape::FunctionSet { domain, range } => {
                    return self.lower_function_set_membership(
                        block_idx, rd, elem_reg, set_reg, *domain, *range,
                    );
                }
                super::AggregateShape::SeqSet { base } => {
                    return self.lower_seq_set_membership(block_idx, rd, elem_reg, set_reg, *base);
                }
                super::AggregateShape::Set { len, element } => {
                    if let (
                        Some(source_slot),
                        Some(elem_shape @ super::AggregateShape::Record { .. }),
                    ) = (
                        self.compact_state_slot_for_use(block_idx, elem_reg)?,
                        self.aggregate_shapes.get(&elem_reg).cloned(),
                    ) {
                        return self.lower_compact_record_materialized_set_membership(
                            block_idx,
                            rd,
                            source_slot,
                            &elem_shape,
                            set_reg,
                            len,
                            element.as_deref(),
                        );
                    }
                }
                super::AggregateShape::SymbolicDomain(domain) => {
                    self.lower_symbolic_domain_membership(block_idx, rd, elem_reg, domain)?;
                    return Ok(Some(block_idx));
                }
                super::AggregateShape::SetBitmask { .. } => {
                    let Some((universe_len, universe)) = shape.set_bitmask_universe() else {
                        return Err(TmirError::UnsupportedOpcode(
                            "SetIn: compact SetBitmask membership requires exact universe metadata"
                                .to_owned(),
                        ));
                    };
                    let elem_val = self.load_reg(block_idx, elem_reg)?;
                    let mask = self.load_reg(block_idx, set_reg)?;
                    let member = self.emit_compact_bitmask_set_membership_i64(
                        block_idx,
                        elem_val,
                        mask,
                        universe_len,
                        &universe,
                        "SetIn: compact SetBitmask membership",
                    )?;
                    self.store_reg_value(block_idx, rd, member)?;
                    return Ok(Some(block_idx));
                }
                _ => {}
            }
        }

        let elem_val = self.load_reg(block_idx, elem_reg)?;
        let set_ptr = self.load_reg_as_ptr(block_idx, set_reg)?;
        let set_len = self.load_at_offset(block_idx, set_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

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

        let loop_header = self.new_aux_block("setin_header");
        let loop_body = self.new_aux_block("setin_body");
        let loop_inc = self.new_aux_block("setin_inc");
        let found_blk = self.new_aux_block("setin_found");
        let not_found_blk = self.new_aux_block("setin_not_found");
        let merge_blk = self.new_aux_block("setin_merge");

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

        // Header: i < len?
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
                rhs: set_len,
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

        // Body: load set[i+1], compare with elem
        let cur_idx2 = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot_idx = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cur_idx2,
                rhs: one,
            },
        );
        let set_elem = self.load_at_dynamic_offset(loop_body, set_ptr, slot_idx);
        let eq = self.emit_with_result(
            loop_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: set_elem,
                rhs: elem_val,
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

        // Found: rd = 1
        self.store_reg_imm(found_blk, rd, 1)?;
        self.emit(
            found_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        // Not found: rd = 0
        self.store_reg_imm(not_found_blk, rd, 0)?;
        self.emit(
            not_found_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge_blk))
    }

    fn i64_value_as_ptr(&mut self, block_idx: usize, value: ValueId) -> ValueId {
        self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: value,
            },
        )
    }

    fn emit_bool_to_i64(&mut self, block_idx: usize, value: ValueId) -> ValueId {
        self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: value,
            },
        )
    }

    pub(super) fn compact_set_bitmask_valid_mask(
        universe_len: u32,
        context: &str,
    ) -> Result<i64, TmirError> {
        match universe_len {
            0 => Ok(0),
            1..=62 => Ok((1_i64 << universe_len) - 1),
            63 => Ok(i64::MAX),
            _ => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SetBitmask universe length {universe_len} exceeds i64 bitmask capacity"
            ))),
        }
    }

    pub(super) fn emit_compact_bitmask_canonical_i64(
        &mut self,
        block_idx: usize,
        mask: ValueId,
        universe_len: u32,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        let valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, context)?;
        let invalid_mask = self.emit_i64_const(block_idx, !valid_mask);
        let zero = self.emit_i64_const(block_idx, 0);
        let non_negative = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Sge,
                ty: Ty::I64,
                lhs: mask,
                rhs: zero,
            },
        );
        let invalid_bits = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: mask,
                rhs: invalid_mask,
            },
        );
        let high_bits_clear = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: invalid_bits,
                rhs: zero,
            },
        );
        let non_negative_i64 = self.emit_bool_to_i64(block_idx, non_negative);
        let high_bits_clear_i64 = self.emit_bool_to_i64(block_idx, high_bits_clear);
        Ok(self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: non_negative_i64,
                rhs: high_bits_clear_i64,
            },
        ))
    }

    fn emit_compact_bitmask_powerset_membership_i64(
        &mut self,
        block_idx: usize,
        mask: ValueId,
        base_shape: &super::AggregateShape,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        base_shape.validate_powerset_base(context)?;
        let valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, context)?;
        let base_mask = if base_shape.compatible_set_bitmask_universe(universe_len, universe) {
            valid_mask
        } else if let Some(base_mask) =
            super::static_int_base_mask_for_set_bitmask_universe(base_shape, universe_len, universe)
        {
            base_mask
        } else if base_shape.matches_set_bitmask_base(universe_len, universe) {
            valid_mask
        } else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SetBitmask universe does not match SUBSET base {base_shape:?}"
            )));
        };

        let canonical =
            self.emit_compact_bitmask_canonical_i64(block_idx, mask, universe_len, context)?;
        let invalid_base_mask = self.emit_i64_const(block_idx, !base_mask);
        let zero = self.emit_i64_const(block_idx, 0);
        let outside_base_bits = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: mask,
                rhs: invalid_base_mask,
            },
        );
        let subset = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: outside_base_bits,
                rhs: zero,
            },
        );
        let subset_i64 = self.emit_bool_to_i64(block_idx, subset);
        Ok(self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: canonical,
                rhs: subset_i64,
            },
        ))
    }

    fn lazy_domain_runtime_payload_is_compact_mask(shape: &super::AggregateShape) -> bool {
        match shape {
            super::AggregateShape::SetBitmask { .. } => true,
            super::AggregateShape::Powerset { base } => {
                matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. })
            }
            _ => false,
        }
    }

    fn guard_compact_sequence_dynamic_len_in_bounds(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        len_slot: ValueId,
        capacity: u32,
        context: &str,
    ) -> usize {
        let len_value = self.load_at_dynamic_offset(block_idx, source_ptr, len_slot);
        let zero = self.emit_i64_const(block_idx, 0);
        let non_negative = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Sge,
                ty: Ty::I64,
                lhs: len_value,
                rhs: zero,
            },
        );

        let check_capacity_blk = self.new_aux_block(&format!("{context}_check_capacity"));
        let ok_blk = self.new_aux_block(&format!("{context}_ok"));
        let error_blk = self.new_aux_block(&format!("{context}_error"));
        let check_capacity_id = self.block_id_of(check_capacity_blk);
        let ok_id = self.block_id_of(ok_blk);
        let error_id = self.block_id_of(error_blk);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: non_negative,
                then_target: check_capacity_id,
                then_args: vec![],
                else_target: error_id,
                else_args: vec![],
            }),
        );

        let checked_len = self.load_at_dynamic_offset(check_capacity_blk, source_ptr, len_slot);
        let capacity_val = self.emit_i64_const(check_capacity_blk, i64::from(capacity));
        let within_capacity = self.emit_with_result(
            check_capacity_blk,
            Inst::ICmp {
                op: ICmpOp::Sle,
                ty: Ty::I64,
                lhs: checked_len,
                rhs: capacity_val,
            },
        );
        self.emit(
            check_capacity_blk,
            InstrNode::new(Inst::CondBr {
                cond: within_capacity,
                then_target: ok_id,
                then_args: vec![],
                else_target: error_id,
                else_args: vec![],
            }),
        );
        self.emit_runtime_error_and_return(error_blk, JitRuntimeErrorKind::TypeMismatch);
        ok_blk
    }

    fn lower_compact_bitmask_runtime_powerset_mask_branch(
        &mut self,
        block_idx: usize,
        mask: ValueId,
        base_mask: ValueId,
        base_shape: &super::AggregateShape,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        success_target: BlockId,
        failure_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        if !base_shape.compatible_set_bitmask_universe(universe_len, universe) {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SetBitmask universe does not match runtime SUBSET base {base_shape:?}"
            )));
        }
        let all_in_universe = self.emit_i64_const(block_idx, 1);
        self.lower_set_bitmask_subseteq_mask_branch(
            block_idx,
            mask,
            all_in_universe,
            base_mask,
            universe_len,
            success_target,
            failure_target,
            context,
        )
    }

    fn lower_compact_bitmask_powerset_branch(
        &mut self,
        block_idx: usize,
        mask: ValueId,
        base_shape: &super::AggregateShape,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        success_target: BlockId,
        failure_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        let member = self.emit_compact_bitmask_powerset_membership_i64(
            block_idx,
            mask,
            base_shape,
            universe_len,
            universe,
            context,
        )?;
        self.branch_on_i64_truth(block_idx, member, success_target, failure_target);
        Ok(())
    }

    fn lower_scalar_in_set_bitmask_shape_branch(
        &mut self,
        block_idx: usize,
        value: ValueId,
        value_shape: Option<&super::AggregateShape>,
        mask: ValueId,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        success_target: BlockId,
        failure_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        if matches!(value_shape, Some(super::AggregateShape::SetBitmask { .. })) {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SetBitmask values are set-valued masks, not scalar elements"
            )));
        }
        let member = self.emit_compact_bitmask_set_membership_i64(
            block_idx,
            value,
            mask,
            universe_len,
            universe,
            context,
        )?;
        self.branch_on_i64_truth(block_idx, member, success_target, failure_target);
        Ok(())
    }

    fn lower_set_bitmask_subseteq_mask_branch(
        &mut self,
        block_idx: usize,
        left: ValueId,
        left_in_universe: ValueId,
        right: ValueId,
        universe_len: u32,
        success_target: BlockId,
        failure_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        let valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, context)?;
        let valid_mask_val = self.emit_i64_const(block_idx, valid_mask);
        let right_complement = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Xor,
                ty: Ty::I64,
                lhs: right,
                rhs: valid_mask_val,
            },
        );
        let missing = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: left,
                rhs: right_complement,
            },
        );
        let zero = self.emit_i64_const(block_idx, 0);
        let no_missing = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: missing,
                rhs: zero,
            },
        );
        let no_missing_i64 = self.emit_bool_to_i64(block_idx, no_missing);
        let left_canonical =
            self.emit_compact_bitmask_canonical_i64(block_idx, left, universe_len, context)?;
        let right_canonical =
            self.emit_compact_bitmask_canonical_i64(block_idx, right, universe_len, context)?;
        let canonical = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: left_canonical,
                rhs: right_canonical,
            },
        );
        let subset = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: no_missing_i64,
                rhs: left_in_universe,
            },
        );
        let member = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: subset,
                rhs: canonical,
            },
        );
        self.branch_on_i64_truth(block_idx, member, success_target, failure_target);
        Ok(())
    }

    fn lower_scalar_in_function_set_range_shape_branch(
        &mut self,
        block_idx: usize,
        value: ValueId,
        value_shape: Option<&super::AggregateShape>,
        range_value: ValueId,
        range_shape: super::AggregateShape,
        success_target: BlockId,
        failure_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        match range_shape {
            super::AggregateShape::Powerset { base }
                if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) =>
            {
                let Some(value_shape @ super::AggregateShape::SetBitmask { .. }) = value_shape
                else {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SUBSET range requires SetBitmask entries, got {value_shape:?}"
                    )));
                };
                let Some((universe_len, universe)) = value_shape.set_bitmask_universe() else {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SUBSET range requires exact universe metadata"
                    )));
                };
                self.lower_compact_bitmask_runtime_powerset_mask_branch(
                    block_idx,
                    value,
                    range_value,
                    &base,
                    universe_len,
                    &universe,
                    success_target,
                    failure_target,
                    context,
                )
            }
            super::AggregateShape::SeqSet { base } => {
                let seq_element_shape = match value_shape {
                    Some(super::AggregateShape::Sequence { element, .. }) => element.as_deref(),
                    _ => None,
                };
                let base_value = if Self::lazy_domain_runtime_payload_is_compact_mask(&base) {
                    range_value
                } else {
                    self.i64_value_as_ptr(block_idx, range_value)
                };
                self.lower_seq_value_in_seq_set_ptr_branch(
                    block_idx,
                    value,
                    seq_element_shape,
                    base_value,
                    *base,
                    success_target,
                    failure_target,
                    context,
                )
            }
            super::AggregateShape::SetBitmask {
                universe_len,
                universe,
            } => self.lower_scalar_in_set_bitmask_shape_branch(
                block_idx,
                value,
                value_shape,
                range_value,
                universe_len,
                &universe,
                success_target,
                failure_target,
                context,
            ),
            range_shape => {
                let range_ptr = self.i64_value_as_ptr(block_idx, range_value);
                self.lower_value_in_domain_ptr_branch(
                    block_idx,
                    value,
                    value_shape,
                    range_ptr,
                    range_shape,
                    success_target,
                    failure_target,
                    context,
                )
            }
        }
    }

    fn compact_powerset_mask_universe_for_value_shape(
        value_shape: Option<&super::AggregateShape>,
        context: &str,
    ) -> Result<(u32, super::SetBitmaskUniverse), TmirError> {
        match value_shape {
            Some(shape @ super::AggregateShape::SetBitmask { .. }) => {
                shape.set_bitmask_universe().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SUBSET range requires exact SetBitmask universe metadata"
                    ))
                })
            }
            Some(other) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SUBSET range requires SetBitmask entries, got {other:?}"
            ))),
            None => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SUBSET range requires tracked sequence entry shape"
            ))),
        }
    }

    fn emit_set_bitmask_universe_bit_i64(
        &mut self,
        block_idx: usize,
        elem_val: ValueId,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        Self::compact_set_bitmask_valid_mask(universe_len, context)?;
        if universe_len == 0 {
            return Ok(self.emit_i64_const(block_idx, 0));
        }
        match universe {
            super::SetBitmaskUniverse::IntRange { lo } => {
                self.emit_int_range_universe_bit_i64(block_idx, elem_val, *lo, universe_len)
            }
            super::SetBitmaskUniverse::ExplicitInt(values) => {
                self.emit_explicit_universe_bit_i64(block_idx, elem_val, values)
            }
            super::SetBitmaskUniverse::Exact(_) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SetBitmask operation requires exact universe metadata with integer elements"
            ))),
            super::SetBitmaskUniverse::Unknown => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact SetBitmask operation requires exact universe metadata"
            ))),
        }
    }

    fn emit_int_range_universe_bit_i64(
        &mut self,
        block_idx: usize,
        elem_val: ValueId,
        lo: i64,
        universe_len: u32,
    ) -> Result<ValueId, TmirError> {
        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);
        let lo_val = self.emit_i64_const(block_idx, lo);
        let hi = lo
            .checked_add(i64::from(universe_len).saturating_sub(1))
            .ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "compact SetBitmask integer universe {lo} plus len {universe_len} overflows i64"
                ))
            })?;
        let hi_val = self.emit_i64_const(block_idx, hi);
        let ge_lo = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Sge,
                ty: Ty::I64,
                lhs: elem_val,
                rhs: lo_val,
            },
        );
        let le_hi = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Sle,
                ty: Ty::I64,
                lhs: elem_val,
                rhs: hi_val,
            },
        );
        let ge_lo_i64 = self.emit_bool_to_i64(block_idx, ge_lo);
        let le_hi_i64 = self.emit_bool_to_i64(block_idx, le_hi);
        let in_range_i64 = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: ge_lo_i64,
                rhs: le_hi_i64,
            },
        );
        let in_range = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: in_range_i64,
                rhs: zero,
            },
        );
        let raw_idx = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: elem_val,
                rhs: lo_val,
            },
        );
        let safe_idx = self.emit_with_result(
            block_idx,
            Inst::Select {
                ty: Ty::I64,
                cond: in_range,
                then_val: raw_idx,
                else_val: zero,
            },
        );
        let raw_bit = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Shl,
                ty: Ty::I64,
                lhs: one,
                rhs: safe_idx,
            },
        );
        Ok(self.emit_with_result(
            block_idx,
            Inst::Select {
                ty: Ty::I64,
                cond: in_range,
                then_val: raw_bit,
                else_val: zero,
            },
        ))
    }

    fn emit_explicit_universe_bit_i64(
        &mut self,
        block_idx: usize,
        elem_val: ValueId,
        values: &[i64],
    ) -> Result<ValueId, TmirError> {
        let mut mask = self.emit_i64_const(block_idx, 0);
        for (idx, element) in values.iter().copied().enumerate() {
            if idx >= 63 {
                return Err(TmirError::UnsupportedOpcode(
                    "compact SetBitmask explicit universe exceeds i64 capacity".to_owned(),
                ));
            }
            let expected = self.emit_i64_const(block_idx, element);
            let is_elem = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: elem_val,
                    rhs: expected,
                },
            );
            let bit = self.emit_i64_const(block_idx, 1_i64 << idx);
            let zero = self.emit_i64_const(block_idx, 0);
            let selected = self.emit_with_result(
                block_idx,
                Inst::Select {
                    ty: Ty::I64,
                    cond: is_elem,
                    then_val: bit,
                    else_val: zero,
                },
            );
            mask = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    lhs: mask,
                    rhs: selected,
                },
            );
        }
        Ok(mask)
    }

    fn emit_compact_bitmask_set_membership_i64(
        &mut self,
        block_idx: usize,
        elem_val: ValueId,
        mask: ValueId,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        let bit = self.emit_set_bitmask_universe_bit_i64(
            block_idx,
            elem_val,
            universe_len,
            universe,
            context,
        )?;
        let present_bits = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: mask,
                rhs: bit,
            },
        );
        let zero = self.emit_i64_const(block_idx, 0);
        let present = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: present_bits,
                rhs: zero,
            },
        );
        let present_i64 = self.emit_bool_to_i64(block_idx, present);
        let canonical =
            self.emit_compact_bitmask_canonical_i64(block_idx, mask, universe_len, context)?;
        Ok(self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: present_i64,
                rhs: canonical,
            },
        ))
    }

    fn emit_set_operand_bitmask_i64_allow_materialized(
        &mut self,
        block_idx: usize,
        reg: u8,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
    ) -> Result<(usize, ValueId), TmirError> {
        match self.aggregate_shapes.get(&reg).cloned() {
            Some(shape @ super::AggregateShape::SetBitmask { .. }) => {
                if !shape.compatible_set_bitmask_universe(universe_len, universe) {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SetBitmask universe mismatch for r{reg}: {shape:?}"
                    )));
                }
                Ok((block_idx, self.load_reg(block_idx, reg)?))
            }
            Some(super::AggregateShape::ExactIntSet { values }) => {
                let mask = self.emit_exact_int_set_operand_bitmask_i64(
                    block_idx,
                    &values,
                    universe_len,
                    universe,
                    context,
                    true,
                )?;
                Ok((block_idx, mask))
            }
            Some(super::AggregateShape::Set { len: 0, .. }) => {
                Ok((block_idx, self.emit_i64_const(block_idx, 0)))
            }
            Some(super::AggregateShape::Set { .. }) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact set operation cannot infer that materialized Set r{reg} is confined to the compact SetBitmask universe"
            ))),
            Some(super::AggregateShape::Interval { lo, hi }) => {
                let mask = self.emit_interval_bitmask_i64(
                    block_idx,
                    lo,
                    hi,
                    universe_len,
                    universe,
                    context,
                )?;
                Ok((block_idx, mask))
            }
            Some(shape) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact set operation requires SetBitmask or compatible materialized integer Set operand, got r{reg} = {shape:?}"
            ))),
            None => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact set operation requires tracked set operand r{reg}"
            ))),
        }
    }

    fn emit_exact_int_set_operand_bitmask_i64(
        &mut self,
        block_idx: usize,
        values: &[i64],
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
        require_all_in_universe: bool,
    ) -> Result<ValueId, TmirError> {
        Self::compact_set_bitmask_valid_mask(universe_len, context)?;
        let mut mask = 0_i64;
        for value in values {
            let bit_idx = match universe {
                super::SetBitmaskUniverse::IntRange { lo } => value
                    .checked_sub(*lo)
                    .filter(|idx| *idx >= 0 && *idx < i64::from(universe_len))
                    .and_then(|idx| u32::try_from(idx).ok()),
                super::SetBitmaskUniverse::ExplicitInt(universe_values) => universe_values
                    .iter()
                    .position(|elem| elem == value)
                    .filter(|idx| *idx < usize::try_from(universe_len).unwrap_or(usize::MAX))
                    .and_then(|idx| u32::try_from(idx).ok()),
                super::SetBitmaskUniverse::Exact(_) => {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SetBitmask operation requires exact universe metadata with integer elements"
                    )));
                }
                super::SetBitmaskUniverse::Unknown => {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SetBitmask operation requires exact universe metadata"
                    )));
                }
            };
            let Some(bit_idx) = bit_idx else {
                if require_all_in_universe {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: exact integer Set contains values outside compact SetBitmask universe"
                    )));
                }
                continue;
            };
            mask |= 1_i64 << bit_idx;
        }
        Ok(self.emit_i64_const(block_idx, mask))
    }

    fn emit_set_intersect_operand_bitmask_i64(
        &mut self,
        block_idx: usize,
        reg: u8,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
    ) -> Result<(usize, ValueId), TmirError> {
        match self.aggregate_shapes.get(&reg).cloned() {
            Some(super::AggregateShape::ExactIntSet { values }) => {
                let mask = self.emit_exact_int_set_operand_bitmask_i64(
                    block_idx,
                    &values,
                    universe_len,
                    universe,
                    context,
                    false,
                )?;
                Ok((block_idx, mask))
            }
            Some(super::AggregateShape::Interval { lo, hi }) => {
                let mask = self.emit_interval_bitmask_i64_allow_clamped(
                    block_idx,
                    lo,
                    hi,
                    universe_len,
                    universe,
                    context,
                )?;
                Ok((block_idx, mask))
            }
            _ => self.emit_set_operand_bitmask_i64_allow_materialized(
                block_idx,
                reg,
                universe_len,
                universe,
                context,
            ),
        }
    }

    pub(super) fn emit_set_subseteq_operand_bitmask_i64(
        &mut self,
        block_idx: usize,
        reg: u8,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
    ) -> Result<(usize, ValueId, ValueId), TmirError> {
        match self.aggregate_shapes.get(&reg).cloned() {
            Some(shape @ super::AggregateShape::SetBitmask { .. }) => {
                if !shape.compatible_set_bitmask_universe(universe_len, universe) {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SetBitmask universe mismatch for r{reg}: {shape:?}"
                    )));
                }
                let all_in_universe = self.emit_i64_const(block_idx, 1);
                Ok((block_idx, self.load_reg(block_idx, reg)?, all_in_universe))
            }
            Some(super::AggregateShape::ExactIntSet { values }) => {
                let mask = self.emit_exact_int_set_operand_bitmask_i64(
                    block_idx,
                    &values,
                    universe_len,
                    universe,
                    context,
                    false,
                )?;
                let all_in_universe = values.iter().all(|value| {
                    super::int_value_in_set_bitmask_universe(*value, universe_len, universe)
                });
                let all_in_universe = self.emit_i64_const(block_idx, i64::from(all_in_universe));
                Ok((block_idx, mask, all_in_universe))
            }
            Some(super::AggregateShape::Set { len: 0, .. }) => {
                let zero = self.emit_i64_const(block_idx, 0);
                let one = self.emit_i64_const(block_idx, 1);
                Ok((block_idx, zero, one))
            }
            Some(super::AggregateShape::Interval { lo, hi }) => {
                let mask = self.emit_interval_bitmask_i64_allow_clamped(
                    block_idx,
                    lo,
                    hi,
                    universe_len,
                    universe,
                    context,
                )?;
                let all_in_universe = hi < lo
                    || super::interval_convertible_to_set_bitmask(lo, hi, universe_len, universe);
                let all_in_universe = self.emit_i64_const(block_idx, i64::from(all_in_universe));
                Ok((block_idx, mask, all_in_universe))
            }
            Some(super::AggregateShape::Set { .. }) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact subset operation cannot infer that materialized Set r{reg} is confined to the compact SetBitmask universe"
            ))),
            Some(shape) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact subset operation requires SetBitmask or compatible finite integer Set operand, got r{reg} = {shape:?}"
            ))),
            None => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact subset operation requires tracked set operand r{reg}"
            ))),
        }
    }

    fn materialized_domain_shape_for_pointer(
        shape: super::AggregateShape,
    ) -> super::AggregateShape {
        match shape {
            super::AggregateShape::ExactIntSet { values } => super::AggregateShape::Set {
                len: u32::try_from(values.len()).unwrap_or(u32::MAX),
                element: Some(Box::new(super::AggregateShape::Scalar(
                    super::ScalarShape::Int,
                ))),
            },
            other => other,
        }
    }

    fn emit_interval_bitmask_i64(
        &mut self,
        block_idx: usize,
        lo: i64,
        hi: i64,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        Self::compact_set_bitmask_valid_mask(universe_len, context)?;
        if hi < lo {
            return Ok(self.emit_i64_const(block_idx, 0));
        }
        let count = hi
            .checked_sub(lo)
            .and_then(|span| span.checked_add(1))
            .ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "{context}: materialized interval rangelength overflows i64"
                ))
            })?;
        if count > i64::from(universe_len) {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: materialized interval {lo}..{hi} is wider than compact SetBitmask universe length {universe_len}"
            )));
        }

        let mut mask = 0_i64;
        match universe {
            super::SetBitmaskUniverse::IntRange { lo: universe_lo } => {
                let universe_hi = universe_lo
                    .checked_add(i64::from(universe_len).saturating_sub(1))
                    .ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "{context}: compact SetBitmask integer universe {universe_lo} plus len {universe_len} overflows i64"
                        ))
                    })?;
                if lo < *universe_lo || hi > universe_hi {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: materialized interval {lo}..{hi} is outside compact SetBitmask universe {universe_lo}..{universe_hi}"
                    )));
                }
                for elem in lo..=hi {
                    let bit_idx = elem - *universe_lo;
                    mask |= 1_i64 << bit_idx;
                }
            }
            super::SetBitmaskUniverse::ExplicitInt(values) => {
                for elem in lo..=hi {
                    let Some(bit_idx) = values.iter().position(|value| *value == elem) else {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "{context}: materialized interval element {elem} is outside compact SetBitmask explicit universe"
                        )));
                    };
                    mask |= 1_i64 << bit_idx;
                }
            }
            super::SetBitmaskUniverse::Exact(_) => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: compact SetBitmask operation requires exact universe metadata with integer elements"
                )));
            }
            super::SetBitmaskUniverse::Unknown => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: compact SetBitmask operation requires exact universe metadata"
                )));
            }
        }
        Ok(self.emit_i64_const(block_idx, mask))
    }

    fn emit_interval_bitmask_i64_allow_clamped(
        &mut self,
        block_idx: usize,
        lo: i64,
        hi: i64,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
        context: &str,
    ) -> Result<ValueId, TmirError> {
        Self::compact_set_bitmask_valid_mask(universe_len, context)?;
        if hi < lo {
            return Ok(self.emit_i64_const(block_idx, 0));
        }

        let mut mask = 0_i64;
        match universe {
            super::SetBitmaskUniverse::IntRange { lo: universe_lo } => {
                let universe_hi = universe_lo
                    .checked_add(i64::from(universe_len).saturating_sub(1))
                    .ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "{context}: compact SetBitmask integer universe {universe_lo} plus len {universe_len} overflows i64"
                        ))
                    })?;
                let start = lo.max(*universe_lo);
                let end = hi.min(universe_hi);
                if start <= end {
                    for elem in start..=end {
                        let bit_idx = elem - *universe_lo;
                        mask |= 1_i64 << bit_idx;
                    }
                }
            }
            super::SetBitmaskUniverse::ExplicitInt(values) => {
                for (bit_idx, elem) in values.iter().enumerate() {
                    if bit_idx >= usize::try_from(universe_len).unwrap_or(usize::MAX) {
                        break;
                    }
                    if *elem >= lo && *elem <= hi {
                        mask |= 1_i64 << bit_idx;
                    }
                }
            }
            super::SetBitmaskUniverse::Exact(_) => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: compact SetBitmask operation requires exact universe metadata with integer elements"
                )));
            }
            super::SetBitmaskUniverse::Unknown => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: compact SetBitmask operation requires exact universe metadata"
                )));
            }
        }
        Ok(self.emit_i64_const(block_idx, mask))
    }

    pub(super) fn compact_binary_set_universe(
        &self,
        op: &str,
        r1: u8,
        r2: u8,
    ) -> Result<Option<(u32, super::SetBitmaskUniverse)>, TmirError> {
        let left = match self.aggregate_shapes.get(&r1) {
            Some(shape @ super::AggregateShape::SetBitmask { .. }) => {
                Some(shape.set_bitmask_universe().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{op}: compact SetBitmask operand r{r1} requires exact universe metadata"
                    ))
                })?)
            }
            _ => None,
        };
        let right = match self.aggregate_shapes.get(&r2) {
            Some(shape @ super::AggregateShape::SetBitmask { .. }) => {
                Some(shape.set_bitmask_universe().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "{op}: compact SetBitmask operand r{r2} requires exact universe metadata"
                    ))
                })?)
            }
            _ => None,
        };
        match (left, right) {
            (Some(left), Some(right)) if left != right => {
                Err(TmirError::UnsupportedOpcode(format!(
                    "{op}: compact SetBitmask universe mismatch: r{r1} has {left:?}, r{r2} has {right:?}"
                )))
            }
            (Some(universe), _) | (_, Some(universe)) => Ok(Some(universe)),
            _ => Ok(None),
        }
    }

    fn small_interval_setdiff_universe(
        &self,
        r1: u8,
        r2: u8,
    ) -> Result<Option<(u32, super::SetBitmaskUniverse)>, TmirError> {
        let Some(super::AggregateShape::Interval { lo, hi }) = self.aggregate_shapes.get(&r1)
        else {
            return Ok(None);
        };
        let universe_len = if hi < lo {
            0
        } else {
            let len = hi
                .checked_sub(*lo)
                .and_then(|span| span.checked_add(1))
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "SetDiff: interval source {lo}..{hi} length overflows i64"
                    ))
                })?;
            let Ok(len) = u32::try_from(len) else {
                return Ok(None);
            };
            if len > 63 {
                return Ok(None);
            }
            len
        };

        let Some(subtract_shape) = self.aggregate_shapes.get(&r2) else {
            return Ok(None);
        };
        if !Self::can_lower_small_setdiff_rhs_as_int_mask(subtract_shape) {
            return Ok(None);
        }

        Ok(Some((
            universe_len,
            super::SetBitmaskUniverse::IntRange { lo: *lo },
        )))
    }

    fn can_lower_small_setdiff_rhs_as_int_mask(shape: &super::AggregateShape) -> bool {
        match shape {
            super::AggregateShape::ExactIntSet { .. } | super::AggregateShape::Interval { .. } => {
                true
            }
            super::AggregateShape::Set { len: 0, .. } => true,
            super::AggregateShape::Set { .. } => false,
            _ => false,
        }
    }

    fn emit_small_setdiff_rhs_int_mask_i64(
        &mut self,
        block_idx: usize,
        reg: u8,
        universe_len: u32,
        universe: &super::SetBitmaskUniverse,
    ) -> Result<ValueId, TmirError> {
        if universe_len == 0 {
            return Ok(self.emit_i64_const(block_idx, 0));
        }

        match self.aggregate_shapes.get(&reg).cloned() {
            Some(super::AggregateShape::ExactIntSet { values }) => self
                .emit_exact_int_set_operand_bitmask_i64(
                    block_idx,
                    &values,
                    universe_len,
                    universe,
                    "SetDiff",
                    false,
                ),
            Some(super::AggregateShape::Interval { lo, hi }) => self
                .emit_interval_bitmask_i64_allow_clamped(
                    block_idx,
                    lo,
                    hi,
                    universe_len,
                    universe,
                    "SetDiff",
                ),
            Some(super::AggregateShape::Set { len: 0, .. }) => {
                Ok(self.emit_i64_const(block_idx, 0))
            }
            Some(shape) => Err(TmirError::UnsupportedOpcode(format!(
                "SetDiff: cannot lower r{reg} as a small integer mask: {shape:?}"
            ))),
            None => Err(TmirError::UnsupportedOpcode(format!(
                "SetDiff: cannot lower untracked r{reg} as a small integer mask"
            ))),
        }
    }

    fn emit_symbolic_domain_membership_i64(
        &mut self,
        block_idx: usize,
        elem_val: ValueId,
        elem_shape: Option<&super::AggregateShape>,
        domain: super::SymbolicDomain,
    ) -> Result<ValueId, TmirError> {
        let Some(elem_shape) = elem_shape else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "SetIn: {domain:?} membership requires a known numeric operand shape"
            )));
        };
        if !elem_shape.is_numeric_scalar_shape() {
            return Ok(self.emit_i64_const(block_idx, 0));
        }

        match domain {
            super::SymbolicDomain::Nat => {
                let zero = self.emit_i64_const(block_idx, 0);
                let ge_zero = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Sge,
                        ty: Ty::I64,
                        lhs: elem_val,
                        rhs: zero,
                    },
                );
                Ok(self.emit_bool_to_i64(block_idx, ge_zero))
            }
            super::SymbolicDomain::Int | super::SymbolicDomain::Real => {
                Ok(self.emit_i64_const(block_idx, 1))
            }
        }
    }

    fn emit_finite_set_membership_i64(
        &mut self,
        block_idx: usize,
        elem_val: ValueId,
        set_ptr: ValueId,
        len: u32,
    ) -> ValueId {
        let mut result = self.emit_i64_const(block_idx, 0);
        for slot in 0..len {
            let set_elem = self.load_at_offset(block_idx, set_ptr, slot + 1);
            let eq = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: elem_val,
                    rhs: set_elem,
                },
            );
            let eq_i64 = self.emit_bool_to_i64(block_idx, eq);
            result = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    lhs: result,
                    rhs: eq_i64,
                },
            );
        }
        result
    }

    fn compact_record_materialized_set_fields(
        value_shape: &super::AggregateShape,
        set_element_shape: Option<&super::AggregateShape>,
    ) -> Result<Vec<(u32, u32)>, TmirError> {
        let Some(set_element_shape) = set_element_shape else {
            return Err(TmirError::UnsupportedOpcode(
                "SetIn: compact record finite-set membership requires tracked record element shape"
                    .to_owned(),
            ));
        };
        let super::AggregateShape::Record { fields: set_fields } = set_element_shape else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "SetIn: compact record finite-set membership requires record element shape, got {set_element_shape:?}"
            )));
        };

        let super::AggregateShape::Record {
            fields: value_fields,
        } = value_shape
        else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "SetIn: compact record finite-set membership requires record value shape, got {value_shape:?}"
            )));
        };
        if value_fields.len() != set_fields.len() {
            return Err(TmirError::UnsupportedOpcode(format!(
                "SetIn: compact record finite-set membership requires compatible record shape, got value {value_shape:?} and set element {set_element_shape:?}"
            )));
        }

        let mut fields = Vec::with_capacity(set_fields.len());
        for (set_field_idx, (field_name, set_field_shape)) in set_fields.iter().enumerate() {
            let Some((compact_offset, value_field_shape)) =
                value_shape.compact_record_field(*field_name)
            else {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: compact record finite-set membership missing field {field_name:?} in value shape {value_shape:?}"
                )));
            };
            let (Some(value_field_shape), Some(set_field_shape)) =
                (value_field_shape.as_ref(), set_field_shape.as_deref())
            else {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: compact record finite-set membership requires tracked field shape for {field_name:?}"
                )));
            };
            if !Self::is_single_slot_flat_aggregate_value(value_field_shape)
                || !Self::is_single_slot_flat_aggregate_value(set_field_shape)
                || !Self::compatible_flat_aggregate_value(value_field_shape, set_field_shape)
            {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: compact record finite-set membership incompatible field {field_name:?}: value {value_field_shape:?}, set element {set_field_shape:?}"
                )));
            }
            fields.push((
                compact_offset,
                u32::try_from(set_field_idx).expect("record field index must fit in u32"),
            ));
        }

        Ok(fields)
    }

    fn lower_compact_record_materialized_set_membership(
        &mut self,
        block_idx: usize,
        rd: u8,
        source_slot: super::CompactStateSlot,
        value_shape: &super::AggregateShape,
        set_reg: u8,
        set_len: u32,
        set_element_shape: Option<&super::AggregateShape>,
    ) -> Result<Option<usize>, TmirError> {
        let fields = Self::compact_record_materialized_set_fields(value_shape, set_element_shape)?;
        if fields.is_empty() {
            self.store_reg_imm(block_idx, rd, if set_len == 0 { 0 } else { 1 })?;
            return Ok(Some(block_idx));
        }

        let set_ptr = self.load_reg_as_ptr(block_idx, set_reg)?;
        let mut found = self.emit_i64_const(block_idx, 0);
        for elem_idx in 0..set_len {
            let record_value = self.load_at_offset(block_idx, set_ptr, elem_idx + 1);
            let record_ptr = self.i64_value_as_ptr(block_idx, record_value);
            let mut record_matches: Option<ValueId> = None;
            for (compact_offset, set_field_idx) in &fields {
                let value_field = self.load_at_offset(
                    block_idx,
                    source_slot.source_ptr,
                    source_slot.offset + *compact_offset,
                );
                let set_field = self.load_at_offset(block_idx, record_ptr, *set_field_idx);
                let eq = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        lhs: value_field,
                        rhs: set_field,
                    },
                );
                let eq_i64 = self.emit_bool_to_i64(block_idx, eq);
                record_matches = Some(match record_matches {
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
            found = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    lhs: found,
                    rhs: record_matches.expect("non-empty record must produce equality result"),
                },
            );
        }

        self.store_reg_value(block_idx, rd, found)?;
        Ok(Some(block_idx))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_compact_record_materialized_set_membership_branch(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        record_base_slot: ValueId,
        value_shape: &super::AggregateShape,
        set_ptr: ValueId,
        set_len: u32,
        set_element_shape: Option<&super::AggregateShape>,
        success_target: BlockId,
        failure_target: BlockId,
    ) -> Result<(), TmirError> {
        let fields = Self::compact_record_materialized_set_fields(value_shape, set_element_shape)?;
        if fields.is_empty() {
            self.emit(
                block_idx,
                InstrNode::new(Inst::Br {
                    target: if set_len == 0 {
                        failure_target
                    } else {
                        success_target
                    },
                    args: vec![],
                }),
            );
            return Ok(());
        }

        let mut found = self.emit_i64_const(block_idx, 0);
        for elem_idx in 0..set_len {
            let record_value = self.load_at_offset(block_idx, set_ptr, elem_idx + 1);
            let record_ptr = self.i64_value_as_ptr(block_idx, record_value);
            let mut record_matches: Option<ValueId> = None;
            for (compact_offset, set_field_idx) in &fields {
                let field_offset = self.emit_i64_const(block_idx, i64::from(*compact_offset));
                let field_slot = self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: record_base_slot,
                        rhs: field_offset,
                    },
                );
                let value_field = self.load_at_dynamic_offset(block_idx, source_ptr, field_slot);
                let set_field = self.load_at_offset(block_idx, record_ptr, *set_field_idx);
                let eq = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        lhs: value_field,
                        rhs: set_field,
                    },
                );
                let eq_i64 = self.emit_bool_to_i64(block_idx, eq);
                record_matches = Some(match record_matches {
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
            found = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    lhs: found,
                    rhs: record_matches.expect("non-empty record must produce equality result"),
                },
            );
        }

        self.branch_on_i64_truth(block_idx, found, success_target, failure_target);
        Ok(())
    }

    fn lower_symbolic_domain_membership(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_reg: u8,
        domain: super::SymbolicDomain,
    ) -> Result<(), TmirError> {
        let elem_val = self.load_reg(block_idx, elem_reg)?;
        let elem_shape = self.aggregate_shapes.get(&elem_reg).cloned();
        let member = self.emit_symbolic_domain_membership_i64(
            block_idx,
            elem_val,
            elem_shape.as_ref(),
            domain,
        )?;
        self.store_reg_value(block_idx, rd, member)
    }

    fn ensure_materialized_set_reg(&self, reg: u8, context: &str) -> Result<(), TmirError> {
        match self.aggregate_shapes.get(&reg) {
            Some(super::AggregateShape::StateValue) => Ok(()),
            Some(super::AggregateShape::SetBitmask { .. }) => {
                Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: compact SetBitmask in r{reg} is a raw mask, not a materialized set aggregate"
                )))
            }
            Some(shape) if shape.is_finite_set_shape() => Ok(()),
            Some(shape) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: expected tracked finite set or state value in r{reg}, got {shape:?}"
            ))),
            None => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: expected tracked finite set or state value in r{reg}"
            ))),
        }
    }

    fn reject_lazy_set_operand(&self, op: &str, reg: u8) -> Result<(), TmirError> {
        if let Some(shape) = self.aggregate_shapes.get(&reg) {
            if shape.is_lazy_set_shape() {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{op}: lazy set shape is only supported by SetIn membership, got r{reg} = {shape:?}"
                )));
            }
            if matches!(shape, super::AggregateShape::SetBitmask { .. }) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{op}: compact SetBitmask operands require mask-native lowering, got r{reg} = {shape:?}"
                )));
            }
        }
        Ok(())
    }

    fn lower_powerset_membership(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_reg: u8,
        powerset_reg: u8,
        base_shape: super::AggregateShape,
    ) -> Result<Option<usize>, TmirError> {
        base_shape.validate_powerset_base("SetIn: SUBSET membership")?;

        if let Some(elem_shape @ super::AggregateShape::SetBitmask { .. }) =
            self.aggregate_shapes.get(&elem_reg).cloned()
        {
            let Some((universe_len, universe)) = elem_shape.set_bitmask_universe() else {
                return Err(TmirError::UnsupportedOpcode(
                    "SetIn: SUBSET compact membership requires exact universe metadata".to_owned(),
                ));
            };
            let elem_mask = self.load_reg(block_idx, elem_reg)?;
            let true_blk = self.new_aux_block("powerset_member_compact_true");
            let false_blk = self.new_aux_block("powerset_member_compact_false");
            let merge_blk = self.new_aux_block("powerset_member_compact_merge");
            let true_id = self.block_id_of(true_blk);
            let false_id = self.block_id_of(false_blk);
            let merge_id = self.block_id_of(merge_blk);

            if matches!(&base_shape, super::AggregateShape::SetBitmask { .. }) {
                let base_mask = self.load_reg(block_idx, powerset_reg)?;
                self.lower_compact_bitmask_runtime_powerset_mask_branch(
                    block_idx,
                    elem_mask,
                    base_mask,
                    &base_shape,
                    universe_len,
                    &universe,
                    true_id,
                    false_id,
                    "SetIn: SUBSET compact membership",
                )?;
            } else {
                self.lower_compact_bitmask_powerset_branch(
                    block_idx,
                    elem_mask,
                    &base_shape,
                    universe_len,
                    &universe,
                    true_id,
                    false_id,
                    "SetIn: SUBSET compact membership",
                )?;
            }

            self.store_reg_imm(true_blk, rd, 1)?;
            self.emit(
                true_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );
            self.store_reg_imm(false_blk, rd, 0)?;
            self.emit(
                false_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );
            return Ok(Some(merge_blk));
        }

        if let super::AggregateShape::SetBitmask {
            universe_len,
            universe,
        } = &base_shape
        {
            let (block_idx, elem_mask, elem_in_universe) = self
                .emit_set_subseteq_operand_bitmask_i64(
                    block_idx,
                    elem_reg,
                    *universe_len,
                    universe,
                    "SetIn: SUBSET compact base membership",
                )?;
            let base_mask = self.load_reg(block_idx, powerset_reg)?;
            let true_blk = self.new_aux_block("powerset_member_compact_base_true");
            let false_blk = self.new_aux_block("powerset_member_compact_base_false");
            let merge_blk = self.new_aux_block("powerset_member_compact_base_merge");
            let true_id = self.block_id_of(true_blk);
            let false_id = self.block_id_of(false_blk);
            let merge_id = self.block_id_of(merge_blk);

            self.lower_set_bitmask_subseteq_mask_branch(
                block_idx,
                elem_mask,
                elem_in_universe,
                base_mask,
                *universe_len,
                true_id,
                false_id,
                "SetIn: SUBSET compact base membership",
            )?;

            self.store_reg_imm(true_blk, rd, 1)?;
            self.emit(
                true_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );
            self.store_reg_imm(false_blk, rd, 0)?;
            self.emit(
                false_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );
            return Ok(Some(merge_blk));
        }

        self.ensure_materialized_set_reg(elem_reg, "SetIn: SUBSET membership element")?;

        let elem_ptr = self.load_reg_as_ptr(block_idx, elem_reg)?;
        // Powerset registers carry the base set pointer as their runtime value.
        let base_ptr = self.load_reg_as_ptr(block_idx, powerset_reg)?;

        let true_blk = self.new_aux_block("powerset_member_true");
        let false_blk = self.new_aux_block("powerset_member_false");
        let merge_blk = self.new_aux_block("powerset_member_merge");
        let true_id = self.block_id_of(true_blk);
        let false_id = self.block_id_of(false_blk);
        let merge_id = self.block_id_of(merge_blk);

        self.lower_subseteq_ptr_branch(
            block_idx,
            elem_ptr,
            base_ptr,
            true_id,
            false_id,
            "powerset_member",
        );

        self.store_reg_imm(true_blk, rd, 1)?;
        self.emit(
            true_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        self.store_reg_imm(false_blk, rd, 0)?;
        self.emit(
            false_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge_blk))
    }

    fn lower_seq_set_membership(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_reg: u8,
        seq_set_reg: u8,
        base_shape: super::AggregateShape,
    ) -> Result<Option<usize>, TmirError> {
        base_shape.validate_seq_base("SetIn: Seq membership")?;
        let elem_shape = self.aggregate_shapes.get(&elem_reg).cloned();
        if let (Some(source_slot), Some(seq_shape @ super::AggregateShape::Sequence { .. })) = (
            self.compact_state_slot_for_use(block_idx, elem_reg)?,
            elem_shape.as_ref(),
        ) {
            return self.lower_compact_sequence_seq_set_membership_to_reg(
                block_idx,
                rd,
                source_slot,
                seq_shape,
                seq_set_reg,
                base_shape,
            );
        }

        let seq_element_shape = match elem_shape {
            Some(super::AggregateShape::Sequence { element, .. }) => element.as_deref().cloned(),
            Some(super::AggregateShape::StateValue) | None => None,
            Some(other) => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: Seq membership requires sequence element shape, got {other:?}"
                )));
            }
        };

        let seq_ptr = self.load_reg_as_ptr(block_idx, elem_reg)?;
        // Seq(S) carries S's runtime payload unchanged; compact bases are masks.
        let base_value = if Self::lazy_domain_runtime_payload_is_compact_mask(&base_shape) {
            self.load_reg(block_idx, seq_set_reg)?
        } else {
            self.load_reg_as_ptr(block_idx, seq_set_reg)?
        };

        let true_blk = self.new_aux_block("seqset_member_true");
        let false_blk = self.new_aux_block("seqset_member_false");
        let merge_blk = self.new_aux_block("seqset_member_merge");
        let true_id = self.block_id_of(true_blk);
        let false_id = self.block_id_of(false_blk);
        let merge_id = self.block_id_of(merge_blk);

        self.lower_seq_ptr_in_seq_set_ptr_branch(
            block_idx,
            seq_ptr,
            seq_element_shape.as_ref(),
            base_value,
            base_shape,
            true_id,
            false_id,
            "seqset_member",
        )?;

        self.store_reg_imm(true_blk, rd, 1)?;
        self.emit(
            true_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        self.store_reg_imm(false_blk, rd, 0)?;
        self.emit(
            false_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge_blk))
    }

    fn lower_compact_sequence_seq_set_membership_to_reg(
        &mut self,
        block_idx: usize,
        rd: u8,
        source_slot: super::CompactStateSlot,
        seq_shape: &super::AggregateShape,
        seq_set_reg: u8,
        base_shape: super::AggregateShape,
    ) -> Result<Option<usize>, TmirError> {
        let true_blk = self.new_aux_block("compact_seqset_member_true");
        let false_blk = self.new_aux_block("compact_seqset_member_false");
        let merge_blk = self.new_aux_block("compact_seqset_member_merge");
        let true_id = self.block_id_of(true_blk);
        let false_id = self.block_id_of(false_blk);
        let merge_id = self.block_id_of(merge_blk);

        let seq_base_slot = self.emit_i64_const(block_idx, i64::from(source_slot.offset));
        let base_value = if Self::lazy_domain_runtime_payload_is_compact_mask(&base_shape) {
            self.load_reg(block_idx, seq_set_reg)?
        } else {
            self.load_reg_as_ptr(block_idx, seq_set_reg)?
        };
        self.lower_compact_sequence_value_in_seq_set_branch(
            block_idx,
            source_slot.source_ptr,
            seq_base_slot,
            Some(seq_shape),
            base_value,
            base_shape,
            true_id,
            false_id,
            "compact_seqset_member",
        )?;

        self.store_reg_imm(true_blk, rd, 1)?;
        self.emit(
            true_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );
        self.store_reg_imm(false_blk, rd, 0)?;
        self.emit(
            false_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge_blk))
    }

    fn lower_seq_value_in_seq_set_ptr_branch(
        &mut self,
        block_idx: usize,
        seq_value: ValueId,
        seq_element_shape: Option<&super::AggregateShape>,
        base_value: ValueId,
        base_shape: super::AggregateShape,
        success_target: BlockId,
        failure_target: BlockId,
        prefix: &str,
    ) -> Result<(), TmirError> {
        let seq_ptr = self.i64_value_as_ptr(block_idx, seq_value);
        self.lower_seq_ptr_in_seq_set_ptr_branch(
            block_idx,
            seq_ptr,
            seq_element_shape,
            base_value,
            base_shape,
            success_target,
            failure_target,
            prefix,
        )
    }

    fn lower_seq_ptr_in_seq_set_ptr_branch(
        &mut self,
        block_idx: usize,
        seq_ptr: ValueId,
        seq_element_shape: Option<&super::AggregateShape>,
        base_value: ValueId,
        base_shape: super::AggregateShape,
        success_target: BlockId,
        failure_target: BlockId,
        prefix: &str,
    ) -> Result<(), TmirError> {
        base_shape.validate_seq_base(prefix)?;

        let zero = self.emit_i64_const(block_idx, 0);
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

        let loop_hdr = self.new_aux_block(&format!("{prefix}_seq_hdr"));
        let loop_body = self.new_aux_block(&format!("{prefix}_seq_body"));
        let loop_inc = self.new_aux_block(&format!("{prefix}_seq_inc"));
        let loop_hdr_id = self.block_id_of(loop_hdr);
        let loop_body_id = self.block_id_of(loop_body);
        let loop_inc_id = self.block_id_of(loop_inc);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        let idx = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let seq_len = self.load_at_offset(loop_hdr, seq_ptr, 0);
        let in_bounds = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: idx,
                rhs: seq_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: loop_body_id,
                then_args: vec![],
                else_target: success_target,
                else_args: vec![],
            }),
        );

        let idx_body = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_body, 1);
        let slot_idx = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: idx_body,
                rhs: one,
            },
        );
        let elem = self.load_at_dynamic_offset(loop_body, seq_ptr, slot_idx);
        match base_shape {
            super::AggregateShape::SetBitmask {
                universe_len,
                universe,
            } => self.lower_scalar_in_set_bitmask_shape_branch(
                loop_body,
                elem,
                seq_element_shape,
                base_value,
                universe_len,
                &universe,
                loop_inc_id,
                failure_target,
                &format!("{prefix}_elem"),
            )?,
            base_shape => self.lower_value_in_domain_ptr_branch(
                loop_body,
                elem,
                seq_element_shape,
                base_value,
                base_shape,
                loop_inc_id,
                failure_target,
                &format!("{prefix}_elem"),
            )?,
        }

        let idx_inc = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_inc, 1);
        let next_idx = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: idx_inc,
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
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        Ok(())
    }

    fn lower_value_in_set_ptr_branch(
        &mut self,
        block_idx: usize,
        elem_val: ValueId,
        set_ptr: ValueId,
        success_target: BlockId,
        failure_target: BlockId,
        prefix: &str,
    ) {
        let set_len = self.load_at_offset(block_idx, set_ptr, 0);
        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

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

        let loop_header = self.new_aux_block(&format!("{prefix}_setin_header"));
        let loop_body = self.new_aux_block(&format!("{prefix}_setin_body"));
        let loop_inc = self.new_aux_block(&format!("{prefix}_setin_inc"));
        let header_id = self.block_id_of(loop_header);
        let body_id = self.block_id_of(loop_body);
        let inc_id = self.block_id_of(loop_inc);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: header_id,
                args: vec![],
            }),
        );

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
                rhs: set_len,
            },
        );
        self.emit(
            loop_header,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: body_id,
                then_args: vec![],
                else_target: failure_target,
                else_args: vec![],
            }),
        );

        let cur_idx2 = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot_idx = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cur_idx2,
                rhs: one,
            },
        );
        let set_elem = self.load_at_dynamic_offset(loop_body, set_ptr, slot_idx);
        let eq = self.emit_with_result(
            loop_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: set_elem,
                rhs: elem_val,
            },
        );
        self.emit(
            loop_body,
            InstrNode::new(Inst::CondBr {
                cond: eq,
                then_target: success_target,
                then_args: vec![],
                else_target: inc_id,
                else_args: vec![],
            }),
        );

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
    }

    fn lower_value_in_domain_ptr_branch(
        &mut self,
        block_idx: usize,
        elem_val: ValueId,
        elem_shape: Option<&super::AggregateShape>,
        domain_ptr: ValueId,
        domain_shape: super::AggregateShape,
        success_target: BlockId,
        failure_target: BlockId,
        prefix: &str,
    ) -> Result<(), TmirError> {
        let domain_shape = Self::materialized_domain_shape_for_pointer(domain_shape);
        match domain_shape {
            super::AggregateShape::Interval { lo, hi } => {
                let member = self.emit_interval_membership_i64(block_idx, elem_val, lo, hi);
                self.branch_on_i64_truth(block_idx, member, success_target, failure_target);
            }
            super::AggregateShape::Set { .. }
            | super::AggregateShape::ExactIntSet { .. }
            | super::AggregateShape::FiniteSet
            | super::AggregateShape::BoundedSet { .. } => {
                self.lower_value_in_set_ptr_branch(
                    block_idx,
                    elem_val,
                    domain_ptr,
                    success_target,
                    failure_target,
                    prefix,
                );
            }
            super::AggregateShape::SymbolicDomain(domain) => {
                let member = self
                    .emit_symbolic_domain_membership_i64(block_idx, elem_val, elem_shape, domain)?;
                self.branch_on_i64_truth(block_idx, member, success_target, failure_target);
            }
            super::AggregateShape::RecordSet { fields } => {
                self.lower_record_value_in_record_set_ptr_branch(
                    block_idx,
                    elem_val,
                    domain_ptr,
                    fields,
                    success_target,
                    failure_target,
                )?;
            }
            super::AggregateShape::Powerset { base } => {
                base.validate_powerset_base(&format!("{prefix}: SUBSET base"))?;
                if let Some(elem_shape @ super::AggregateShape::SetBitmask { .. }) = elem_shape {
                    let Some((universe_len, universe)) = elem_shape.set_bitmask_universe() else {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "{prefix}: SUBSET compact membership requires exact universe metadata"
                        )));
                    };
                    if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) {
                        self.lower_compact_bitmask_runtime_powerset_mask_branch(
                            block_idx,
                            elem_val,
                            domain_ptr,
                            &base,
                            universe_len,
                            &universe,
                            success_target,
                            failure_target,
                            prefix,
                        )?;
                    } else {
                        self.lower_compact_bitmask_powerset_branch(
                            block_idx,
                            elem_val,
                            &base,
                            universe_len,
                            &universe,
                            success_target,
                            failure_target,
                            prefix,
                        )?;
                    }
                } else {
                    if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) {
                        return Err(TmirError::UnsupportedOpcode(format!(
                            "{prefix}: compact SUBSET membership requires SetBitmask element shape, got {elem_shape:?}"
                        )));
                    }
                    let elem_ptr = self.i64_value_as_ptr(block_idx, elem_val);
                    self.lower_subseteq_ptr_branch(
                        block_idx,
                        elem_ptr,
                        domain_ptr,
                        success_target,
                        failure_target,
                        prefix,
                    );
                }
            }
            super::AggregateShape::FunctionSet { domain, range } => {
                self.lower_function_like_value_in_function_set_ptr_branch(
                    block_idx,
                    elem_val,
                    elem_shape,
                    domain_ptr,
                    *domain,
                    *range,
                    success_target,
                    failure_target,
                    prefix,
                )?;
            }
            super::AggregateShape::SeqSet { base } => {
                let seq_element_shape = match elem_shape {
                    Some(super::AggregateShape::Sequence { element, .. }) => element.as_deref(),
                    _ => None,
                };
                self.lower_seq_value_in_seq_set_ptr_branch(
                    block_idx,
                    elem_val,
                    seq_element_shape,
                    domain_ptr,
                    *base,
                    success_target,
                    failure_target,
                    prefix,
                )?;
            }
            other => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{prefix}: unsupported membership domain shape: {other:?}"
                )));
            }
        }
        Ok(())
    }

    fn branch_on_i64_truth(
        &mut self,
        block_idx: usize,
        value: ValueId,
        success_target: BlockId,
        failure_target: BlockId,
    ) {
        let zero = self.emit_i64_const(block_idx, 0);
        let is_true = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: value,
                rhs: zero,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: is_true,
                then_target: success_target,
                then_args: vec![],
                else_target: failure_target,
                else_args: vec![],
            }),
        );
    }

    fn lower_subseteq_ptr_branch(
        &mut self,
        block_idx: usize,
        set1_ptr: ValueId,
        set2_ptr: ValueId,
        success_target: BlockId,
        failure_target: BlockId,
        prefix: &str,
    ) {
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

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

        let outer_hdr = self.new_aux_block(&format!("{prefix}_subseteq_outer_hdr"));
        let outer_body = self.new_aux_block(&format!("{prefix}_subseteq_outer_body"));
        let inner_hdr = self.new_aux_block(&format!("{prefix}_subseteq_inner_hdr"));
        let inner_body = self.new_aux_block(&format!("{prefix}_subseteq_inner_body"));
        let inner_inc = self.new_aux_block(&format!("{prefix}_subseteq_inner_inc"));
        let outer_inc = self.new_aux_block(&format!("{prefix}_subseteq_outer_inc"));

        let outer_hdr_id = self.block_id_of(outer_hdr);
        let outer_body_id = self.block_id_of(outer_body);
        let inner_hdr_id = self.block_id_of(inner_hdr);
        let inner_body_id = self.block_id_of(inner_body);
        let inner_inc_id = self.block_id_of(inner_inc);
        let outer_inc_id = self.block_id_of(outer_inc);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: outer_hdr_id,
                args: vec![],
            }),
        );

        let i_val = self.emit_with_result(
            outer_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp = self.emit_with_result(
            outer_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: len1,
            },
        );
        self.emit(
            outer_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: outer_body_id,
                then_args: vec![],
                else_target: success_target,
                else_args: vec![],
            }),
        );

        let i_val2 = self.emit_with_result(
            outer_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot = self.emit_with_result(
            outer_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        let elem1 = self.load_at_dynamic_offset(outer_body, set1_ptr, slot);

        let j_alloca = self.emit_with_result(
            outer_body,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            outer_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: j_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            outer_body,
            InstrNode::new(Inst::Br {
                target: inner_hdr_id,
                args: vec![],
            }),
        );

        let j_val = self.emit_with_result(
            inner_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp2 = self.emit_with_result(
            inner_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: j_val,
                rhs: len2,
            },
        );
        self.emit(
            inner_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp2,
                then_target: inner_body_id,
                then_args: vec![],
                else_target: failure_target,
                else_args: vec![],
            }),
        );

        let j_val2 = self.emit_with_result(
            inner_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot2 = self.emit_with_result(
            inner_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: j_val2,
                rhs: one,
            },
        );
        let elem2 = self.load_at_dynamic_offset(inner_body, set2_ptr, slot2);
        let eq = self.emit_with_result(
            inner_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: elem1,
                rhs: elem2,
            },
        );
        self.emit(
            inner_body,
            InstrNode::new(Inst::CondBr {
                cond: eq,
                then_target: outer_inc_id,
                then_args: vec![],
                else_target: inner_inc_id,
                else_args: vec![],
            }),
        );

        let j_val3 = self.emit_with_result(
            inner_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_j = self.emit_with_result(
            inner_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: j_val3,
                rhs: one,
            },
        );
        self.emit(
            inner_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: j_alloca,
                value: next_j,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            inner_inc,
            InstrNode::new(Inst::Br {
                target: inner_hdr_id,
                args: vec![],
            }),
        );

        let i_val3 = self.emit_with_result(
            outer_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_i = self.emit_with_result(
            outer_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val3,
                rhs: one,
            },
        );
        self.emit(
            outer_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            outer_inc,
            InstrNode::new(Inst::Br {
                target: outer_hdr_id,
                args: vec![],
            }),
        );
    }

    fn lower_function_like_set_membership_to_reg(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_reg: u8,
        funcset_reg: u8,
        elem_shape: Option<&super::AggregateShape>,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
    ) -> Result<Option<usize>, TmirError> {
        let true_blk = self.new_aux_block("funcset_member_true");
        let false_blk = self.new_aux_block("funcset_member_false");
        let merge_blk = self.new_aux_block("funcset_member_merge");
        let true_id = self.block_id_of(true_blk);
        let false_id = self.block_id_of(false_blk);
        let merge_id = self.block_id_of(merge_blk);

        let elem_value = self.load_reg(block_idx, elem_reg)?;
        let funcset_ptr = self.load_reg_as_ptr(block_idx, funcset_reg)?;
        self.lower_function_like_value_in_function_set_ptr_branch(
            block_idx,
            elem_value,
            elem_shape,
            funcset_ptr,
            domain_shape,
            range_shape,
            true_id,
            false_id,
            "funcset_member",
        )?;

        self.store_reg_imm(true_blk, rd, 1)?;
        self.emit(
            true_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        self.store_reg_imm(false_blk, rd, 0)?;
        self.emit(
            false_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge_blk))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_compact_sequence_function_set_membership_to_reg(
        &mut self,
        block_idx: usize,
        rd: u8,
        source_slot: super::CompactStateSlot,
        seq_shape: &super::AggregateShape,
        funcset_reg: u8,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
    ) -> Result<Option<usize>, TmirError> {
        let true_blk = self.new_aux_block("compact_seq_funcset_member_true");
        let false_blk = self.new_aux_block("compact_seq_funcset_member_false");
        let merge_blk = self.new_aux_block("compact_seq_funcset_member_merge");
        let true_id = self.block_id_of(true_blk);
        let false_id = self.block_id_of(false_blk);
        let merge_id = self.block_id_of(merge_blk);

        let seq_base_slot = self.emit_i64_const(block_idx, i64::from(source_slot.offset));
        let funcset_ptr = self.load_reg_as_ptr(block_idx, funcset_reg)?;
        self.lower_compact_sequence_value_in_function_set_ptr_branch(
            block_idx,
            source_slot.source_ptr,
            seq_base_slot,
            seq_shape,
            funcset_ptr,
            domain_shape,
            range_shape,
            true_id,
            false_id,
            "compact_seq_funcset_member",
        )?;

        self.store_reg_imm(true_blk, rd, 1)?;
        self.emit(
            true_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );
        self.store_reg_imm(false_blk, rd, 0)?;
        self.emit(
            false_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge_blk))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_compact_sequence_value_in_function_set_ptr_branch(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        seq_base_slot: ValueId,
        seq_shape: &super::AggregateShape,
        funcset_ptr: ValueId,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
        then_target: BlockId,
        else_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        domain_shape.validate_powerset_base(&format!("{context}: function-set domain"))?;
        range_shape.validate_function_set_range(&format!("{context}: function-set range"))?;

        let domain_len = domain_shape.tracked_len().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: function-set domain cardinality is not statically known: {domain_shape:?}"
            ))
        })?;
        let super::AggregateShape::Sequence {
            extent: seq_extent,
            element,
        } = seq_shape
        else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact sequence membership requires tracked sequence shape, got {seq_shape:?}"
            )));
        };
        let domain_is_sequence_domain =
            matches!(domain_shape, super::AggregateShape::Interval { lo: 1, .. });
        let seq_capacity = seq_extent.capacity();
        let compatible_domain = seq_extent
            .exact_count()
            .map_or(domain_len <= seq_capacity, |seq_len| seq_len == domain_len);
        if !domain_is_sequence_domain || !compatible_domain {
            self.emit(
                block_idx,
                InstrNode::new(Inst::Br {
                    target: else_target,
                    args: vec![],
                }),
            );
            return Ok(());
        }

        let value_shape = element.as_deref();
        let Some(value_stride) = value_shape.and_then(super::AggregateShape::compact_slot_count)
        else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact sequence membership requires fixed-width element layout, got {value_shape:?}"
            )));
        };

        let range_value = self.load_at_offset(block_idx, funcset_ptr, 1);

        let len_ok_blk = self.new_aux_block("compact_seq_funcset_member_len_ok");
        let loop_hdr = self.new_aux_block("compact_seq_funcset_member_hdr");
        let loop_body = self.new_aux_block("compact_seq_funcset_member_body");
        let range_ok_blk = self.new_aux_block("compact_seq_funcset_member_range_ok");
        let loop_inc = self.new_aux_block("compact_seq_funcset_member_inc");
        let len_ok_id = self.block_id_of(len_ok_blk);
        let loop_hdr_id = self.block_id_of(loop_hdr);
        let loop_body_id = self.block_id_of(loop_body);
        let range_ok_id = self.block_id_of(range_ok_blk);
        let loop_inc_id = self.block_id_of(loop_inc);

        let len_check_blk = self.guard_compact_sequence_dynamic_len_in_bounds(
            block_idx,
            source_ptr,
            seq_base_slot,
            seq_capacity,
            &format!("{context}_sequence_len"),
        );
        let actual_len = self.load_at_dynamic_offset(len_check_blk, source_ptr, seq_base_slot);
        let expected_len_for_cmp = self.emit_i64_const(len_check_blk, i64::from(domain_len));
        let len_matches = self.emit_with_result(
            len_check_blk,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: actual_len,
                rhs: expected_len_for_cmp,
            },
        );
        self.emit(
            len_check_blk,
            InstrNode::new(Inst::CondBr {
                cond: len_matches,
                then_target: len_ok_id,
                then_args: vec![],
                else_target,
                else_args: vec![],
            }),
        );

        let zero = self.emit_i64_const(len_ok_blk, 0);
        let idx_alloca = self.emit_with_result(
            len_ok_blk,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let expected_len = self.emit_i64_const(loop_hdr, i64::from(domain_len));
        let in_bounds = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: expected_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: loop_body_id,
                then_args: vec![],
                else_target: then_target,
                else_args: vec![],
            }),
        );

        let i_body = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let stride = self.emit_i64_const(loop_body, i64::from(value_stride));
        let one = self.emit_i64_const(loop_body, 1);
        let elem_offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: i_body,
                rhs: stride,
            },
        );
        let first_elem_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: seq_base_slot,
                rhs: one,
            },
        );
        let value_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: first_elem_slot,
                rhs: elem_offset,
            },
        );
        let value_val = self.load_at_dynamic_offset(loop_body, source_ptr, value_slot);

        match range_shape {
            super::AggregateShape::Powerset { base } => {
                let (universe_len, universe) =
                    Self::compact_powerset_mask_universe_for_value_shape(value_shape, context)?;
                if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) {
                    self.lower_compact_bitmask_runtime_powerset_mask_branch(
                        loop_body,
                        value_val,
                        range_value,
                        &base,
                        universe_len,
                        &universe,
                        range_ok_id,
                        else_target,
                        context,
                    )?;
                } else {
                    self.lower_compact_bitmask_powerset_branch(
                        loop_body,
                        value_val,
                        &base,
                        universe_len,
                        &universe,
                        range_ok_id,
                        else_target,
                        context,
                    )?;
                }
            }
            super::AggregateShape::Set { .. }
            | super::AggregateShape::ExactIntSet { .. }
            | super::AggregateShape::SetBitmask { .. }
            | super::AggregateShape::FiniteSet
            | super::AggregateShape::BoundedSet { .. }
            | super::AggregateShape::Interval { .. }
            | super::AggregateShape::SymbolicDomain(_) => {
                self.lower_scalar_in_function_set_range_shape_branch(
                    loop_body,
                    value_val,
                    value_shape,
                    range_value,
                    range_shape,
                    range_ok_id,
                    else_target,
                    context,
                )?;
            }
            super::AggregateShape::RecordSet { fields } => {
                let range_ptr = self.i64_value_as_ptr(loop_body, range_value);
                self.lower_compact_record_value_in_record_set_branch(
                    loop_body,
                    source_ptr,
                    value_slot,
                    value_shape,
                    range_ptr,
                    fields,
                    range_ok_id,
                    else_target,
                )?;
            }
            super::AggregateShape::FunctionSet { domain, range } => match value_shape {
                Some(seq_shape @ super::AggregateShape::Sequence { .. }) => {
                    let range_ptr = self.i64_value_as_ptr(loop_body, range_value);
                    self.lower_compact_sequence_value_in_function_set_ptr_branch(
                        loop_body,
                        source_ptr,
                        value_slot,
                        seq_shape,
                        range_ptr,
                        *domain,
                        *range,
                        range_ok_id,
                        else_target,
                        context,
                    )?;
                }
                _ => {
                    let range_ptr = self.i64_value_as_ptr(loop_body, range_value);
                    self.lower_compact_function_value_in_function_set_ptr_branch(
                        loop_body,
                        source_ptr,
                        value_slot,
                        value_shape,
                        range_ptr,
                        *domain,
                        *range,
                        range_ok_id,
                        else_target,
                        context,
                    )?;
                }
            },
            super::AggregateShape::SeqSet { base } => {
                let range_value = if Self::lazy_domain_runtime_payload_is_compact_mask(&base) {
                    range_value
                } else {
                    self.i64_value_as_ptr(loop_body, range_value)
                };
                self.lower_compact_sequence_value_in_seq_set_branch(
                    loop_body,
                    source_ptr,
                    value_slot,
                    value_shape,
                    range_value,
                    *base,
                    range_ok_id,
                    else_target,
                    context,
                )?;
            }
            other => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: unsupported compact sequence function-set range shape: {other:?}"
                )));
            }
        }

        self.emit(
            range_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_inc_id,
                args: vec![],
            }),
        );

        let i_inc = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_inc, 1);
        let next_i = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_inc,
                rhs: one,
            },
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        Ok(())
    }

    fn lower_function_like_value_in_function_set_ptr_branch(
        &mut self,
        block_idx: usize,
        func_value: ValueId,
        elem_shape: Option<&super::AggregateShape>,
        funcset_ptr: ValueId,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
        then_target: BlockId,
        else_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        match elem_shape {
            Some(super::AggregateShape::Sequence { extent, element }) => self
                .lower_sequence_value_in_function_set_ptr_branch(
                    block_idx,
                    func_value,
                    *extent,
                    element.as_deref(),
                    funcset_ptr,
                    domain_shape,
                    range_shape,
                    then_target,
                    else_target,
                    context,
                ),
            Some(super::AggregateShape::Function { value, .. }) => self
                .lower_function_value_in_function_set_ptr_branch(
                    block_idx,
                    func_value,
                    value.as_deref(),
                    funcset_ptr,
                    domain_shape,
                    range_shape,
                    then_target,
                    else_target,
                    context,
                ),
            Some(super::AggregateShape::StateValue) | None => self
                .lower_function_value_in_function_set_ptr_branch(
                    block_idx,
                    func_value,
                    None,
                    funcset_ptr,
                    domain_shape,
                    range_shape,
                    then_target,
                    else_target,
                    context,
                ),
            Some(other) => Err(TmirError::UnsupportedOpcode(format!(
                "{context}: function-set membership requires function or sequence element shape, got {other:?}"
            ))),
        }
    }

    fn lower_sequence_value_in_function_set_ptr_branch(
        &mut self,
        block_idx: usize,
        seq_value: ValueId,
        seq_extent: super::SequenceExtent,
        seq_element_shape: Option<&super::AggregateShape>,
        funcset_ptr: ValueId,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
        then_target: BlockId,
        else_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        domain_shape.validate_powerset_base(&format!("{context}: function-set domain"))?;
        range_shape.validate_function_set_range(&format!("{context}: function-set range"))?;

        let domain_len = domain_shape.tracked_len().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: function-set domain cardinality is not statically known: {domain_shape:?}"
            ))
        })?;
        let domain_is_sequence_domain =
            matches!(domain_shape, super::AggregateShape::Interval { lo: 1, .. });
        let seq_capacity = seq_extent.capacity();
        let compatible_domain = seq_extent
            .exact_count()
            .map_or(domain_len <= seq_capacity, |seq_len| seq_len == domain_len);
        if !domain_is_sequence_domain || !compatible_domain {
            self.emit(
                block_idx,
                InstrNode::new(Inst::Br {
                    target: else_target,
                    args: vec![],
                }),
            );
            return Ok(());
        }

        if matches!(range_shape, super::AggregateShape::Powerset { .. }) {
            let Some(value_shape) = seq_element_shape else {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: SUBSET range membership requires tracked set-valued sequence entries"
                )));
            };
            if !value_shape.is_finite_set_shape() {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: SUBSET range membership requires set-valued sequence entries, got {value_shape:?}"
                )));
            }
        }

        let seq_ptr = self.i64_value_as_ptr(block_idx, seq_value);
        let range_value = self.load_at_offset(block_idx, funcset_ptr, 1);

        let len_ok_blk = self.new_aux_block("seq_funcset_member_len_ok");
        let loop_hdr = self.new_aux_block("seq_funcset_member_hdr");
        let loop_body = self.new_aux_block("seq_funcset_member_body");
        let loop_inc = self.new_aux_block("seq_funcset_member_inc");
        let len_ok_id = self.block_id_of(len_ok_blk);
        let loop_hdr_id = self.block_id_of(loop_hdr);
        let loop_body_id = self.block_id_of(loop_body);
        let loop_inc_id = self.block_id_of(loop_inc);

        let actual_len = self.load_at_offset(block_idx, seq_ptr, 0);
        let expected_len = self.emit_i64_const(block_idx, i64::from(domain_len));
        let len_matches = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: actual_len,
                rhs: expected_len,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: len_matches,
                then_target: len_ok_id,
                then_args: vec![],
                else_target,
                else_args: vec![],
            }),
        );

        let zero = self.emit_i64_const(len_ok_blk, 0);
        let idx_alloca = self.emit_with_result(
            len_ok_blk,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let expected_len = self.emit_i64_const(loop_hdr, i64::from(domain_len));
        let in_bounds = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: expected_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: loop_body_id,
                then_args: vec![],
                else_target: then_target,
                else_args: vec![],
            }),
        );

        let i_body = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_body, 1);
        let value_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_body,
                rhs: one,
            },
        );
        let value_val = self.load_at_dynamic_offset(loop_body, seq_ptr, value_slot);
        self.lower_scalar_in_function_set_range_shape_branch(
            loop_body,
            value_val,
            seq_element_shape,
            range_value,
            range_shape,
            loop_inc_id,
            else_target,
            "seq_funcset_member_range",
        )?;

        let i_inc = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_inc, 1);
        let next_i = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_inc,
                rhs: one,
            },
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        Ok(())
    }

    fn lower_function_value_in_function_set_ptr_branch(
        &mut self,
        block_idx: usize,
        func_value: ValueId,
        function_value_shape: Option<&super::AggregateShape>,
        funcset_ptr: ValueId,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
        then_target: BlockId,
        else_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        domain_shape.validate_powerset_base(&format!("{context}: function-set domain"))?;
        range_shape.validate_function_set_range(&format!("{context}: function-set range"))?;

        let value_shape = function_value_shape.cloned().map(Box::new).or_else(|| {
            super::AggregateShape::function_value_shape_from_range(&range_shape).map(Box::new)
        });
        let domain_len = domain_shape.tracked_len().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: function-set domain cardinality is not statically known: {domain_shape:?}"
            ))
        })?;
        if matches!(range_shape, super::AggregateShape::Powerset { .. }) {
            let Some(value_shape) = value_shape.as_deref() else {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: SUBSET range membership requires tracked set-valued function shape"
                )));
            };
            if !value_shape.is_finite_set_shape() {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: SUBSET range membership requires set-valued function entries, got {value_shape:?}"
                )));
            }
        }

        let func_ptr = self.i64_value_as_ptr(block_idx, func_value);
        let domain_value = self.load_at_offset(block_idx, funcset_ptr, 0);
        let range_value = self.load_at_offset(block_idx, funcset_ptr, 1);
        let domain_ptr = self.i64_value_as_ptr(block_idx, domain_value);

        let len_ok_blk = self.new_aux_block("nested_funcset_member_len_ok");
        let loop_hdr = self.new_aux_block("nested_funcset_member_hdr");
        let loop_body = self.new_aux_block("nested_funcset_member_body");
        let domain_ok_blk = self.new_aux_block("nested_funcset_member_domain_ok");
        let range_ok_blk = self.new_aux_block("nested_funcset_member_range_ok");
        let loop_inc = self.new_aux_block("nested_funcset_member_inc");

        let len_ok_id = self.block_id_of(len_ok_blk);
        let loop_hdr_id = self.block_id_of(loop_hdr);
        let loop_body_id = self.block_id_of(loop_body);
        let domain_ok_id = self.block_id_of(domain_ok_blk);
        let range_ok_id = self.block_id_of(range_ok_blk);
        let loop_inc_id = self.block_id_of(loop_inc);

        let actual_len = self.load_at_offset(block_idx, func_ptr, 0);
        let expected_len = self.emit_i64_const(block_idx, i64::from(domain_len));
        let len_matches = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: actual_len,
                rhs: expected_len,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: len_matches,
                then_target: len_ok_id,
                then_args: vec![],
                else_target,
                else_args: vec![],
            }),
        );

        let zero = self.emit_i64_const(len_ok_blk, 0);
        let idx_alloca = self.emit_with_result(
            len_ok_blk,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let expected_len = self.emit_i64_const(loop_hdr, i64::from(domain_len));
        let in_bounds = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: expected_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: loop_body_id,
                then_args: vec![],
                else_target: then_target,
                else_args: vec![],
            }),
        );

        let i_body = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_body, 1);
        let two = self.emit_i64_const(loop_body, 2);
        let pair_offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: i_body,
                rhs: two,
            },
        );
        let key_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: pair_offset,
                rhs: one,
            },
        );
        let value_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: pair_offset,
                rhs: two,
            },
        );
        let key_val = self.load_at_dynamic_offset(loop_body, func_ptr, key_slot);
        let value_val = self.load_at_dynamic_offset(loop_body, func_ptr, value_slot);
        self.lower_value_in_set_ptr_branch(
            loop_body,
            key_val,
            domain_ptr,
            domain_ok_id,
            else_target,
            "nested_funcset_member_domain",
        );

        match range_shape {
            super::AggregateShape::Powerset { base } => {
                base.validate_powerset_base("nested function-set SUBSET range")?;
                if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) {
                    self.lower_scalar_in_function_set_range_shape_branch(
                        domain_ok_blk,
                        value_val,
                        value_shape.as_deref(),
                        range_value,
                        super::AggregateShape::Powerset { base },
                        range_ok_id,
                        else_target,
                        "nested_funcset_member_range_subset",
                    )?;
                } else {
                    let value_ptr = self.i64_value_as_ptr(domain_ok_blk, value_val);
                    let range_ptr = self.i64_value_as_ptr(domain_ok_blk, range_value);
                    self.lower_subseteq_ptr_branch(
                        domain_ok_blk,
                        value_ptr,
                        range_ptr,
                        range_ok_id,
                        else_target,
                        "nested_funcset_member_range_subset",
                    );
                }
            }
            super::AggregateShape::Set { .. }
            | super::AggregateShape::ExactIntSet { .. }
            | super::AggregateShape::SetBitmask { .. }
            | super::AggregateShape::FiniteSet
            | super::AggregateShape::BoundedSet { .. }
            | super::AggregateShape::Interval { .. } => {
                self.lower_scalar_in_function_set_range_shape_branch(
                    domain_ok_blk,
                    value_val,
                    value_shape.as_deref(),
                    range_value,
                    range_shape,
                    range_ok_id,
                    else_target,
                    "nested_funcset_member_range",
                )?;
            }
            super::AggregateShape::RecordSet { fields } => {
                let range_ptr = self.i64_value_as_ptr(domain_ok_blk, range_value);
                self.lower_record_value_in_record_set_ptr_branch(
                    domain_ok_blk,
                    value_val,
                    range_ptr,
                    fields,
                    range_ok_id,
                    else_target,
                )?;
            }
            super::AggregateShape::SymbolicDomain(domain) => {
                let member = self.emit_symbolic_domain_membership_i64(
                    domain_ok_blk,
                    value_val,
                    value_shape.as_deref(),
                    domain,
                )?;
                let zero = self.emit_i64_const(domain_ok_blk, 0);
                let is_member = self.emit_with_result(
                    domain_ok_blk,
                    Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I64,
                        lhs: member,
                        rhs: zero,
                    },
                );
                self.emit(
                    domain_ok_blk,
                    InstrNode::new(Inst::CondBr {
                        cond: is_member,
                        then_target: range_ok_id,
                        then_args: vec![],
                        else_target,
                        else_args: vec![],
                    }),
                );
            }
            super::AggregateShape::FunctionSet { domain, range } => {
                let range_ptr = self.i64_value_as_ptr(domain_ok_blk, range_value);
                self.lower_function_like_value_in_function_set_ptr_branch(
                    domain_ok_blk,
                    value_val,
                    value_shape.as_deref(),
                    range_ptr,
                    *domain,
                    *range,
                    range_ok_id,
                    else_target,
                    "nested_funcset_member_range_function",
                )?;
            }
            super::AggregateShape::SeqSet { base } => {
                let seq_element_shape = match value_shape.as_deref() {
                    Some(super::AggregateShape::Sequence { element, .. }) => element.as_deref(),
                    _ => None,
                };
                let range_value = if Self::lazy_domain_runtime_payload_is_compact_mask(&base) {
                    range_value
                } else {
                    self.i64_value_as_ptr(domain_ok_blk, range_value)
                };
                self.lower_seq_value_in_seq_set_ptr_branch(
                    domain_ok_blk,
                    value_val,
                    seq_element_shape,
                    range_value,
                    *base,
                    range_ok_id,
                    else_target,
                    "nested_funcset_member_range_seq",
                )?;
            }
            other => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: unsupported function-set range shape: {other:?}"
                )));
            }
        }

        self.emit(
            range_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_inc_id,
                args: vec![],
            }),
        );

        let i_inc = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_inc, 1);
        let next_i = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_inc,
                rhs: one,
            },
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_compact_state_function_set_membership(
        &mut self,
        block_idx: usize,
        rd: u8,
        _elem_reg: u8,
        funcset_reg: u8,
        source_slot: super::CompactStateSlot,
        len: u32,
        value_shape: Option<&super::AggregateShape>,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
    ) -> Result<Option<usize>, TmirError> {
        let domain_len = domain_shape.tracked_len().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "SetIn: compact function-set domain cardinality is not statically known: {domain_shape:?}"
            ))
        })?;
        if len != domain_len {
            self.store_reg_imm(block_idx, rd, 0)?;
            return Ok(Some(block_idx));
        }
        range_shape.validate_function_set_range("SetIn: compact function-set range")?;
        if matches!(range_shape, super::AggregateShape::Powerset { .. }) {
            let Some(value_shape) = value_shape else {
                return Err(TmirError::UnsupportedOpcode(
                    "SetIn: compact function-set SUBSET range requires tracked set-valued function entries"
                        .to_owned(),
                ));
            };
            if !matches!(value_shape, super::AggregateShape::SetBitmask { .. }) {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: compact function-set SUBSET range requires SetBitmask entries, got {value_shape:?}"
                )));
            }
            if value_shape.set_bitmask_universe().is_none() {
                return Err(TmirError::UnsupportedOpcode(
                    "SetIn: compact function-set SUBSET range requires exact universe metadata"
                        .to_owned(),
                ));
            }
        }
        let Some(value_stride) = value_shape.and_then(super::AggregateShape::compact_slot_count)
        else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "SetIn: compact function-set range requires fixed-width value layout, got {value_shape:?}"
            )));
        };

        let funcset_ptr = self.load_reg_as_ptr(block_idx, funcset_reg)?;
        let range_value = self.load_at_offset(block_idx, funcset_ptr, 1);

        let false_blk = self.new_aux_block("compact_funcset_member_false");
        let true_blk = self.new_aux_block("compact_funcset_member_true");
        let merge_blk = self.new_aux_block("compact_funcset_member_merge");
        let loop_hdr = self.new_aux_block("compact_funcset_member_hdr");
        let loop_body = self.new_aux_block("compact_funcset_member_body");
        let range_ok_blk = self.new_aux_block("compact_funcset_member_range_ok");
        let loop_inc = self.new_aux_block("compact_funcset_member_inc");

        let false_id = self.block_id_of(false_blk);
        let true_id = self.block_id_of(true_blk);
        let merge_id = self.block_id_of(merge_blk);
        let loop_hdr_id = self.block_id_of(loop_hdr);
        let loop_body_id = self.block_id_of(loop_body);
        let range_ok_id = self.block_id_of(range_ok_blk);
        let loop_inc_id = self.block_id_of(loop_inc);

        let zero = self.emit_i64_const(block_idx, 0);
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
        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let expected_len = self.emit_i64_const(loop_hdr, i64::from(domain_len));
        let in_bounds = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: expected_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: loop_body_id,
                then_args: vec![],
                else_target: true_id,
                else_args: vec![],
            }),
        );

        let i_body = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let stride = self.emit_i64_const(loop_body, i64::from(value_stride));
        let base = self.emit_i64_const(loop_body, i64::from(source_slot.offset));
        let offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: i_body,
                rhs: stride,
            },
        );
        let value_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: base,
                rhs: offset,
            },
        );
        let value_val = self.load_at_dynamic_offset(loop_body, source_slot.source_ptr, value_slot);

        match range_shape {
            super::AggregateShape::Powerset { base } => {
                let Some(value_shape @ super::AggregateShape::SetBitmask { .. }) = value_shape
                else {
                    return Err(TmirError::UnsupportedOpcode(
                        "SetIn: compact function-set SUBSET range requires SetBitmask entries"
                            .to_owned(),
                    ));
                };
                let Some((universe_len, universe)) = value_shape.set_bitmask_universe() else {
                    return Err(TmirError::UnsupportedOpcode(
                        "SetIn: compact function-set SUBSET range requires exact universe metadata"
                            .to_owned(),
                    ));
                };
                if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) {
                    self.lower_compact_bitmask_runtime_powerset_mask_branch(
                        loop_body,
                        value_val,
                        range_value,
                        &base,
                        universe_len,
                        &universe,
                        range_ok_id,
                        false_id,
                        "compact_funcset_member_range_subset",
                    )?;
                } else {
                    self.lower_compact_bitmask_powerset_branch(
                        loop_body,
                        value_val,
                        &base,
                        universe_len,
                        &universe,
                        range_ok_id,
                        false_id,
                        "compact_funcset_member_range_subset",
                    )?;
                }
            }
            super::AggregateShape::Set { .. }
            | super::AggregateShape::ExactIntSet { .. }
            | super::AggregateShape::SetBitmask { .. }
            | super::AggregateShape::FiniteSet
            | super::AggregateShape::BoundedSet { .. }
            | super::AggregateShape::Interval { .. }
            | super::AggregateShape::SymbolicDomain(_) => {
                self.lower_scalar_in_function_set_range_shape_branch(
                    loop_body,
                    value_val,
                    value_shape,
                    range_value,
                    range_shape,
                    range_ok_id,
                    false_id,
                    "compact_funcset_member_range",
                )?;
            }
            super::AggregateShape::RecordSet { fields } => {
                let range_ptr = self.i64_value_as_ptr(loop_body, range_value);
                self.lower_compact_record_value_in_record_set_branch(
                    loop_body,
                    source_slot.source_ptr,
                    value_slot,
                    value_shape,
                    range_ptr,
                    fields,
                    range_ok_id,
                    false_id,
                )?;
            }
            super::AggregateShape::FunctionSet { domain, range } => {
                let range_ptr = self.i64_value_as_ptr(loop_body, range_value);
                self.lower_compact_function_value_in_function_set_ptr_branch(
                    loop_body,
                    source_slot.source_ptr,
                    value_slot,
                    value_shape,
                    range_ptr,
                    *domain,
                    *range,
                    range_ok_id,
                    false_id,
                    "compact_funcset_member_range_function",
                )?;
            }
            super::AggregateShape::SeqSet { base } => {
                let range_value = if Self::lazy_domain_runtime_payload_is_compact_mask(&base) {
                    range_value
                } else {
                    self.i64_value_as_ptr(loop_body, range_value)
                };
                self.lower_compact_sequence_value_in_seq_set_branch(
                    loop_body,
                    source_slot.source_ptr,
                    value_slot,
                    value_shape,
                    range_value,
                    *base,
                    range_ok_id,
                    false_id,
                    "compact_funcset_member_range_seq",
                )?;
            }
            other => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: unsupported compact function-set range shape: {other:?}"
                )));
            }
        }

        self.emit(
            range_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_inc_id,
                args: vec![],
            }),
        );

        let i_inc = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_inc, 1);
        let next_i = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_inc,
                rhs: one,
            },
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        self.store_reg_imm(true_blk, rd, 1)?;
        self.emit(
            true_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );
        self.store_reg_imm(false_blk, rd, 0)?;
        self.emit(
            false_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge_blk))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_compact_function_value_in_function_set_ptr_branch(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        func_base_slot: ValueId,
        function_shape: Option<&super::AggregateShape>,
        funcset_ptr: ValueId,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
        then_target: BlockId,
        else_target: BlockId,
        context: &str,
    ) -> Result<(), TmirError> {
        domain_shape.validate_powerset_base(&format!("{context}: function-set domain"))?;
        range_shape.validate_function_set_range(&format!("{context}: function-set range"))?;

        let domain_len = domain_shape.tracked_len().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "{context}: function-set domain cardinality is not statically known: {domain_shape:?}"
            ))
        })?;
        let Some(super::AggregateShape::Function { len, value, .. }) = function_shape else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact nested function membership requires tracked function shape, got {function_shape:?}"
            )));
        };
        if *len != domain_len {
            self.emit(
                block_idx,
                InstrNode::new(Inst::Br {
                    target: else_target,
                    args: vec![],
                }),
            );
            return Ok(());
        }
        let value_shape = value.as_deref();
        let Some(value_stride) = value_shape.and_then(super::AggregateShape::compact_slot_count)
        else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{context}: compact nested function requires fixed-width value layout, got {value_shape:?}"
            )));
        };

        let range_value = self.load_at_offset(block_idx, funcset_ptr, 1);

        let loop_hdr = self.new_aux_block(&format!("{context}_hdr"));
        let loop_body = self.new_aux_block(&format!("{context}_body"));
        let range_ok_blk = self.new_aux_block(&format!("{context}_range_ok"));
        let loop_inc = self.new_aux_block(&format!("{context}_inc"));

        let loop_hdr_id = self.block_id_of(loop_hdr);
        let loop_body_id = self.block_id_of(loop_body);
        let range_ok_id = self.block_id_of(range_ok_blk);
        let loop_inc_id = self.block_id_of(loop_inc);

        let zero = self.emit_i64_const(block_idx, 0);
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
        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let expected_len = self.emit_i64_const(loop_hdr, i64::from(domain_len));
        let in_bounds = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: expected_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: loop_body_id,
                then_args: vec![],
                else_target: then_target,
                else_args: vec![],
            }),
        );

        let i_body = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let stride = self.emit_i64_const(loop_body, i64::from(value_stride));
        let offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: i_body,
                rhs: stride,
            },
        );
        let value_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: func_base_slot,
                rhs: offset,
            },
        );
        let value_val = self.load_at_dynamic_offset(loop_body, source_ptr, value_slot);

        match range_shape {
            super::AggregateShape::Powerset { base } => {
                let Some(value_shape @ super::AggregateShape::SetBitmask { .. }) = value_shape
                else {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SUBSET range requires SetBitmask entries, got {value_shape:?}"
                    )));
                };
                let Some((universe_len, universe)) = value_shape.set_bitmask_universe() else {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "{context}: compact SUBSET range requires exact universe metadata"
                    )));
                };
                if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) {
                    self.lower_compact_bitmask_runtime_powerset_mask_branch(
                        loop_body,
                        value_val,
                        range_value,
                        &base,
                        universe_len,
                        &universe,
                        range_ok_id,
                        else_target,
                        context,
                    )?;
                } else {
                    self.lower_compact_bitmask_powerset_branch(
                        loop_body,
                        value_val,
                        &base,
                        universe_len,
                        &universe,
                        range_ok_id,
                        else_target,
                        context,
                    )?;
                }
            }
            super::AggregateShape::Set { .. }
            | super::AggregateShape::ExactIntSet { .. }
            | super::AggregateShape::SetBitmask { .. }
            | super::AggregateShape::FiniteSet
            | super::AggregateShape::BoundedSet { .. }
            | super::AggregateShape::Interval { .. }
            | super::AggregateShape::SymbolicDomain(_) => {
                self.lower_scalar_in_function_set_range_shape_branch(
                    loop_body,
                    value_val,
                    value_shape,
                    range_value,
                    range_shape,
                    range_ok_id,
                    else_target,
                    context,
                )?;
            }
            super::AggregateShape::RecordSet { fields } => {
                let range_ptr = self.i64_value_as_ptr(loop_body, range_value);
                self.lower_compact_record_value_in_record_set_branch(
                    loop_body,
                    source_ptr,
                    value_slot,
                    value_shape,
                    range_ptr,
                    fields,
                    range_ok_id,
                    else_target,
                )?;
            }
            super::AggregateShape::FunctionSet { domain, range } => {
                let range_ptr = self.i64_value_as_ptr(loop_body, range_value);
                self.lower_compact_function_value_in_function_set_ptr_branch(
                    loop_body,
                    source_ptr,
                    value_slot,
                    value_shape,
                    range_ptr,
                    *domain,
                    *range,
                    range_ok_id,
                    else_target,
                    context,
                )?;
            }
            super::AggregateShape::SeqSet { base } => {
                let range_value = if Self::lazy_domain_runtime_payload_is_compact_mask(&base) {
                    range_value
                } else {
                    self.i64_value_as_ptr(loop_body, range_value)
                };
                self.lower_compact_sequence_value_in_seq_set_branch(
                    loop_body,
                    source_ptr,
                    value_slot,
                    value_shape,
                    range_value,
                    *base,
                    range_ok_id,
                    else_target,
                    context,
                )?;
            }
            other => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{context}: unsupported compact nested function-set range shape: {other:?}"
                )));
            }
        }

        self.emit(
            range_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_inc_id,
                args: vec![],
            }),
        );
        let i_inc = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_inc, 1);
        let next_i = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_inc,
                rhs: one,
            },
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_compact_sequence_value_in_seq_set_branch(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        seq_base_slot: ValueId,
        seq_shape: Option<&super::AggregateShape>,
        base_value: ValueId,
        base_shape: super::AggregateShape,
        success_target: BlockId,
        failure_target: BlockId,
        prefix: &str,
    ) -> Result<(), TmirError> {
        base_shape.validate_seq_base(prefix)?;
        let Some(super::AggregateShape::Sequence { extent, element }) = seq_shape else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{prefix}: compact Seq membership requires tracked sequence shape, got {seq_shape:?}"
            )));
        };
        let element_shape = element.as_deref();
        let Some(element_stride) =
            element_shape.and_then(super::AggregateShape::compact_slot_count)
        else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "{prefix}: compact Seq membership requires fixed-width element layout, got {element_shape:?}"
            )));
        };

        let len_ok_blk = self.guard_compact_sequence_dynamic_len_in_bounds(
            block_idx,
            source_ptr,
            seq_base_slot,
            extent.capacity(),
            &format!("{prefix}_seq_len"),
        );
        let loop_hdr = self.new_aux_block(&format!("{prefix}_seq_hdr"));
        let loop_body = self.new_aux_block(&format!("{prefix}_seq_body"));
        let elem_ok_blk = self.new_aux_block(&format!("{prefix}_seq_elem_ok"));
        let loop_inc = self.new_aux_block(&format!("{prefix}_seq_inc"));
        let loop_hdr_id = self.block_id_of(loop_hdr);
        let loop_body_id = self.block_id_of(loop_body);
        let elem_ok_id = self.block_id_of(elem_ok_blk);
        let loop_inc_id = self.block_id_of(loop_inc);

        let idx_alloca = self.emit_with_result(
            len_ok_blk,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        let zero = self.emit_i64_const(len_ok_blk, 0);
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        let idx = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let seq_len = self.load_at_dynamic_offset(loop_hdr, source_ptr, seq_base_slot);
        let in_bounds = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: idx,
                rhs: seq_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: loop_body_id,
                then_args: vec![],
                else_target: success_target,
                else_args: vec![],
            }),
        );

        let idx_body = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_body, 1);
        let stride = self.emit_i64_const(loop_body, i64::from(element_stride));
        let elem_offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: idx_body,
                rhs: stride,
            },
        );
        let first_elem_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: seq_base_slot,
                rhs: one,
            },
        );
        let elem_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: first_elem_slot,
                rhs: elem_offset,
            },
        );
        let elem_val = self.load_at_dynamic_offset(loop_body, source_ptr, elem_slot);

        match base_shape {
            super::AggregateShape::SetBitmask {
                universe_len,
                universe,
            } => {
                self.lower_scalar_in_set_bitmask_shape_branch(
                    loop_body,
                    elem_val,
                    element_shape,
                    base_value,
                    universe_len,
                    &universe,
                    elem_ok_id,
                    failure_target,
                    prefix,
                )?;
            }
            super::AggregateShape::RecordSet { fields } => {
                self.lower_compact_record_value_in_record_set_branch(
                    loop_body,
                    source_ptr,
                    elem_slot,
                    element_shape,
                    base_value,
                    fields,
                    elem_ok_id,
                    failure_target,
                )?;
            }
            super::AggregateShape::Set { len, element } => {
                let base_element_is_record = matches!(
                    element.as_deref(),
                    Some(super::AggregateShape::Record { .. })
                );
                let seq_element_is_record =
                    matches!(element_shape, Some(super::AggregateShape::Record { .. }));
                if base_element_is_record && seq_element_is_record {
                    self.lower_compact_record_materialized_set_membership_branch(
                        loop_body,
                        source_ptr,
                        elem_slot,
                        element_shape.ok_or_else(|| {
                            TmirError::UnsupportedOpcode(format!(
                                "{prefix}: compact Seq finite-record-set membership requires tracked record element shape"
                            ))
                        })?,
                        base_value,
                        len,
                        element.as_deref(),
                        elem_ok_id,
                        failure_target,
                    )?;
                } else if base_element_is_record || seq_element_is_record {
                    self.emit(
                        loop_body,
                        InstrNode::new(Inst::Br {
                            target: failure_target,
                            args: vec![],
                        }),
                    );
                } else {
                    self.lower_value_in_domain_ptr_branch(
                        loop_body,
                        elem_val,
                        element_shape,
                        base_value,
                        super::AggregateShape::Set { len, element },
                        elem_ok_id,
                        failure_target,
                        prefix,
                    )?;
                }
            }
            super::AggregateShape::ExactIntSet { .. }
            | super::AggregateShape::FiniteSet
            | super::AggregateShape::BoundedSet { .. }
            | super::AggregateShape::Interval { .. }
            | super::AggregateShape::SymbolicDomain(_) => {
                self.lower_value_in_domain_ptr_branch(
                    loop_body,
                    elem_val,
                    element_shape,
                    base_value,
                    base_shape,
                    elem_ok_id,
                    failure_target,
                    prefix,
                )?;
            }
            super::AggregateShape::Powerset { base } => {
                let (universe_len, universe) =
                    Self::compact_powerset_mask_universe_for_value_shape(element_shape, prefix)?;
                if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) {
                    self.lower_compact_bitmask_runtime_powerset_mask_branch(
                        loop_body,
                        elem_val,
                        base_value,
                        &base,
                        universe_len,
                        &universe,
                        elem_ok_id,
                        failure_target,
                        prefix,
                    )?;
                } else {
                    self.lower_compact_bitmask_powerset_branch(
                        loop_body,
                        elem_val,
                        &base,
                        universe_len,
                        &universe,
                        elem_ok_id,
                        failure_target,
                        prefix,
                    )?;
                }
            }
            other => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "{prefix}: unsupported compact sequence base shape: {other:?}"
                )));
            }
        }

        self.emit(
            elem_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_inc_id,
                args: vec![],
            }),
        );
        let idx_inc = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_inc, 1);
        let next_idx = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: idx_inc,
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
                target: loop_hdr_id,
                args: vec![],
            }),
        );
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_compact_record_value_in_record_set_branch(
        &mut self,
        block_idx: usize,
        source_ptr: ValueId,
        record_base_slot: ValueId,
        record_shape: Option<&super::AggregateShape>,
        record_set_ptr: ValueId,
        fields: Vec<(tla_core::NameId, super::AggregateShape)>,
        success_target: BlockId,
        failure_target: BlockId,
    ) -> Result<(), TmirError> {
        let Some(record_shape @ super::AggregateShape::Record { .. }) = record_shape else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "compact record-set membership requires tracked record shape, got {record_shape:?}"
            )));
        };
        if fields.is_empty() {
            self.emit(
                block_idx,
                InstrNode::new(Inst::Br {
                    target: success_target,
                    args: vec![],
                }),
            );
            return Ok(());
        }

        let mut result: Option<ValueId> = None;
        for (domain_slot, (field_name, field_set_shape)) in fields.iter().enumerate() {
            let Some((field_idx, field_shape)) = record_shape.compact_record_field(*field_name)
            else {
                self.emit(
                    block_idx,
                    InstrNode::new(Inst::Br {
                        target: failure_target,
                        args: vec![],
                    }),
                );
                return Ok(());
            };
            let field_offset = self.emit_i64_const(block_idx, i64::from(field_idx));
            let field_slot = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: record_base_slot,
                    rhs: field_offset,
                },
            );
            let field_val = self.load_at_dynamic_offset(block_idx, source_ptr, field_slot);
            let field_set_shape =
                Self::materialized_domain_shape_for_pointer(field_set_shape.clone());
            let field_ok = match &field_set_shape {
                super::AggregateShape::Interval { lo, hi } => {
                    self.emit_interval_membership_i64(block_idx, field_val, *lo, *hi)
                }
                super::AggregateShape::Set { len, .. } => {
                    let domain_slot =
                        u32::try_from(domain_slot).expect("record set slot index must fit in u32");
                    let domain_value = self.load_at_offset(block_idx, record_set_ptr, domain_slot);
                    let domain_ptr = self.i64_value_as_ptr(block_idx, domain_value);
                    self.emit_finite_set_membership_i64(block_idx, field_val, domain_ptr, *len)
                }
                super::AggregateShape::SymbolicDomain(domain) => self
                    .emit_symbolic_domain_membership_i64(
                        block_idx,
                        field_val,
                        field_shape.as_ref(),
                        *domain,
                    )?,
                other => {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "compact record-set field domain is not directly lowerable: {other:?}"
                    )));
                }
            };
            result = Some(match result {
                None => field_ok,
                Some(prev) => self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: prev,
                        rhs: field_ok,
                    },
                ),
            });
        }

        self.branch_on_i64_truth(
            block_idx,
            result.expect("non-empty record-set fields must produce a result"),
            success_target,
            failure_target,
        );
        Ok(())
    }

    fn lower_function_set_membership(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_reg: u8,
        funcset_reg: u8,
        domain_shape: super::AggregateShape,
        range_shape: super::AggregateShape,
    ) -> Result<Option<usize>, TmirError> {
        domain_shape.validate_powerset_base("SetIn: function-set domain")?;
        range_shape.validate_function_set_range("SetIn: function-set range")?;

        let elem_shape = self.aggregate_shapes.get(&elem_reg).cloned();
        if let (Some(base_slot), Some(super::AggregateShape::Function { len, value, .. })) = (
            self.compact_state_slot_for_use(block_idx, elem_reg)?,
            elem_shape.clone(),
        ) {
            return self.lower_compact_state_function_set_membership(
                block_idx,
                rd,
                elem_reg,
                funcset_reg,
                base_slot,
                len,
                value.as_deref(),
                domain_shape,
                range_shape,
            );
        }
        if let (Some(source_slot), Some(seq_shape @ super::AggregateShape::Sequence { .. })) = (
            self.compact_state_slot_for_use(block_idx, elem_reg)?,
            elem_shape.as_ref(),
        ) {
            return self.lower_compact_sequence_function_set_membership_to_reg(
                block_idx,
                rd,
                source_slot,
                seq_shape,
                funcset_reg,
                domain_shape,
                range_shape,
            );
        }
        if matches!(elem_shape, Some(super::AggregateShape::Sequence { .. })) {
            return self.lower_function_like_set_membership_to_reg(
                block_idx,
                rd,
                elem_reg,
                funcset_reg,
                elem_shape.as_ref(),
                domain_shape,
                range_shape,
            );
        }
        let value_shape = match elem_shape {
            Some(super::AggregateShape::Function { len, value, .. }) => {
                let domain_len = domain_shape.tracked_len().ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "SetIn: function-set domain cardinality is not statically known: {domain_shape:?}"
                    ))
                })?;
                if len != domain_len {
                    self.store_reg_imm(block_idx, rd, 0)?;
                    return Ok(Some(block_idx));
                }
                value
            }
            Some(super::AggregateShape::StateValue) => {
                let inferred = super::AggregateShape::function_from_function_set_domains(
                    &domain_shape,
                    &range_shape,
                )?;
                let super::AggregateShape::Function { value, .. } = inferred else {
                    unreachable!("function_from_function_set_domains must return Function");
                };
                value
            }
            Some(shape) => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: function-set membership requires tracked function element shape, got {shape:?}"
                )));
            }
            None => {
                return Err(TmirError::UnsupportedOpcode(
                    "SetIn: function-set membership requires tracked function element shape"
                        .to_owned(),
                ));
            }
        };
        let domain_len = domain_shape.tracked_len().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "SetIn: function-set domain cardinality is not statically known: {domain_shape:?}"
            ))
        })?;
        if matches!(range_shape, super::AggregateShape::Powerset { .. }) {
            let Some(value_shape) = value_shape.as_deref() else {
                return Err(TmirError::UnsupportedOpcode(
                    "SetIn: function-set range SUBSET membership requires tracked set-valued function shape"
                        .to_owned(),
                ));
            };
            if !value_shape.is_finite_set_shape() {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: function-set range SUBSET membership requires set-valued function entries, got {value_shape:?}"
                )));
            }
        }

        let func_ptr = self.load_reg_as_ptr(block_idx, elem_reg)?;
        let funcset_ptr = self.load_reg_as_ptr(block_idx, funcset_reg)?;
        let domain_value = self.load_at_offset(block_idx, funcset_ptr, 0);
        let range_value = self.load_at_offset(block_idx, funcset_ptr, 1);
        let domain_ptr = self.i64_value_as_ptr(block_idx, domain_value);

        let false_blk = self.new_aux_block("funcset_member_false");
        let true_blk = self.new_aux_block("funcset_member_true");
        let merge_blk = self.new_aux_block("funcset_member_merge");
        let len_ok_blk = self.new_aux_block("funcset_member_len_ok");
        let loop_hdr = self.new_aux_block("funcset_member_hdr");
        let loop_body = self.new_aux_block("funcset_member_body");
        let domain_ok_blk = self.new_aux_block("funcset_member_domain_ok");
        let range_ok_blk = self.new_aux_block("funcset_member_range_ok");
        let loop_inc = self.new_aux_block("funcset_member_inc");

        let false_id = self.block_id_of(false_blk);
        let true_id = self.block_id_of(true_blk);
        let merge_id = self.block_id_of(merge_blk);
        let len_ok_id = self.block_id_of(len_ok_blk);
        let loop_hdr_id = self.block_id_of(loop_hdr);
        let loop_body_id = self.block_id_of(loop_body);
        let domain_ok_id = self.block_id_of(domain_ok_blk);
        let range_ok_id = self.block_id_of(range_ok_blk);
        let loop_inc_id = self.block_id_of(loop_inc);

        let actual_len = self.load_at_offset(block_idx, func_ptr, 0);
        let expected_len = self.emit_i64_const(block_idx, i64::from(domain_len));
        let len_matches = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: actual_len,
                rhs: expected_len,
            },
        );
        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: len_matches,
                then_target: len_ok_id,
                then_args: vec![],
                else_target: false_id,
                else_args: vec![],
            }),
        );

        let zero = self.emit_i64_const(len_ok_blk, 0);
        let idx_alloca = self.emit_with_result(
            len_ok_blk,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            len_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        let i_val = self.emit_with_result(
            loop_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let expected_len = self.emit_i64_const(loop_hdr, i64::from(domain_len));
        let in_bounds = self.emit_with_result(
            loop_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: expected_len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: in_bounds,
                then_target: loop_body_id,
                then_args: vec![],
                else_target: true_id,
                else_args: vec![],
            }),
        );

        let i_body = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_body, 1);
        let two = self.emit_i64_const(loop_body, 2);
        let pair_offset = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: i_body,
                rhs: two,
            },
        );
        let key_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: pair_offset,
                rhs: one,
            },
        );
        let value_slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: pair_offset,
                rhs: two,
            },
        );
        let key_val = self.load_at_dynamic_offset(loop_body, func_ptr, key_slot);
        let value_val = self.load_at_dynamic_offset(loop_body, func_ptr, value_slot);
        self.lower_value_in_set_ptr_branch(
            loop_body,
            key_val,
            domain_ptr,
            domain_ok_id,
            false_id,
            "funcset_member_domain",
        );

        match range_shape {
            super::AggregateShape::Powerset { base } => {
                base.validate_powerset_base("SetIn: function-set SUBSET range")?;
                if matches!(base.as_ref(), super::AggregateShape::SetBitmask { .. }) {
                    self.lower_scalar_in_function_set_range_shape_branch(
                        domain_ok_blk,
                        value_val,
                        value_shape.as_deref(),
                        range_value,
                        super::AggregateShape::Powerset { base },
                        range_ok_id,
                        false_id,
                        "funcset_member_range_subset",
                    )?;
                } else {
                    let value_ptr = self.i64_value_as_ptr(domain_ok_blk, value_val);
                    let range_ptr = self.i64_value_as_ptr(domain_ok_blk, range_value);
                    self.lower_subseteq_ptr_branch(
                        domain_ok_blk,
                        value_ptr,
                        range_ptr,
                        range_ok_id,
                        false_id,
                        "funcset_member_range_subset",
                    );
                }
            }
            super::AggregateShape::Set { .. }
            | super::AggregateShape::ExactIntSet { .. }
            | super::AggregateShape::SetBitmask { .. }
            | super::AggregateShape::FiniteSet
            | super::AggregateShape::BoundedSet { .. }
            | super::AggregateShape::Interval { .. } => {
                self.lower_scalar_in_function_set_range_shape_branch(
                    domain_ok_blk,
                    value_val,
                    value_shape.as_deref(),
                    range_value,
                    range_shape,
                    range_ok_id,
                    false_id,
                    "funcset_member_range",
                )?;
            }
            super::AggregateShape::RecordSet { fields } => {
                let range_ptr = self.i64_value_as_ptr(domain_ok_blk, range_value);
                self.lower_record_value_in_record_set_ptr_branch(
                    domain_ok_blk,
                    value_val,
                    range_ptr,
                    fields,
                    range_ok_id,
                    false_id,
                )?;
            }
            super::AggregateShape::SymbolicDomain(domain) => {
                let member = self.emit_symbolic_domain_membership_i64(
                    domain_ok_blk,
                    value_val,
                    value_shape.as_deref(),
                    domain,
                )?;
                let zero = self.emit_i64_const(domain_ok_blk, 0);
                let is_member = self.emit_with_result(
                    domain_ok_blk,
                    Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I64,
                        lhs: member,
                        rhs: zero,
                    },
                );
                self.emit(
                    domain_ok_blk,
                    InstrNode::new(Inst::CondBr {
                        cond: is_member,
                        then_target: range_ok_id,
                        then_args: vec![],
                        else_target: false_id,
                        else_args: vec![],
                    }),
                );
            }
            super::AggregateShape::FunctionSet { domain, range } => {
                let range_ptr = self.i64_value_as_ptr(domain_ok_blk, range_value);
                self.lower_function_like_value_in_function_set_ptr_branch(
                    domain_ok_blk,
                    value_val,
                    value_shape.as_deref(),
                    range_ptr,
                    *domain,
                    *range,
                    range_ok_id,
                    false_id,
                    "funcset_member_range_function",
                )?;
            }
            super::AggregateShape::SeqSet { base } => {
                let seq_element_shape = match value_shape.as_deref() {
                    Some(super::AggregateShape::Sequence { element, .. }) => element.as_deref(),
                    _ => None,
                };
                let range_value = if Self::lazy_domain_runtime_payload_is_compact_mask(&base) {
                    range_value
                } else {
                    self.i64_value_as_ptr(domain_ok_blk, range_value)
                };
                self.lower_seq_value_in_seq_set_ptr_branch(
                    domain_ok_blk,
                    value_val,
                    seq_element_shape,
                    range_value,
                    *base,
                    range_ok_id,
                    false_id,
                    "funcset_member_range_seq",
                )?;
            }
            other => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: unsupported function-set range shape: {other:?}"
                )));
            }
        }

        self.emit(
            range_ok_blk,
            InstrNode::new(Inst::Br {
                target: loop_inc_id,
                args: vec![],
            }),
        );

        let i_inc = self.emit_with_result(
            loop_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: idx_alloca,
                align: None,
                volatile: false,
            },
        );
        let one = self.emit_i64_const(loop_inc, 1);
        let next_i = self.emit_with_result(
            loop_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_inc,
                rhs: one,
            },
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: idx_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            loop_inc,
            InstrNode::new(Inst::Br {
                target: loop_hdr_id,
                args: vec![],
            }),
        );

        self.store_reg_imm(true_blk, rd, 1)?;
        self.emit(
            true_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        self.store_reg_imm(false_blk, rd, 0)?;
        self.emit(
            false_blk,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge_blk))
    }

    fn lower_interval_membership_value(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_val: tmir::value::ValueId,
        lo: i64,
        hi: i64,
    ) -> Result<(), TmirError> {
        let in_range = self.emit_interval_membership_i64(block_idx, elem_val, lo, hi);
        self.store_reg_value(block_idx, rd, in_range)
    }

    fn lower_record_set_membership(
        &mut self,
        block_idx: usize,
        rd: u8,
        elem_reg: u8,
        record_set_reg: u8,
        fields: Vec<(tla_core::NameId, super::AggregateShape)>,
    ) -> Result<Option<usize>, TmirError> {
        let record_shape = match self.aggregate_shapes.get(&elem_reg).cloned() {
            Some(record_shape @ super::AggregateShape::Record { .. }) => record_shape,
            Some(super::AggregateShape::StateValue) => {
                super::AggregateShape::record_from_record_set_domains(&fields)
            }
            Some(other) => {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "SetIn: record-set membership requires tracked record element shape, got {other:?}"
                )));
            }
            None => {
                return Err(TmirError::UnsupportedOpcode(
                    "SetIn: record-set membership requires tracked record element shape".to_owned(),
                ));
            }
        };

        let super::AggregateShape::Record {
            fields: record_fields,
        } = &record_shape
        else {
            unreachable!("record_shape was matched as a record");
        };
        if record_fields.len() != fields.len() {
            self.store_reg_imm(block_idx, rd, 0)?;
            return Ok(Some(block_idx));
        }

        if fields.is_empty() {
            self.store_reg_imm(block_idx, rd, 1)?;
            return Ok(Some(block_idx));
        }

        if let Some(source_slot) = self.compact_state_slot_for_use(block_idx, elem_reg)? {
            let true_blk = self.new_aux_block("record_set_compact_true");
            let false_blk = self.new_aux_block("record_set_compact_false");
            let merge_blk = self.new_aux_block("record_set_compact_merge");
            let true_id = self.block_id_of(true_blk);
            let false_id = self.block_id_of(false_blk);
            let merge_id = self.block_id_of(merge_blk);

            let record_base_slot = self.emit_i64_const(block_idx, i64::from(source_slot.offset));
            let record_set_ptr = self.load_reg_as_ptr(block_idx, record_set_reg)?;
            self.lower_compact_record_value_in_record_set_branch(
                block_idx,
                source_slot.source_ptr,
                record_base_slot,
                Some(&record_shape),
                record_set_ptr,
                fields,
                true_id,
                false_id,
            )?;

            self.store_reg_imm(true_blk, rd, 1)?;
            self.emit(
                true_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );
            self.store_reg_imm(false_blk, rd, 0)?;
            self.emit(
                false_blk,
                InstrNode::new(Inst::Br {
                    target: merge_id,
                    args: vec![],
                }),
            );

            return Ok(Some(merge_blk));
        }

        let rec_ptr = self.load_reg_as_ptr(block_idx, elem_reg)?;
        let record_set_ptr = self.load_reg_as_ptr(block_idx, record_set_reg)?;
        let mut result: Option<tmir::value::ValueId> = None;

        for (domain_slot, (field_name, field_set_shape)) in fields.iter().enumerate() {
            let Some((field_idx, _)) = record_shape.record_field(*field_name) else {
                self.store_reg_imm(block_idx, rd, 0)?;
                return Ok(Some(block_idx));
            };
            let field_shape = record_shape
                .record_field(*field_name)
                .and_then(|(_, shape)| shape);
            let field_val = self.load_at_offset(block_idx, rec_ptr, field_idx);
            let field_set_shape =
                Self::materialized_domain_shape_for_pointer(field_set_shape.clone());
            let field_ok = match &field_set_shape {
                super::AggregateShape::Interval { lo, hi } => {
                    self.emit_interval_membership_i64(block_idx, field_val, *lo, *hi)
                }
                super::AggregateShape::Set { len, .. } => {
                    let domain_slot =
                        u32::try_from(domain_slot).expect("record set slot index must fit in u32");
                    let domain_value = self.load_at_offset(block_idx, record_set_ptr, domain_slot);
                    let domain_ptr = self.i64_value_as_ptr(block_idx, domain_value);
                    self.emit_finite_set_membership_i64(block_idx, field_val, domain_ptr, *len)
                }
                super::AggregateShape::SymbolicDomain(domain) => self
                    .emit_symbolic_domain_membership_i64(
                        block_idx,
                        field_val,
                        field_shape.as_ref(),
                        *domain,
                    )?,
                other => {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "SetIn: record-set field domain is not directly lowerable: {other:?}"
                    )));
                }
            };

            result = Some(match result {
                None => field_ok,
                Some(prev) => self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: prev,
                        rhs: field_ok,
                    },
                ),
            });
        }

        self.store_reg_value(
            block_idx,
            rd,
            result.expect("non-empty record-set fields must produce a result"),
        )?;
        Ok(Some(block_idx))
    }

    fn lower_record_value_in_record_set_ptr_branch(
        &mut self,
        block_idx: usize,
        record_value: ValueId,
        record_set_ptr: ValueId,
        fields: Vec<(tla_core::NameId, super::AggregateShape)>,
        success_target: BlockId,
        failure_target: BlockId,
    ) -> Result<(), TmirError> {
        let record_shape = super::AggregateShape::record_from_record_set_domains(&fields);
        let super::AggregateShape::Record {
            fields: record_fields,
        } = &record_shape
        else {
            unreachable!("record_from_record_set_domains must return Record");
        };
        if record_fields.len() != fields.len() {
            self.emit(
                block_idx,
                InstrNode::new(Inst::Br {
                    target: failure_target,
                    args: vec![],
                }),
            );
            return Ok(());
        }
        if fields.is_empty() {
            self.emit(
                block_idx,
                InstrNode::new(Inst::Br {
                    target: success_target,
                    args: vec![],
                }),
            );
            return Ok(());
        }

        let rec_ptr = self.i64_value_as_ptr(block_idx, record_value);
        let mut result: Option<ValueId> = None;
        for (domain_slot, (field_name, field_set_shape)) in fields.iter().enumerate() {
            let Some((field_idx, _)) = record_shape.record_field(*field_name) else {
                self.emit(
                    block_idx,
                    InstrNode::new(Inst::Br {
                        target: failure_target,
                        args: vec![],
                    }),
                );
                return Ok(());
            };
            let field_shape = record_shape
                .record_field(*field_name)
                .and_then(|(_, shape)| shape);
            let field_val = self.load_at_offset(block_idx, rec_ptr, field_idx);
            let field_set_shape =
                Self::materialized_domain_shape_for_pointer(field_set_shape.clone());
            let field_ok = match &field_set_shape {
                super::AggregateShape::Interval { lo, hi } => {
                    self.emit_interval_membership_i64(block_idx, field_val, *lo, *hi)
                }
                super::AggregateShape::Set { len, .. } => {
                    let domain_slot =
                        u32::try_from(domain_slot).expect("record set slot index must fit in u32");
                    let domain_value = self.load_at_offset(block_idx, record_set_ptr, domain_slot);
                    let domain_ptr = self.i64_value_as_ptr(block_idx, domain_value);
                    self.emit_finite_set_membership_i64(block_idx, field_val, domain_ptr, *len)
                }
                super::AggregateShape::SymbolicDomain(domain) => self
                    .emit_symbolic_domain_membership_i64(
                        block_idx,
                        field_val,
                        field_shape.as_ref(),
                        *domain,
                    )?,
                other => {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "SetIn: record-set field domain is not directly lowerable: {other:?}"
                    )));
                }
            };

            result = Some(match result {
                None => field_ok,
                Some(prev) => self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: prev,
                        rhs: field_ok,
                    },
                ),
            });
        }

        self.branch_on_i64_truth(
            block_idx,
            result.expect("non-empty record-set fields must produce a result"),
            success_target,
            failure_target,
        );
        Ok(())
    }

    fn emit_interval_membership_i64(
        &mut self,
        block_idx: usize,
        elem_val: tmir::value::ValueId,
        lo: i64,
        hi: i64,
    ) -> tmir::value::ValueId {
        if hi < lo {
            return self.emit_i64_const(block_idx, 0);
        }

        let lo_val = self.emit_i64_const(block_idx, lo);
        let hi_val = self.emit_i64_const(block_idx, hi);
        let ge_lo = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Sge,
                ty: Ty::I64,
                lhs: elem_val,
                rhs: lo_val,
            },
        );
        let le_hi = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Sle,
                ty: Ty::I64,
                lhs: elem_val,
                rhs: hi_val,
            },
        );
        let ge_lo_i64 = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: ge_lo,
            },
        );
        let le_hi_i64 = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: le_hi,
            },
        );
        self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: ge_lo_i64,
                rhs: le_hi_i64,
            },
        )
    }

    /// Lower SetUnion { rd, r1, r2 }: union of two sets.
    ///
    /// Creates a new set containing all elements from both sets.
    pub(super) fn lower_set_union(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let Some((universe_len, universe)) =
            self.compact_binary_set_universe("SetUnion", r1, r2)?
        {
            let (block_idx, left) = self.emit_set_operand_bitmask_i64_allow_materialized(
                block_idx,
                r1,
                universe_len,
                &universe,
                "SetUnion",
            )?;
            let (block_idx, right) = self.emit_set_operand_bitmask_i64_allow_materialized(
                block_idx,
                r2,
                universe_len,
                &universe,
                "SetUnion",
            )?;
            let raw = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    lhs: left,
                    rhs: right,
                },
            );
            let valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, "SetUnion")?;
            let valid_mask_val = self.emit_i64_const(block_idx, valid_mask);
            let result = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: raw,
                    rhs: valid_mask_val,
                },
            );
            self.store_reg_value(block_idx, rd, result)?;
            self.aggregate_shapes.insert(
                rd,
                super::AggregateShape::SetBitmask {
                    universe_len,
                    universe,
                },
            );
            self.const_set_sizes.remove(&rd);
            self.const_scalar_values.remove(&rd);
            return Ok(Some(block_idx));
        }

        self.reject_lazy_set_operand("SetUnion", r1)?;
        self.reject_lazy_set_operand("SetUnion", r2)?;

        // Load both set pointers and lengths
        let set1_ptr = self.load_reg_as_ptr(block_idx, r1)?;
        let set2_ptr = self.load_reg_as_ptr(block_idx, r2)?;
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        let result_ptr = match (
            self.const_set_sizes.get(&r1).copied(),
            self.const_set_sizes.get(&r2).copied(),
        ) {
            (Some(len1), Some(len2)) => {
                let total_slots = len1
                    .checked_add(len2)
                    .and_then(|slots| slots.checked_add(1))
                    .ok_or_else(|| {
                        TmirError::UnsupportedOpcode(format!(
                            "SetUnion: static result allocation size overflows u32: {len1} + {len2} + 1"
                        ))
                    })?;
                self.alloc_aggregate(block_idx, total_slots)
            }
            _ => {
                // Max result size = len1 + len2 + 1 (header)
                let total_elem = self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: len1,
                        rhs: len2,
                    },
                );
                let one_64 = self.emit_i64_const(block_idx, 1);
                let total_slots = self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: total_elem,
                        rhs: one_64,
                    },
                );
                let total_i32 = self.emit_with_result(
                    block_idx,
                    Inst::Cast {
                        op: CastOp::Trunc,
                        src_ty: Ty::I64,
                        dst_ty: Ty::I32,
                        operand: total_slots,
                    },
                );
                self.emit_with_result(
                    block_idx,
                    Inst::Alloca {
                        ty: Ty::I64,
                        count: Some(total_i32),
                        align: None,
                    },
                )
            }
        };

        // Copy all elements from set1 (slots 1..=len1)
        // For the tMIR-level representation, we use a simple loop to copy elements.
        // Store initial result length as len1 (we'll copy set1 completely first).
        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        // Alloca for write cursor (starts at 1)
        let cursor_alloca = self.emit_with_result(
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
                ptr: cursor_alloca,
                value: one,
                align: None,
                volatile: false,
            }),
        );

        // Copy loop for set1
        let copy1_header = self.new_aux_block("union_copy1_hdr");
        let copy1_body = self.new_aux_block("union_copy1_body");
        let copy1_done = self.new_aux_block("union_copy1_done");

        let hdr1_id = self.block_id_of(copy1_header);
        let body1_id = self.block_id_of(copy1_body);
        let done1_id = self.block_id_of(copy1_done);

        // Alloca for loop index
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
        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: hdr1_id,
                args: vec![],
            }),
        );

        // Header: i < len1?
        let i_val = self.emit_with_result(
            copy1_header,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp1 = self.emit_with_result(
            copy1_header,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: len1,
            },
        );
        self.emit(
            copy1_header,
            InstrNode::new(Inst::CondBr {
                cond: cmp1,
                then_target: body1_id,
                then_args: vec![],
                else_target: done1_id,
                else_args: vec![],
            }),
        );

        // Body: copy element
        let i_val2 = self.emit_with_result(
            copy1_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let src_slot = self.emit_with_result(
            copy1_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        let elem = self.load_at_dynamic_offset(copy1_body, set1_ptr, src_slot);
        let cursor = self.emit_with_result(
            copy1_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: cursor_alloca,
                align: None,
                volatile: false,
            },
        );
        self.store_at_dynamic_offset(copy1_body, result_ptr, cursor, elem);
        // Increment
        let next_i = self.emit_with_result(
            copy1_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        self.emit(
            copy1_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        let next_cursor = self.emit_with_result(
            copy1_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cursor,
                rhs: one,
            },
        );
        self.emit(
            copy1_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: cursor_alloca,
                value: next_cursor,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            copy1_body,
            InstrNode::new(Inst::Br {
                target: hdr1_id,
                args: vec![],
            }),
        );

        // After copying set1, copy set2 elements
        let copy2_header = self.new_aux_block("union_copy2_hdr");
        let copy2_body = self.new_aux_block("union_copy2_body");
        let finalize = self.new_aux_block("union_finalize");

        let hdr2_id = self.block_id_of(copy2_header);
        let body2_id = self.block_id_of(copy2_body);
        let finalize_id = self.block_id_of(finalize);

        // Reset loop index
        self.emit(
            copy1_done,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            copy1_done,
            InstrNode::new(Inst::Br {
                target: hdr2_id,
                args: vec![],
            }),
        );

        // Header: i < len2?
        let i_val3 = self.emit_with_result(
            copy2_header,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp2 = self.emit_with_result(
            copy2_header,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val3,
                rhs: len2,
            },
        );
        self.emit(
            copy2_header,
            InstrNode::new(Inst::CondBr {
                cond: cmp2,
                then_target: body2_id,
                then_args: vec![],
                else_target: finalize_id,
                else_args: vec![],
            }),
        );

        // Body: copy element
        let i_val4 = self.emit_with_result(
            copy2_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let src_slot2 = self.emit_with_result(
            copy2_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val4,
                rhs: one,
            },
        );
        let elem2 = self.load_at_dynamic_offset(copy2_body, set2_ptr, src_slot2);
        let cursor2 = self.emit_with_result(
            copy2_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: cursor_alloca,
                align: None,
                volatile: false,
            },
        );
        self.store_at_dynamic_offset(copy2_body, result_ptr, cursor2, elem2);
        let next_i2 = self.emit_with_result(
            copy2_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val4,
                rhs: one,
            },
        );
        self.emit(
            copy2_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i2,
                align: None,
                volatile: false,
            }),
        );
        let next_cursor2 = self.emit_with_result(
            copy2_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cursor2,
                rhs: one,
            },
        );
        self.emit(
            copy2_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: cursor_alloca,
                value: next_cursor2,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            copy2_body,
            InstrNode::new(Inst::Br {
                target: hdr2_id,
                args: vec![],
            }),
        );

        // Finalize: store final length = cursor - 1
        let final_cursor = self.emit_with_result(
            finalize,
            Inst::Load {
                ty: Ty::I64,
                ptr: cursor_alloca,
                align: None,
                volatile: false,
            },
        );
        let final_len = self.emit_with_result(
            finalize,
            Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: final_cursor,
                rhs: one,
            },
        );
        self.store_at_offset(finalize, result_ptr, 0, final_len);
        self.store_reg_ptr(finalize, rd, result_ptr)?;

        Ok(Some(finalize))
    }

    /// Lower SetIntersect { rd, r1, r2 }: intersection of two sets.
    ///
    /// Creates a new set containing elements present in both sets.
    /// Uses nested loops: for each element in set1, scan set2 for a match.
    pub(super) fn lower_set_intersect(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let Some((universe_len, universe)) =
            self.compact_binary_set_universe("SetIntersect", r1, r2)?
        {
            let (block_idx, left) = self.emit_set_intersect_operand_bitmask_i64(
                block_idx,
                r1,
                universe_len,
                &universe,
                "SetIntersect",
            )?;
            let (block_idx, right) = self.emit_set_intersect_operand_bitmask_i64(
                block_idx,
                r2,
                universe_len,
                &universe,
                "SetIntersect",
            )?;
            let result = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: left,
                    rhs: right,
                },
            );
            self.store_reg_value(block_idx, rd, result)?;
            self.aggregate_shapes.insert(
                rd,
                super::AggregateShape::SetBitmask {
                    universe_len,
                    universe,
                },
            );
            self.const_set_sizes.remove(&rd);
            self.const_scalar_values.remove(&rd);
            return Ok(Some(block_idx));
        }

        self.reject_lazy_set_operand("SetIntersect", r1)?;
        self.reject_lazy_set_operand("SetIntersect", r2)?;

        let set1_ptr = self.load_reg_as_ptr(block_idx, r1)?;
        let set2_ptr = self.load_reg_as_ptr(block_idx, r2)?;
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let _len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        // Allocate result set with max size = len1 + 1
        let one_64 = self.emit_i64_const(block_idx, 1);
        let max_slots = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: len1,
                rhs: one_64,
            },
        );
        let result_ptr = if let Some(max_len) = self.const_set_sizes.get(&r1).copied() {
            self.alloc_aggregate(block_idx, max_len + 1)
        } else {
            let max_i32 = self.emit_with_result(
                block_idx,
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I64,
                    dst_ty: Ty::I32,
                    operand: max_slots,
                },
            );
            self.emit_with_result(
                block_idx,
                Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(max_i32),
                    align: None,
                },
            )
        };

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        // Write cursor for result
        let cursor_alloca = self.emit_with_result(
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
                ptr: cursor_alloca,
                value: one,
                align: None,
                volatile: false,
            }),
        );

        // Outer loop index
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

        let outer_hdr = self.new_aux_block("isect_outer_hdr");
        let outer_body = self.new_aux_block("isect_outer_body");
        let inner_hdr = self.new_aux_block("isect_inner_hdr");
        let inner_body = self.new_aux_block("isect_inner_body");
        let inner_inc = self.new_aux_block("isect_inner_inc");
        let found_blk = self.new_aux_block("isect_found");
        let outer_inc = self.new_aux_block("isect_outer_inc");
        let finalize = self.new_aux_block("isect_finalize");

        let outer_hdr_id = self.block_id_of(outer_hdr);
        let outer_body_id = self.block_id_of(outer_body);
        let inner_hdr_id = self.block_id_of(inner_hdr);
        let inner_body_id = self.block_id_of(inner_body);
        let inner_inc_id = self.block_id_of(inner_inc);
        let found_blk_id = self.block_id_of(found_blk);
        let outer_inc_id = self.block_id_of(outer_inc);
        let finalize_id = self.block_id_of(finalize);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: outer_hdr_id,
                args: vec![],
            }),
        );

        // Outer header: i < len1?
        let i_val = self.emit_with_result(
            outer_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp_outer = self.emit_with_result(
            outer_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: len1,
            },
        );
        self.emit(
            outer_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp_outer,
                then_target: outer_body_id,
                then_args: vec![],
                else_target: finalize_id,
                else_args: vec![],
            }),
        );

        // Outer body: load element from set1
        let i_val2 = self.emit_with_result(
            outer_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot = self.emit_with_result(
            outer_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        let elem1 = self.load_at_dynamic_offset(outer_body, set1_ptr, slot);

        // Inner loop: search set2 for elem1
        let j_alloca = self.emit_with_result(
            outer_body,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            outer_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: j_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            outer_body,
            InstrNode::new(Inst::Br {
                target: inner_hdr_id,
                args: vec![],
            }),
        );

        // Inner header: j < len2?
        let j_val = self.emit_with_result(
            inner_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp_inner = self.emit_with_result(
            inner_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: j_val,
                rhs: _len2,
            },
        );
        self.emit(
            inner_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp_inner,
                then_target: inner_body_id,
                then_args: vec![],
                else_target: outer_inc_id,
                else_args: vec![], // not found
            }),
        );

        // Inner body: compare
        let j_val2 = self.emit_with_result(
            inner_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot2 = self.emit_with_result(
            inner_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: j_val2,
                rhs: one,
            },
        );
        let elem2 = self.load_at_dynamic_offset(inner_body, set2_ptr, slot2);
        let eq = self.emit_with_result(
            inner_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: elem1,
                rhs: elem2,
            },
        );
        self.emit(
            inner_body,
            InstrNode::new(Inst::CondBr {
                cond: eq,
                then_target: found_blk_id,
                then_args: vec![],
                else_target: inner_inc_id,
                else_args: vec![],
            }),
        );

        // Inner increment
        let j_val3 = self.emit_with_result(
            inner_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_j = self.emit_with_result(
            inner_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: j_val3,
                rhs: one,
            },
        );
        self.emit(
            inner_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: j_alloca,
                value: next_j,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            inner_inc,
            InstrNode::new(Inst::Br {
                target: inner_hdr_id,
                args: vec![],
            }),
        );

        // Found: add elem1 to result
        let cursor = self.emit_with_result(
            found_blk,
            Inst::Load {
                ty: Ty::I64,
                ptr: cursor_alloca,
                align: None,
                volatile: false,
            },
        );
        self.store_at_dynamic_offset(found_blk, result_ptr, cursor, elem1);
        let next_cursor = self.emit_with_result(
            found_blk,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cursor,
                rhs: one,
            },
        );
        self.emit(
            found_blk,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: cursor_alloca,
                value: next_cursor,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            found_blk,
            InstrNode::new(Inst::Br {
                target: outer_inc_id,
                args: vec![],
            }),
        );

        // Outer increment
        let i_val3 = self.emit_with_result(
            outer_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_i = self.emit_with_result(
            outer_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val3,
                rhs: one,
            },
        );
        self.emit(
            outer_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            outer_inc,
            InstrNode::new(Inst::Br {
                target: outer_hdr_id,
                args: vec![],
            }),
        );

        // Finalize
        let final_cursor = self.emit_with_result(
            finalize,
            Inst::Load {
                ty: Ty::I64,
                ptr: cursor_alloca,
                align: None,
                volatile: false,
            },
        );
        let final_len = self.emit_with_result(
            finalize,
            Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: final_cursor,
                rhs: one,
            },
        );
        self.store_at_offset(finalize, result_ptr, 0, final_len);
        self.store_reg_ptr(finalize, rd, result_ptr)?;

        Ok(Some(finalize))
    }

    /// Lower SetDiff { rd, r1, r2 }: set difference (r1 \ r2).
    ///
    /// Creates a new set containing elements in r1 that are NOT in r2.
    pub(super) fn lower_set_diff(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let Some((universe_len, universe)) =
            self.compact_binary_set_universe("SetDiff", r1, r2)?
        {
            let (block_idx, left) = self.emit_set_operand_bitmask_i64_allow_materialized(
                block_idx,
                r1,
                universe_len,
                &universe,
                "SetDiff",
            )?;
            let (block_idx, right) = self.emit_set_operand_bitmask_i64_allow_materialized(
                block_idx,
                r2,
                universe_len,
                &universe,
                "SetDiff",
            )?;
            let valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, "SetDiff")?;
            let valid_mask_val = self.emit_i64_const(block_idx, valid_mask);
            let right_complement = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    lhs: right,
                    rhs: valid_mask_val,
                },
            );
            let result = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: left,
                    rhs: right_complement,
                },
            );
            self.store_reg_value(block_idx, rd, result)?;
            self.aggregate_shapes.insert(
                rd,
                super::AggregateShape::SetBitmask {
                    universe_len,
                    universe,
                },
            );
            self.const_set_sizes.remove(&rd);
            self.const_scalar_values.remove(&rd);
            return Ok(Some(block_idx));
        }

        if let Some((universe_len, universe)) = self.small_interval_setdiff_universe(r1, r2)? {
            let valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, "SetDiff")?;
            let left = self.emit_i64_const(block_idx, valid_mask);
            let right =
                self.emit_small_setdiff_rhs_int_mask_i64(block_idx, r2, universe_len, &universe)?;
            let valid_mask_val = self.emit_i64_const(block_idx, valid_mask);
            let right_complement = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    lhs: right,
                    rhs: valid_mask_val,
                },
            );
            let result = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: left,
                    rhs: right_complement,
                },
            );
            self.store_reg_value(block_idx, rd, result)?;
            self.aggregate_shapes.insert(
                rd,
                super::AggregateShape::SetBitmask {
                    universe_len,
                    universe,
                },
            );
            self.const_set_sizes.remove(&rd);
            self.const_scalar_values.remove(&rd);
            return Ok(Some(block_idx));
        }

        self.reject_lazy_set_operand("SetDiff", r1)?;
        self.reject_lazy_set_operand("SetDiff", r2)?;

        let set1_ptr = self.load_reg_as_ptr(block_idx, r1)?;
        let set2_ptr = self.load_reg_as_ptr(block_idx, r2)?;
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        // Allocate result set with max size = len1 + 1
        let one_64 = self.emit_i64_const(block_idx, 1);
        let max_slots = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: len1,
                rhs: one_64,
            },
        );
        let result_ptr = if let Some(max_len) = self.const_set_sizes.get(&r1).copied() {
            self.alloc_aggregate(block_idx, max_len + 1)
        } else {
            let max_i32 = self.emit_with_result(
                block_idx,
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I64,
                    dst_ty: Ty::I32,
                    operand: max_slots,
                },
            );
            self.emit_with_result(
                block_idx,
                Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(max_i32),
                    align: None,
                },
            )
        };

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

        let cursor_alloca = self.emit_with_result(
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
                ptr: cursor_alloca,
                value: one,
                align: None,
                volatile: false,
            }),
        );

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

        let outer_hdr = self.new_aux_block("sdiff_outer_hdr");
        let outer_body = self.new_aux_block("sdiff_outer_body");
        let inner_hdr = self.new_aux_block("sdiff_inner_hdr");
        let inner_body = self.new_aux_block("sdiff_inner_body");
        let inner_inc = self.new_aux_block("sdiff_inner_inc");
        let not_found = self.new_aux_block("sdiff_not_found");
        let outer_inc = self.new_aux_block("sdiff_outer_inc");
        let finalize = self.new_aux_block("sdiff_finalize");

        let outer_hdr_id = self.block_id_of(outer_hdr);
        let outer_body_id = self.block_id_of(outer_body);
        let inner_hdr_id = self.block_id_of(inner_hdr);
        let inner_body_id = self.block_id_of(inner_body);
        let inner_inc_id = self.block_id_of(inner_inc);
        let not_found_id = self.block_id_of(not_found);
        let outer_inc_id = self.block_id_of(outer_inc);
        let finalize_id = self.block_id_of(finalize);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: outer_hdr_id,
                args: vec![],
            }),
        );

        // Outer header
        let i_val = self.emit_with_result(
            outer_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp_outer = self.emit_with_result(
            outer_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: len1,
            },
        );
        self.emit(
            outer_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp_outer,
                then_target: outer_body_id,
                then_args: vec![],
                else_target: finalize_id,
                else_args: vec![],
            }),
        );

        // Outer body: load elem from set1
        let i_val2 = self.emit_with_result(
            outer_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot = self.emit_with_result(
            outer_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        let elem1 = self.load_at_dynamic_offset(outer_body, set1_ptr, slot);

        // Inner loop: search set2 for elem1
        let j_alloca = self.emit_with_result(
            outer_body,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            outer_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: j_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            outer_body,
            InstrNode::new(Inst::Br {
                target: inner_hdr_id,
                args: vec![],
            }),
        );

        // Inner header
        let j_val = self.emit_with_result(
            inner_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp_inner = self.emit_with_result(
            inner_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: j_val,
                rhs: len2,
            },
        );
        self.emit(
            inner_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp_inner,
                then_target: inner_body_id,
                then_args: vec![],
                else_target: not_found_id,
                else_args: vec![], // not found = include in result
            }),
        );

        // Inner body
        let j_val2 = self.emit_with_result(
            inner_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot2 = self.emit_with_result(
            inner_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: j_val2,
                rhs: one,
            },
        );
        let elem2 = self.load_at_dynamic_offset(inner_body, set2_ptr, slot2);
        let eq = self.emit_with_result(
            inner_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: elem1,
                rhs: elem2,
            },
        );
        self.emit(
            inner_body,
            InstrNode::new(Inst::CondBr {
                cond: eq,
                then_target: outer_inc_id,
                then_args: vec![], // found in set2 => skip
                else_target: inner_inc_id,
                else_args: vec![],
            }),
        );

        // Inner increment
        let j_val3 = self.emit_with_result(
            inner_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_j = self.emit_with_result(
            inner_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: j_val3,
                rhs: one,
            },
        );
        self.emit(
            inner_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: j_alloca,
                value: next_j,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            inner_inc,
            InstrNode::new(Inst::Br {
                target: inner_hdr_id,
                args: vec![],
            }),
        );

        // Not found in set2: add to result
        let cursor = self.emit_with_result(
            not_found,
            Inst::Load {
                ty: Ty::I64,
                ptr: cursor_alloca,
                align: None,
                volatile: false,
            },
        );
        self.store_at_dynamic_offset(not_found, result_ptr, cursor, elem1);
        let next_cursor = self.emit_with_result(
            not_found,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cursor,
                rhs: one,
            },
        );
        self.emit(
            not_found,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: cursor_alloca,
                value: next_cursor,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            not_found,
            InstrNode::new(Inst::Br {
                target: outer_inc_id,
                args: vec![],
            }),
        );

        // Outer increment
        let i_val3 = self.emit_with_result(
            outer_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_i = self.emit_with_result(
            outer_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val3,
                rhs: one,
            },
        );
        self.emit(
            outer_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            outer_inc,
            InstrNode::new(Inst::Br {
                target: outer_hdr_id,
                args: vec![],
            }),
        );

        // Finalize
        let final_cursor = self.emit_with_result(
            finalize,
            Inst::Load {
                ty: Ty::I64,
                ptr: cursor_alloca,
                align: None,
                volatile: false,
            },
        );
        let final_len = self.emit_with_result(
            finalize,
            Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: final_cursor,
                rhs: one,
            },
        );
        self.store_at_offset(finalize, result_ptr, 0, final_len);
        self.store_reg_ptr(finalize, rd, result_ptr)?;

        Ok(Some(finalize))
    }

    /// Lower Subseteq { rd, r1, r2 }: test r1 \subseteq r2.
    ///
    /// For each element in r1, check if it exists in r2. If any element
    /// is not found, result is 0 (false). Otherwise 1 (true).
    pub(super) fn lower_subseteq(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<Option<usize>, TmirError> {
        if let Some((universe_len, universe)) =
            self.compact_binary_set_universe("Subseteq", r1, r2)?
        {
            let (block_idx, left, left_in_universe) = self.emit_set_subseteq_operand_bitmask_i64(
                block_idx,
                r1,
                universe_len,
                &universe,
                "Subseteq",
            )?;
            let (block_idx, right, _right_in_universe) = self
                .emit_set_subseteq_operand_bitmask_i64(
                    block_idx,
                    r2,
                    universe_len,
                    &universe,
                    "Subseteq",
                )?;
            let valid_mask = Self::compact_set_bitmask_valid_mask(universe_len, "Subseteq")?;
            let valid_mask_val = self.emit_i64_const(block_idx, valid_mask);
            let right_complement = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    lhs: right,
                    rhs: valid_mask_val,
                },
            );
            let missing = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: left,
                    rhs: right_complement,
                },
            );
            let zero = self.emit_i64_const(block_idx, 0);
            let no_missing = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: missing,
                    rhs: zero,
                },
            );
            let no_missing_i64 = self.emit_bool_to_i64(block_idx, no_missing);
            let left_canonical =
                self.emit_compact_bitmask_canonical_i64(block_idx, left, universe_len, "Subseteq")?;
            let right_canonical = self.emit_compact_bitmask_canonical_i64(
                block_idx,
                right,
                universe_len,
                "Subseteq",
            )?;
            let canonical = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: left_canonical,
                    rhs: right_canonical,
                },
            );
            let present_subset = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: no_missing_i64,
                    rhs: left_in_universe,
                },
            );
            let result = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: present_subset,
                    rhs: canonical,
                },
            );
            self.store_reg_value(block_idx, rd, result)?;
            return Ok(Some(block_idx));
        }

        self.reject_lazy_set_operand("Subseteq", r1)?;
        self.reject_lazy_set_operand("Subseteq", r2)?;

        let set1_ptr = self.load_reg_as_ptr(block_idx, r1)?;
        let set2_ptr = self.load_reg_as_ptr(block_idx, r2)?;
        let len1 = self.load_at_offset(block_idx, set1_ptr, 0);
        let len2 = self.load_at_offset(block_idx, set2_ptr, 0);

        let zero = self.emit_i64_const(block_idx, 0);
        let one = self.emit_i64_const(block_idx, 1);

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

        let outer_hdr = self.new_aux_block("subseteq_outer_hdr");
        let outer_body = self.new_aux_block("subseteq_outer_body");
        let inner_hdr = self.new_aux_block("subseteq_inner_hdr");
        let inner_body = self.new_aux_block("subseteq_inner_body");
        let inner_inc = self.new_aux_block("subseteq_inner_inc");
        let not_found = self.new_aux_block("subseteq_not_found");
        let outer_inc = self.new_aux_block("subseteq_outer_inc");
        let result_true = self.new_aux_block("subseteq_true");

        let outer_hdr_id = self.block_id_of(outer_hdr);
        let outer_body_id = self.block_id_of(outer_body);
        let inner_hdr_id = self.block_id_of(inner_hdr);
        let inner_body_id = self.block_id_of(inner_body);
        let inner_inc_id = self.block_id_of(inner_inc);
        let not_found_id = self.block_id_of(not_found);
        let outer_inc_id = self.block_id_of(outer_inc);
        let result_true_id = self.block_id_of(result_true);

        self.emit(
            block_idx,
            InstrNode::new(Inst::Br {
                target: outer_hdr_id,
                args: vec![],
            }),
        );

        // Outer header: i < len1?
        let i_val = self.emit_with_result(
            outer_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp = self.emit_with_result(
            outer_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: i_val,
                rhs: len1,
            },
        );
        self.emit(
            outer_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: outer_body_id,
                then_args: vec![],
                else_target: result_true_id,
                else_args: vec![],
            }),
        );

        // Outer body
        let i_val2 = self.emit_with_result(
            outer_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot = self.emit_with_result(
            outer_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        let elem1 = self.load_at_dynamic_offset(outer_body, set1_ptr, slot);

        let j_alloca = self.emit_with_result(
            outer_body,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            outer_body,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: j_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            outer_body,
            InstrNode::new(Inst::Br {
                target: inner_hdr_id,
                args: vec![],
            }),
        );

        // Inner header
        let j_val = self.emit_with_result(
            inner_hdr,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let cmp2 = self.emit_with_result(
            inner_hdr,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: j_val,
                rhs: len2,
            },
        );
        self.emit(
            inner_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp2,
                then_target: inner_body_id,
                then_args: vec![],
                else_target: not_found_id,
                else_args: vec![],
            }),
        );

        // Inner body
        let j_val2 = self.emit_with_result(
            inner_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let slot2 = self.emit_with_result(
            inner_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: j_val2,
                rhs: one,
            },
        );
        let elem2 = self.load_at_dynamic_offset(inner_body, set2_ptr, slot2);
        let eq = self.emit_with_result(
            inner_body,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: elem1,
                rhs: elem2,
            },
        );
        self.emit(
            inner_body,
            InstrNode::new(Inst::CondBr {
                cond: eq,
                then_target: outer_inc_id,
                then_args: vec![], // found
                else_target: inner_inc_id,
                else_args: vec![],
            }),
        );

        // Inner increment
        let j_val3 = self.emit_with_result(
            inner_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: j_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_j = self.emit_with_result(
            inner_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: j_val3,
                rhs: one,
            },
        );
        self.emit(
            inner_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: j_alloca,
                value: next_j,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            inner_inc,
            InstrNode::new(Inst::Br {
                target: inner_hdr_id,
                args: vec![],
            }),
        );

        // Not found: result is false
        self.store_reg_imm(not_found, rd, 0)?;
        // We need a merge block for the final result
        let merge = self.new_aux_block("subseteq_merge");
        let merge_id = self.block_id_of(merge);
        self.emit(
            not_found,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        // Outer increment
        let i_val3 = self.emit_with_result(
            outer_inc,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let next_i = self.emit_with_result(
            outer_inc,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val3,
                rhs: one,
            },
        );
        self.emit(
            outer_inc,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: next_i,
                align: None,
                volatile: false,
            }),
        );
        self.emit(
            outer_inc,
            InstrNode::new(Inst::Br {
                target: outer_hdr_id,
                args: vec![],
            }),
        );

        // Result true
        self.store_reg_imm(result_true, rd, 1)?;
        self.emit(
            result_true,
            InstrNode::new(Inst::Br {
                target: merge_id,
                args: vec![],
            }),
        );

        Ok(Some(merge))
    }

    /// Lower Range { rd, lo, hi }: build the integer interval set lo..hi.
    ///
    /// Layout: slot[0] = max(hi - lo + 1, 0) (length), slot[1..=len] = lo, lo+1, ..., hi.
    pub(super) fn lower_range(
        &mut self,
        block_idx: usize,
        rd: u8,
        lo_reg: u8,
        hi_reg: u8,
    ) -> Result<Option<usize>, TmirError> {
        let lo = self.load_reg(block_idx, lo_reg)?;
        let hi = self.load_reg(block_idx, hi_reg)?;

        let is_empty = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: hi,
                rhs: lo,
            },
        );
        let empty_block = self.new_aux_block("range_empty");
        let nonempty_block = self.new_aux_block("range_nonempty");
        let done_block = self.new_aux_block("range_done");

        let empty_id = self.block_id_of(empty_block);
        let nonempty_id = self.block_id_of(nonempty_block);
        let done_id = self.block_id_of(done_block);

        self.emit(
            block_idx,
            InstrNode::new(Inst::CondBr {
                cond: is_empty,
                then_target: empty_id,
                then_args: vec![],
                else_target: nonempty_id,
                else_args: vec![],
            }),
        );

        let zero = self.emit_i64_const(empty_block, 0);
        let empty_ptr = self.alloc_aggregate(empty_block, 1);
        self.store_at_offset(empty_block, empty_ptr, 0, zero);
        self.store_reg_ptr(empty_block, rd, empty_ptr)?;
        self.emit(
            empty_block,
            InstrNode::new(Inst::Br {
                target: done_id,
                args: vec![],
            }),
        );

        let one = self.emit_i64_const(nonempty_block, 1);

        // len = hi - lo + 1
        let diff = self.emit_with_result(
            nonempty_block,
            Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: hi,
                rhs: lo,
            },
        );
        let len = self.emit_with_result(
            nonempty_block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: diff,
                rhs: one,
            },
        );

        // total slots = len + 1
        let total = self.emit_with_result(
            nonempty_block,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: len,
                rhs: one,
            },
        );
        let agg_ptr = if let (Some(lo_imm), Some(hi_imm)) =
            (self.scalar_of(lo_reg), self.scalar_of(hi_reg))
        {
            if hi_imm >= lo_imm {
                let total_slots = hi_imm
                    .checked_sub(lo_imm)
                    .and_then(|diff| diff.checked_add(2))
                    .and_then(|slots| u32::try_from(slots).ok());
                if let Some(total_slots) = total_slots {
                    self.alloc_aggregate(nonempty_block, total_slots)
                } else {
                    self.alloc_dynamic_i64_slots(nonempty_block, total)
                }
            } else {
                self.alloc_aggregate(nonempty_block, 1)
            }
        } else {
            self.alloc_dynamic_i64_slots(nonempty_block, total)
        };

        // Store length at slot 0
        self.store_at_offset(nonempty_block, agg_ptr, 0, len);

        // Fill loop: for i in 0..len, store lo+i at slot i+1
        let zero = self.emit_i64_const(nonempty_block, 0);
        let i_alloca = self.emit_with_result(
            nonempty_block,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        );
        self.emit(
            nonempty_block,
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: i_alloca,
                value: zero,
                align: None,
                volatile: false,
            }),
        );

        let loop_hdr = self.new_aux_block("range_hdr");
        let loop_body = self.new_aux_block("range_body");
        let loop_done = self.new_aux_block("range_store");

        let hdr_id = self.block_id_of(loop_hdr);
        let body_id = self.block_id_of(loop_body);
        let loop_done_id = self.block_id_of(loop_done);

        self.emit(
            nonempty_block,
            InstrNode::new(Inst::Br {
                target: hdr_id,
                args: vec![],
            }),
        );

        // Header
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
                rhs: len,
            },
        );
        self.emit(
            loop_hdr,
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: body_id,
                then_args: vec![],
                else_target: loop_done_id,
                else_args: vec![],
            }),
        );

        // Body
        let i_val2 = self.emit_with_result(
            loop_body,
            Inst::Load {
                ty: Ty::I64,
                ptr: i_alloca,
                align: None,
                volatile: false,
            },
        );
        let elem = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: lo,
                rhs: i_val2,
            },
        );
        let slot = self.emit_with_result(
            loop_body,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: i_val2,
                rhs: one,
            },
        );
        self.store_at_dynamic_offset(loop_body, agg_ptr, slot, elem);
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
        self.store_reg_ptr(loop_done, rd, agg_ptr)?;
        self.emit(
            loop_done,
            InstrNode::new(Inst::Br {
                target: done_id,
                args: vec![],
            }),
        );

        Ok(Some(done_block))
    }
}
