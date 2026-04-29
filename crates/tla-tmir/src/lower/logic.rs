// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Comparison and boolean operation lowering: Eq, Neq, Lt, Le, Gt, Ge,
//! And, Or, Not, Implies, Equiv, CondMove.

use crate::TmirError;
use tmir::inst::*;
use tmir::ty::Ty;
use tmir::Constant;

use super::{AggregateShape, Ctx, ScalarShape, SequenceExtent};

impl<'cp> Ctx<'cp> {
    fn store_bool_reg(
        &mut self,
        block_idx: usize,
        rd: u8,
        value: tmir::value::ValueId,
    ) -> Result<(), TmirError> {
        self.store_reg_value(block_idx, rd, value)?;
        self.aggregate_shapes
            .insert(rd, AggregateShape::Scalar(ScalarShape::Bool));
        self.const_scalar_values.remove(&rd);
        self.const_set_sizes.remove(&rd);
        self.compact_state_slots.remove(&rd);
        Ok(())
    }

    pub(super) fn lower_comparison(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        predicate: ICmpOp,
    ) -> Result<(), TmirError> {
        if let Some(value) = self.scalar_equality_static_result(r1, r2, predicate) {
            let result = self.emit_i64_const(block_idx, i64::from(value));
            return self.store_bool_reg(block_idx, rd, result);
        }
        if self.lower_compact_set_bitmask_comparison(block_idx, rd, r1, r2, predicate)? {
            return Ok(());
        }
        if self.lower_sequence_comparison(block_idx, rd, r1, r2, predicate)? {
            return Ok(());
        }
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;
        let cmp = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: predicate,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        // Zero-extend bool to i64 (0 or 1).
        let result = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: cmp,
            },
        );
        self.store_bool_reg(block_idx, rd, result)
    }

    fn lower_compact_set_bitmask_comparison(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        predicate: ICmpOp,
    ) -> Result<bool, TmirError> {
        if !matches!(predicate, ICmpOp::Eq | ICmpOp::Ne) {
            return Ok(false);
        }

        let Some((universe_len, universe)) =
            self.compact_binary_set_universe("Set equality", r1, r2)?
        else {
            return Ok(false);
        };

        let (block_idx, left, left_in_universe) = self.emit_set_subseteq_operand_bitmask_i64(
            block_idx,
            r1,
            universe_len,
            &universe,
            "Set equality",
        )?;
        let (block_idx, right, right_in_universe) = self.emit_set_subseteq_operand_bitmask_i64(
            block_idx,
            r2,
            universe_len,
            &universe,
            "Set equality",
        )?;

        let same_mask = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: left,
                rhs: right,
            },
        );
        let same_mask = self.emit_logic_bool_to_i64(block_idx, same_mask);
        let both_in_universe = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::And,
                ty: Ty::I64,
                lhs: left_in_universe,
                rhs: right_in_universe,
            },
        );
        let left_canonical =
            self.emit_compact_bitmask_canonical_i64(block_idx, left, universe_len, "Set equality")?;
        let right_canonical = self.emit_compact_bitmask_canonical_i64(
            block_idx,
            right,
            universe_len,
            "Set equality",
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

        let result = match predicate {
            ICmpOp::Eq => {
                let equal_core = self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: same_mask,
                        rhs: both_in_universe,
                    },
                );
                self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: equal_core,
                        rhs: canonical,
                    },
                )
            }
            ICmpOp::Ne => {
                let zero = self.emit_i64_const(block_idx, 0);
                let masks_differ = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        lhs: same_mask,
                        rhs: zero,
                    },
                );
                let masks_differ = self.emit_logic_bool_to_i64(block_idx, masks_differ);
                let outside_universe = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        lhs: both_in_universe,
                        rhs: zero,
                    },
                );
                let outside_universe = self.emit_logic_bool_to_i64(block_idx, outside_universe);
                let not_equal_core = self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::Or,
                        ty: Ty::I64,
                        lhs: masks_differ,
                        rhs: outside_universe,
                    },
                );
                self.emit_with_result(
                    block_idx,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: not_equal_core,
                        rhs: canonical,
                    },
                )
            }
            _ => unreachable!("caller filters to Eq/Ne"),
        };

        self.store_bool_reg(block_idx, rd, result)?;
        Ok(true)
    }

    fn lower_sequence_comparison(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        predicate: ICmpOp,
    ) -> Result<bool, TmirError> {
        if !matches!(predicate, ICmpOp::Eq | ICmpOp::Ne) {
            return Ok(false);
        }
        let lhs_shape = self.aggregate_shapes.get(&r1).cloned();
        let rhs_shape = self.aggregate_shapes.get(&r2).cloned();
        let lhs_is_sequence = matches!(lhs_shape, Some(AggregateShape::Sequence { .. }));
        let rhs_is_sequence = matches!(rhs_shape, Some(AggregateShape::Sequence { .. }));
        if !lhs_is_sequence && !rhs_is_sequence {
            return Ok(false);
        }
        if lhs_is_sequence != rhs_is_sequence {
            if lhs_shape
                .as_ref()
                .zip(rhs_shape.as_ref())
                .is_some_and(|(lhs, rhs)| {
                    !matches!(lhs, AggregateShape::StateValue)
                        && !matches!(rhs, AggregateShape::StateValue)
                })
            {
                let value = match predicate {
                    ICmpOp::Eq => 0,
                    ICmpOp::Ne => 1,
                    _ => unreachable!("caller filters to Eq/Ne"),
                };
                let result = self.emit_i64_const(block_idx, value);
                self.store_bool_reg(block_idx, rd, result)?;
                return Ok(true);
            }
            return Err(TmirError::UnsupportedOpcode(format!(
                "sequence equality requires both operands to have tracked sequence shapes, got r{r1}={lhs_shape:?}, r{r2}={rhs_shape:?}"
            )));
        }

        let (
            Some(
                lhs_shape @ AggregateShape::Sequence {
                    extent: lhs_extent, ..
                },
            ),
            Some(
                rhs_shape @ AggregateShape::Sequence {
                    extent: rhs_extent, ..
                },
            ),
        ) = (lhs_shape.clone(), rhs_shape.clone())
        else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "sequence equality requires tracked sequence shapes, got r{r1}={lhs_shape:?}, r{r2}={rhs_shape:?}"
            )));
        };

        let lhs_empty = lhs_extent.exact_count() == Some(0);
        let rhs_empty = rhs_extent.exact_count() == Some(0);
        let result = match (lhs_empty, rhs_empty) {
            (true, true) => {
                let value = match predicate {
                    ICmpOp::Eq => 1,
                    ICmpOp::Ne => 0,
                    _ => unreachable!("caller filters to Eq/Ne"),
                };
                self.emit_i64_const(block_idx, value)
            }
            (false, true) => {
                self.emit_sequence_len_comparison(block_idx, r1, &lhs_shape, predicate)?
            }
            (true, false) => {
                self.emit_sequence_len_comparison(block_idx, r2, &rhs_shape, predicate)?
            }
            (false, false) => {
                return self.lower_structural_sequence_comparison(
                    block_idx, rd, r1, &lhs_shape, r2, &rhs_shape, predicate,
                );
            }
        };
        self.store_bool_reg(block_idx, rd, result)?;
        Ok(true)
    }

    fn lower_structural_sequence_comparison(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        lhs_shape: &AggregateShape,
        r2: u8,
        rhs_shape: &AggregateShape,
        predicate: ICmpOp,
    ) -> Result<bool, TmirError> {
        let (
            AggregateShape::Sequence {
                extent: lhs_extent, ..
            },
            AggregateShape::Sequence {
                extent: rhs_extent, ..
            },
        ) = (lhs_shape, rhs_shape)
        else {
            return Ok(false);
        };

        if let (Some(lhs_len), Some(rhs_len)) = (lhs_extent.exact_count(), rhs_extent.exact_count())
        {
            if lhs_len != rhs_len {
                let value = match predicate {
                    ICmpOp::Eq => 0,
                    ICmpOp::Ne => 1,
                    _ => unreachable!("caller filters to Eq/Ne"),
                };
                let result = self.emit_i64_const(block_idx, value);
                self.store_bool_reg(block_idx, rd, result)?;
                return Ok(true);
            }
        }

        let comparison_shape = Self::sequence_comparison_shape(lhs_shape, rhs_shape)?;
        let lhs_materialized =
            self.materialize_reg_as_compact_source(block_idx, r1, &comparison_shape)?;
        let rhs_materialized = self.materialize_reg_as_compact_source(
            lhs_materialized.block_idx,
            r2,
            &comparison_shape,
        )?;
        let block_idx = rhs_materialized.block_idx;
        let slot_count = comparison_shape.compact_slot_count().ok_or_else(|| {
            TmirError::UnsupportedOpcode(format!(
                "sequence equality requires fixed-width compact shape, got {comparison_shape:?}"
            ))
        })?;

        let mut equal = self.emit_i64_const(block_idx, 1);
        for slot in 0..slot_count {
            let lhs_offset = lhs_materialized
                .slot
                .offset
                .checked_add(slot)
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "sequence equality left compact slot offset overflows u32".to_owned(),
                    )
                })?;
            let rhs_offset = rhs_materialized
                .slot
                .offset
                .checked_add(slot)
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "sequence equality right compact slot offset overflows u32".to_owned(),
                    )
                })?;
            let lhs = self.load_at_offset(block_idx, lhs_materialized.slot.source_ptr, lhs_offset);
            let rhs = self.load_at_offset(block_idx, rhs_materialized.slot.source_ptr, rhs_offset);
            let slot_eq = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs,
                    rhs,
                },
            );
            let slot_eq = self.emit_logic_bool_to_i64(block_idx, slot_eq);
            equal = self.emit_with_result(
                block_idx,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    lhs: equal,
                    rhs: slot_eq,
                },
            );
        }

        let result = match predicate {
            ICmpOp::Eq => equal,
            ICmpOp::Ne => {
                let zero = self.emit_i64_const(block_idx, 0);
                let neq = self.emit_with_result(
                    block_idx,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        lhs: equal,
                        rhs: zero,
                    },
                );
                self.emit_logic_bool_to_i64(block_idx, neq)
            }
            _ => unreachable!("caller filters to Eq/Ne"),
        };
        self.store_bool_reg(block_idx, rd, result)?;
        Ok(true)
    }

    fn sequence_comparison_shape(
        lhs_shape: &AggregateShape,
        rhs_shape: &AggregateShape,
    ) -> Result<AggregateShape, TmirError> {
        let (
            AggregateShape::Sequence {
                extent: lhs_extent,
                element: lhs_element,
            },
            AggregateShape::Sequence {
                extent: rhs_extent,
                element: rhs_element,
            },
        ) = (lhs_shape, rhs_shape)
        else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "sequence equality requires sequence shapes, got {lhs_shape:?} and {rhs_shape:?}"
            )));
        };

        let capacity = lhs_extent.capacity().max(rhs_extent.capacity());
        let extent = match (lhs_extent.exact_count(), rhs_extent.exact_count()) {
            (Some(lhs_len), Some(rhs_len)) if lhs_len == rhs_len => SequenceExtent::Exact(lhs_len),
            _ => SequenceExtent::Capacity(capacity),
        };
        let element = if capacity == 0 {
            None
        } else {
            let lhs_element = lhs_element.as_deref().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "structural sequence equality requires tracked left element shape, got {lhs_shape:?}"
                ))
            })?;
            let rhs_element = rhs_element.as_deref().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "structural sequence equality requires tracked right element shape, got {rhs_shape:?}"
                ))
            })?;
            let element = super::merge_compatible_shapes(Some(lhs_element), Some(rhs_element))
                .ok_or_else(|| {
                    TmirError::UnsupportedOpcode(format!(
                        "structural sequence equality requires compatible element shapes, got {lhs_element:?} and {rhs_element:?}"
                    ))
                })?;
            if !Self::compatible_compact_materialization_value(lhs_element, &element)
                || !Self::compatible_compact_materialization_value(rhs_element, &element)
                || element.compact_slot_count().is_none()
            {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "structural sequence equality requires fixed-width compatible element materialization, got {lhs_element:?}, {rhs_element:?}, merged={element:?}"
                )));
            }
            Some(Box::new(element))
        };
        Ok(AggregateShape::Sequence { extent, element })
    }

    fn emit_logic_bool_to_i64(
        &mut self,
        block_idx: usize,
        value: tmir::value::ValueId,
    ) -> tmir::value::ValueId {
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

    fn emit_sequence_len_comparison(
        &mut self,
        block_idx: usize,
        reg: u8,
        shape: &AggregateShape,
        predicate: ICmpOp,
    ) -> Result<tmir::value::ValueId, TmirError> {
        let len = self.sequence_len_value(block_idx, reg, shape)?;
        let zero = self.emit_i64_const(block_idx, 0);
        let cmp = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: predicate,
                ty: Ty::I64,
                lhs: len,
                rhs: zero,
            },
        );
        Ok(self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: cmp,
            },
        ))
    }

    fn sequence_len_value(
        &mut self,
        block_idx: usize,
        reg: u8,
        shape: &AggregateShape,
    ) -> Result<tmir::value::ValueId, TmirError> {
        let AggregateShape::Sequence { extent, .. } = shape else {
            return Err(TmirError::UnsupportedOpcode(format!(
                "sequence equality expected sequence shape for r{reg}, got {shape:?}"
            )));
        };
        if let Some(exact) = extent.exact_count() {
            return Ok(self.emit_i64_const(block_idx, i64::from(exact)));
        }
        if let Some(source_slot) = self.compact_state_slot_for_use(block_idx, reg)? {
            return Ok(self.load_at_offset(block_idx, source_slot.source_ptr, source_slot.offset));
        }
        let ptr = self.load_reg_as_ptr(block_idx, reg)?;
        Ok(self.load_at_offset(block_idx, ptr, 0))
    }

    fn scalar_equality_static_result(&self, r1: u8, r2: u8, predicate: ICmpOp) -> Option<bool> {
        if !matches!(predicate, ICmpOp::Eq | ICmpOp::Ne) {
            return None;
        }

        let lhs = self.aggregate_shapes.get(&r1);
        let rhs = self.aggregate_shapes.get(&r2);
        match (lhs, rhs) {
            (Some(AggregateShape::Scalar(left)), Some(AggregateShape::Scalar(right)))
                if left != right =>
            {
                Some(matches!(predicate, ICmpOp::Ne))
            }
            _ => None,
        }
    }

    pub(super) fn lower_boolean_binary(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
        op: BinOp,
    ) -> Result<(), TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;
        let result = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        self.store_bool_reg(block_idx, rd, result)
    }

    pub(super) fn lower_not(&mut self, block_idx: usize, rd: u8, rs: u8) -> Result<(), TmirError> {
        let value = self.load_reg(block_idx, rs)?;
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        // NOT: value == 0
        let cmp = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs: value,
                rhs: zero,
            },
        );
        let result = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: cmp,
            },
        );
        self.store_bool_reg(block_idx, rd, result)
    }

    pub(super) fn lower_implies(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<(), TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        // !lhs: lhs == 0
        let not_lhs = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs,
                rhs: zero,
            },
        );
        // rhs != 0
        let rhs_bool = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: rhs,
                rhs: zero,
            },
        );
        // implies = !lhs || rhs
        let or_result = self.emit_with_result(
            block_idx,
            Inst::BinOp {
                op: BinOp::Or,
                ty: Ty::Bool,
                lhs: not_lhs,
                rhs: rhs_bool,
            },
        );
        let result = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: or_result,
            },
        );
        self.store_bool_reg(block_idx, rd, result)
    }

    pub(super) fn lower_equiv(
        &mut self,
        block_idx: usize,
        rd: u8,
        r1: u8,
        r2: u8,
    ) -> Result<(), TmirError> {
        let lhs = self.load_reg(block_idx, r1)?;
        let rhs = self.load_reg(block_idx, r2)?;
        // Equivalence on i64 booleans: lhs == rhs
        let cmp = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        );
        let result = self.emit_with_result(
            block_idx,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: cmp,
            },
        );
        self.store_bool_reg(block_idx, rd, result)
    }

    pub(super) fn lower_cond_move(
        &mut self,
        block_idx: usize,
        rd: u8,
        cond: u8,
        rs: u8,
    ) -> Result<usize, TmirError> {
        let merged_shape = super::merge_compatible_shapes(
            self.aggregate_shapes.get(&rd),
            self.aggregate_shapes.get(&rs),
        );
        if merged_shape.is_none() {
            if let (Some(AggregateShape::Scalar(left)), Some(AggregateShape::Scalar(right))) = (
                self.aggregate_shapes.get(&rd),
                self.aggregate_shapes.get(&rs),
            ) {
                if left != right {
                    return Err(TmirError::UnsupportedOpcode(format!(
                        "CondMove over incompatible scalar lanes requires tagged selection: {left:?} vs {right:?}"
                    )));
                }
            }
        }
        if merged_shape
            .as_ref()
            .is_some_and(Self::is_compact_compound_aggregate)
        {
            let shape = merged_shape.as_ref().ok_or_else(|| {
                TmirError::UnsupportedOpcode(
                    "CondMove over compact aggregate values requires a merged shape".to_owned(),
                )
            })?;
            let current_shape = self.aggregate_shapes.get(&rd).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "CondMove over compact aggregate r{rd} requires tracked current shape"
                ))
            })?;
            let source_shape = self.aggregate_shapes.get(&rs).ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "CondMove over compact aggregate r{rs} requires tracked source shape"
                ))
            })?;
            if !Self::compatible_compact_materialization_value(current_shape, shape)
                || !Self::compatible_compact_materialization_value(source_shape, shape)
            {
                return Err(TmirError::UnsupportedOpcode(format!(
                    "CondMove over compact aggregate values requires compatible slot materialization, got current={current_shape:?}, source={source_shape:?}, merged={shape:?}"
                )));
            }
            let slot_count = shape.compact_slot_count().ok_or_else(|| {
                TmirError::UnsupportedOpcode(format!(
                    "CondMove over compact aggregate requires fixed-width shape, got {shape:?}"
                ))
            })?;
            let current_materialized =
                self.materialize_reg_as_compact_source(block_idx, rd, shape)?;
            let source_materialized =
                self.materialize_reg_as_compact_source(current_materialized.block_idx, rs, shape)?;
            let block_idx = source_materialized.block_idx;
            let current_slot = current_materialized.slot;
            let source_slot = source_materialized.slot;
            let cond_value = self.load_reg(block_idx, cond)?;
            let zero = self.emit_with_result(
                block_idx,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                },
            );
            let cond_bool = self.emit_with_result(
                block_idx,
                Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: Ty::I64,
                    lhs: cond_value,
                    rhs: zero,
                },
            );
            let result_ptr = self.alloc_aggregate(block_idx, slot_count);
            for offset in 0..slot_count {
                let current_offset = current_slot.offset.checked_add(offset).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "CondMove compact aggregate current slot overflows u32".to_owned(),
                    )
                })?;
                let source_offset = source_slot.offset.checked_add(offset).ok_or_else(|| {
                    TmirError::UnsupportedOpcode(
                        "CondMove compact aggregate source slot overflows u32".to_owned(),
                    )
                })?;
                let current_value =
                    self.load_at_offset(block_idx, current_slot.source_ptr, current_offset);
                let source_value =
                    self.load_at_offset(block_idx, source_slot.source_ptr, source_offset);
                let result = self.emit_with_result(
                    block_idx,
                    Inst::Select {
                        ty: Ty::I64,
                        cond: cond_bool,
                        then_val: source_value,
                        else_val: current_value,
                    },
                );
                self.store_at_offset(block_idx, result_ptr, offset, result);
            }
            self.store_reg_ptr(block_idx, rd, result_ptr)?;
            self.compact_state_slots
                .insert(rd, super::CompactStateSlot::pointer_backed(result_ptr, 0));
            self.const_scalar_values.remove(&rd);
            self.const_set_sizes.remove(&rd);
            if let Some(len) = shape.tracked_len() {
                self.const_set_sizes.insert(rd, len);
            }
            self.aggregate_shapes.insert(rd, shape.clone());
            return Ok(block_idx);
        }
        let cond_value = self.load_reg(block_idx, cond)?;
        let current = self.load_reg(block_idx, rd)?;
        let source = self.load_reg(block_idx, rs)?;
        let zero = self.emit_with_result(
            block_idx,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        );
        let cond_bool = self.emit_with_result(
            block_idx,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: cond_value,
                rhs: zero,
            },
        );
        let result = self.emit_with_result(
            block_idx,
            Inst::Select {
                ty: Ty::I64,
                cond: cond_bool,
                then_val: source,
                else_val: current,
            },
        );
        self.store_reg_value(block_idx, rd, result)?;
        self.compact_state_slots.remove(&rd);
        self.const_scalar_values.remove(&rd);
        self.const_set_sizes.remove(&rd);
        if let Some(shape) = merged_shape {
            if let Some(len) = shape.tracked_len() {
                self.const_set_sizes.insert(rd, len);
            }
            self.aggregate_shapes.insert(rd, shape);
        } else {
            self.aggregate_shapes.remove(&rd);
        }
        Ok(block_idx)
    }
}
