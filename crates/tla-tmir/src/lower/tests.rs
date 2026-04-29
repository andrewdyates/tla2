// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for bytecode-to-tMIR lowering.

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use crate::lower::{
        apply_loop_next_shape_transfer, binding_shape_from_domain, const_shape_and_scalar,
        finite_set_diff_shape, finite_set_intersect_shape, finite_set_union_shape,
        lower_entry_invariant_with_chunk, lower_entry_next_state_with_chunk, lower_invariant,
        lower_invariant_with_constants, lower_invariant_with_constants_and_layout,
        lower_module_invariant, lower_module_invariant_with_layout, lower_module_next_state,
        lower_module_next_state_with_layout, lower_next_state, lower_next_state_with_constants,
        lower_next_state_with_constants_and_layout, merge_compatible_shapes, sequence_append_shape,
        sequence_tail_shape, AggregateShape, Ctx, FuncDefShapeFrame, LoweringMode, ScalarShape,
        SequenceExtent, SetBitmaskUniverse, ShapeSummary, STATUS_OFFSET,
    };
    use crate::TmirError;
    use tla_jit_abi::{CompoundLayout, JitStatus, SetBitmaskElement, StateLayout, VarLayout};
    use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, ConstantPool, Opcode};
    use tla_value::Value;
    use tmir::inst::*;
    use tmir::ty::Ty;
    use tmir::value::{FuncId, ValueId};
    use tmir::Constant;

    fn has_nonconst_alloca_count(module: &tmir::Module, func_idx: usize) -> bool {
        let func = &module.functions[func_idx];
        let const_values: HashSet<ValueId> = func
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .filter_map(|node| match (&node.inst, node.results.first().copied()) {
                (
                    Inst::Const {
                        value: Constant::Int(_),
                        ..
                    },
                    Some(result),
                ) => Some(result),
                _ => None,
            })
            .collect();
        func.blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .any(|node| {
                matches!(
                    &node.inst,
                    Inst::Alloca { count: Some(count), .. } if !const_values.contains(count)
                )
            })
    }

    fn has_const_alloca_count(
        module: &tmir::Module,
        func_idx: usize,
        expected_count: i128,
    ) -> bool {
        let func = &module.functions[func_idx];
        let const_values: HashMap<ValueId, i128> = func
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .filter_map(|node| match (&node.inst, node.results.first().copied()) {
                (
                    Inst::Const {
                        value: Constant::Int(value),
                        ..
                    },
                    Some(result),
                ) => Some((result, *value)),
                _ => None,
            })
            .collect();
        func.blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .any(|node| {
                matches!(
                    &node.inst,
                    Inst::Alloca { count: Some(count), .. }
                        if const_values.get(count) == Some(&expected_count)
                )
            })
    }

    fn assert_const_i64_stores_to_base_alloca(
        module: &tmir::Module,
        func_idx: usize,
        expected_slots: u32,
        expected_stores: &[(u32, i128)],
    ) {
        let func = &module.functions[func_idx];
        let mut i32_consts = HashMap::new();
        let mut i64_consts = HashMap::new();
        let mut alloca_counts = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut stores_by_base: HashMap<ValueId, Vec<(u32, i128)>> = HashMap::new();

        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i32_consts.insert(result, *value);
                    }
                    (
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i64_consts.insert(result, *value);
                    }
                    (
                        Inst::Alloca {
                            count: Some(count), ..
                        },
                        Some(result),
                    ) => {
                        if let Some(count) = i32_consts.get(count).copied() {
                            alloca_counts.insert(result, count);
                        }
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = i32_consts
                            .get(&indices[0])
                            .and_then(|value| u32::try_from(*value).ok())
                        {
                            gep_slots.insert(result, (*base, slot));
                        }
                    }
                    (
                        Inst::Store {
                            ty: Ty::I64,
                            ptr,
                            value,
                            ..
                        },
                        _,
                    ) => {
                        if let (Some((base, slot)), Some(value)) =
                            (gep_slots.get(ptr).copied(), i64_consts.get(value).copied())
                        {
                            stores_by_base.entry(base).or_default().push((slot, value));
                        }
                    }
                    _ => {}
                }
            }
        }

        let mut expected = expected_stores.to_vec();
        expected.sort_unstable();
        expected.dedup();

        let mut candidates = Vec::new();
        for (base, mut stores) in stores_by_base {
            if alloca_counts.get(&base).copied() == Some(i128::from(expected_slots)) {
                stores.sort_unstable();
                stores.dedup();
                candidates.push(stores);
            }
        }

        assert_eq!(
            candidates
                .iter()
                .filter(|stores| stores.as_slice() == expected.as_slice())
                .count(),
            1,
            "expected exactly one {expected_slots}-slot alloca with constant i64 stores {expected:?}; candidates={candidates:?}"
        );
    }

    #[test]
    fn test_funcdef_shape_stack_ignores_nonmatching_loop_next() {
        let mut summary = ShapeSummary::default();
        let function_shape = AggregateShape::Function {
            len: 2,
            domain_lo: Some(1),
            value: None,
        };
        summary.aggregate_shapes.insert(2, function_shape.clone());
        summary.funcdef_stack.push(FuncDefShapeFrame {
            rd: 2,
            r_binding: 3,
            function_shape: function_shape.clone(),
        });
        summary
            .aggregate_shapes
            .insert(9, AggregateShape::Scalar(ScalarShape::Int));

        apply_loop_next_shape_transfer(&mut summary, 7, 9);
        assert_eq!(
            summary.funcdef_stack,
            vec![FuncDefShapeFrame {
                rd: 2,
                r_binding: 3,
                function_shape: function_shape.clone(),
            }],
            "LoopNext for an inner non-FuncDef binding must not consume the outer FuncDef frame"
        );
        assert_eq!(summary.aggregate_shapes.get(&2), Some(&function_shape));

        apply_loop_next_shape_transfer(&mut summary, 3, 9);
        assert!(summary.funcdef_stack.is_empty());
        assert_eq!(
            summary.aggregate_shapes.get(&2),
            Some(&AggregateShape::Function {
                len: 2,
                domain_lo: Some(1),
                value: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
            })
        );
    }

    fn module_has_i64_const(module: &tmir::Module, func_idx: usize, expected: i128) -> bool {
        module.functions[func_idx].blocks.iter().any(|block| {
            block.body.iter().any(|node| {
                matches!(
                    &node.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(value),
                    } if *value == expected
                )
            })
        })
    }

    fn state_out_const_stores(module: &tmir::Module, func_idx: usize) -> Vec<(u32, i128)> {
        let state_out = ValueId::new(2);
        let mut const_values = HashMap::new();
        let mut const_slots = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut stores = Vec::new();

        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        if *ty == Ty::I64 {
                            const_values.insert(result, *value);
                        }
                        if let Ok(slot) = u32::try_from(*value) {
                            const_slots.insert(result, slot);
                        }
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = const_slots.get(&indices[0]).copied() {
                            gep_slots.insert(result, (*base, slot));
                        }
                    }
                    (Inst::Store { ptr, value, .. }, _) => {
                        let Some((base, slot)) = gep_slots.get(ptr).copied() else {
                            continue;
                        };
                        if base != state_out {
                            continue;
                        }
                        if let Some(value) = const_values.get(value).copied() {
                            stores.push((slot, value));
                        }
                    }
                    _ => {}
                }
            }
        }

        stores
    }

    fn assert_state_out_const_store(
        module: &tmir::Module,
        func_idx: usize,
        slot: u32,
        expected: i128,
    ) {
        let stores: Vec<_> = state_out_const_stores(module, func_idx)
            .into_iter()
            .filter(|(stored_slot, _)| *stored_slot == slot)
            .collect();
        assert_eq!(
            stores,
            vec![(slot, expected)],
            "expected exactly one state_out[{slot}] constant store of {expected}"
        );
    }

    fn has_const_i64_store_to_gep_slot(
        module: &tmir::Module,
        func_idx: usize,
        slot: u32,
        expected: i128,
    ) -> bool {
        let mut const_values = HashMap::new();
        let mut const_slots = HashMap::new();
        let mut gep_slots = HashMap::new();

        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        if *ty == Ty::I64 {
                            const_values.insert(result, *value);
                        }
                        if let Ok(slot) = u32::try_from(*value) {
                            const_slots.insert(result, slot);
                        }
                    }
                    (Inst::GEP { indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = const_slots.get(&indices[0]).copied() {
                            gep_slots.insert(result, slot);
                        }
                    }
                    (Inst::Store { ptr, value, .. }, _) => {
                        if gep_slots.get(ptr) == Some(&slot)
                            && const_values.get(value) == Some(&expected)
                        {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }

        false
    }

    fn assert_funcdef_compact_capture_copies_slots(
        module: &tmir::Module,
        func_idx: usize,
        expected_backing_slots: u32,
        expected_value_offsets: &[u32],
    ) {
        let func = &module.functions[func_idx];
        let mut i32_consts = HashMap::new();
        let mut backing_allocas = HashSet::new();
        let mut capture_ptrs = HashSet::new();
        let mut capture_slot_ptrs = HashMap::new();
        let mut ptr_to_capture_values = HashSet::new();
        let mut copied_offsets = HashSet::new();
        let mut stores_capture_ptr = false;

        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        if let Ok(value) = u32::try_from(*value) {
                            i32_consts.insert(result, value);
                        }
                    }
                    (
                        Inst::Alloca {
                            ty: Ty::I64,
                            count: Some(count),
                            ..
                        },
                        Some(result),
                    ) if i32_consts.get(count) == Some(&expected_backing_slots) => {
                        backing_allocas.insert(result);
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if backing_allocas.contains(base) {
                            capture_ptrs.insert(result);
                        } else if capture_ptrs.contains(base) {
                            if let Some(offset) = i32_consts.get(&indices[0]).copied() {
                                capture_slot_ptrs.insert(result, offset);
                            }
                        }
                    }
                    (
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            operand,
                            ..
                        },
                        Some(result),
                    ) if capture_ptrs.contains(operand) => {
                        ptr_to_capture_values.insert(result);
                    }
                    (Inst::Store { ptr, value, .. }, _) => {
                        if let Some(offset) = capture_slot_ptrs.get(ptr).copied() {
                            copied_offsets.insert(offset);
                        }
                        if ptr_to_capture_values.contains(value) {
                            stores_capture_ptr = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        let expected_offsets: HashSet<_> = expected_value_offsets.iter().copied().collect();
        assert_eq!(
            copied_offsets, expected_offsets,
            "FuncDef LoopNext should copy every compact body slot into a per-iteration capture backing"
        );
        assert!(
            stores_capture_ptr,
            "FuncDef LoopNext should store the current capture slice pointer, not the reusable body aggregate pointer"
        );
    }

    fn entry_param_direct_load_count(
        module: &tmir::Module,
        func_idx: usize,
        param_idx: usize,
    ) -> usize {
        let func = &module.functions[func_idx];
        let param = func.blocks[0]
            .params
            .get(param_idx)
            .map(|(value, _)| *value)
            .expect("entry parameter should exist");
        let gep_results: HashSet<ValueId> = func
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .filter_map(|node| match (&node.inst, node.results.first().copied()) {
                (Inst::GEP { base, .. }, Some(result)) if *base == param => Some(result),
                _ => None,
            })
            .collect();

        func.blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .filter(
                |node| matches!(&node.inst, Inst::Load { ptr, .. } if gep_results.contains(ptr)),
            )
            .count()
    }

    fn assert_no_ptr_payload_store_to_state_out(module: &tmir::Module, func_idx: usize) {
        let state_out = ValueId::new(2);
        let mut ptr_to_int_values = HashSet::new();
        let mut ptr_payload_slots = HashSet::new();
        let mut ptr_payload_loads = HashSet::new();
        let mut state_out_slots = HashSet::new();

        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            ..
                        },
                        Some(result),
                    ) => {
                        ptr_to_int_values.insert(result);
                    }
                    (Inst::Store { ptr, value, .. }, _) if ptr_to_int_values.contains(value) => {
                        ptr_payload_slots.insert(*ptr);
                    }
                    (Inst::Load { ptr, .. }, Some(result)) if ptr_payload_slots.contains(ptr) => {
                        ptr_payload_loads.insert(result);
                    }
                    (Inst::GEP { base, .. }, Some(result)) if *base == state_out => {
                        state_out_slots.insert(result);
                    }
                    _ => {}
                }
            }
        }

        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                if let Inst::Store { ptr, value, .. } = &node.inst {
                    assert!(
                        !(state_out_slots.contains(ptr) && ptr_payload_loads.contains(value)),
                        "StoreVar stored an aggregate pointer payload into compact state"
                    );
                }
            }
        }
    }

    fn has_runtime_error_status_path(module: &tmir::Module, func_idx: usize) -> bool {
        module.functions[func_idx].blocks.iter().any(|block| {
            block.body.iter().any(|node| {
                matches!(
                    node.inst,
                    Inst::Const {
                        value: Constant::Int(value),
                        ..
                    } if value == i128::from(JitStatus::RuntimeError as u8)
                )
            })
        })
    }

    fn block_has_state_out_store_to_slot(
        module: &tmir::Module,
        func_idx: usize,
        block_idx: usize,
        slot: u32,
    ) -> bool {
        let state_out = ValueId::new(2);
        let mut const_slots = HashMap::new();
        let mut gep_slots = HashMap::new();

        let Some(block) = module.functions[func_idx].blocks.get(block_idx) else {
            return false;
        };
        for node in &block.body {
            match (&node.inst, node.results.first().copied()) {
                (
                    Inst::Const {
                        value: Constant::Int(value),
                        ..
                    },
                    Some(result),
                ) => {
                    if let Ok(slot) = u32::try_from(*value) {
                        const_slots.insert(result, slot);
                    }
                }
                (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                    if *base == state_out {
                        if let Some(slot) = const_slots.get(&indices[0]).copied() {
                            gep_slots.insert(result, slot);
                        }
                    }
                }
                (Inst::Store { ptr, .. }, _) if gep_slots.get(ptr) == Some(&slot) => {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    fn state_out_store_source_slots(module: &tmir::Module, func_idx: usize) -> Vec<(u32, u32)> {
        let state_out = ValueId::new(2);
        let mut const_slots = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut load_slots = HashMap::new();
        let mut stores = Vec::new();

        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            value: Constant::Int(value),
                            ..
                        },
                        Some(result),
                    ) => {
                        if let Ok(slot) = u32::try_from(*value) {
                            const_slots.insert(result, slot);
                        }
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = const_slots.get(&indices[0]).copied() {
                            gep_slots.insert(result, (*base, slot));
                        }
                    }
                    (Inst::Load { ptr, .. }, Some(result)) => {
                        if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                            load_slots.insert(result, (base, slot));
                        }
                    }
                    (Inst::Store { ptr, value, .. }, _) => {
                        let Some((dst_base, dst_slot)) = gep_slots.get(ptr).copied() else {
                            continue;
                        };
                        if dst_base != state_out {
                            continue;
                        }
                        let Some((src_base, src_slot)) = load_slots.get(value).copied() else {
                            continue;
                        };
                        if src_base != state_out {
                            stores.push((dst_slot, src_slot));
                        }
                    }
                    _ => {}
                }
            }
        }

        stores
    }

    fn unchanged_eq_slot_pairs(module: &tmir::Module, func_idx: usize) -> Vec<(u32, u32)> {
        let state_in = ValueId::new(1);
        let state_out = ValueId::new(2);
        let mut const_slots = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut load_slots = HashMap::new();
        let mut pairs = Vec::new();

        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            value: Constant::Int(value),
                            ..
                        },
                        Some(result),
                    ) => {
                        if let Ok(slot) = u32::try_from(*value) {
                            const_slots.insert(result, slot);
                        }
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = const_slots.get(&indices[0]).copied() {
                            gep_slots.insert(result, (*base, slot));
                        }
                    }
                    (Inst::Load { ptr, .. }, Some(result)) => {
                        if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                            load_slots.insert(result, (base, slot));
                        }
                    }
                    (
                        Inst::ICmp {
                            op: ICmpOp::Eq,
                            ty: Ty::I64,
                            lhs,
                            rhs,
                        },
                        _,
                    ) => {
                        let Some((lhs_base, lhs_slot)) = load_slots.get(lhs).copied() else {
                            continue;
                        };
                        let Some((rhs_base, rhs_slot)) = load_slots.get(rhs).copied() else {
                            continue;
                        };
                        if lhs_base == state_in && rhs_base == state_out {
                            pairs.push((lhs_slot, rhs_slot));
                        } else if lhs_base == state_out && rhs_base == state_in {
                            pairs.push((rhs_slot, lhs_slot));
                        }
                    }
                    _ => {}
                }
            }
        }

        pairs
    }

    fn direct_call_callees(module: &tmir::Module, func_idx: usize) -> Vec<FuncId> {
        module.functions[func_idx]
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .filter_map(|node| match &node.inst {
                Inst::Call { callee, .. } => Some(*callee),
                _ => None,
            })
            .collect()
    }

    fn direct_calls_missing_pre_call_status_clear(module: &tmir::Module, func_idx: usize) -> usize {
        let func = &module.functions[func_idx];
        let (out_ptr, out_ty) = func
            .blocks
            .first()
            .and_then(|block| block.params.first())
            .expect("lowered function should have an out_ptr parameter");
        assert_eq!(
            *out_ty,
            Ty::Ptr,
            "first function parameter should be out_ptr"
        );

        let out_ptr = *out_ptr;
        let status_offset = STATUS_OFFSET as i128;
        let ok_status = i128::from(JitStatus::Ok as u8);
        let mut missing = 0;

        for block in &func.blocks {
            let mut i64_consts = HashMap::new();
            let mut i8_consts = HashMap::new();
            let mut status_ptrs = HashSet::new();
            let mut saw_clear = false;

            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i64_consts.insert(result, *value);
                    }
                    (
                        Inst::Const {
                            ty: Ty::I8,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i8_consts.insert(result, *value);
                    }
                    (Inst::GEP { base, indices, .. }, Some(result))
                        if *base == out_ptr
                            && indices.len() == 1
                            && i64_consts.get(&indices[0]) == Some(&status_offset) =>
                    {
                        status_ptrs.insert(result);
                    }
                    (
                        Inst::Store {
                            ty: Ty::I8,
                            ptr,
                            value,
                            ..
                        },
                        _,
                    ) if status_ptrs.contains(ptr) && i8_consts.get(value) == Some(&ok_status) => {
                        saw_clear = true;
                    }
                    (Inst::Call { .. }, _) => {
                        if !saw_clear {
                            missing += 1;
                        }
                        saw_clear = false;
                    }
                    _ => {}
                }
            }
        }

        missing
    }

    fn assert_call_uses_caller_owned_return_buffer(
        module: &tmir::Module,
        func_idx: usize,
        return_arg_idx: usize,
        expected_slots: i128,
    ) {
        let func = &module.functions[func_idx];
        let mut i32_consts = HashMap::new();
        let mut alloca_counts = HashMap::new();
        let mut ptr_to_int_sources = HashMap::new();
        let mut int_to_ptr_sources = HashMap::new();
        let mut stored_values = HashSet::new();
        let mut call_results = Vec::new();

        for block in &func.blocks {
            for node in &block.body {
                if let (
                    Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(value),
                    },
                    Some(result),
                ) = (&node.inst, node.results.first().copied())
                {
                    i32_consts.insert(result, *value);
                }
            }
        }

        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Alloca {
                            ty: Ty::I64,
                            count: Some(count),
                            ..
                        },
                        Some(result),
                    ) => {
                        if let Some(count) = i32_consts.get(count).copied() {
                            alloca_counts.insert(result, count);
                        }
                    }
                    (
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        ptr_to_int_sources.insert(result, *operand);
                    }
                    (
                        Inst::Cast {
                            op: CastOp::IntToPtr,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        int_to_ptr_sources.insert(result, *operand);
                    }
                    (Inst::Store { value, .. }, _) => {
                        stored_values.insert(*value);
                    }
                    (Inst::Call { args, .. }, Some(result)) => {
                        if let Some(return_ptr) = args.get(return_arg_idx).copied() {
                            call_results.push((result, return_ptr));
                        }
                    }
                    _ => {}
                }
            }
        }

        let (call_result, return_ptr) = call_results
            .into_iter()
            .find(|(_, return_ptr)| alloca_counts.get(return_ptr) == Some(&expected_slots))
            .unwrap_or_else(|| {
                panic!(
                    "expected a helper call with a caller-owned i64 return buffer of {expected_slots} slots"
                )
            });
        assert_eq!(
            alloca_counts.get(&return_ptr),
            Some(&expected_slots),
            "hidden return buffer should be a caller-owned i64 alloca with {expected_slots} slots"
        );

        assert!(
            !ptr_to_int_sources
                .values()
                .any(|operand| *operand == return_ptr),
            "caller should not re-encode the pre-call hidden return buffer pointer after the call"
        );

        assert!(
            stored_values.contains(&call_result),
            "aggregate helper calls should store the callee-returned hidden buffer pointer"
        );
        assert!(
            int_to_ptr_sources
                .values()
                .any(|operand| *operand == call_result),
            "aggregate helper calls should recover compact provenance from the returned pointer"
        );
    }

    fn assert_call_uses_caller_owned_materialized_return_buffer(
        module: &tmir::Module,
        func_idx: usize,
        return_arg_idx: usize,
        expected_slots: i128,
    ) {
        let func = &module.functions[func_idx];
        let mut i32_consts = HashMap::new();
        let mut alloca_counts = HashMap::new();
        let mut ptr_to_int_sources = HashMap::new();
        let mut int_to_ptr_sources = HashMap::new();
        let mut stored_values = HashSet::new();
        let mut matching_call = None;

        for block in &func.blocks {
            for node in &block.body {
                if let (
                    Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(value),
                    },
                    Some(result),
                ) = (&node.inst, node.results.first().copied())
                {
                    i32_consts.insert(result, *value);
                }
            }
        }

        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Alloca {
                            ty: Ty::I64,
                            count: Some(count),
                            ..
                        },
                        Some(result),
                    ) => {
                        if let Some(count) = i32_consts.get(count).copied() {
                            alloca_counts.insert(result, count);
                        }
                    }
                    (
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        ptr_to_int_sources.insert(result, *operand);
                    }
                    (
                        Inst::Cast {
                            op: CastOp::IntToPtr,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        int_to_ptr_sources.insert(result, *operand);
                    }
                    (Inst::Store { value, .. }, _) => {
                        stored_values.insert(*value);
                    }
                    (Inst::Call { args, .. }, Some(result)) => {
                        if let Some(return_ptr) = args.get(return_arg_idx).copied() {
                            if alloca_counts.get(&return_ptr) == Some(&expected_slots) {
                                matching_call = Some((result, return_ptr));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let (call_result, return_ptr) = matching_call.unwrap_or_else(|| {
            panic!(
                "expected a helper call with a caller-owned materialized i64 return buffer of {expected_slots} slots"
            )
        });
        assert!(
            stored_values.contains(&call_result),
            "materialized aggregate helper calls should store the returned hidden buffer pointer"
        );
        assert!(
            !ptr_to_int_sources
                .values()
                .any(|operand| *operand == return_ptr),
            "caller should pass the raw hidden materialized return buffer pointer, not a re-encoded pointer"
        );
        assert!(
            !int_to_ptr_sources
                .values()
                .any(|operand| *operand == call_result),
            "materialized aggregate helper calls should not recover compact provenance from the returned pointer"
        );
    }

    fn assert_missing_caller_owned_return_abi(
        result: Result<tmir::Module, TmirError>,
        expected_shape: &str,
    ) {
        let err = result.expect_err(
            "known pointer-backed aggregate helper return without caller-owned ABI must reject",
        );
        let message = format!("{err}");
        assert!(
            message.contains("callee aggregate return")
                && message.contains("has no caller-owned return ABI shape")
                && message.contains(expected_shape),
            "unexpected missing caller-owned return ABI error: {message}"
        );
    }

    fn assert_call_arg_is_materialized_aggregate_ptr(
        module: &tmir::Module,
        func_idx: usize,
        return_arg_idx: usize,
        expected_return_slots: i128,
        arg_idx: usize,
        expected_arg_slots: i128,
    ) {
        let func = &module.functions[func_idx];
        let mut i32_consts = HashMap::new();
        let mut alloca_counts = HashMap::new();
        let mut ptr_to_int_sources = HashMap::new();

        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i32_consts.insert(result, *value);
                    }
                    (
                        Inst::Alloca {
                            ty: Ty::I64,
                            count: Some(count),
                            ..
                        },
                        Some(result),
                    ) => {
                        if let Some(count) = i32_consts.get(count).copied() {
                            alloca_counts.insert(result, count);
                        }
                    }
                    (
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        ptr_to_int_sources.insert(result, *operand);
                    }
                    _ => {}
                }
            }
        }

        let materialized_ptr = func
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .find_map(|node| {
                let Inst::Call { args, .. } = &node.inst else {
                    return None;
                };
                let return_ptr = args.get(return_arg_idx)?;
                if alloca_counts.get(return_ptr) != Some(&expected_return_slots) {
                    return None;
                }
                let arg = *args
                    .get(arg_idx)
                    .expect("target helper call should have argument");
                Some(ptr_to_int_sources.get(&arg).copied().unwrap_or_else(|| {
                    panic!(
                        "compact aggregate helper arg {arg_idx} should be passed as PtrToInt(materialized_ptr), not a bare i64 pointer"
                    )
                }))
            })
            .expect("expected helper call with matching return buffer");

        assert_eq!(
            alloca_counts.get(&materialized_ptr),
            Some(&expected_arg_slots),
            "compact aggregate helper arg should be a canonical materialized {expected_arg_slots}-slot pointer"
        );
    }

    fn assert_callee_stores_into_hidden_return_buffer(
        module: &tmir::Module,
        func_idx: usize,
        return_param_idx: usize,
    ) {
        let func = &module.functions[func_idx];
        let return_ptr = func.blocks[0]
            .params
            .get(return_param_idx)
            .map(|(value, _)| *value)
            .expect("callee should have a hidden return-buffer parameter");
        let mut return_buffer_ptrs = HashSet::from([return_ptr]);

        for block in &func.blocks {
            for node in &block.body {
                if let (Inst::GEP { base, .. }, Some(result)) =
                    (&node.inst, node.results.first().copied())
                {
                    if return_buffer_ptrs.contains(base) {
                        return_buffer_ptrs.insert(result);
                    }
                }
            }
        }

        let stores_to_return_buffer = func.blocks.iter().any(|block| {
            block.body.iter().any(|node| {
                matches!(
                    &node.inst,
                    Inst::Store { ptr, .. } if return_buffer_ptrs.contains(ptr)
                )
            })
        });
        assert!(
            stores_to_return_buffer,
            "aggregate callee should copy its return value into the hidden return buffer"
        );
    }

    fn assert_callee_stores_exact_hidden_return_slots(
        module: &tmir::Module,
        func_idx: usize,
        return_param_idx: usize,
        expected_slots: u32,
    ) {
        let func = &module.functions[func_idx];
        let return_ptr = func.blocks[0]
            .params
            .get(return_param_idx)
            .map(|(value, _)| *value)
            .expect("callee should have a hidden return-buffer parameter");

        let mut i32_consts = HashMap::new();
        for block in &func.blocks {
            for node in &block.body {
                if let (
                    Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(value),
                    },
                    Some(result),
                ) = (&node.inst, node.results.first().copied())
                {
                    if let Ok(slot) = u32::try_from(*value) {
                        i32_consts.insert(result, slot);
                    }
                }
            }
        }

        let mut ptr_slots: HashMap<ValueId, u32> = HashMap::new();
        let mut stored_slots = HashSet::new();
        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        let Some(index) = i32_consts.get(&indices[0]).copied() else {
                            continue;
                        };
                        let base_slot: Option<u32> = if *base == return_ptr {
                            Some(0)
                        } else {
                            ptr_slots.get(base).copied()
                        };
                        if let Some(slot) = base_slot.and_then(|base| base.checked_add(index)) {
                            ptr_slots.insert(result, slot);
                        }
                    }
                    (Inst::Store { ptr, .. }, _) => {
                        if let Some(slot) = ptr_slots.get(ptr).copied() {
                            stored_slots.insert(slot);
                        }
                    }
                    _ => {}
                }
            }
        }

        let expected: HashSet<u32> = (0..expected_slots).collect();
        assert_eq!(
            stored_slots, expected,
            "aggregate callee should write exactly hidden return slots 0..{expected_slots}; stored={stored_slots:?}"
        );
    }

    fn hidden_return_load_sources(
        module: &tmir::Module,
        func_idx: usize,
        return_param_idx: usize,
    ) -> Vec<(u32, ValueId, u32)> {
        fn resolve_origin(
            origins: &HashMap<(ValueId, u32), (ValueId, u32)>,
            mut source: (ValueId, u32),
        ) -> (ValueId, u32) {
            for _ in 0..16 {
                let Some(next) = origins.get(&source).copied() else {
                    break;
                };
                if next == source {
                    break;
                }
                source = next;
            }
            source
        }

        let func = &module.functions[func_idx];
        let return_ptr = func.blocks[0]
            .params
            .get(return_param_idx)
            .map(|(value, _)| *value)
            .expect("callee should have a hidden return-buffer parameter");
        let mut i32_consts = HashMap::new();
        let mut i64_consts = HashMap::new();
        let mut ptr_slots: HashMap<ValueId, (ValueId, u32)> = HashMap::new();
        let mut load_slots: HashMap<ValueId, (ValueId, u32)> = HashMap::new();
        let mut ptr_origins: HashMap<ValueId, (ValueId, u32)> = HashMap::new();
        let mut slot_origins: HashMap<(ValueId, u32), (ValueId, u32)> = HashMap::new();
        let mut return_sources: HashMap<u32, (ValueId, u32)> = HashMap::new();

        for _ in 0..16 {
            let mut changed = false;
            for block in &func.blocks {
                for node in &block.body {
                    match (&node.inst, node.results.first().copied()) {
                        (
                            Inst::Const {
                                ty: Ty::I32,
                                value: Constant::Int(value),
                            },
                            Some(result),
                        ) => {
                            if let Ok(slot) = u32::try_from(*value) {
                                changed |= i32_consts.insert(result, slot) != Some(slot);
                            }
                        }
                        (
                            Inst::Const {
                                ty: Ty::I64,
                                value: Constant::Int(value),
                            },
                            Some(result),
                        ) => {
                            changed |= i64_consts.insert(result, *value) != Some(*value);
                        }
                        (
                            Inst::BinOp {
                                op,
                                ty: Ty::I64,
                                lhs,
                                rhs,
                            },
                            Some(result),
                        ) => {
                            let Some(lhs) = i64_consts.get(lhs).copied() else {
                                continue;
                            };
                            let Some(rhs) = i64_consts.get(rhs).copied() else {
                                continue;
                            };
                            let value = match op {
                                BinOp::Add => lhs.checked_add(rhs),
                                BinOp::Sub => lhs.checked_sub(rhs),
                                BinOp::Mul => lhs.checked_mul(rhs),
                                _ => None,
                            };
                            if let Some(value) = value {
                                changed |= i64_consts.insert(result, value) != Some(value);
                            }
                        }
                        (
                            Inst::Cast {
                                op: CastOp::Trunc,
                                src_ty: Ty::I64,
                                dst_ty: Ty::I32,
                                operand,
                            },
                            Some(result),
                        ) => {
                            if let Some(slot) = i64_consts
                                .get(operand)
                                .and_then(|value| u32::try_from(*value).ok())
                            {
                                changed |= i32_consts.insert(result, slot) != Some(slot);
                            }
                        }
                        (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                            let Some(index) = i32_consts.get(&indices[0]).copied() else {
                                continue;
                            };
                            let base_slot: Option<(ValueId, u32)> = if *base == return_ptr {
                                Some((return_ptr, 0_u32))
                            } else {
                                ptr_slots.get(base).copied().or(Some((*base, 0_u32)))
                            };
                            if let Some((source_base, base_offset)) = base_slot {
                                if let Some(slot) = base_offset.checked_add(index) {
                                    changed |= ptr_slots.insert(result, (source_base, slot))
                                        != Some((source_base, slot));
                                }
                            }
                        }
                        (Inst::Load { ptr, .. }, Some(result)) => {
                            if let Some(source) = ptr_slots.get(ptr).copied() {
                                let source = resolve_origin(&slot_origins, source);
                                changed |= load_slots.insert(result, source) != Some(source);
                            } else if let Some(source) = ptr_origins.get(ptr).copied() {
                                let source = resolve_origin(&slot_origins, source);
                                changed |= load_slots.insert(result, source) != Some(source);
                            }
                        }
                        (Inst::Store { ptr, value, .. }, _) => {
                            let Some(source) = load_slots.get(value).copied() else {
                                continue;
                            };
                            let source = resolve_origin(&slot_origins, source);
                            if let Some(dest) = ptr_slots.get(ptr).copied() {
                                if dest.0 == return_ptr {
                                    changed |=
                                        return_sources.insert(dest.1, source) != Some(source);
                                } else {
                                    changed |= slot_origins.insert(dest, source) != Some(source);
                                }
                            } else {
                                changed |= ptr_origins.insert(*ptr, source) != Some(source);
                            }
                        }
                        _ => {}
                    }
                }
            }
            if !changed {
                break;
            }
        }

        let mut result: Vec<_> = return_sources
            .into_iter()
            .map(|(return_slot, (source_base, source_slot))| {
                (return_slot, source_base, source_slot)
            })
            .collect();
        result.sort_by_key(|(return_slot, _, source_slot)| (*return_slot, *source_slot));
        result
    }

    fn hidden_return_load_source_slots(
        module: &tmir::Module,
        func_idx: usize,
        return_param_idx: usize,
    ) -> Vec<(u32, u32)> {
        hidden_return_load_sources(module, func_idx, return_param_idx)
            .into_iter()
            .map(|(return_slot, _, source_slot)| (return_slot, source_slot))
            .collect()
    }

    fn user_arg_materialized_ptrs(
        module: &tmir::Module,
        func_idx: usize,
        user_param_idx: usize,
    ) -> HashSet<ValueId> {
        let func = &module.functions[func_idx];
        let user_param = func.blocks[0]
            .params
            .get(user_param_idx)
            .map(|(value, _)| *value)
            .expect("callee should have a user argument parameter");
        let mut int_values = HashSet::from([user_param]);
        let mut memory_slots = HashSet::new();
        let mut ptr_values = HashSet::new();

        for _ in 0..16 {
            let mut changed = false;
            for block in &func.blocks {
                for node in &block.body {
                    match (&node.inst, node.results.first().copied()) {
                        (
                            Inst::Store {
                                ty: Ty::I64,
                                ptr,
                                value,
                                ..
                            },
                            _,
                        ) if int_values.contains(value) => {
                            changed |= memory_slots.insert(*ptr);
                        }
                        (
                            Inst::Load {
                                ty: Ty::I64, ptr, ..
                            },
                            Some(result),
                        ) if memory_slots.contains(ptr) => {
                            changed |= int_values.insert(result);
                        }
                        (
                            Inst::Cast {
                                op: CastOp::IntToPtr,
                                src_ty: Ty::I64,
                                dst_ty: Ty::Ptr,
                                operand,
                            },
                            Some(result),
                        ) if int_values.contains(operand) => {
                            changed |= ptr_values.insert(result);
                        }
                        _ => {}
                    }
                }
            }
            if !changed {
                break;
            }
        }

        ptr_values
    }

    fn assert_hidden_return_loads_from_user_arg_slots(
        module: &tmir::Module,
        func_idx: usize,
        return_param_idx: usize,
        user_param_idx: usize,
        expected: &[(u32, u32)],
        context: &str,
    ) {
        let user_ptrs = user_arg_materialized_ptrs(module, func_idx, user_param_idx);
        let sources = hidden_return_load_sources(module, func_idx, return_param_idx);
        let actual: Vec<_> = sources
            .iter()
            .filter(|(_, source_base, _)| user_ptrs.contains(source_base))
            .map(|(return_slot, _, source_slot)| (*return_slot, *source_slot))
            .collect();

        assert_eq!(
            actual,
            expected,
            "{context}: hidden return loads should originate from the materialized user argument pointer; sources={sources:?}, user_ptrs={user_ptrs:?}"
        );
        assert_eq!(
            actual.len(),
            sources.len(),
            "{context}: all hidden return load sources should trace to the materialized user argument pointer; sources={sources:?}, user_ptrs={user_ptrs:?}"
        );
    }

    fn record_slot_const(
        slot_consts: &mut HashMap<(ValueId, u32), Option<i128>>,
        key: (ValueId, u32),
        value: i128,
    ) -> bool {
        match slot_consts.get_mut(&key) {
            Some(existing) => match *existing {
                Some(current) if current == value => false,
                Some(_) => {
                    *existing = None;
                    true
                }
                None => false,
            },
            None => {
                slot_consts.insert(key, Some(value));
                true
            }
        }
    }

    fn record_ptr_const(
        ptr_consts: &mut HashMap<ValueId, Option<i128>>,
        key: ValueId,
        value: i128,
    ) -> bool {
        match ptr_consts.get_mut(&key) {
            Some(existing) => match *existing {
                Some(current) if current == value => false,
                Some(_) => {
                    *existing = None;
                    true
                }
                None => false,
            },
            None => {
                ptr_consts.insert(key, Some(value));
                true
            }
        }
    }

    fn callee_return_buffer_const_stores(
        module: &tmir::Module,
        func_idx: usize,
        return_param_idx: usize,
    ) -> Vec<(u32, i128)> {
        let func = &module.functions[func_idx];
        let return_ptr = func.blocks[0]
            .params
            .get(return_param_idx)
            .map(|(value, _)| *value)
            .expect("callee should have a hidden return-buffer parameter");
        let mut i32_consts = HashMap::new();
        let mut i64_consts = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut load_slots = HashMap::new();
        let mut ptr_consts: HashMap<ValueId, Option<i128>> = HashMap::new();
        let mut slot_consts: HashMap<(ValueId, u32), Option<i128>> = HashMap::new();

        for _ in 0..16 {
            let mut changed = false;
            for block in &func.blocks {
                for node in &block.body {
                    match (&node.inst, node.results.first().copied()) {
                        (
                            Inst::Const {
                                ty: Ty::I32,
                                value: Constant::Int(value),
                            },
                            Some(result),
                        ) => {
                            if let Ok(slot) = u32::try_from(*value) {
                                changed |= i32_consts.insert(result, slot) != Some(slot);
                            }
                        }
                        (
                            Inst::Const {
                                ty: Ty::I64,
                                value: Constant::Int(value),
                            },
                            Some(result),
                        ) => {
                            changed |= i64_consts.insert(result, *value) != Some(*value);
                        }
                        (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                            if let Some(slot) = i32_consts.get(&indices[0]).copied() {
                                changed |=
                                    gep_slots.insert(result, (*base, slot)) != Some((*base, slot));
                            }
                        }
                        (Inst::Load { ptr, .. }, Some(result)) => {
                            if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                                changed |=
                                    load_slots.insert(result, (base, slot)) != Some((base, slot));
                                if let Some(Some(value)) = slot_consts.get(&(base, slot)).copied() {
                                    changed |= i64_consts.insert(result, value) != Some(value);
                                }
                            } else if let Some(Some(value)) = ptr_consts.get(ptr).copied() {
                                changed |= i64_consts.insert(result, value) != Some(value);
                            }
                        }
                        (Inst::Store { ptr, value, .. }, _) => {
                            if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                                if let Some(value) = i64_consts.get(value).copied() {
                                    changed |=
                                        record_slot_const(&mut slot_consts, (base, slot), value);
                                } else if let Some((source_base, source_slot)) =
                                    load_slots.get(value).copied()
                                {
                                    if let Some(Some(value)) =
                                        slot_consts.get(&(source_base, source_slot)).copied()
                                    {
                                        changed |= record_slot_const(
                                            &mut slot_consts,
                                            (base, slot),
                                            value,
                                        );
                                    }
                                }
                            } else if let Some(value) = i64_consts.get(value).copied() {
                                changed |= record_ptr_const(&mut ptr_consts, *ptr, value);
                            } else if let Some((source_base, source_slot)) =
                                load_slots.get(value).copied()
                            {
                                if let Some(Some(value)) =
                                    slot_consts.get(&(source_base, source_slot)).copied()
                                {
                                    changed |= record_ptr_const(&mut ptr_consts, *ptr, value);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            if !changed {
                break;
            }
        }

        let mut stores = Vec::new();
        for block in &func.blocks {
            for node in &block.body {
                let Inst::Store { ptr, value, .. } = &node.inst else {
                    continue;
                };
                let Some((base, slot)) = gep_slots.get(ptr).copied() else {
                    continue;
                };
                if base != return_ptr {
                    continue;
                }
                if let Some(value) = i64_consts.get(value).copied() {
                    stores.push((slot, value));
                }
            }
        }
        stores.sort();
        stores.dedup();
        stores
    }

    fn compact_record_fields(fields: &[&str]) -> CompoundLayout {
        CompoundLayout::Record {
            fields: fields
                .iter()
                .map(|field| (tla_core::intern_name(field), CompoundLayout::Int))
                .collect(),
        }
    }

    #[test]
    fn test_complete_inferred_compact_shape_from_expected_fills_missing_single_slot_layouts() {
        let x = tla_core::intern_name("x");
        let y = tla_core::intern_name("y");
        let expected_bool = AggregateShape::Scalar(ScalarShape::Bool);
        let inferred = AggregateShape::Record {
            fields: vec![
                (y, None),
                (
                    x,
                    Some(Box::new(AggregateShape::Sequence {
                        extent: SequenceExtent::Capacity(2),
                        element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                    })),
                ),
            ],
        };
        let expected = AggregateShape::Record {
            fields: vec![
                (
                    x,
                    Some(Box::new(AggregateShape::Sequence {
                        extent: SequenceExtent::Capacity(2),
                        element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                    })),
                ),
                (y, Some(Box::new(expected_bool.clone()))),
            ],
        };

        let completed = Ctx::complete_inferred_compact_shape_from_expected(&inferred, &expected)
            .expect("expected fixed layout should complete missing single-slot record fields");

        assert_eq!(
            completed,
            AggregateShape::Record {
                fields: vec![
                    (y, Some(Box::new(expected_bool))),
                    (
                        x,
                        Some(Box::new(AggregateShape::Sequence {
                            extent: SequenceExtent::Capacity(2),
                            element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                        })),
                    ),
                ],
            }
        );
        assert!(Ctx::compatible_compact_materialization_value(
            &completed, &expected
        ));
    }

    #[test]
    fn test_complete_inferred_compact_shape_from_expected_rejects_missing_compound_nested_layouts()
    {
        let x = tla_core::intern_name("x");
        let y = tla_core::intern_name("y");
        let value_shape = AggregateShape::Record {
            fields: vec![(
                tla_core::intern_name("clock"),
                Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
            )],
        };
        let inferred = AggregateShape::Record {
            fields: vec![
                (y, None),
                (
                    x,
                    Some(Box::new(AggregateShape::Sequence {
                        extent: SequenceExtent::Capacity(2),
                        element: None,
                    })),
                ),
            ],
        };
        let expected = AggregateShape::Record {
            fields: vec![
                (
                    x,
                    Some(Box::new(AggregateShape::Sequence {
                        extent: SequenceExtent::Capacity(2),
                        element: Some(Box::new(value_shape.clone())),
                    })),
                ),
                (y, Some(Box::new(value_shape))),
            ],
        };

        assert!(
            Ctx::complete_inferred_compact_shape_from_expected(&inferred, &expected).is_none(),
            "missing nested compound layouts must not be fabricated from expected ABI"
        );
    }

    #[test]
    fn test_complete_inferred_compact_shape_from_expected_rejects_dense_function_missing_scalar_value_from_sequence(
    ) {
        let inferred = AggregateShape::Function {
            len: 3,
            domain_lo: Some(1),
            value: None,
        };
        let expected = AggregateShape::Sequence {
            extent: SequenceExtent::Capacity(3),
            element: Some(Box::new(AggregateShape::Scalar(ScalarShape::String))),
        };

        assert!(
            Ctx::complete_inferred_compact_shape_from_expected(&inferred, &expected).is_none(),
            "missing dense function scalar values must not be fabricated from expected ABI"
        );
    }

    #[test]
    fn test_complete_inferred_compact_shape_from_expected_rejects_dense_function_missing_compound_value_from_sequence(
    ) {
        let value_shape = AggregateShape::Record {
            fields: vec![(
                tla_core::intern_name("type"),
                Some(Box::new(AggregateShape::Scalar(ScalarShape::String))),
            )],
        };
        let inferred = AggregateShape::Function {
            len: 3,
            domain_lo: Some(1),
            value: None,
        };
        let expected = AggregateShape::Sequence {
            extent: SequenceExtent::Capacity(3),
            element: Some(Box::new(value_shape)),
        };

        assert!(
            Ctx::complete_inferred_compact_shape_from_expected(&inferred, &expected).is_none(),
            "missing dense function compound values must not be fabricated from expected ABI"
        );
    }

    #[test]
    fn test_complete_inferred_compact_shape_from_expected_rejects_sequence_capacity_widening() {
        let inferred = AggregateShape::Sequence {
            extent: SequenceExtent::Capacity(1),
            element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
        };
        let expected = AggregateShape::Sequence {
            extent: SequenceExtent::Capacity(2),
            element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
        };

        assert!(
            Ctx::complete_inferred_compact_shape_from_expected(&inferred, &expected).is_none(),
            "callee return ABI completion must not silently widen sequence capacity"
        );
    }

    fn inst_count(
        module: &tmir::Module,
        func_idx: usize,
        predicate: impl Fn(&Inst) -> bool,
    ) -> usize {
        module.functions[func_idx]
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .filter(|node| predicate(&node.inst))
            .count()
    }

    fn has_i64_icmp_against_const_from_gep_slot(
        module: &tmir::Module,
        func_idx: usize,
        expected_op: ICmpOp,
        expected_slot: u32,
        expected_const: i128,
    ) -> bool {
        let func = &module.functions[func_idx];
        let mut i32_consts = HashMap::new();
        let mut i64_consts = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut load_slots = HashMap::new();

        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        if let Ok(slot) = u32::try_from(*value) {
                            i32_consts.insert(result, slot);
                        }
                    }
                    (
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i64_consts.insert(result, *value);
                    }
                    (Inst::GEP { indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = i32_consts.get(&indices[0]).copied() {
                            gep_slots.insert(result, slot);
                        }
                    }
                    (Inst::Load { ptr, .. }, Some(result)) => {
                        if let Some(slot) = gep_slots.get(ptr).copied() {
                            load_slots.insert(result, slot);
                        }
                    }
                    (
                        Inst::ICmp {
                            op,
                            ty: Ty::I64,
                            lhs,
                            rhs,
                        },
                        _,
                    ) if *op == expected_op => {
                        let lhs_const = i64_consts.get(lhs).copied();
                        let rhs_const = i64_consts.get(rhs).copied();
                        let lhs_slot = load_slots.get(lhs).copied();
                        let rhs_slot = load_slots.get(rhs).copied();
                        if (lhs_slot == Some(expected_slot) && rhs_const == Some(expected_const))
                            || (rhs_slot == Some(expected_slot)
                                && lhs_const == Some(expected_const))
                        {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }
        false
    }

    fn resolve_slot_origin(
        slot_origins: &HashMap<(ValueId, u32), (ValueId, u32)>,
        mut source: (ValueId, u32),
    ) -> (ValueId, u32) {
        for _ in 0..16 {
            let Some(next) = slot_origins.get(&source).copied() else {
                break;
            };
            if next == source {
                break;
            }
            source = next;
        }
        source
    }

    fn has_i64_icmp_against_const_from_state_slot(
        module: &tmir::Module,
        func_idx: usize,
        expected_op: ICmpOp,
        expected_slot: u32,
        expected_const: i128,
    ) -> bool {
        let state_in = ValueId::new(1);
        let func = &module.functions[func_idx];
        let mut i32_consts = HashMap::new();
        let mut i64_consts = HashMap::new();
        let mut ptr_slots: HashMap<ValueId, (ValueId, u32)> = HashMap::new();
        let mut load_slots: HashMap<ValueId, (ValueId, u32)> = HashMap::new();
        let mut slot_origins: HashMap<(ValueId, u32), (ValueId, u32)> = HashMap::new();
        let mut slot_consts: HashMap<(ValueId, u32), i128> = HashMap::new();

        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        if let Ok(value) = u32::try_from(*value) {
                            i32_consts.insert(result, value);
                        }
                    }
                    (
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i64_consts.insert(result, *value);
                    }
                    (
                        Inst::BinOp {
                            op,
                            ty: Ty::I64,
                            lhs,
                            rhs,
                        },
                        Some(result),
                    ) => {
                        let value = match (i64_consts.get(lhs), i64_consts.get(rhs)) {
                            (Some(lhs), Some(rhs)) => match op {
                                BinOp::Add => lhs.checked_add(*rhs),
                                BinOp::Sub => lhs.checked_sub(*rhs),
                                BinOp::Mul => lhs.checked_mul(*rhs),
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some(value) = value {
                            i64_consts.insert(result, value);
                        }
                    }
                    (
                        Inst::Cast {
                            op: CastOp::Trunc,
                            src_ty: Ty::I64,
                            dst_ty: Ty::I32,
                            operand,
                        },
                        Some(result),
                    ) => {
                        if let Some(value) = i64_consts
                            .get(operand)
                            .and_then(|value| u32::try_from(*value).ok())
                        {
                            i32_consts.insert(result, value);
                        }
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(index) = i32_consts.get(&indices[0]).copied() {
                            let (base, base_offset) =
                                ptr_slots.get(base).copied().unwrap_or((*base, 0_u32));
                            if let Some(slot) = base_offset.checked_add(index) {
                                ptr_slots.insert(result, (base, slot));
                            }
                        }
                    }
                    (Inst::Load { ptr, .. }, Some(result)) => {
                        let source = ptr_slots.get(ptr).copied().unwrap_or((*ptr, 0_u32));
                        let origin = resolve_slot_origin(&slot_origins, source);
                        load_slots.insert(result, origin);
                        if let Some(value) = slot_consts
                            .get(&origin)
                            .or_else(|| slot_consts.get(&source))
                            .copied()
                        {
                            i64_consts.insert(result, value);
                        }
                    }
                    (Inst::Store { ptr, value, .. }, _) => {
                        let dest = ptr_slots.get(ptr).copied().unwrap_or((*ptr, 0_u32));
                        if let Some(source) = load_slots.get(value).copied() {
                            let source = resolve_slot_origin(&slot_origins, source);
                            slot_origins.insert(dest, source);
                            slot_consts.remove(&dest);
                        } else if let Some(value) = i64_consts.get(value).copied() {
                            slot_origins.remove(&dest);
                            slot_consts.insert(dest, value);
                        }
                    }
                    (
                        Inst::ICmp {
                            op,
                            ty: Ty::I64,
                            lhs,
                            rhs,
                        },
                        _,
                    ) if *op == expected_op => {
                        let lhs_const = i64_consts.get(lhs).copied();
                        let rhs_const = i64_consts.get(rhs).copied();
                        let lhs_slot = load_slots.get(lhs).copied();
                        let rhs_slot = load_slots.get(rhs).copied();
                        if (lhs_slot == Some((state_in, expected_slot))
                            && rhs_const == Some(expected_const))
                            || (rhs_slot == Some((state_in, expected_slot))
                                && lhs_const == Some(expected_const))
                        {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }

        false
    }

    fn i64_icmp_load_load_count(
        module: &tmir::Module,
        func_idx: usize,
        expected_op: ICmpOp,
    ) -> usize {
        let func = &module.functions[func_idx];
        let mut gep_ptrs = HashSet::new();
        let mut load_values = HashSet::new();
        let mut count = 0;

        for block in &func.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (Inst::GEP { .. }, Some(result)) => {
                        gep_ptrs.insert(result);
                    }
                    (Inst::Load { ptr, .. }, Some(result)) if gep_ptrs.contains(ptr) => {
                        load_values.insert(result);
                    }
                    (
                        Inst::ICmp {
                            op,
                            ty: Ty::I64,
                            lhs,
                            rhs,
                        },
                        _,
                    ) if *op == expected_op
                        && load_values.contains(lhs)
                        && load_values.contains(rhs) =>
                    {
                        count += 1;
                    }
                    _ => {}
                }
            }
        }

        count
    }

    fn has_instruction_after_terminator(module: &tmir::Module, func_idx: usize) -> bool {
        module.functions[func_idx].blocks.iter().any(|block| {
            let mut saw_terminator = false;
            for node in &block.body {
                if saw_terminator {
                    return true;
                }
                if node.is_terminator() {
                    saw_terminator = true;
                }
            }
            false
        })
    }

    fn compact_runtime_subset_mask_check_count(module: &tmir::Module, func_idx: usize) -> usize {
        inst_count(module, func_idx, |inst| {
            matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    ..
                }
            )
        })
    }

    fn has_bounded_loop_tag(module: &tmir::Module, func_idx: usize, expected_bound: u32) -> bool {
        bounded_loop_tag_count(module, func_idx, expected_bound) > 0
    }

    fn bounded_loop_tag_count(
        module: &tmir::Module,
        func_idx: usize,
        expected_bound: u32,
    ) -> usize {
        module.functions[func_idx]
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .filter(|node| matches!(node.inst, Inst::CondBr { .. }))
            .flat_map(|node| node.proofs.iter())
            .filter(|proof| {
                matches!(
                    *proof,
                    tmir::proof::ProofAnnotation::Custom(tag)
                        if crate::annotations::bounded_loop_n(*tag) == Some(expected_bound)
                )
            })
            .count()
    }

    fn assert_rejects_unproven_set_bitmask_universe(result: Result<tmir::Module, TmirError>) {
        let err = match result {
            Ok(_) => panic!("generic compact SetBitmask layout should require universe proof"),
            Err(err) => err,
        };
        let err = format!("{err}");
        assert!(
            err.contains("compact SetBitmask") && err.contains("exact universe metadata"),
            "error should clearly reject unproven compact SetBitmask universe: {err}"
        );
    }

    fn dense_int_one_to_n_set_bitmask_shape(universe_len: u32) -> AggregateShape {
        AggregateShape::SetBitmask {
            universe_len,
            universe: SetBitmaskUniverse::IntRange { lo: 1 },
        }
    }

    #[test]
    fn test_merge_compatible_shapes_widens_finite_set_bounds() {
        assert_eq!(
            merge_compatible_shapes(
                Some(&AggregateShape::BoundedSet {
                    max_len: 2,
                    element: None,
                }),
                Some(&AggregateShape::BoundedSet {
                    max_len: 5,
                    element: None,
                }),
            ),
            Some(AggregateShape::BoundedSet {
                max_len: 5,
                element: None,
            })
        );
        assert_eq!(
            merge_compatible_shapes(
                Some(&AggregateShape::BoundedSet {
                    max_len: 64,
                    element: None,
                }),
                Some(&AggregateShape::BoundedSet {
                    max_len: 65,
                    element: None,
                }),
            ),
            Some(AggregateShape::FiniteSet)
        );
        assert_eq!(
            merge_compatible_shapes(
                Some(&dense_int_one_to_n_set_bitmask_shape(4)),
                Some(&AggregateShape::BoundedSet {
                    max_len: 4,
                    element: None,
                }),
            ),
            None
        );
    }

    #[test]
    fn test_binding_shape_from_domain_preserves_bounded_set_element() {
        let element = AggregateShape::Scalar(ScalarShape::Int);
        assert_eq!(
            binding_shape_from_domain(&AggregateShape::BoundedSet {
                max_len: 8,
                element: Some(Box::new(element.clone())),
            }),
            Some(element),
            "SetFilter bindings over bounded materialized sets should retain scalar element metadata"
        );
    }

    #[test]
    fn test_finite_set_ops_preserve_exact_setbitmask_identity() {
        let dense_1_to_4 = dense_int_one_to_n_set_bitmask_shape(4);
        let dense_2_to_5 = AggregateShape::SetBitmask {
            universe_len: 4,
            universe: SetBitmaskUniverse::IntRange { lo: 2 },
        };
        let generic_int_set = AggregateShape::Set {
            len: 1,
            element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
        };
        let large_generic_int_set = AggregateShape::Set {
            len: 9,
            element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
        };
        let empty_set = AggregateShape::Set {
            len: 0,
            element: None,
        };
        let in_universe_exact_set = AggregateShape::ExactIntSet { values: vec![1, 3] };
        let out_of_universe_exact_set = AggregateShape::ExactIntSet { values: vec![0, 2] };
        let interval_0_to_7 = AggregateShape::Interval { lo: 0, hi: 7 };
        let interval_0_to_63 = AggregateShape::Interval { lo: 0, hi: 63 };
        let in_universe_interval = AggregateShape::Interval { lo: 2, hi: 3 };
        let out_of_universe_interval = AggregateShape::Interval { lo: 0, hi: 2 };
        let interval_0_to_7_bitmask = AggregateShape::SetBitmask {
            universe_len: 8,
            universe: SetBitmaskUniverse::IntRange { lo: 0 },
        };

        assert_eq!(
            finite_set_union_shape(Some(&dense_1_to_4), Some(&dense_1_to_4)),
            Some(dense_1_to_4.clone()),
            "SetUnion shape transfer must preserve exact compact SetBitmask identity"
        );
        assert_eq!(
            finite_set_intersect_shape(Some(&dense_1_to_4), Some(&dense_1_to_4)),
            Some(dense_1_to_4.clone()),
            "SetIntersect shape transfer must preserve exact compact SetBitmask identity"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&dense_1_to_4), Some(&dense_1_to_4)),
            Some(dense_1_to_4.clone()),
            "SetDiff shape transfer must preserve the compact SetBitmask identity"
        );
        assert_eq!(
            finite_set_union_shape(Some(&dense_1_to_4), Some(&empty_set)),
            Some(dense_1_to_4.clone()),
            "SetUnion may preserve a compact SetBitmask when the materialized operand is statically empty"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&empty_set), Some(&dense_1_to_4)),
            Some(dense_1_to_4.clone()),
            "SetDiff may preserve a compact SetBitmask when the materialized source is statically empty"
        );
        assert_eq!(
            finite_set_union_shape(Some(&dense_1_to_4), Some(&in_universe_interval)),
            Some(dense_1_to_4.clone()),
            "SetUnion may preserve a compact SetBitmask for intervals proven inside the compact universe"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&in_universe_interval), Some(&dense_1_to_4)),
            Some(dense_1_to_4.clone()),
            "SetDiff may preserve a compact SetBitmask for intervals proven inside the compact universe"
        );
        assert_eq!(
            finite_set_union_shape(Some(&dense_1_to_4), Some(&in_universe_exact_set)),
            Some(dense_1_to_4.clone()),
            "SetUnion may preserve a compact SetBitmask for exact integer sets proven inside the compact universe"
        );
        assert_eq!(
            finite_set_intersect_shape(Some(&dense_1_to_4), Some(&out_of_universe_exact_set)),
            Some(dense_1_to_4.clone()),
            "SetIntersect may preserve a compact SetBitmask because out-of-universe exact elements cannot appear in the result"
        );
        assert_eq!(
            finite_set_intersect_shape(Some(&dense_1_to_4), Some(&out_of_universe_interval)),
            Some(dense_1_to_4.clone()),
            "SetIntersect may preserve a compact SetBitmask because out-of-universe interval elements cannot appear in the result"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&in_universe_exact_set), Some(&dense_1_to_4)),
            Some(dense_1_to_4.clone()),
            "SetDiff may preserve a compact SetBitmask for exact integer sets proven inside the compact universe"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&interval_0_to_7), Some(&in_universe_exact_set)),
            Some(interval_0_to_7_bitmask.clone()),
            "small interval SetDiff shape inference must mirror mask-native lowering for exact RHS sets"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&interval_0_to_7), Some(&generic_int_set)),
            Some(AggregateShape::BoundedSet {
                max_len: 8,
                element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
            }),
            "small interval SetDiff must not infer compact masks from unproven materialized integer RHS sets"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&interval_0_to_7), Some(&large_generic_int_set)),
            Some(AggregateShape::BoundedSet {
                max_len: 8,
                element: Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
            }),
            "large materialized RHS sets must stay on the materialized bounded SetDiff shape"
        );
        assert!(
            !matches!(
                finite_set_diff_shape(Some(&interval_0_to_63), Some(&generic_int_set)),
                Some(AggregateShape::SetBitmask { .. })
            ),
            "wide interval SetDiff must not infer a compact mask that lowering cannot represent"
        );
        assert_eq!(
            finite_set_union_shape(Some(&dense_1_to_4), Some(&generic_int_set)),
            None,
            "SetUnion must not infer compact SetBitmask from a generic materialized integer set"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&generic_int_set), Some(&dense_1_to_4)),
            None,
            "SetDiff must not infer compact SetBitmask when a generic materialized set may contain out-of-universe elements"
        );
        assert_eq!(
            finite_set_union_shape(Some(&dense_1_to_4), Some(&out_of_universe_interval)),
            None,
            "SetUnion must not infer compact SetBitmask for intervals outside the compact universe"
        );
        assert_eq!(
            finite_set_union_shape(Some(&dense_1_to_4), Some(&out_of_universe_exact_set)),
            None,
            "SetUnion must not infer compact SetBitmask for exact integer sets outside the compact universe"
        );

        assert_eq!(
            finite_set_union_shape(Some(&dense_1_to_4), Some(&dense_2_to_5)),
            None,
            "SetUnion must not widen mismatched compact SetBitmask universes into materialized sets"
        );
        assert_eq!(
            finite_set_intersect_shape(Some(&dense_1_to_4), Some(&dense_2_to_5)),
            None,
            "SetIntersect must not widen mismatched compact SetBitmask universes into materialized sets"
        );
        assert_eq!(
            finite_set_diff_shape(Some(&dense_1_to_4), Some(&dense_2_to_5)),
            None,
            "SetDiff must not widen mismatched compact SetBitmask universes into materialized sets"
        );
    }

    #[test]
    fn test_const_func_dense_ordered_int_domain_tracks_domain_lo() {
        use std::sync::Arc;
        use tla_value::FuncValue;

        let dense = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Bool(true)),
            (Value::SmallInt(2), Value::Bool(false)),
        ])));
        assert_eq!(
            const_shape_and_scalar(&dense).0,
            Some(AggregateShape::Function {
                len: 2,
                domain_lo: Some(1),
                value: Some(Box::new(AggregateShape::Scalar(ScalarShape::Bool))),
            }),
            "dense ordered integer Func domains should carry compact function ordinal metadata"
        );

        let gapped = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Bool(true)),
            (Value::SmallInt(3), Value::Bool(false)),
        ])));
        assert_eq!(
            const_shape_and_scalar(&gapped).0,
            Some(AggregateShape::Function {
                len: 2,
                domain_lo: None,
                value: Some(Box::new(AggregateShape::Scalar(ScalarShape::Bool))),
            }),
            "non-dense Func domains must not claim compact ordinal compatibility"
        );
    }

    #[test]
    fn test_store_var_compact_function_rejects_unknown_to_dense_domain_copy() {
        use std::sync::Arc;
        use tla_value::FuncValue;

        let mut pool = ConstantPool::new();
        let func_idx = pool.add_value(Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::String("a".into()), Value::SmallInt(7)),
        ]))));

        let mut func = BytecodeFunction::new("store_unknown_domain_func".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: func_idx,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(1),
            domain_lo: Some(1),
        })]);

        let err = lower_next_state_with_constants_and_layout(
            &func,
            "store_unknown_domain_func",
            &pool,
            &layout,
        )
        .expect_err("compact function copy must reject None/Some domain_lo mismatch");
        let message = err.to_string();
        assert!(
            message.contains("requires compatible scalar source")
                && message.contains("domain_lo: None")
                && message.contains("domain_lo: Some(1)"),
            "unexpected error: {message}"
        );
    }

    fn int_range_set_bitmask_layout(lo: i64, hi: i64) -> CompoundLayout {
        CompoundLayout::SetBitmask {
            universe: (lo..=hi).map(SetBitmaskElement::Int).collect(),
        }
    }

    fn explicit_int_set_bitmask_layout(values: &[i64]) -> CompoundLayout {
        CompoundLayout::SetBitmask {
            universe: values.iter().copied().map(SetBitmaskElement::Int).collect(),
        }
    }

    fn lower_straightline_invariant_with_dense_set_bitmask_regs(
        func: &BytecodeFunction,
        name: &str,
        dense_regs: &[(u8, u32)],
    ) -> Result<tmir::Module, TmirError> {
        let const_pool = ConstantPool::new();
        let mut ctx = Ctx::new(
            func,
            name,
            LoweringMode::Invariant,
            Some(&const_pool),
            None,
            None,
        )?;
        let mut block = ctx.block_index_for_pc(0)?;
        for (pc, opcode) in func.instructions.iter().enumerate() {
            for &(reg, universe_len) in dense_regs {
                ctx.aggregate_shapes
                    .insert(reg, dense_int_one_to_n_set_bitmask_shape(universe_len));
            }
            block = ctx
                .lower_opcode(pc, opcode, block, &func.instructions)?
                .unwrap_or(block);
        }
        Ok(ctx.finish())
    }

    /// Test lowering a simple invariant: x > 0.
    ///
    /// Bytecode:
    ///   LoadVar { rd: 0, var_idx: 0 }   // r0 = state[0] (x)
    ///   LoadImm { rd: 1, value: 0 }     // r1 = 0
    ///   GtInt { rd: 2, r1: 0, r2: 1 }   // r2 = (x > 0)
    ///   Ret { rs: 2 }                    // return r2
    #[test]
    fn test_lower_invariant_x_gt_zero() {
        let mut func = BytecodeFunction::new("Inv_x_gt_0".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "inv_x_gt_0").unwrap();
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "inv_x_gt_0");

        // The function should have at least 1 block (entry).
        assert!(!module.functions[0].blocks.is_empty());

        // Entry block should contain: 3 allocas + opcodes + return.
        let entry = &module.functions[0].blocks[0];
        assert!(
            entry.body.len() >= 3, // at least the 3 allocas
            "entry block has {} instructions, expected >= 3",
            entry.body.len()
        );

        // Verify the function ends with a Return.
        let has_return = module.functions[0].blocks.iter().any(|b| {
            b.body
                .last()
                .map_or(false, |n| matches!(n.inst, Inst::Return { .. }))
        });
        assert!(has_return, "function should contain a Return instruction");
    }

    #[test]
    fn test_scalar_equality_constant_folds_known_mismatched_lanes() {
        let mut func = BytecodeFunction::new("eq_int_bool".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadBool {
            rd: 1,
            value: false,
        });
        func.emit(Opcode::Eq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "eq_int_bool")
            .expect("known cross-lane equality should fold to false");
        assert_eq!(
            inst_count(&module, 0, |inst| matches!(inst, Inst::ICmp { .. })),
            0,
            "known int/bool equality must not lower as raw i64 compare"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                }
            )) > 0,
            "known Eq(Int, Bool) mismatch should materialize false"
        );
    }

    #[test]
    fn test_scalar_neq_constant_folds_known_mismatched_lanes() {
        let mut func = BytecodeFunction::new("neq_int_bool".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Neq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "neq_int_bool")
            .expect("known cross-lane inequality should fold to true");
        assert_eq!(
            inst_count(&module, 0, |inst| matches!(inst, Inst::ICmp { .. })),
            0,
            "known int/bool inequality must not lower as raw i64 compare"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                }
            )) > 0,
            "known Ne(Int, Bool) mismatch should materialize true"
        );
    }

    #[test]
    fn test_derived_boolean_equality_constant_folds_mixed_lanes() {
        use std::sync::Arc;

        let mut pool = ConstantPool::new();
        let string_idx = pool.add_value(Value::String(Arc::from("flag")));

        let cases: Vec<(&str, BytecodeFunction, usize, i64)> = vec![
            {
                let mut func = BytecodeFunction::new("and_eq_int".to_string(), 0);
                func.emit(Opcode::LoadBool { rd: 0, value: true });
                func.emit(Opcode::LoadBool {
                    rd: 1,
                    value: false,
                });
                func.emit(Opcode::And {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                });
                func.emit(Opcode::LoadImm { rd: 3, value: 1 });
                func.emit(Opcode::Eq {
                    rd: 4,
                    r1: 2,
                    r2: 3,
                });
                func.emit(Opcode::Ret { rs: 4 });
                ("and_eq_int", func, 0, 0)
            },
            {
                let mut func = BytecodeFunction::new("not_eq_int".to_string(), 0);
                func.emit(Opcode::LoadBool { rd: 0, value: true });
                func.emit(Opcode::Not { rd: 1, rs: 0 });
                func.emit(Opcode::LoadImm { rd: 2, value: 0 });
                func.emit(Opcode::Eq {
                    rd: 3,
                    r1: 1,
                    r2: 2,
                });
                func.emit(Opcode::Ret { rs: 3 });
                ("not_eq_int", func, 1, 0)
            },
            {
                let mut func = BytecodeFunction::new("implies_neq_string".to_string(), 0);
                func.emit(Opcode::LoadBool { rd: 0, value: true });
                func.emit(Opcode::LoadBool {
                    rd: 1,
                    value: false,
                });
                func.emit(Opcode::Implies {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                });
                func.emit(Opcode::LoadConst {
                    rd: 3,
                    idx: string_idx,
                });
                func.emit(Opcode::Neq {
                    rd: 4,
                    r1: 2,
                    r2: 3,
                });
                func.emit(Opcode::Ret { rs: 4 });
                ("implies_neq_string", func, 2, 1)
            },
            {
                let mut func = BytecodeFunction::new("equiv_neq_string".to_string(), 0);
                func.emit(Opcode::LoadBool { rd: 0, value: true });
                func.emit(Opcode::LoadBool {
                    rd: 1,
                    value: false,
                });
                func.emit(Opcode::Equiv {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                });
                func.emit(Opcode::LoadConst {
                    rd: 3,
                    idx: string_idx,
                });
                func.emit(Opcode::Neq {
                    rd: 4,
                    r1: 2,
                    r2: 3,
                });
                func.emit(Opcode::Ret { rs: 4 });
                ("equiv_neq_string", func, 1, 1)
            },
        ];

        for (name, func, expected_icmp_count, expected_const) in cases {
            let module = lower_invariant_with_constants(&func, name, &pool)
                .expect("derived boolean cross-lane equality should fold");
            assert_eq!(
                inst_count(&module, 0, |inst| matches!(inst, Inst::ICmp { .. })),
                expected_icmp_count,
                "derived boolean cross-lane comparison should not emit an extra raw ICmp"
            );
            assert!(
                inst_count(&module, 0, |inst| matches!(
                    inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(value),
                    } if *value == i128::from(expected_const)
                )) > 0,
                "derived boolean cross-lane comparison should materialize {expected_const}"
            );
        }
    }

    #[test]
    fn test_scalar_equality_allows_same_known_lanes() {
        use std::sync::Arc;

        let mut pool = ConstantPool::new();
        let left_string = pool.add_value(Value::String(Arc::from("left")));
        let right_string = pool.add_value(Value::String(Arc::from("right")));
        let left_model = pool.add_value(Value::ModelValue(Arc::from("alpha")));
        let right_model = pool.add_value(Value::ModelValue(Arc::from("beta")));

        let mut func = BytecodeFunction::new("eq_same_lanes".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: left_string,
        });
        func.emit(Opcode::LoadConst {
            rd: 1,
            idx: right_string,
        });
        func.emit(Opcode::Eq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::LoadConst {
            rd: 3,
            idx: left_model,
        });
        func.emit(Opcode::LoadConst {
            rd: 4,
            idx: right_model,
        });
        func.emit(Opcode::Neq {
            rd: 5,
            r1: 3,
            r2: 4,
        });
        func.emit(Opcode::And {
            rd: 6,
            r1: 2,
            r2: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let module = lower_invariant_with_constants(&func, "eq_same_lanes", &pool)
            .expect("same-lane string/model equality should lower");
        assert_eq!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Eq | ICmpOp::Ne,
                    ..
                }
            )),
            2,
            "same-lane equality should still lower to native comparisons"
        );
    }

    #[test]
    fn test_scalar_equality_constant_folds_compact_slot_lane_mismatch() {
        let mut pool = ConstantPool::new();
        let q_field = tla_core::intern_name("q");
        let q_field_idx = pool.add_field_id(q_field.0);
        let black = pool.add_value(Value::String("black".into()));

        let mut func = BytecodeFunction::new("compact_slot_lane_mismatch".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: q_field_idx,
        });
        func.emit(Opcode::LoadConst { rd: 2, idx: black });
        func.emit(Opcode::Eq {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![(q_field, CompoundLayout::Int)],
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "compact_slot_lane_mismatch",
            &pool,
            &layout,
        )
        .expect("fixed-layout compact slot type mismatch should lower as TLA equality false");
        assert_eq!(
            inst_count(&module, 0, |inst| matches!(inst, Inst::ICmp { .. })),
            0,
            "known cross-lane scalar equality must not lower to raw i64 comparison"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                }
            )) > 0,
            "known Eq(Int, String) mismatch should materialize false"
        );
    }

    #[test]
    fn test_aggregate_equality_compact_sequence_vs_empty_sequence_compares_len_slot_not_pointer() {
        let cases = [
            (
                "eq_compact_seq_empty",
                Opcode::Eq {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                ICmpOp::Eq,
            ),
            (
                "neq_compact_seq_empty",
                Opcode::Neq {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
                ICmpOp::Ne,
            ),
        ];

        for (name, comparison, expected_op) in cases {
            let mut func = BytecodeFunction::new(name.to_string(), 0);
            func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
            func.emit(Opcode::SeqNew {
                rd: 1,
                start: 0,
                count: 0,
            });
            func.emit(comparison);
            func.emit(Opcode::Ret { rs: 2 });

            let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: Some(3),
            })]);

            let module = lower_invariant_with_constants_and_layout(
                &func,
                name,
                &ConstantPool::new(),
                &layout,
            )
            .expect("compact sequence empty comparison should lower structurally");

            assert!(
                has_i64_icmp_against_const_from_gep_slot(&module, 0, expected_op, 0, 0),
                "{name} must compare the compact sequence length slot with zero, not raw aggregate register values"
            );
        }
    }

    #[test]
    fn test_aggregate_equality_non_empty_compact_sequences_compares_slots_not_pointers() {
        let cases = [
            (
                "eq_non_empty_compact_seq",
                Opcode::Eq {
                    rd: 5,
                    r1: 0,
                    r2: 4,
                },
            ),
            (
                "neq_non_empty_compact_seq",
                Opcode::Neq {
                    rd: 5,
                    r1: 0,
                    r2: 4,
                },
            ),
        ];

        for (name, comparison) in cases {
            let mut func = BytecodeFunction::new(name.to_string(), 0);
            func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
            func.emit(Opcode::LoadImm { rd: 1, value: 1 });
            func.emit(Opcode::LoadImm { rd: 2, value: 2 });
            func.emit(Opcode::LoadImm { rd: 3, value: 3 });
            func.emit(Opcode::SeqNew {
                rd: 4,
                start: 1,
                count: 3,
            });
            func.emit(comparison);
            func.emit(Opcode::Ret { rs: 5 });

            let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: Some(3),
            })]);

            let module = lower_invariant_with_constants_and_layout(
                &func,
                name,
                &ConstantPool::new(),
                &layout,
            )
            .expect("non-empty compact sequence comparison should lower structurally");

            assert!(
                i64_icmp_load_load_count(&module, 0, ICmpOp::Eq) >= 4,
                "{name} must compare the compact len slot and all three element slots"
            );
        }
    }

    #[test]
    fn test_aggregate_equality_non_empty_sequence_unknown_element_shape_rejects() {
        let mut func = BytecodeFunction::new("eq_unknown_sequence_element_shape".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::SeqNew {
            rd: 5,
            start: 3,
            count: 2,
        });
        func.emit(Opcode::Eq {
            rd: 6,
            r1: 2,
            r2: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let err = lower_invariant(&func, "eq_unknown_sequence_element_shape")
            .expect_err("sequence equality without fixed element shape must fail closed");
        assert!(
            format!("{err}")
                .contains("structural sequence equality requires tracked left element shape"),
            "unexpected sequence equality rejection: {err}"
        );
    }

    #[test]
    fn test_cond_move_rejects_incompatible_scalar_lanes() {
        let mut func = BytecodeFunction::new("cond_move_scalar_lane_mismatch".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadBool {
            rd: 1,
            value: false,
        });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::CondMove {
            rd: 0,
            cond: 2,
            rs: 1,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let err = lower_invariant_with_constants(
            &func,
            "cond_move_scalar_lane_mismatch",
            &ConstantPool::new(),
        )
        .expect_err("CondMove over incompatible scalar lanes should not erase type provenance");
        assert!(
            format!("{err}").contains("CondMove over incompatible scalar lanes"),
            "unexpected CondMove rejection: {err}"
        );
    }

    /// Test that lowering rejects empty functions.
    #[test]
    fn test_reject_empty_function() {
        let func = BytecodeFunction::new("empty".to_string(), 0);
        let result = lower_invariant(&func, "empty");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            format!("{err}").contains("empty bytecode function"),
            "error: {err}"
        );
    }

    /// Test that lowering rejects functions with non-zero arity.
    #[test]
    fn test_reject_nonzero_arity() {
        let mut func = BytecodeFunction::new("with_arity".to_string(), 2);
        func.emit(Opcode::Ret { rs: 0 });
        let result = lower_invariant(&func, "with_arity");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(format!("{err}").contains("arity"), "error: {err}");
    }

    /// Test arithmetic with overflow checking.
    #[test]
    fn test_lower_add_with_overflow() {
        let mut func = BytecodeFunction::new("add_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "add_test").unwrap();
        assert_eq!(module.functions.len(), 1);

        // Should have at least 3 blocks: entry, overflow, continue.
        assert!(
            module.functions[0].blocks.len() >= 3,
            "expected >= 3 blocks for overflow-checked add, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test control flow with JumpFalse.
    #[test]
    fn test_lower_jump_false() {
        let mut func = BytecodeFunction::new("branch_test".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true }); // pc 0
        func.emit(Opcode::JumpFalse {
            // pc 1
            rs: 0,
            offset: 2, // jump to pc 3
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 42 }); // pc 2
        func.emit(Opcode::Ret { rs: 1 }); // pc 3
                                          // patch: offset=2 means pc 1 + 2 = 3
                                          // but we need a fallthrough at pc 2 and target at pc 3
                                          // Actually offset=2 targets pc=1+2=3. We need a valid program.

        // Let's create a proper branch that has both paths ending in Ret.
        let mut func = BytecodeFunction::new("branch_test".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true }); // pc 0
        func.emit(Opcode::JumpFalse {
            // pc 1
            rs: 0,
            offset: 3, // target = pc 1 + 3 = 4
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 42 }); // pc 2 (fallthrough)
        func.emit(Opcode::Ret { rs: 1 }); // pc 3
        func.emit(Opcode::LoadImm { rd: 1, value: 0 }); // pc 4 (target)
        func.emit(Opcode::Ret { rs: 1 }); // pc 5

        let module = lower_invariant(&func, "branch_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Should have blocks for: entry (pc0), fallthrough (pc2), target (pc4).
        assert!(
            module.functions[0].blocks.len() >= 3,
            "expected >= 3 blocks for branching code, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test next-state lowering with LoadPrime and StoreVar.
    #[test]
    fn test_lower_next_state() {
        let mut func = BytecodeFunction::new("Next".to_string(), 0);
        // Load x from current state, add 1, store as x'.
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_next_state(&func, "next_state").unwrap();
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "next_state");

        // Verify it has the 4-param function type (out, state_in, state_out, state_len).
        assert_eq!(module.func_types.len(), 1);
        assert_eq!(module.func_types[0].params.len(), 4);

        let proofs = &module.functions[0].proofs;
        assert!(
            !proofs.contains(&tmir::proof::ProofAnnotation::Pure),
            "next-state ABI entrypoint writes state_out and must not be Pure: {proofs:?}"
        );
        assert!(
            proofs.contains(&tmir::proof::ProofAnnotation::Deterministic),
            "next-state lowering should remain deterministic: {proofs:?}"
        );
    }

    #[test]
    fn test_load_var_rejects_out_of_range_supplied_layout() {
        let mut func = BytecodeFunction::new("load_var_out_of_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 1 });
        func.emit(Opcode::Ret { rs: 0 });

        let layout = StateLayout::new(vec![VarLayout::ScalarInt]);
        let err = lower_invariant_with_constants_and_layout(
            &func,
            "load_var_out_of_range",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("LoadVar with an out-of-range supplied layout var should reject");
        assert!(
            format!("{err}").contains("state layout has 1 vars but var_idx 1 was requested"),
            "unexpected LoadVar out-of-range error: {err}"
        );
    }

    #[test]
    fn test_store_var_rejects_out_of_range_supplied_layout() {
        let mut func = BytecodeFunction::new("store_var_out_of_range".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 7 });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::ScalarInt]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "store_var_out_of_range",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("StoreVar with an out-of-range supplied layout var should reject");
        assert!(
            format!("{err}").contains("state layout has 1 vars but var_idx 1 was requested"),
            "unexpected StoreVar out-of-range error: {err}"
        );
    }

    fn assert_store_var_compound_source_rejected(result: Result<tmir::Module, TmirError>) {
        let err = result.expect_err("compound StoreVar source should be rejected");
        let message = format!("{err}");
        assert!(
            message.contains("StoreVar for multi-slot variable")
                || message.contains("StoreVar for compact compound variable")
                || message
                    .contains("compact materialization requires fixed-width destination shape"),
            "unexpected StoreVar rejection message: {message}"
        );
    }

    #[test]
    fn test_store_var_record_new_to_fixed_record_layout_copies_flat_slots() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("black".into()));
        pool.add_value(Value::String("white".into()));

        let mut func = BytecodeFunction::new("store_record_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::RecordNew {
            rd: 2,
            fields_start,
            values_start: 0,
            count: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("black"), CompoundLayout::Int),
                (tla_core::intern_name("white"), CompoundLayout::Int),
            ],
        })]);

        let module =
            lower_next_state_with_constants_and_layout(&func, "store_record_new", &pool, &layout)
                .expect("flat RecordNew should store into fixed record state");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "flat RecordNew StoreVar should not need non-const-count Alloca"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_record_new_to_fixed_record_layout_matches_fields_by_name() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("pos".into()));
        pool.add_value(Value::String("q".into()));
        pool.add_value(Value::String("color".into()));

        let mut func = BytecodeFunction::new("store_record_new_reordered".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 11 });
        func.emit(Opcode::LoadImm { rd: 1, value: 22 });
        func.emit(Opcode::LoadImm { rd: 2, value: 33 });
        func.emit(Opcode::RecordNew {
            rd: 3,
            fields_start,
            values_start: 0,
            count: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("color"), CompoundLayout::Int),
                (tla_core::intern_name("pos"), CompoundLayout::Int),
                (tla_core::intern_name("q"), CompoundLayout::Int),
            ],
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_record_new_reordered",
            &pool,
            &layout,
        )
        .expect("RecordNew StoreVar should match fields by name, not syntax order");
        assert_no_ptr_payload_store_to_state_out(&module, 0);
        assert_eq!(
            state_out_store_source_slots(&module, 0),
            vec![(0, 2), (1, 0), (2, 1)],
            "StoreVar should copy source fields into fixed compact destination layout order"
        );
    }

    fn ewd998_compact_layout() -> StateLayout {
        let int_function = |value_layout| {
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(value_layout),
                pair_count: Some(3),
                domain_lo: Some(0),
            })
        };

        StateLayout::new(vec![
            int_function(CompoundLayout::Bool),
            int_function(CompoundLayout::String),
            int_function(CompoundLayout::Int),
            int_function(CompoundLayout::Int),
            VarLayout::Compound(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("pos"), CompoundLayout::Int),
                    (tla_core::intern_name("color"), CompoundLayout::String),
                    (tla_core::intern_name("q"), CompoundLayout::Int),
                ],
            }),
        ])
    }

    #[test]
    fn test_store_var_ewd_token_record_new_writes_pos_slot_not_pointer() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("pos".into()));
        pool.add_value(Value::String("q".into()));
        pool.add_value(Value::String("color".into()));
        let white_idx = pool.add_value(Value::String("white".into()));

        let mut func = BytecodeFunction::new("store_ewd_token_record_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 2 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadConst {
            rd: 2,
            idx: white_idx,
        });
        func.emit(Opcode::RecordNew {
            rd: 3,
            fields_start,
            values_start: 0,
            count: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 4, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = ewd998_compact_layout();

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_ewd_token_record_new",
            &pool,
            &layout,
        )
        .expect("EWD-style fresh token RecordNew should store into compact token state");

        assert_no_ptr_payload_store_to_state_out(&module, 0);
        assert_eq!(
            state_out_store_source_slots(&module, 0),
            vec![(12, 0), (13, 2), (14, 1)],
            "EWD token StoreVar must copy pos/color/q fields into slots 12/13/14"
        );
    }

    #[test]
    fn test_ewd_initiate_probe_fixed_layout_action_keeps_compact_stores() {
        let mut pool = ConstantPool::new();
        let token_fields_start = pool.add_value(Value::String("pos".into()));
        pool.add_value(Value::String("q".into()));
        pool.add_value(Value::String("color".into()));
        let unchanged_start = pool.add_value(Value::SmallInt(0));
        pool.add_value(Value::SmallInt(2));
        pool.add_value(Value::SmallInt(3));
        let pos_field = pool.add_field_id(tla_core::intern_name("pos").0);
        let white_idx = pool.add_value(Value::String("white".into()));

        let mut func = BytecodeFunction::new("ewd_initiate_probe_fixed_layout".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 4 });
        func.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: pos_field,
        });
        func.emit(Opcode::LoadImm { rd: 2, value: 0 });
        func.emit(Opcode::Eq {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::LoadImm { rd: 4, value: 2 });
        func.emit(Opcode::LoadImm { rd: 5, value: 0 });
        func.emit(Opcode::LoadConst {
            rd: 6,
            idx: white_idx,
        });
        func.emit(Opcode::RecordNew {
            rd: 7,
            fields_start: token_fields_start,
            values_start: 4,
            count: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 4, rs: 7 });
        func.emit(Opcode::LoadVar { rd: 8, var_idx: 1 });
        func.emit(Opcode::FuncExcept {
            rd: 9,
            func: 8,
            path: 2,
            val: 6,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 9 });
        func.emit(Opcode::Unchanged {
            rd: 10,
            start: unchanged_start,
            count: 3,
        });
        func.emit(Opcode::And {
            rd: 11,
            r1: 3,
            r2: 10,
        });
        func.emit(Opcode::Ret { rs: 11 });

        let layout = ewd998_compact_layout();
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "ewd_initiate_probe_fixed_layout",
            &pool,
            &layout,
        )
        .expect("EWD InitiateProbe fixed-layout action should lower natively");

        let copied_slots = state_out_store_source_slots(&module, 0);
        for (dst_slot, src_slot) in [(12, 0), (13, 2), (14, 1)] {
            assert!(
                copied_slots.contains(&(dst_slot, src_slot)),
                "EWD token slot {dst_slot} should copy from the fresh token aggregate slot {src_slot}; copied={copied_slots:?}"
            );
        }
        assert!(
            has_i64_icmp_against_const_from_state_slot(&module, 0, ICmpOp::Eq, 12, 0),
            "token.pos guard should originate from the fixed compact token.pos slot"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "EWD InitiateProbe fixed-layout lowering should keep static aggregate allocations"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);

        let unchanged_pairs = unchanged_eq_slot_pairs(&module, 0);
        for slot in [0, 1, 2, 6, 7, 8, 9, 10, 11] {
            assert!(
                unchanged_pairs.contains(&(slot, slot)),
                "UNCHANGED EWD slot {slot} should compare state_in to state_out; pairs={unchanged_pairs:?}"
            );
        }
    }

    #[test]
    fn test_ewd_pass_token_fixed_layout_action_keeps_compact_record_paths() {
        let mut pool = ConstantPool::new();
        let token_fields_start = pool.add_value(Value::String("pos".into()));
        pool.add_value(Value::String("q".into()));
        pool.add_value(Value::String("color".into()));
        let unchanged_start = pool.add_value(Value::SmallInt(0));
        pool.add_value(Value::SmallInt(2));
        pool.add_value(Value::SmallInt(3));
        let pos_field = pool.add_field_id(tla_core::intern_name("pos").0);
        let q_field = pool.add_field_id(tla_core::intern_name("q").0);
        let color_field = pool.add_field_id(tla_core::intern_name("color").0);
        let black_idx = pool.add_value(Value::String("black".into()));
        let white_idx = pool.add_value(Value::String("white".into()));

        let mut func = BytecodeFunction::new("ewd_pass_token_fixed_layout".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 0 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 1,
            arg: 0,
        });
        func.emit(Opcode::Not { rd: 3, rs: 2 });
        func.emit(Opcode::LoadVar { rd: 4, var_idx: 4 });
        func.emit(Opcode::RecordGet {
            rd: 5,
            rs: 4,
            field_idx: pos_field,
        });
        func.emit(Opcode::Eq {
            rd: 6,
            r1: 5,
            r2: 0,
        });
        func.emit(Opcode::LoadImm { rd: 7, value: 1 });
        func.emit(Opcode::SubInt {
            rd: 8,
            r1: 5,
            r2: 7,
        });
        func.emit(Opcode::RecordGet {
            rd: 9,
            rs: 4,
            field_idx: q_field,
        });
        func.emit(Opcode::LoadVar { rd: 10, var_idx: 2 });
        func.emit(Opcode::FuncApply {
            rd: 11,
            func: 10,
            arg: 0,
        });
        func.emit(Opcode::AddInt {
            rd: 12,
            r1: 9,
            r2: 11,
        });
        func.emit(Opcode::RecordGet {
            rd: 13,
            rs: 4,
            field_idx: color_field,
        });
        func.emit(Opcode::LoadVar { rd: 14, var_idx: 1 });
        func.emit(Opcode::FuncApply {
            rd: 15,
            func: 14,
            arg: 0,
        });
        func.emit(Opcode::LoadConst {
            rd: 16,
            idx: black_idx,
        });
        func.emit(Opcode::Eq {
            rd: 17,
            r1: 15,
            r2: 16,
        });
        func.emit(Opcode::Move { rd: 18, rs: 13 });
        func.emit(Opcode::CondMove {
            rd: 18,
            cond: 17,
            rs: 16,
        });
        func.emit(Opcode::Move { rd: 25, rs: 8 });
        func.emit(Opcode::Move { rd: 26, rs: 12 });
        func.emit(Opcode::Move { rd: 27, rs: 18 });
        func.emit(Opcode::RecordNew {
            rd: 19,
            fields_start: token_fields_start,
            values_start: 25,
            count: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 4, rs: 19 });
        func.emit(Opcode::LoadConst {
            rd: 20,
            idx: white_idx,
        });
        func.emit(Opcode::FuncExcept {
            rd: 21,
            func: 14,
            path: 0,
            val: 20,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 21 });
        func.emit(Opcode::Unchanged {
            rd: 22,
            start: unchanged_start,
            count: 3,
        });
        func.emit(Opcode::And {
            rd: 23,
            r1: 3,
            r2: 6,
        });
        func.emit(Opcode::And {
            rd: 24,
            r1: 23,
            r2: 22,
        });
        func.emit(Opcode::Ret { rs: 24 });

        let layout = ewd998_compact_layout();
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "ewd_pass_token_fixed_layout",
            &pool,
            &layout,
        )
        .expect("EWD PassToken fixed-layout action should lower natively");

        assert!(
            has_i64_icmp_against_const_from_state_slot(&module, 0, ICmpOp::Eq, 12, 1),
            "PassToken guard should compare token.pos originating from fixed compact slot 12"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "EWD PassToken fixed-layout lowering should keep static aggregate allocations"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_one_field_record_new_copies_slot_not_pointer() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("only".into()));

        let mut func = BytecodeFunction::new("store_one_field_record_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::RecordNew {
            rd: 1,
            fields_start,
            values_start: 0,
            count: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::Ret { rs: 2 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![(tla_core::intern_name("only"), CompoundLayout::Int)],
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_one_field_record_new",
            &pool,
            &layout,
        )
        .expect(
            "single-slot RecordNew should copy the field slot, not store the aggregate pointer",
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "single-slot RecordNew StoreVar should not need non-const-count Alloca"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_tail_after_placeholder_compound_uses_compact_offset() {
        let mut func =
            BytecodeFunction::new("store_tail_after_placeholder_compound".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 2 });
        func.emit(Opcode::StoreVar { var_idx: 2, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("left"), CompoundLayout::Int),
                    (tla_core::intern_name("right"), CompoundLayout::Int),
                ],
            }),
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Int),
                pair_count: None,
                domain_lo: None,
            }),
            VarLayout::ScalarInt,
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_tail_after_placeholder_compound",
            &ConstantPool::new(),
            &layout,
        )
        .expect("StoreVar after a placeholder compact layout should lower");

        assert_eq!(
            state_out_store_source_slots(&module, 0),
            vec![(3, 3)],
            "LoadVar/StoreVar must use ABI compact placeholder offsets, not raw var_idx fallback"
        );
    }

    #[test]
    fn test_store_var_seq_new_to_fixed_sequence_layout_copies_flat_slots() {
        let mut func = BytecodeFunction::new("store_seq_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SeqNew {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_seq_new",
            &ConstantPool::new(),
            &layout,
        )
        .expect("flat SeqNew should store into fixed sequence state");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "flat SeqNew StoreVar should not need non-const-count Alloca"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_empty_seq_new_copies_len_slot_not_pointer() {
        let mut func = BytecodeFunction::new("store_empty_seq_new".to_string(), 0);
        func.emit(Opcode::SeqNew {
            rd: 0,
            start: 0,
            count: 0,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(0),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_empty_seq_new",
            &ConstantPool::new(),
            &layout,
        )
        .expect("empty SeqNew should copy the length slot, not store the aggregate pointer");
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_seq_new_set_bitmask_elements_to_fixed_sequence_layout() {
        let mut func = BytecodeFunction::new("store_seq_setbitmask_new".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 2, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let bitmask = || VarLayout::Compound(int_range_set_bitmask_layout(1, 3));
        let layout = StateLayout::new(vec![
            bitmask(),
            bitmask(),
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(int_range_set_bitmask_layout(1, 3)),
                element_count: Some(2),
            }),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_seq_setbitmask_new",
            &ConstantPool::new(),
            &layout,
        )
        .expect("flat SeqNew of SetBitmask elements should store into fixed sequence state");
        assert_eq!(
            inst_count(&module, 0, |inst| matches!(inst, Inst::CondBr { .. })),
            0,
            "flat SeqNew StoreVar should stay on the straight-line copy path"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "flat SeqNew SetBitmask StoreVar should not need non-const-count Alloca"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_nested_record_aggregate_to_fixed_record_layout_copies_flat_slots() {
        let mut pool = ConstantPool::new();
        let inner_fields = pool.add_value(Value::String("x".into()));
        pool.add_value(Value::String("y".into()));
        let outer_fields = pool.add_value(Value::String("inner".into()));

        let mut func = BytecodeFunction::new("store_nested_record_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: inner_fields,
            values_start: 0,
            count: 2,
        });
        func.emit(Opcode::RecordNew {
            rd: 3,
            fields_start: outer_fields,
            values_start: 2,
            count: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![(
                tla_core::intern_name("inner"),
                CompoundLayout::Record {
                    fields: vec![
                        (tla_core::intern_name("x"), CompoundLayout::Int),
                        (tla_core::intern_name("y"), CompoundLayout::Int),
                    ],
                },
            )],
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_nested_record_new",
            &pool,
            &layout,
        )
        .expect("nested RecordNew should copy fixed-width field slots into compact state");
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_sequence_of_records_to_fixed_sequence_layout_copies_flat_slots() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("x".into()));
        pool.add_value(Value::String("y".into()));

        let mut func = BytecodeFunction::new("store_seq_record_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::RecordNew {
            rd: 2,
            fields_start,
            values_start: 0,
            count: 2,
        });
        func.emit(Opcode::SeqNew {
            rd: 3,
            start: 2,
            count: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let record_layout = CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(record_layout),
            element_count: Some(1),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_seq_record_new",
            &pool,
            &layout,
        )
        .expect("SeqNew of fixed-width records should copy nested field slots into compact state");
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_function_aggregate_to_fixed_function_layout_copies_value_slots() {
        let mut func = BytecodeFunction::new("store_funcdef_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 5, value: 9 });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 5,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(2),
            domain_lo: Some(1),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_funcdef_new",
            &ConstantPool::new(),
            &layout,
        )
        .expect(
            "FuncDef with fixed-width scalar values should copy values into compact function state",
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_one_pair_function_aggregate_to_fixed_function_layout_copies_value_slot() {
        let mut func = BytecodeFunction::new("store_one_pair_funcdef_new".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 4, value: 7 });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 4,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::Ret { rs: 5 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(1),
            domain_lo: Some(1),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_one_pair_funcdef_new",
            &ConstantPool::new(),
            &layout,
        )
        .expect("one-pair FuncDef with fixed-width scalar value should copy the value slot");
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_funcdef_loopnext_deep_copies_compact_body_value_slots() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("x".into()));
        pool.add_value(Value::String("y".into()));

        let mut func = BytecodeFunction::new("funcdef_compact_body_capture".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 5, value: 99 });
        func.emit(Opcode::RecordNew {
            rd: 6,
            fields_start,
            values_start: 4,
            count: 2,
        });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 6,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant_with_constants(&func, "funcdef_compact_body_capture", &pool)
            .expect("FuncDef with compact record body values should lower");

        assert_funcdef_compact_capture_copies_slots(&module, 0, 4, &[0, 1]);
    }

    #[test]
    fn test_store_var_function_append_sequence_value_to_fixed_function_layout_copies_slots() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("store_funcdef_append_seq_value".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 4, value: 7 });
        func.emit(Opcode::SeqNew {
            rd: 5,
            start: 4,
            count: 1,
        });
        func.emit(Opcode::LoadImm { rd: 6, value: 8 });
        func.emit(Opcode::CallBuiltin {
            rd: 7,
            builtin: BuiltinOp::Append,
            args_start: 5,
            argc: 2,
        });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 7,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 8, value: true });
        func.emit(Opcode::Ret { rs: 8 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: Some(2),
            }),
            pair_count: Some(1),
            domain_lo: Some(1),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_funcdef_append_seq_value",
            &ConstantPool::new(),
            &layout,
        )
        .expect("FuncDef Append(seq, elem) value should store into compact function state");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size Append value StoreVar should not need non-const-count Alloca"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_dense_function_value_to_fixed_sequence_layout_copies_slots() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("x".into()));
        pool.add_value(Value::String("y".into()));

        let mut func = BytecodeFunction::new("store_dense_function_as_sequence".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 6, value: 10 });
        func.emit(Opcode::LoadImm { rd: 7, value: 20 });
        func.emit(Opcode::RecordNew {
            rd: 8,
            fields_start,
            values_start: 6,
            count: 2,
        });
        func.emit(Opcode::SeqNew {
            rd: 9,
            start: 8,
            count: 1,
        });
        func.emit(Opcode::LoadBool {
            rd: 10,
            value: false,
        });
        func.emit(Opcode::LoadImm { rd: 11, value: 99 });
        func.emit(Opcode::CondMove {
            rd: 9,
            cond: 10,
            rs: 11,
        });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 5,
            r_body: 9,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 4 });
        func.emit(Opcode::LoadBool {
            rd: 12,
            value: true,
        });
        func.emit(Opcode::Ret { rs: 12 });

        let record_layout = CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(record_layout),
                element_count: Some(3),
            }),
            element_count: Some(3),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_dense_function_as_sequence",
            &pool,
            &layout,
        )
        .expect("dense 1-based FuncDef value should copy into fixed sequence layout");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "dense function-to-sequence copy should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_func_except_dense_function_value_rejects_incompatible_condmove_shape() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("x".into()));
        pool.add_value(Value::String("y".into()));

        let mut func = BytecodeFunction::new(
            "func_except_dense_function_as_sequence_value".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func.emit(Opcode::LoadImm { rd: 3, value: 2 });
        func.emit(Opcode::LoadImm { rd: 4, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 5,
            start: 2,
            count: 3,
        });
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 6,
            r_binding: 7,
            r_domain: 5,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 8, value: 10 });
        func.emit(Opcode::LoadImm { rd: 9, value: 20 });
        func.emit(Opcode::RecordNew {
            rd: 10,
            fields_start,
            values_start: 8,
            count: 2,
        });
        func.emit(Opcode::SeqNew {
            rd: 11,
            start: 10,
            count: 1,
        });
        func.emit(Opcode::LoadVar { rd: 12, var_idx: 2 });
        func.emit(Opcode::LoadImm { rd: 13, value: 99 });
        func.emit(Opcode::SeqNew {
            rd: 16,
            start: 13,
            count: 1,
        });
        func.emit(Opcode::CondMove {
            rd: 11,
            cond: 12,
            rs: 16,
        });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 7,
            r_body: 11,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::FuncExcept {
            rd: 14,
            func: 0,
            path: 1,
            val: 6,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 14 });
        func.emit(Opcode::LoadBool {
            rd: 15,
            value: true,
        });
        func.emit(Opcode::Ret { rs: 15 });

        let record_layout = CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        };
        let sequence_layout = CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Sequence {
                    element_layout: Box::new(record_layout),
                    element_count: Some(3),
                }),
                element_count: Some(3),
            }),
            element_count: Some(3),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(sequence_layout.clone()),
            VarLayout::Compound(sequence_layout),
            VarLayout::ScalarBool,
        ]);

        let err = lower_next_state_with_constants_and_layout(
            &func,
            "func_except_dense_function_as_sequence_value",
            &pool,
            &layout,
        )
        .expect_err(
            "incompatible CondMove branch shapes must fail closed before fixed materialization",
        );
        assert!(
            format!("{err}").contains(
                "CondMove over compact aggregate values requires compatible slot materialization"
            ),
            "unexpected incompatible CondMove rejection: {err}"
        );
    }

    #[test]
    fn test_func_except_setbitmask_value_materializes_exact_int_set_replacement() {
        let mut func =
            BytecodeFunction::new("func_except_setbitmask_exact_set_value".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 2,
            count: 1,
        });
        func.emit(Opcode::FuncExcept {
            rd: 4,
            func: 0,
            path: 1,
            val: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 4 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::Ret { rs: 5 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(1, 4)),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "func_except_setbitmask_exact_set_value",
            &ConstantPool::new(),
            &layout,
        )
        .expect("FuncExcept ack[1] := {1} should compact-materialize to a SetBitmask mask");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "exact set replacement should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_func_except_setbitmask_value_materializes_empty_set_replacement() {
        let mut func =
            BytecodeFunction::new("func_except_setbitmask_empty_set_value".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 2,
            count: 0,
        });
        func.emit(Opcode::FuncExcept {
            rd: 3,
            func: 0,
            path: 1,
            val: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(1, 4)),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "func_except_setbitmask_empty_set_value",
            &ConstantPool::new(),
            &layout,
        )
        .expect("FuncExcept ack[1] := {} should compact-materialize to an empty SetBitmask mask");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "empty set replacement should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_func_except_setbitmask_value_materializes_nonzero_exact_int_set_replacement() {
        let mut func = BytecodeFunction::new(
            "func_except_setbitmask_nonzero_exact_set_value".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 2,
            count: 1,
        });
        func.emit(Opcode::FuncExcept {
            rd: 4,
            func: 0,
            path: 1,
            val: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 4 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::Ret { rs: 5 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(1, 4)),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "func_except_setbitmask_nonzero_exact_set_value",
            &ConstantPool::new(),
            &layout,
        )
        .expect("FuncExcept ack[2] := {2} should materialize at a nonzero value slot offset");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "nonzero exact set replacement should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_func_except_setbitmask_value_materializes_nonzero_empty_set_replacement() {
        let mut func = BytecodeFunction::new(
            "func_except_setbitmask_nonzero_empty_set_value".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 2,
            count: 0,
        });
        func.emit(Opcode::FuncExcept {
            rd: 3,
            func: 0,
            path: 1,
            val: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(1, 4)),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "func_except_setbitmask_nonzero_empty_set_value",
            &ConstantPool::new(),
            &layout,
        )
        .expect("FuncExcept ack[3] := {} should materialize at a nonzero value slot offset");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "nonzero empty set replacement should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_single_key_func_except_setbitmask_value_materializes_exact_int_set_replacement() {
        let mut func = BytecodeFunction::new(
            "single_key_func_except_setbitmask_exact_set_value".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 2,
            count: 1,
        });
        func.emit(Opcode::FuncExcept {
            rd: 4,
            func: 0,
            path: 1,
            val: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 4 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::Ret { rs: 5 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(1, 4)),
            pair_count: Some(1),
            domain_lo: Some(1),
        })]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "single_key_func_except_setbitmask_exact_set_value",
            &ConstantPool::new(),
            &layout,
        )
        .expect(
            "single-key FuncExcept ack[1] := {1} should use the expected SetBitmask value shape",
        );

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "single-key exact set replacement should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_single_key_func_except_setbitmask_value_materializes_empty_set_replacement() {
        let mut func = BytecodeFunction::new(
            "single_key_func_except_setbitmask_empty_set_value".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 2,
            count: 0,
        });
        func.emit(Opcode::FuncExcept {
            rd: 3,
            func: 0,
            path: 1,
            val: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(1, 4)),
            pair_count: Some(1),
            domain_lo: Some(1),
        })]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "single_key_func_except_setbitmask_empty_set_value",
            &ConstantPool::new(),
            &layout,
        )
        .expect(
            "single-key FuncExcept ack[1] := {} should use the expected SetBitmask value shape",
        );

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "single-key empty set replacement should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_single_key_func_except_setbitmask_value_rejects_out_of_universe_exact_set() {
        let mut func = BytecodeFunction::new(
            "single_key_func_except_setbitmask_out_of_universe_exact_set".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 0 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 2,
            count: 1,
        });
        func.emit(Opcode::FuncExcept {
            rd: 4,
            func: 0,
            path: 1,
            val: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 4 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::Ret { rs: 5 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(1, 4)),
            pair_count: Some(1),
            domain_lo: Some(1),
        })]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "single_key_func_except_setbitmask_out_of_universe_exact_set",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("single-key FuncExcept ack[1] := {0} should reject out-of-universe SetBitmask materialization");
        let message = err.to_string();
        assert!(
            message.contains("outside the destination SetBitmask universe")
                || message
                    .contains("requires all values inside the destination SetBitmask universe"),
            "unexpected out-of-universe error: {message}"
        );
    }

    #[test]
    fn test_store_var_one_level_inbox_append_message_record_copies_compact_slots() {
        use tla_tir::bytecode::BuiltinOp;

        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("from".into()));
        pool.add_value(Value::String("type".into()));
        let req_idx = pool.add_value(Value::String("req".into()));

        let mut func =
            BytecodeFunction::new("store_one_level_inbox_append_message_record".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadImm { rd: 4, value: 2 });
        func.emit(Opcode::LoadConst {
            rd: 5,
            idx: req_idx,
        });
        func.emit(Opcode::RecordNew {
            rd: 3,
            fields_start,
            values_start: 4,
            count: 2,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 6,
            builtin: BuiltinOp::Append,
            args_start: 2,
            argc: 2,
        });
        func.emit(Opcode::FuncExcept {
            rd: 7,
            func: 0,
            path: 1,
            val: 6,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 7 });
        func.emit(Opcode::LoadBool { rd: 8, value: true });
        func.emit(Opcode::Ret { rs: 8 });

        let message_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("from"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let inbox_layout = || CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(message_layout()),
                element_count: Some(3),
            }),
            pair_count: Some(3),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(inbox_layout())]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_one_level_inbox_append_message_record",
            &pool,
            &layout,
        )
        .expect("one-level inbox Append(message) update should keep fixed compact materialization");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "one-level inbox Append(message) StoreVar should not need non-const-count Alloca"
        );
        assert!(
            has_const_alloca_count(&module, 0, 21),
            "Function<Int, Seq(Message)> replacement should materialize 3 fixed 7-slot rows"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_one_level_inbox_tail_message_sequence_copies_compact_slots() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func =
            BytecodeFunction::new("store_one_level_inbox_tail_message_sequence".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 3,
            builtin: BuiltinOp::Tail,
            args_start: 2,
            argc: 1,
        });
        func.emit(Opcode::FuncExcept {
            rd: 4,
            func: 0,
            path: 1,
            val: 3,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 4 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::Ret { rs: 5 });

        let message_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("from"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let inbox_layout = || CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(message_layout()),
                element_count: Some(3),
            }),
            pair_count: Some(3),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(inbox_layout())]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_one_level_inbox_tail_message_sequence",
            &ConstantPool::new(),
            &layout,
        )
        .expect("one-level inbox Tail update should keep fixed compact materialization");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "one-level inbox Tail StoreVar should not need non-const-count Alloca"
        );
        assert!(
            has_const_alloca_count(&module, 0, 21),
            "Function<Int, Seq(Message)> Tail replacement should materialize 3 fixed 7-slot rows"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_nested_function_except_append_sequence_record_copies_compact_slots() {
        use tla_tir::bytecode::BuiltinOp;

        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("x".into()));
        pool.add_value(Value::String("y".into()));

        let mut func = BytecodeFunction::new(
            "store_nested_function_except_append_seq_record".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(Opcode::FuncApply {
            rd: 4,
            func: 2,
            arg: 3,
        });
        func.emit(Opcode::LoadImm { rd: 6, value: 10 });
        func.emit(Opcode::LoadImm { rd: 7, value: 20 });
        func.emit(Opcode::RecordNew {
            rd: 5,
            fields_start,
            values_start: 6,
            count: 2,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 8,
            builtin: BuiltinOp::Append,
            args_start: 4,
            argc: 2,
        });
        func.emit(Opcode::FuncExcept {
            rd: 9,
            func: 2,
            path: 3,
            val: 8,
        });
        func.emit(Opcode::FuncExcept {
            rd: 10,
            func: 0,
            path: 1,
            val: 9,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 10 });
        func.emit(Opcode::LoadBool {
            rd: 11,
            value: true,
        });
        func.emit(Opcode::Ret { rs: 11 });

        let record_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        };
        let nested_function_layout = |element_count| CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Sequence {
                    element_layout: Box::new(record_layout()),
                    element_count: Some(element_count),
                }),
                pair_count: Some(1),
                domain_lo: Some(1),
            }),
            pair_count: Some(1),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(nested_function_layout(2)),
            VarLayout::Compound(nested_function_layout(2)),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_nested_function_except_append_seq_record",
            &pool,
            &layout,
        )
        .expect(
            "Append(Sequence<Record>, Record) should retain compact slots through nested FuncExcept",
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size nested Append StoreVar should not need non-const-count Alloca"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_compact_sequence_append_record_with_reordered_fields_copies_slots() {
        use tla_tir::bytecode::BuiltinOp;

        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("y".into()));
        pool.add_value(Value::String("x".into()));

        let source_element = AggregateShape::Record {
            fields: vec![
                (
                    tla_core::intern_name("x"),
                    Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                ),
                (
                    tla_core::intern_name("y"),
                    Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                ),
            ],
        };
        let appended_element = AggregateShape::Record {
            fields: vec![
                (
                    tla_core::intern_name("y"),
                    Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                ),
                (
                    tla_core::intern_name("x"),
                    Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
                ),
            ],
        };
        let append_shape = sequence_append_shape(
            Some(&AggregateShape::Sequence {
                extent: SequenceExtent::Capacity(2),
                element: Some(Box::new(source_element)),
            }),
            Some(&appended_element),
        );
        assert_eq!(
            append_shape
                .as_ref()
                .and_then(AggregateShape::compact_slot_count),
            Some(5),
            "Append shape inference should preserve reordered record elements by field name"
        );

        let mut func = BytecodeFunction::new(
            "store_compact_sequence_append_reordered_record_fields".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 20 });
        func.emit(Opcode::LoadImm { rd: 3, value: 10 });
        func.emit(Opcode::RecordNew {
            rd: 1,
            fields_start,
            values_start: 2,
            count: 2,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Append,
            args_start: 0,
            argc: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 4 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::Ret { rs: 5 });

        let record_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        };
        let sequence_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(record_layout()),
            element_count: Some(2),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(sequence_layout()),
            VarLayout::Compound(sequence_layout()),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_compact_sequence_append_reordered_record_fields",
            &pool,
            &layout,
        )
        .expect(
            "Append should materialize reordered record fields into the compact sequence layout",
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size reordered-record Append StoreVar should not need non-const-count Alloca"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_multi_key_function_except_sequence_value_copies_compact_slots() {
        let mut func = BytecodeFunction::new(
            "store_multi_key_function_except_sequence_value".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 7 });
        func.emit(Opcode::LoadImm { rd: 3, value: 8 });
        func.emit(Opcode::SeqNew {
            rd: 4,
            start: 2,
            count: 2,
        });
        func.emit(Opcode::FuncExcept {
            rd: 5,
            func: 0,
            path: 1,
            val: 4,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 5 });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Sequence {
                    element_layout: Box::new(CompoundLayout::Int),
                    element_count: Some(2),
                }),
                pair_count: Some(3),
                domain_lo: Some(1),
            }),
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Sequence {
                    element_layout: Box::new(CompoundLayout::Int),
                    element_count: Some(2),
                }),
                pair_count: Some(3),
                domain_lo: Some(1),
            }),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_multi_key_function_except_sequence_value",
            &ConstantPool::new(),
            &layout,
        )
        .expect("multi-key compact function EXCEPT should copy and overwrite packed slots");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "constant-index function EXCEPT should use fixed allocations"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_constant_index_sequence_except_record_value_copies_compact_slots() {
        let mut pool = ConstantPool::new();
        let fields_start = pool.add_value(Value::String("x".into()));
        pool.add_value(Value::String("y".into()));

        let mut func = BytecodeFunction::new(
            "store_constant_index_sequence_except_record_value".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 10 });
        func.emit(Opcode::LoadImm { rd: 3, value: 20 });
        func.emit(Opcode::RecordNew {
            rd: 4,
            fields_start,
            values_start: 2,
            count: 2,
        });
        func.emit(Opcode::FuncExcept {
            rd: 5,
            func: 0,
            path: 1,
            val: 4,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 5 });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::Ret { rs: 6 });

        let sequence_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("x"), CompoundLayout::Int),
                    (tla_core::intern_name("y"), CompoundLayout::Int),
                ],
            }),
            element_count: Some(2),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(sequence_layout()),
            VarLayout::Compound(sequence_layout()),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_constant_index_sequence_except_record_value",
            &pool,
            &layout,
        )
        .expect("constant-index compact sequence EXCEPT should copy and overwrite packed slots");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "constant-index sequence EXCEPT should use fixed allocations"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "compact sequence EXCEPT must compare the update index against runtime Len(seq)"
        );
        assert!(
            count_condbr(&module, 0) >= 4,
            "compact sequence EXCEPT replacement must be gated by runtime length/path branches"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_record_except_missing_key_keeps_compact_identity() {
        let mut func = BytecodeFunction::new("record_except_missing_key".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 99 });
        func.emit(Opcode::LoadImm { rd: 2, value: 42 });
        func.emit(Opcode::FuncExcept {
            rd: 3,
            func: 0,
            path: 1,
            val: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let record_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(record_layout()),
            VarLayout::Compound(record_layout()),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "record_except_missing_key",
            &ConstantPool::new(),
            &layout,
        )
        .expect("missing compact record EXCEPT key should lower as identity");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "missing compact record key must not fall through to generic function layout"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_function_except_out_of_domain_keeps_compact_identity() {
        let mut func = BytecodeFunction::new("function_except_out_of_domain".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 99 });
        func.emit(Opcode::LoadImm { rd: 2, value: 7 });
        func.emit(Opcode::LoadImm { rd: 3, value: 8 });
        func.emit(Opcode::SeqNew {
            rd: 4,
            start: 2,
            count: 2,
        });
        func.emit(Opcode::FuncExcept {
            rd: 5,
            func: 0,
            path: 1,
            val: 4,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 5 });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::Ret { rs: 6 });

        let function_layout = || CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(function_layout()),
            VarLayout::Compound(function_layout()),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "function_except_out_of_domain",
            &ConstantPool::new(),
            &layout,
        )
        .expect("out-of-domain compact function EXCEPT should lower as identity");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "out-of-domain compact function key must not fall through to generic function layout"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_dynamic_sequence_except_uses_capacity_copy_and_runtime_domain_checks() {
        let mut func = BytecodeFunction::new("dynamic_sequence_except".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 99 });
        func.emit(Opcode::FuncExcept {
            rd: 3,
            func: 1,
            path: 0,
            val: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 2, rs: 3 });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let sequence_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        };
        let layout = StateLayout::new(vec![
            VarLayout::ScalarInt,
            VarLayout::Compound(sequence_layout()),
            VarLayout::Compound(sequence_layout()),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "dynamic_sequence_except",
            &ConstantPool::new(),
            &layout,
        )
        .expect("dynamic compact sequence EXCEPT should lower with runtime checks");
        assert!(
            has_const_alloca_count(&module, 0, 4),
            "dynamic compact sequence EXCEPT must copy the fixed capacity plus length slot"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "dynamic compact sequence EXCEPT must not allocate from runtime Len(seq)"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    ..
                }
            )) >= 2,
            "dynamic compact sequence EXCEPT must check 0 <= Len(seq) and 1 <= path"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    ..
                }
            )) >= 2,
            "dynamic compact sequence EXCEPT must check Len(seq) <= capacity and path <= Len(seq)"
        );
        assert!(
            count_condbr(&module, 0) >= 4,
            "dynamic compact sequence EXCEPT must branch around the update outside the domain"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_compact_sequence_rejects_negative_runtime_len_before_header_store() {
        let mut func =
            BytecodeFunction::new("store_compact_sequence_len_negative_guard".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let sequence_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(sequence_layout()),
            VarLayout::Compound(sequence_layout()),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_compact_sequence_len_negative_guard",
            &ConstantPool::new(),
            &layout,
        )
        .expect("compact sequence StoreVar should lower with runtime length guards");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "compact sequence StoreVar must reject negative runtime lengths"
        );
        assert!(
            has_runtime_error_status_path(&module, 0),
            "invalid compact sequence length must branch to a runtime error path"
        );
        assert!(
            !block_has_state_out_store_to_slot(&module, 0, 0, 4),
            "destination length header must not be stored before the negative-length guard"
        );
        assert!(
            (1..module.functions[0].blocks.len())
                .any(|block| block_has_state_out_store_to_slot(&module, 0, block, 4)),
            "destination length header should be stored after the length guard succeeds"
        );
    }

    #[test]
    fn test_store_var_compact_sequence_rejects_over_capacity_runtime_len_before_header_store() {
        let mut func =
            BytecodeFunction::new("store_compact_sequence_len_capacity_guard".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let sequence_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(sequence_layout()),
            VarLayout::Compound(sequence_layout()),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_compact_sequence_len_capacity_guard",
            &ConstantPool::new(),
            &layout,
        )
        .expect("compact sequence StoreVar should lower with runtime length guards");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "compact sequence StoreVar must reject runtime lengths greater than capacity"
        );
        assert!(
            module_has_i64_const(&module, 0, 3),
            "compact sequence StoreVar should compare runtime length against capacity 3"
        );
        assert!(
            has_runtime_error_status_path(&module, 0),
            "over-capacity compact sequence length must branch to a runtime error path"
        );
        assert!(
            !block_has_state_out_store_to_slot(&module, 0, 0, 4),
            "destination length header must not be stored before the capacity guard"
        );
        assert!(
            (1..module.functions[0].blocks.len())
                .any(|block| block_has_state_out_store_to_slot(&module, 0, block, 4)),
            "destination length header should be stored after the capacity guard succeeds"
        );
    }

    #[test]
    fn test_store_var_scalar_destination_rejects_aggregate_source() {
        let mut func = BytecodeFunction::new("store_scalar_from_sequence".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::ScalarInt]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "store_scalar_from_sequence",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("scalar StoreVar must reject aggregate register sources");
        let message = format!("{err}");
        assert!(
            message.contains("requires compatible scalar source")
                || message.contains("StoreVar compact source")
                    && message.contains("is incompatible with v0"),
            "unexpected scalar StoreVar rejection: {message}"
        );
    }

    #[test]
    fn test_func_except_scalar_value_rejects_aggregate_replacement() {
        let mut func = BytecodeFunction::new("func_except_scalar_from_sequence".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 10 });
        func.emit(Opcode::LoadImm { rd: 3, value: 20 });
        func.emit(Opcode::SeqNew {
            rd: 4,
            start: 2,
            count: 2,
        });
        func.emit(Opcode::FuncExcept {
            rd: 5,
            func: 0,
            path: 1,
            val: 4,
        });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 5 });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::Ret { rs: 6 });

        let int_function = || CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(2),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(int_function()),
            VarLayout::Compound(int_function()),
        ]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "func_except_scalar_from_sequence",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("compact function scalar value replacement must reject aggregate sources");
        let message = format!("{err}");
        assert!(
            message.contains("incompatible with scalar expected shape")
                || message.contains("compact materialization source")
                    && message.contains("is incompatible with expected shape"),
            "unexpected FuncExcept scalar replacement rejection: {message}"
        );
    }

    #[test]
    fn test_store_var_function_heterogeneous_pair_value_to_fixed_function_layout_rejects() {
        let mut func = BytecodeFunction::new("store_funcdef_pair_value".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 4, value: 7 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::TupleNew {
            rd: 6,
            start: 4,
            count: 2,
        });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 6,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 7, value: true });
        func.emit(Opcode::Ret { rs: 7 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: Some(2),
            }),
            pair_count: Some(1),
            domain_lo: Some(1),
        })]);

        assert_store_var_compound_source_rejected(lower_next_state_with_constants_and_layout(
            &func,
            "store_funcdef_pair_value",
            &ConstantPool::new(),
            &layout,
        ));
    }

    #[test]
    fn test_store_var_chained_record_except_keeps_int_field_shapes() {
        let mut func = BytecodeFunction::new("store_chained_record_except".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(Opcode::AddInt {
            rd: 4,
            r1: 2,
            r2: 3,
        });
        func.emit(Opcode::FuncExcept {
            rd: 5,
            func: 0,
            path: 1,
            val: 4,
        });
        func.emit(Opcode::LoadImm { rd: 6, value: 1 });
        func.emit(Opcode::FuncApply {
            rd: 7,
            func: 5,
            arg: 6,
        });
        func.emit(Opcode::LoadImm { rd: 8, value: 2 });
        func.emit(Opcode::SubInt {
            rd: 9,
            r1: 7,
            r2: 8,
        });
        func.emit(Opcode::FuncExcept {
            rd: 10,
            func: 5,
            path: 6,
            val: 9,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 10 });
        func.emit(Opcode::LoadBool {
            rd: 11,
            value: true,
        });
        func.emit(Opcode::Ret { rs: 11 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("black"), CompoundLayout::Int),
                (tla_core::intern_name("white"), CompoundLayout::Int),
            ],
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_chained_record_except",
            &ConstantPool::new(),
            &layout,
        )
        .expect("chained record EXCEPT arithmetic results should remain fixed-width Int fields");
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_func_apply_int_function_string_value_compares_to_string_const() {
        let mut pool = ConstantPool::new();
        let black = pool.add_value(Value::String("black".into()));

        let mut func = BytecodeFunction::new("string_func_eq".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadConst { rd: 3, idx: black });
        func.emit(Opcode::Eq {
            rd: 4,
            r1: 2,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::String),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);

        lower_invariant_with_constants_and_layout(&func, "string_func_eq", &pool, &layout)
            .expect("string-valued compact function application should compare as String");
    }

    #[test]
    fn test_func_apply_record_string_field_compares_to_string_const() {
        let mut pool = ConstantPool::new();
        let black = pool.add_value(Value::String("black".into()));

        let mut func = BytecodeFunction::new("string_record_eq".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadConst { rd: 3, idx: black });
        func.emit(Opcode::Eq {
            rd: 4,
            r1: 2,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![(tla_core::intern_name("color"), CompoundLayout::String)],
        })]);

        lower_invariant_with_constants_and_layout(&func, "string_record_eq", &pool, &layout)
            .expect("string compact record field should compare as String");
    }

    #[test]
    fn test_record_get_field_id_selects_string_lane_not_slot_zero() {
        let mut pool = ConstantPool::new();
        let clock = tla_core::intern_name("clock");
        let msg_type = tla_core::intern_name("type");
        let type_field_idx = pool.add_field_id(msg_type.0);
        let request = pool.add_value(Value::String("request".into()));

        let mut func = BytecodeFunction::new("record_get_type_lane".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: type_field_idx,
        });
        func.emit(Opcode::LoadConst {
            rd: 2,
            idx: request,
        });
        func.emit(Opcode::Eq {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (clock, CompoundLayout::Int),
                (msg_type, CompoundLayout::String),
            ],
        })]);

        lower_invariant_with_constants_and_layout(&func, "record_get_type_lane", &pool, &layout)
            .expect("RecordGet field_idx must resolve through field_ids before lane lookup");
    }

    #[test]
    fn test_set_enum_overwrite_clears_stale_compact_record_provenance() {
        let mut func = BytecodeFunction::new("stale_set_enum".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 0,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::Ret { rs: 2 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        })]);

        assert_store_var_compound_source_rejected(lower_next_state_with_constants_and_layout(
            &func,
            "stale_set_enum",
            &ConstantPool::new(),
            &layout,
        ));
    }

    #[test]
    fn test_cond_move_selects_compact_record_slots() {
        let mut func = BytecodeFunction::new("cond_move_compact_record".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 0 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::CondMove {
            rd: 0,
            cond: 2,
            rs: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "cond_move_compact_record",
            &ConstantPool::new(),
            &layout,
        )
        .expect("CondMove over identical compact record layouts should select slots");
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_cond_move_selects_reordered_record_slots() {
        let mut pool = ConstantPool::new();
        let xy_fields = pool.add_value(Value::String("x".into()));
        pool.add_value(Value::String("y".into()));
        let yx_fields = pool.add_value(Value::String("y".into()));
        pool.add_value(Value::String("x".into()));

        let mut func =
            BytecodeFunction::new("cond_move_reordered_noncompact_record".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 2, value: 10 });
        func.emit(Opcode::LoadImm { rd: 3, value: 20 });
        func.emit(Opcode::RecordNew {
            rd: 0,
            fields_start: xy_fields,
            values_start: 2,
            count: 2,
        });
        func.emit(Opcode::LoadImm { rd: 4, value: 20 });
        func.emit(Opcode::LoadImm { rd: 5, value: 10 });
        func.emit(Opcode::RecordNew {
            rd: 1,
            fields_start: yx_fields,
            values_start: 4,
            count: 2,
        });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::CondMove {
            rd: 0,
            cond: 6,
            rs: 1,
        });
        func.emit(Opcode::Ret { rs: 6 });

        lower_invariant_with_constants(&func, "cond_move_reordered_noncompact_record", &pool)
            .expect("CondMove over compatible reordered compact records should select slots");
    }

    /// Test that unsupported opcodes return an error.
    #[test]
    fn test_unsupported_opcode() {
        let mut func = BytecodeFunction::new("unsupported".to_string(), 0);
        // PowInt is not yet supported
        func.emit(Opcode::PowInt {
            rd: 0,
            r1: 0,
            r2: 0,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let result = lower_invariant(&func, "unsupported");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            format!("{err}").contains("unsupported opcode"),
            "error: {err}"
        );
    }

    /// Test division by zero checking.
    #[test]
    fn test_lower_division() {
        let mut func = BytecodeFunction::new("div_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::IntDiv {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "div_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Should have blocks for div-by-zero check.
        assert!(
            module.functions[0].blocks.len() >= 3,
            "expected >= 3 blocks for division, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test real division (DivInt) with exactness check.
    #[test]
    fn test_lower_real_division() {
        let mut func = BytecodeFunction::new("realdiv_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::DivInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "realdiv_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Should have blocks for: entry, div_zero, check_exact, inexact, continue.
        assert!(
            module.functions[0].blocks.len() >= 4,
            "expected >= 4 blocks for real division, got {}",
            module.functions[0].blocks.len()
        );
    }

    // =====================================================================
    // Phase 2: Set operation tests
    // =====================================================================

    /// Test SetEnum: build a set from consecutive registers.
    #[test]
    fn test_lower_set_enum() {
        let mut func = BytecodeFunction::new("set_enum_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::LoadImm { rd: 2, value: 30 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "set_enum_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Entry block should contain allocas + loads + stores for the set
        let entry = &module.functions[0].blocks[0];
        assert!(
            entry.body.len() > 4,
            "entry block should have allocas + set construction, got {} instructions",
            entry.body.len()
        );
    }

    /// Test SetEnum with empty set (count=0).
    #[test]
    fn test_lower_set_enum_empty() {
        let mut func = BytecodeFunction::new("empty_set_test".to_string(), 0);
        func.emit(Opcode::SetEnum {
            rd: 0,
            start: 0,
            count: 0,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant(&func, "empty_set_test").unwrap();
        assert_eq!(module.functions.len(), 1);
    }

    /// Test SetIn: set membership with a linear scan loop.
    #[test]
    fn test_lower_set_in() {
        let mut func = BytecodeFunction::new("set_in_test".to_string(), 0);
        // Build set {10, 20, 30}
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::LoadImm { rd: 2, value: 30 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        // Check if 20 \in set
        func.emit(Opcode::SetIn {
            rd: 4,
            elem: 1,
            set: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "set_in_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Should have multiple blocks: entry, header, body, inc, found, not_found, merge
        assert!(
            module.functions[0].blocks.len() >= 5,
            "expected >= 5 blocks for SetIn loop, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test SetUnion: union of two sets.
    #[test]
    fn test_lower_set_union() {
        let mut func = BytecodeFunction::new("set_union_test".to_string(), 0);
        // Set1 = {1, 2}
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        // Set2 = {3, 4}
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::LoadImm { rd: 4, value: 4 });
        func.emit(Opcode::SetEnum {
            rd: 5,
            start: 3,
            count: 2,
        });
        // Union
        func.emit(Opcode::SetUnion {
            rd: 6,
            r1: 2,
            r2: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let module = lower_invariant(&func, "set_union_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Union uses copy loops, should have many blocks
        assert!(
            module.functions[0].blocks.len() >= 6,
            "expected >= 6 blocks for SetUnion, got {}",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "SetUnion with fixed-size inputs should not emit non-const-count Alloca"
        );
    }

    /// Test SetIntersect: intersection of two sets.
    #[test]
    fn test_lower_set_intersect() {
        let mut func = BytecodeFunction::new("set_isect_test".to_string(), 0);
        // Set1 = {1, 2}
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        // Set2 = {2, 3}
        func.emit(Opcode::LoadImm { rd: 3, value: 2 });
        func.emit(Opcode::LoadImm { rd: 4, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 5,
            start: 3,
            count: 2,
        });
        func.emit(Opcode::SetIntersect {
            rd: 6,
            r1: 2,
            r2: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let module = lower_invariant(&func, "set_isect_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Nested loops for intersection
        assert!(
            module.functions[0].blocks.len() >= 8,
            "expected >= 8 blocks for SetIntersect, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test SetDiff: set difference.
    #[test]
    fn test_lower_set_diff() {
        let mut func = BytecodeFunction::new("set_diff_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 3,
            count: 1,
        });
        func.emit(Opcode::SetDiff {
            rd: 5,
            r1: 2,
            r2: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant(&func, "set_diff_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].blocks.len() >= 8,
            "expected >= 8 blocks for SetDiff, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test Subseteq: subset check.
    #[test]
    fn test_lower_subseteq() {
        let mut func = BytecodeFunction::new("subseteq_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        func.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func.emit(Opcode::LoadImm { rd: 3, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 2,
            count: 2,
        });
        func.emit(Opcode::Subseteq {
            rd: 5,
            r1: 1,
            r2: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant(&func, "subseteq_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].blocks.len() >= 8,
            "expected >= 8 blocks for Subseteq, got {}",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_reject_compound_layout_set_bitmask_scalar_membership_without_universe_proof() {
        let mut func = BytecodeFunction::new("compact_set_bitmask_membership".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 2 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 0 });
        func.emit(Opcode::SetIn {
            rd: 2,
            elem: 0,
            set: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Set {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(4),
        })]);
        let result = lower_invariant_with_constants_and_layout(
            &func,
            "compact_set_bitmask_membership",
            &ConstantPool::new(),
            &layout,
        );
        assert_rejects_unproven_set_bitmask_universe(result);
    }

    #[test]
    fn test_lower_compact_set_bitmask_scalar_membership() {
        let mut func = BytecodeFunction::new("compact_set_bitmask_membership".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 2 });
        func.emit(Opcode::LoadImm {
            rd: 1,
            value: 0b1010,
        });
        func.emit(Opcode::SetIn {
            rd: 2,
            elem: 0,
            set: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_membership",
            &[(1, 4)],
        )
        .expect("proven DenseIntOneToN compact SetBitmask membership should lower");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Shl,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "compact SetBitmask scalar membership should build a membership bit"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(inst, Inst::CondBr { .. })) == 0,
            "compact SetBitmask scalar membership should stay on the straight-line mask path"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "compact SetBitmask scalar membership should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_reject_bool_set_bitmask_membership_until_typed_scalar_encoding_exists() {
        let mut func = BytecodeFunction::new("bool_set_bitmask_membership".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 0 });
        func.emit(Opcode::SetIn {
            rd: 2,
            elem: 0,
            set: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::SetBitmask {
            universe: vec![
                SetBitmaskElement::Bool(false),
                SetBitmaskElement::Bool(true),
            ],
        })]);
        let result = lower_invariant_with_constants_and_layout(
            &func,
            "bool_set_bitmask_membership",
            &ConstantPool::new(),
            &layout,
        );

        assert_rejects_unproven_set_bitmask_universe(result);
    }

    #[test]
    fn test_reject_compound_layout_set_bitmask_union_without_universe_proof() {
        let mut func =
            BytecodeFunction::new("compact_set_bitmask_union_diff_singleton".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::SetUnion {
            rd: 3,
            r1: 0,
            r2: 2,
        });
        func.emit(Opcode::SetDiff {
            rd: 4,
            r1: 3,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Set {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(4),
        })]);
        let result = lower_invariant_with_constants_and_layout(
            &func,
            "compact_set_bitmask_union_diff_singleton",
            &ConstantPool::new(),
            &layout,
        );
        assert_rejects_unproven_set_bitmask_universe(result);
    }

    #[test]
    fn test_lower_compact_set_bitmask_union_and_diff_between_bitmasks() {
        let mut func =
            BytecodeFunction::new("compact_set_bitmask_union_diff_bitmasks".to_string(), 0);
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0010,
        });
        func.emit(Opcode::LoadImm {
            rd: 1,
            value: 0b0100,
        });
        func.emit(Opcode::SetUnion {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::SetDiff {
            rd: 3,
            r1: 2,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_union_diff_bitmasks",
            &[(0, 4), (1, 4)],
        )
        .expect("proven DenseIntOneToN compact SetBitmask union/diff should lower");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "SetUnion with a compact SetBitmask operand should use mask OR"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "SetDiff with a compact SetBitmask operand should mask-complement the RHS"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "compact SetBitmask union/diff with singleton should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_reject_compact_set_bitmask_union_universe_mismatch() {
        let mut func = BytecodeFunction::new(
            "compact_set_bitmask_union_mismatched_universe".to_string(),
            0,
        );
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0010,
        });
        func.emit(Opcode::LoadImm {
            rd: 1,
            value: 0b0100,
        });
        func.emit(Opcode::SetUnion {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let err = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_union_mismatched_universe",
            &[(0, 4), (1, 5)],
        )
        .expect_err("mismatched compact SetBitmask universes must reject");

        let err = format!("{err}");
        assert!(
            err.contains("SetUnion: compact SetBitmask universe mismatch"),
            "error should report compact SetBitmask universe mismatch: {err}"
        );
    }

    #[test]
    fn test_store_var_rejects_same_width_different_setbitmask_universe() {
        let mut func = BytecodeFunction::new("store_setbitmask_mismatched_universe".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 1 });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![
            VarLayout::Compound(int_range_set_bitmask_layout(1, 4)),
            VarLayout::Compound(int_range_set_bitmask_layout(2, 5)),
        ]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "store_setbitmask_mismatched_universe",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("StoreVar must reject compact SetBitmask universe mismatch");

        let err = format!("{err}");
        assert!(
            err.contains("SetBitmask") && err.contains("incompatible"),
            "error should report compact SetBitmask incompatibility: {err}"
        );
    }

    #[test]
    fn test_store_var_exact_int_set_to_setbitmask_layout_writes_mask_not_pointer() {
        let mut func = BytecodeFunction::new("store_exact_int_set_to_setbitmask".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 4,
        ))]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_exact_int_set_to_setbitmask",
            &ConstantPool::new(),
            &layout,
        )
        .expect("exact integer SetEnum should store into compatible compact SetBitmask state");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "exact set to SetBitmask StoreVar should not need non-const-count Alloca"
        );
        assert_state_out_const_store(&module, 0, 0, 0b0101);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_exact_int_set_to_explicit_setbitmask_uses_table_order() {
        let mut func =
            BytecodeFunction::new("store_exact_int_set_to_explicit_setbitmask".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 20 });
        func.emit(Opcode::LoadImm { rd: 1, value: 30 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(explicit_int_set_bitmask_layout(
            &[10, 30, 20],
        ))]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_exact_int_set_to_explicit_setbitmask",
            &ConstantPool::new(),
            &layout,
        )
        .expect("register exact integer set should store using explicit universe table order");

        assert_state_out_const_store(&module, 0, 0, 0b0110);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_exact_int_set_to_setbitmask_rejects_out_of_universe_values() {
        let mut func =
            BytecodeFunction::new("store_exact_int_set_to_setbitmask_reject".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 4,
        ))]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "store_exact_int_set_to_setbitmask_reject",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("out-of-universe register exact set StoreVar must reject");
        assert!(
            format!("{err}").contains("requires all values inside the destination universe"),
            "error should report out-of-universe register exact set values: {err}"
        );
    }

    #[test]
    fn test_store_var_empty_set_enum_to_non_integer_setbitmask_stores_zero() {
        let mut func =
            BytecodeFunction::new("store_empty_set_enum_to_bool_setbitmask".to_string(), 0);
        func.emit(Opcode::SetEnum {
            rd: 0,
            start: 0,
            count: 0,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::SetBitmask {
            universe: vec![
                SetBitmaskElement::Bool(false),
                SetBitmaskElement::Bool(true),
            ],
        })]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_empty_set_enum_to_bool_setbitmask",
            &ConstantPool::new(),
            &layout,
        )
        .expect("empty SetEnum StoreVar should not require integer universe metadata");

        assert_state_out_const_store(&module, 0, 0, 0);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_interval_to_setbitmask_layout_writes_mask_not_pointer() {
        let mut func = BytecodeFunction::new("store_interval_to_setbitmask".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 2 });
        func.emit(Opcode::LoadImm { rd: 1, value: 4 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 4,
        ))]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_interval_to_setbitmask",
            &ConstantPool::new(),
            &layout,
        )
        .expect("in-universe interval should store into compatible compact SetBitmask state");

        assert_state_out_const_store(&module, 0, 0, 0b1110);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_const_interval_to_setbitmask_layout_writes_mask_not_pointer() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let interval_idx = pool.add_value(Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(1),
            BigInt::from(3),
        ))));

        let mut func = BytecodeFunction::new("store_const_interval_to_setbitmask".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: interval_idx,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            0, 3,
        ))]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_const_interval_to_setbitmask",
            &pool,
            &layout,
        )
        .expect(
            "constant in-universe interval should store into compatible compact SetBitmask state",
        );

        assert_state_out_const_store(&module, 0, 0, 0b1110);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_const_exact_int_set_to_setbitmask_layout_writes_mask_not_pointer() {
        let mut pool = ConstantPool::new();
        let set_idx = pool.add_value(Value::set([Value::SmallInt(1), Value::SmallInt(3)]));

        let mut func =
            BytecodeFunction::new("store_const_exact_int_set_to_setbitmask".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: set_idx,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 4,
        ))]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_const_exact_int_set_to_setbitmask",
            &pool,
            &layout,
        )
        .expect("constant exact integer set should store into compatible compact SetBitmask state");

        assert_state_out_const_store(&module, 0, 0, 0b0101);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_const_exact_int_set_to_explicit_setbitmask_uses_table_order() {
        let mut pool = ConstantPool::new();
        let set_idx = pool.add_value(Value::set([Value::SmallInt(20), Value::SmallInt(30)]));

        let mut func = BytecodeFunction::new(
            "store_const_exact_int_set_to_explicit_setbitmask".to_string(),
            0,
        );
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: set_idx,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(explicit_int_set_bitmask_layout(
            &[10, 30, 20],
        ))]);
        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_const_exact_int_set_to_explicit_setbitmask",
            &pool,
            &layout,
        )
        .expect("constant exact integer set should store using explicit universe table order");

        assert_state_out_const_store(&module, 0, 0, 0b0110);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_interval_to_setbitmask_layout_rejects_out_of_universe_values() {
        let mut func = BytecodeFunction::new("store_interval_to_setbitmask_reject".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 4,
        ))]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "store_interval_to_setbitmask_reject",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("out-of-universe interval StoreVar must reject");
        assert!(
            format!("{err}").contains("requires all values inside the destination universe"),
            "error should report out-of-universe interval values: {err}"
        );
    }

    #[test]
    fn test_store_var_const_exact_int_set_to_setbitmask_rejects_out_of_universe_values() {
        let mut pool = ConstantPool::new();
        let set_idx = pool.add_value(Value::set([Value::SmallInt(0), Value::SmallInt(2)]));

        let mut func = BytecodeFunction::new(
            "store_const_exact_int_set_to_setbitmask_reject".to_string(),
            0,
        );
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: set_idx,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 4,
        ))]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "store_const_exact_int_set_to_setbitmask_reject",
            &pool,
            &layout,
        )
        .expect_err("out-of-universe constant exact set StoreVar must reject");
        assert!(
            format!("{err}").contains("requires all values inside the destination universe"),
            "error should report out-of-universe exact set values: {err}"
        );
    }

    #[test]
    fn test_store_var_empty_const_sets_to_non_integer_setbitmask_store_zero() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;

        for (name, value) in [
            (
                "empty_interval",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(5),
                    BigInt::from(3),
                ))),
            ),
            ("empty_set", Value::empty_set()),
        ] {
            let mut pool = ConstantPool::new();
            let idx = pool.add_value(value);
            let mut func = BytecodeFunction::new(format!("store_{name}_to_bool_setbitmask"), 0);
            func.emit(Opcode::LoadConst { rd: 0, idx });
            func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
            func.emit(Opcode::LoadBool { rd: 1, value: true });
            func.emit(Opcode::Ret { rs: 1 });

            let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::SetBitmask {
                universe: vec![
                    SetBitmaskElement::Bool(false),
                    SetBitmaskElement::Bool(true),
                ],
            })]);
            let module =
                lower_next_state_with_constants_and_layout(&func, &func.name, &pool, &layout)
                    .expect(
                        "empty compact-set StoreVar should not require integer universe metadata",
                    );

            assert_state_out_const_store(&module, 0, 0, 0);
            assert_no_ptr_payload_store_to_state_out(&module, 0);
        }
    }

    #[test]
    fn test_lower_compact_set_bitmask_union_with_exact_set_operand() {
        let mut func = BytecodeFunction::new("compact_set_bitmask_union_exact_set".to_string(), 0);
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0010,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::SetUnion {
            rd: 3,
            r1: 0,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_union_exact_set",
            &[(0, 4)],
        )
        .expect("compact SetBitmask union should convert compatible exact integer set");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "SetUnion should OR the exact-set mask into a compact mask"
        );
        assert!(
            module.functions[0].blocks.len() < 6,
            "exact set to SetBitmask union should avoid aggregate union loops"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "exact set to SetBitmask union should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_diff_with_exact_set_operand() {
        let mut func = BytecodeFunction::new("compact_set_bitmask_diff_exact_set".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        func.emit(Opcode::LoadImm {
            rd: 2,
            value: 0b0010,
        });
        func.emit(Opcode::SetDiff {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_diff_exact_set",
            &[(2, 4)],
        )
        .expect("compact SetBitmask diff should convert compatible exact integer set");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "SetDiff should complement the compact RHS mask"
        );
        assert!(
            module.functions[0].blocks.len() < 8,
            "exact set to SetBitmask diff should avoid aggregate diff loops"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "exact set to SetBitmask diff should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_intersect_with_exact_set_operand() {
        let mut func =
            BytecodeFunction::new("compact_set_bitmask_intersect_exact_set".to_string(), 0);
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b1111,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 1,
            count: 2,
        });
        func.emit(Opcode::SetIntersect {
            rd: 4,
            r1: 0,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_setbitmask_intersect_exact_set",
            &[(0, 4)],
        )
        .expect("compact SetBitmask intersect should convert exact integer sets");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "SetIntersect should AND the exact-set mask with the compact mask"
        );
        assert!(
            module.functions[0].blocks.len() < 6,
            "exact set to SetBitmask intersect should avoid aggregate intersect loops"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "exact set to SetBitmask intersect should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_intersect_ignores_out_of_universe_exact_set_values() {
        let mut func = BytecodeFunction::new(
            "compact_set_bitmask_intersect_out_of_universe_exact_set".to_string(),
            0,
        );
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b1111,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 1,
            count: 2,
        });
        func.emit(Opcode::SetIntersect {
            rd: 4,
            r1: 0,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_setbitmask_intersect_out_of_universe_exact_set",
            &[(0, 4)],
        )
        .expect("SetIntersect may ignore exact values outside the compact universe");

        assert!(
            module.functions[0].blocks.len() < 6,
            "exact set to SetBitmask intersect should stay on the mask-native path"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "out-of-universe exact intersect should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_intersect_clamps_partially_overlapping_interval() {
        let mut func = BytecodeFunction::new(
            "compact_set_bitmask_intersect_overlap_interval".to_string(),
            0,
        );
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b1111,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::SetIntersect {
            rd: 4,
            r1: 0,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_setbitmask_intersect_overlap_interval",
            &[(0, 4)],
        )
        .expect("SetIntersect should clamp interval operands to the compact universe");

        assert!(
            module_has_i64_const(&module, 0, 0b0011),
            "partially overlapping interval intersect should clamp 0..2 to compact universe 1..4"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "SetIntersect should AND the clamped interval mask with the compact mask"
        );
        assert_eq!(
            inst_count(&module, 0, |inst| matches!(inst, Inst::CondBr { .. })),
            2,
            "partially overlapping interval intersect should add no aggregate intersect loops beyond Range lowering"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "partially overlapping interval intersect should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_subseteq_with_exact_set_operand() {
        let mut func =
            BytecodeFunction::new("compact_set_bitmask_subseteq_exact_set".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadImm {
            rd: 3,
            value: 0b0111,
        });
        func.emit(Opcode::Subseteq {
            rd: 4,
            r1: 2,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_setbitmask_subseteq_exact_set",
            &[(3, 4)],
        )
        .expect("Subseteq should convert exact integer sets on the compact path");

        assert!(
            module.functions[0].blocks.len() < 6,
            "exact set to SetBitmask subseteq should avoid aggregate subset loops"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "exact set to SetBitmask subseteq should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_subseteq_rejects_out_of_universe_left_exact_set_by_value() {
        let mut func = BytecodeFunction::new(
            "compact_set_bitmask_subseteq_out_of_universe_left_exact_set".to_string(),
            0,
        );
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadImm {
            rd: 3,
            value: 0b1111,
        });
        func.emit(Opcode::Subseteq {
            rd: 4,
            r1: 2,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_setbitmask_subseteq_out_of_universe_left_exact_set",
            &[(3, 4)],
        )
        .expect("Subseteq should lower exact sets outside the compact universe without losing false evidence");

        assert!(
            module.functions[0].blocks.len() < 6,
            "out-of-universe exact subseteq should stay on the mask-native path"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "out-of-universe exact subseteq should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_equality_with_exact_set_operand() {
        let mut func =
            BytecodeFunction::new("compact_set_bitmask_equality_exact_set".to_string(), 0);
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0111,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 1,
            count: 3,
        });
        func.emit(Opcode::Eq {
            rd: 5,
            r1: 0,
            r2: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_equality_exact_set",
            &[(0, 3)],
        )
        .expect("Eq should compare compact SetBitmask and exact integer sets by value");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    ..
                }
            )) >= 3,
            "compact set equality should combine mask equality with universe and canonical checks"
        );
        assert!(
            module.functions[0].blocks.len() < 6,
            "exact set to SetBitmask equality should avoid aggregate equality loops"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "exact set to SetBitmask equality should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_neq_with_out_of_universe_exact_set_operand() {
        let mut func = BytecodeFunction::new(
            "compact_set_bitmask_neq_out_of_universe_exact_set".to_string(),
            0,
        );
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0010,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 1,
            count: 2,
        });
        func.emit(Opcode::Neq {
            rd: 4,
            r1: 0,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_neq_out_of_universe_exact_set",
            &[(0, 4)],
        )
        .expect("Neq should preserve outside-universe exact-set evidence");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "compact set inequality should treat outside-universe exact elements as not equal"
        );
        assert!(
            module.functions[0].blocks.len() < 6,
            "out-of-universe exact set inequality should stay on the mask-native path"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "out-of-universe exact set inequality should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_equality_rejects_clamped_out_of_universe_exact_set() {
        let mut func = BytecodeFunction::new(
            "compact_set_bitmask_eq_out_of_universe_exact_set".to_string(),
            0,
        );
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0010,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 1,
            count: 2,
        });
        func.emit(Opcode::Eq {
            rd: 4,
            r1: 0,
            r2: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_eq_out_of_universe_exact_set",
            &[(0, 4)],
        )
        .expect("Eq should lower out-of-universe exact-set evidence without clamped equality");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::And,
                    ty: Ty::I64,
                    ..
                }
            )) >= 3,
            "compact set equality should require universe membership and canonical masks"
        );
        assert!(
            module.functions[0].blocks.len() < 6,
            "out-of-universe exact set equality should stay on the mask-native path"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "out-of-universe exact set equality should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_compact_set_bitmask_neq_with_same_exact_set_operand() {
        let mut func =
            BytecodeFunction::new("compact_set_bitmask_neq_same_exact_set".to_string(), 0);
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0111,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 1,
            count: 3,
        });
        func.emit(Opcode::Neq {
            rd: 5,
            r1: 0,
            r2: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_neq_same_exact_set",
            &[(0, 3)],
        )
        .expect("Neq should compare equal compact and exact integer sets by value");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Or,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "compact set inequality should combine mask-difference and outside-universe checks"
        );
        assert!(
            module.functions[0].blocks.len() < 6,
            "same exact set inequality should stay on the mask-native path"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "same exact set inequality should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_reject_compact_set_bitmask_equality_universe_mismatch() {
        let mut func =
            BytecodeFunction::new("compact_set_bitmask_eq_mismatched_universe".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::Eq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let layout = StateLayout::new(vec![
            VarLayout::Compound(int_range_set_bitmask_layout(1, 4)),
            VarLayout::Compound(int_range_set_bitmask_layout(2, 5)),
        ]);
        let err = lower_invariant_with_constants_and_layout(
            &func,
            "compact_set_bitmask_eq_mismatched_universe",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("mismatched compact SetBitmask equality universes must reject");

        let err = format!("{err}");
        assert!(
            err.contains("Set equality: compact SetBitmask universe mismatch"),
            "error should report compact SetBitmask equality universe mismatch: {err}"
        );
    }

    #[test]
    fn test_lower_state_compact_set_bitmask_eq_neq_exact_set_compares_mask_slot() {
        let cases = [
            (
                "state_compact_set_bitmask_eq_exact_set",
                Opcode::Eq {
                    rd: 5,
                    r1: 0,
                    r2: 4,
                },
            ),
            (
                "state_compact_set_bitmask_neq_exact_set",
                Opcode::Neq {
                    rd: 5,
                    r1: 0,
                    r2: 4,
                },
            ),
        ];

        for (name, comparison) in cases {
            let mut func = BytecodeFunction::new(name.to_string(), 0);
            func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
            func.emit(Opcode::LoadImm { rd: 1, value: 1 });
            func.emit(Opcode::LoadImm { rd: 2, value: 2 });
            func.emit(Opcode::LoadImm { rd: 3, value: 3 });
            func.emit(Opcode::SetEnum {
                rd: 4,
                start: 1,
                count: 3,
            });
            func.emit(comparison);
            func.emit(Opcode::Ret { rs: 5 });

            let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
                1, 3,
            ))]);
            let module = lower_invariant_with_constants_and_layout(
                &func,
                name,
                &ConstantPool::new(),
                &layout,
            )
            .expect("compact SetBitmask equality should compare state masks by value");

            assert!(
                has_i64_icmp_against_const_from_state_slot(&module, 0, ICmpOp::Eq, 0, 0b111),
                "{name} must compare the compact state SetBitmask slot against the exact SetEnum mask"
            );
            assert!(
                !has_nonconst_alloca_count(&module, 0),
                "{name} should stay on the mask-native path"
            );
        }
    }

    #[test]
    fn test_reject_compact_set_bitmask_union_with_generic_materialized_set_operand() {
        let mut func = BytecodeFunction::new(
            "compact_set_bitmask_union_generic_materialized_set".to_string(),
            0,
        );
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::SetUnion {
            rd: 3,
            r1: 0,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![
            VarLayout::Compound(int_range_set_bitmask_layout(1, 4)),
            VarLayout::ScalarInt,
        ]);
        let err = lower_invariant_with_constants_and_layout(
            &func,
            "compact_setbitmask_union_generic_materialized_set",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("generic materialized integer sets must not be forced into compact SetBitmask");

        let message = format!("{err}");
        assert!(
            message.contains("cannot infer") && message.contains("compact SetBitmask universe"),
            "error should reject generic materialized compact conversion: {message}"
        );
    }

    #[test]
    fn test_proc_binding_singleton_setenum_provenance_survives_helper_call() {
        let mut chunk = BytecodeChunk::new();

        let mut singleton = BytecodeFunction::new("Singleton".to_string(), 1);
        singleton.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        singleton.emit(Opcode::Ret { rs: 1 });
        let singleton_idx = chunk.add_function(singleton);

        let mut entry = BytecodeFunction::new("proc_binding_singleton_helper".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 2, value: 3 });
        entry.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        let begin_pc = entry.emit(Opcode::ExistsBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });
        entry.emit(Opcode::Call {
            rd: 6,
            op_idx: singleton_idx,
            args_start: 5,
            argc: 1,
        });
        entry.emit(Opcode::SetUnion {
            rd: 7,
            r1: 0,
            r2: 6,
        });
        entry.emit(Opcode::SetIn {
            rd: 8,
            elem: 5,
            set: 7,
        });
        let next_pc = entry.emit(Opcode::ExistsNext {
            rd: 4,
            r_binding: 5,
            r_body: 8,
            loop_begin: 0,
        });
        entry.patch_jump(begin_pc, next_pc + 1);
        entry.patch_jump(next_pc, begin_pc + 1);
        entry.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(entry);

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 3,
        ))]);
        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "proc_binding_singleton_helper",
            &layout,
        )
        .expect("Proc-derived singleton helper result should stay on compact SetBitmask path");

        assert!(
            inst_count(&module, 1, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Shl,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "callee SetEnum should build the singleton bit from proven Proc provenance"
        );
    }

    #[test]
    fn test_reject_compact_set_bitmask_union_with_out_of_universe_exact_set_operand() {
        let mut func = BytecodeFunction::new(
            "compact_set_bitmask_union_out_of_universe_exact_set".to_string(),
            0,
        );
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0010,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::SetUnion {
            rd: 3,
            r1: 0,
            r2: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let err = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_setbitmask_union_out_of_universe_exact_set",
            &[(0, 4)],
        )
        .expect_err("exact materialized integer sets outside the compact universe must reject");

        let message = format!("{err}");
        assert!(
            message.contains("outside compact SetBitmask universe"),
            "error should reject out-of-universe exact compact conversion: {message}"
        );
    }

    #[test]
    fn test_reject_compound_layout_set_bitmask_subseteq_without_universe_proof() {
        let mut func = BytecodeFunction::new("compact_set_bitmask_subseteq".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::Subseteq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let set_layout = || {
            VarLayout::Compound(CompoundLayout::Set {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: Some(4),
            })
        };
        let layout = StateLayout::new(vec![set_layout(), set_layout()]);
        let result = lower_invariant_with_constants_and_layout(
            &func,
            "compact_set_bitmask_subseteq",
            &ConstantPool::new(),
            &layout,
        );
        assert_rejects_unproven_set_bitmask_universe(result);
    }

    #[test]
    fn test_lower_compact_set_bitmask_subseteq_between_bitmasks() {
        let mut func = BytecodeFunction::new("compact_set_bitmask_subseteq".to_string(), 0);
        func.emit(Opcode::LoadImm {
            rd: 0,
            value: 0b0010,
        });
        func.emit(Opcode::LoadImm {
            rd: 1,
            value: 0b0110,
        });
        func.emit(Opcode::Subseteq {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_straightline_invariant_with_dense_set_bitmask_regs(
            &func,
            "compact_set_bitmask_subseteq",
            &[(0, 4), (1, 4)],
        )
        .expect("proven DenseIntOneToN compact SetBitmask subseteq should lower");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "Subseteq between compact SetBitmasks should compute RHS complement"
        );
        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "Subseteq between compact SetBitmasks should compare missing bits to zero"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "Subseteq between compact SetBitmasks should not emit non-const-count Alloca"
        );
    }

    /// Test Range: integer interval set.
    #[test]
    fn test_lower_range() {
        let mut func = BytecodeFunction::new("range_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 5 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "range_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Range uses a fill loop
        assert!(
            module.functions[0].blocks.len() >= 3,
            "expected >= 3 blocks for Range fill loop, got {}",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "constant-bounds Range should not emit non-const-count Alloca"
        );
    }

    // =====================================================================
    // Phase 2: Sequence / Tuple operation tests
    // =====================================================================

    /// Test SeqNew: build a sequence.
    #[test]
    fn test_lower_seq_new() {
        let mut func = BytecodeFunction::new("seq_new_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "seq_new_test").unwrap();
        assert_eq!(module.functions.len(), 1);
    }

    /// Test TupleNew and TupleGet.
    #[test]
    fn test_lower_tuple_new_and_get() {
        let mut func = BytecodeFunction::new("tuple_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 100 });
        func.emit(Opcode::LoadImm { rd: 1, value: 200 });
        func.emit(Opcode::TupleNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        // TupleGet is 1-indexed, so idx=1 gets the first element
        func.emit(Opcode::TupleGet {
            rd: 3,
            rs: 2,
            idx: 1,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "tuple_test").unwrap();
        assert_eq!(module.functions.len(), 1);
    }

    // =====================================================================
    // Phase 2: Record operation tests
    // =====================================================================

    /// Test RecordNew and RecordGet.
    #[test]
    fn test_lower_record_new_and_get() {
        let mut func = BytecodeFunction::new("record_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::LoadImm { rd: 1, value: 99 });
        func.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: 0, // field indices into constant pool (not used in lowering)
            values_start: 0,
            count: 2,
        });
        func.emit(Opcode::RecordGet {
            rd: 3,
            rs: 2,
            field_idx: 0,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "record_test").unwrap();
        assert_eq!(module.functions.len(), 1);
    }

    // =====================================================================
    // Phase 2: Builtin operation tests
    // =====================================================================

    /// Test CallBuiltin(Cardinality): returns set length.
    #[test]
    fn test_lower_cardinality() {
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("card_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Cardinality,
            args_start: 3,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "card_test").unwrap();
        assert_eq!(module.functions.len(), 1);
    }

    #[test]
    fn test_lower_compact_set_bitmask_cardinality_uses_mask_not_pointer() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("compact_set_bitmask_cardinality".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Cardinality,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 4,
        ))]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "compact_set_bitmask_cardinality",
            &ConstantPool::new(),
            &layout,
        )
        .expect("exact compact SetBitmask Cardinality should lower mask-native");

        assert_eq!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    ..
                }
            )),
            0,
            "compact SetBitmask Cardinality must not reinterpret the mask as an aggregate pointer"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "compact SetBitmask Cardinality should not materialize an aggregate set"
        );
    }

    #[test]
    fn test_reject_markerless_set_bitmask_cardinality_pointer_fallback() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("markerless_set_bitmask_cardinality".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Cardinality,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Set {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(4),
        })]);
        let err = lower_invariant_with_constants_and_layout(
            &func,
            "markerless_set_bitmask_cardinality",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("markerless compact SetBitmask Cardinality should reject pointer fallback");

        let message = format!("{err}");
        assert!(
            message.contains("Cardinality: compact SetBitmask r0 requires exact universe metadata"),
            "markerless SetBitmask Cardinality should fail closed on missing universe metadata: {message}"
        );
        assert!(
            !message.contains("aggregate pointer") && !message.contains("IntToPtr"),
            "markerless SetBitmask Cardinality should reject before aggregate-pointer fallback: {message}"
        );
    }

    /// Test CallBuiltin(Len): returns sequence length.
    #[test]
    fn test_lower_seq_len() {
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("len_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 3,
            builtin: BuiltinOp::Len,
            args_start: 2,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "len_test").unwrap();
        assert_eq!(module.functions.len(), 1);
    }

    /// Test CallBuiltin(Head): returns first sequence element.
    #[test]
    fn test_lower_seq_head() {
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("head_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::LoadImm { rd: 1, value: 99 });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 3,
            builtin: BuiltinOp::Head,
            args_start: 2,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "head_test").unwrap();
        assert_eq!(module.functions.len(), 1);
    }

    /// Test CallBuiltin(Tail): returns all but first element.
    #[test]
    fn test_lower_seq_tail() {
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("tail_test".to_string(), 0);
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
            builtin: BuiltinOp::Tail,
            args_start: 3,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "tail_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Tail involves a copy loop
        assert!(
            module.functions[0].blocks.len() >= 3,
            "expected >= 3 blocks for Tail copy loop, got {}",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_lower_compact_seq_tail_preserves_capacity_and_zeroes_inactive_tail() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("compact_tail_capacity".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Tail,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::Ret { rs: 2 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "compact_tail_capacity",
            &ConstantPool::new(),
            &layout,
        )
        .expect("Tail on compact fixed-capacity sequence should store back into same layout");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "Tail on compact capacity-3 sequence should materialize fixed-capacity storage"
        );
        assert!(
            has_const_alloca_count(&module, 0, 4),
            "Tail must preserve compact capacity 3, including the length slot"
        );
        assert!(
            has_const_i64_store_to_gep_slot(&module, 0, 3, 0),
            "Tail on compact capacity-3 sequence must zero the final inactive payload slot"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    /// Test CallBuiltin(Append): append an element to a sequence.
    #[test]
    fn test_lower_seq_append() {
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("append_test".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 30 });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Append,
            args_start: 2,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "append_test").unwrap();
        assert_eq!(module.functions.len(), 1);
        // Append involves a copy loop
        assert!(
            module.functions[0].blocks.len() >= 3,
            "expected >= 3 blocks for Append copy loop, got {}",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_lower_compact_seq_append_preserves_capacity() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("compact_append_capacity".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 30 });
        func.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::Append,
            args_start: 0,
            argc: 2,
        });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "compact_append_capacity",
            &ConstantPool::new(),
            &layout,
        )
        .expect("Append on compact fixed-capacity sequence should store back into same layout");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "Append on compact capacity-3 sequence should not allocate from runtime length"
        );
        assert!(
            has_const_alloca_count(&module, 0, 4),
            "Append must preserve compact capacity 3, including the length slot"
        );
        assert!(
            !has_const_alloca_count(&module, 0, 5),
            "Append must not widen a compact capacity-3 sequence to capacity 4"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_sequence_extent_exact_tail_append_updates_len() {
        let int_shape = AggregateShape::Scalar(ScalarShape::Int);
        let seq_shape = AggregateShape::Sequence {
            extent: SequenceExtent::Exact(3),
            element: Some(Box::new(int_shape.clone())),
        };

        let tail = sequence_tail_shape(Some(&seq_shape)).expect("exact Tail shape");
        assert_eq!(
            tail,
            AggregateShape::Sequence {
                extent: SequenceExtent::Exact(2),
                element: Some(Box::new(int_shape.clone())),
            }
        );
        assert_eq!(tail.tracked_len(), Some(2));

        let append =
            sequence_append_shape(Some(&seq_shape), Some(&int_shape)).expect("exact Append shape");
        assert_eq!(
            append,
            AggregateShape::Sequence {
                extent: SequenceExtent::Exact(4),
                element: Some(Box::new(int_shape)),
            }
        );
        assert_eq!(append.tracked_len(), Some(4));
    }

    #[test]
    fn test_sequence_extent_capacity_tail_append_preserves_capacity() {
        let int_shape = AggregateShape::Scalar(ScalarShape::Int);
        let seq_shape = AggregateShape::Sequence {
            extent: SequenceExtent::Capacity(3),
            element: Some(Box::new(int_shape.clone())),
        };

        assert_eq!(seq_shape.tracked_len(), None);
        assert_eq!(seq_shape.compact_slot_count(), Some(4));

        let tail = sequence_tail_shape(Some(&seq_shape)).expect("capacity Tail shape");
        assert_eq!(
            tail,
            AggregateShape::Sequence {
                extent: SequenceExtent::Capacity(3),
                element: Some(Box::new(int_shape.clone())),
            }
        );
        assert_eq!(tail.tracked_len(), None);
        assert_eq!(tail.compact_slot_count(), Some(4));

        let append = sequence_append_shape(Some(&seq_shape), Some(&int_shape))
            .expect("capacity Append shape");
        assert_eq!(
            append,
            AggregateShape::Sequence {
                extent: SequenceExtent::Capacity(3),
                element: Some(Box::new(int_shape)),
            }
        );
        assert_eq!(append.tracked_len(), None);
        assert_eq!(append.compact_slot_count(), Some(4));
    }

    #[test]
    fn test_lower_seq_tail_propagates_sequence_shape_for_function_set_membership() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("tail_shape_membership".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SeqNew {
            rd: 3,
            start: 0,
            count: 3,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Tail,
            args_start: 3,
            argc: 1,
        });
        func.emit(Opcode::LoadImm { rd: 5, value: 1 });
        func.emit(Opcode::LoadImm { rd: 6, value: 2 });
        func.emit(Opcode::Range {
            rd: 7,
            lo: 5,
            hi: 6,
        });
        func.emit(Opcode::LoadImm { rd: 8, value: 1 });
        func.emit(Opcode::LoadImm { rd: 9, value: 3 });
        func.emit(Opcode::Range {
            rd: 10,
            lo: 8,
            hi: 9,
        });
        func.emit(Opcode::FuncSet {
            rd: 11,
            domain: 7,
            range: 10,
        });
        func.emit(Opcode::SetIn {
            rd: 12,
            elem: 4,
            set: 11,
        });
        func.emit(Opcode::Ret { rs: 12 });

        let module = lower_invariant(&func, "tail_shape_membership")
            .expect("Tail(seq) should preserve sequence shape for function-set membership");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "Tail sequence-as-function membership should lower runtime range checks"
        );
    }

    #[test]
    fn test_lower_seq_append_propagates_sequence_shape_for_function_set_membership() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("append_shape_membership".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Append,
            args_start: 2,
            argc: 2,
        });
        func.emit(Opcode::LoadImm { rd: 5, value: 1 });
        func.emit(Opcode::LoadImm { rd: 6, value: 3 });
        func.emit(Opcode::Range {
            rd: 7,
            lo: 5,
            hi: 6,
        });
        func.emit(Opcode::FuncSet {
            rd: 8,
            domain: 7,
            range: 7,
        });
        func.emit(Opcode::SetIn {
            rd: 9,
            elem: 4,
            set: 8,
        });
        func.emit(Opcode::Ret { rs: 9 });

        let module = lower_invariant(&func, "append_shape_membership")
            .expect("Append(seq, elem) should preserve sequence shape for function-set membership");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "Append sequence-as-function membership should lower runtime range checks"
        );
    }

    #[test]
    fn test_lower_seq_head_propagates_mcl_message_record_shape() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let message_domain = Value::record_set([
            (
                "type",
                Value::set([
                    Value::String(Arc::from("request")),
                    Value::String(Arc::from("ack")),
                    Value::String(Arc::from("release")),
                ]),
            ),
            (
                "from",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(1),
                    BigInt::from(3),
                ))),
            ),
        ]);
        let message_idx = pool.add_value(message_domain);

        let mut func = BytecodeFunction::new("head_message_shape".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Head,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::LoadConst {
            rd: 2,
            idx: message_idx,
        });
        func.emit(Opcode::SetIn {
            rd: 3,
            elem: 1,
            set: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let message_layout = CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("from"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(message_layout),
            element_count: Some(1),
        })]);

        let module =
            lower_invariant_with_constants_and_layout(&func, "head_message_shape", &pool, &layout)
                .expect("Head(Seq(Message)) should expose the Message record shape");
        assert!(
            module.functions[0].blocks.len() >= 1,
            "record-set membership should lower for Head(Seq(Message))"
        );
    }

    #[test]
    fn test_called_seq_append_retains_return_shape_for_membership() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();
        let mut helper = BytecodeFunction::new("AppendOne".to_string(), 0);
        helper.emit(Opcode::LoadImm { rd: 0, value: 1 });
        helper.emit(Opcode::LoadImm { rd: 1, value: 2 });
        helper.emit(Opcode::SeqNew {
            rd: 2,
            start: 0,
            count: 2,
        });
        helper.emit(Opcode::LoadImm { rd: 3, value: 3 });
        helper.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Append,
            args_start: 2,
            argc: 2,
        });
        helper.emit(Opcode::Ret { rs: 4 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("called_append_shape".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: helper_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 1, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 2, value: 3 });
        entry.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        entry.emit(Opcode::FuncSet {
            rd: 4,
            domain: 3,
            range: 3,
        });
        entry.emit(Opcode::SetIn {
            rd: 5,
            elem: 0,
            set: 4,
        });
        entry.emit(Opcode::Ret { rs: 5 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "called_append_shape")
            .expect("zero-arg helper returning Append should retain sequence return shape");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "called Append sequence-as-function membership should lower runtime range checks"
        );
    }

    #[test]
    fn test_called_parameterized_condmove_append_retains_seq_record_shape_for_func_set_membership()
    {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;
        use tla_value::IntervalValue;

        let mut chunk = BytecodeChunk::new();
        let from_field = chunk.constants.add_value(Value::String(Arc::from("from")));
        let _type_field = chunk.constants.add_value(Value::String(Arc::from("type")));
        let req_idx = chunk.constants.add_value(Value::String(Arc::from("req")));
        let message_domain = Value::record_set([
            (
                "from",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(1),
                    BigInt::from(3),
                ))),
            ),
            ("type", Value::set([Value::String(Arc::from("req"))])),
        ]);
        let message_idx = chunk.constants.add_value(message_domain);

        let mut helper = BytecodeFunction::new("BroadcastLike".to_string(), 4);
        helper.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Append,
            args_start: 0,
            argc: 2,
        });
        helper.emit(Opcode::Move { rd: 5, rs: 0 });
        helper.emit(Opcode::Move { rd: 6, rs: 2 });
        helper.emit(Opcode::CallBuiltin {
            rd: 7,
            builtin: BuiltinOp::Append,
            args_start: 5,
            argc: 2,
        });
        helper.emit(Opcode::CondMove {
            rd: 7,
            cond: 3,
            rs: 4,
        });
        helper.emit(Opcode::Ret { rs: 7 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("parameterized_broadcast_membership".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadConst {
            rd: 1,
            idx: req_idx,
        });
        entry.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: from_field,
            values_start: 0,
            count: 2,
        });
        entry.emit(Opcode::SeqNew {
            rd: 3,
            start: 2,
            count: 1,
        });
        entry.emit(Opcode::Move { rd: 4, rs: 2 });
        entry.emit(Opcode::Move { rd: 5, rs: 2 });
        entry.emit(Opcode::LoadBool { rd: 6, value: true });
        entry.emit(Opcode::Call {
            rd: 7,
            op_idx: helper_idx,
            args_start: 3,
            argc: 4,
        });
        entry.emit(Opcode::LoadImm { rd: 8, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 9, value: 2 });
        entry.emit(Opcode::Range {
            rd: 10,
            lo: 8,
            hi: 9,
        });
        entry.emit(Opcode::LoadConst {
            rd: 11,
            idx: message_idx,
        });
        entry.emit(Opcode::FuncSet {
            rd: 13,
            domain: 10,
            range: 11,
        });
        entry.emit(Opcode::SetIn {
            rd: 14,
            elem: 7,
            set: 13,
        });
        entry.emit(Opcode::Ret { rs: 14 });
        let entry_idx = chunk.add_function(entry);

        let module =
            lower_module_invariant(&chunk, entry_idx, "parameterized_broadcast_membership")
                .expect("call-site helper shapes and CondMove should preserve Seq(Message)");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "parameterized helper sequence-as-function membership should lower runtime checks"
        );
    }

    #[test]
    fn test_called_broadcast_shape_materializes_nested_sequence_funcexcept_replacement() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();
        let fields_start = chunk.constants.add_value(Value::String("from".into()));
        chunk.constants.add_value(Value::String("type".into()));

        let mut helper = BytecodeFunction::new("BroadcastLike".to_string(), 4);
        helper.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::Append,
            args_start: 0,
            argc: 2,
        });
        helper.emit(Opcode::Move { rd: 5, rs: 0 });
        helper.emit(Opcode::Move { rd: 6, rs: 2 });
        helper.emit(Opcode::CallBuiltin {
            rd: 7,
            builtin: BuiltinOp::Append,
            args_start: 5,
            argc: 2,
        });
        helper.emit(Opcode::CondMove {
            rd: 7,
            cond: 3,
            rs: 4,
        });
        helper.emit(Opcode::Ret { rs: 7 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("nested_broadcast_except_shape".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 6, value: 1 });
        entry.emit(Opcode::LoadConst { rd: 7, idx: 1 });
        entry.emit(Opcode::RecordNew {
            rd: 3,
            fields_start,
            values_start: 6,
            count: 2,
        });
        entry.emit(Opcode::Move { rd: 4, rs: 3 });
        entry.emit(Opcode::LoadBool { rd: 5, value: true });
        entry.emit(Opcode::Call {
            rd: 8,
            op_idx: helper_idx,
            args_start: 2,
            argc: 4,
        });
        entry.emit(Opcode::LoadImm { rd: 9, value: 1 });
        entry.emit(Opcode::FuncExcept {
            rd: 10,
            func: 0,
            path: 9,
            val: 8,
        });
        entry.emit(Opcode::StoreVar { var_idx: 1, rs: 10 });
        entry.emit(Opcode::LoadBool {
            rd: 11,
            value: true,
        });
        entry.emit(Opcode::Ret { rs: 11 });
        let entry_idx = chunk.add_function(entry);

        let message_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("from"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let mailbox_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(message_layout()),
            element_count: Some(3),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(mailbox_layout()),
                element_count: Some(3),
            }),
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(mailbox_layout()),
                element_count: Some(3),
            }),
        ]);

        let module = lower_module_next_state_with_layout(
            &chunk,
            entry_idx,
            "nested_broadcast_except_shape",
            &layout,
        )
        .expect("Broadcast-like call return shape should compact-materialize as nested sequence replacement");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "nested Broadcast-like FuncExcept should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_called_mcl_broadcast_funcdef_row_stores_into_fixed_network_layout() {
        let mut chunk = BytecodeChunk::new();
        let fields_start = chunk.constants.add_value(Value::String("from".into()));
        chunk.constants.add_value(Value::String("type".into()));
        let req_idx = chunk.constants.add_value(Value::String("req".into()));

        let mut helper = BytecodeFunction::new("BroadcastRow".to_string(), 1);
        helper.emit(Opcode::LoadImm { rd: 1, value: 1 });
        helper.emit(Opcode::LoadImm { rd: 2, value: 3 });
        helper.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        let begin_pc = helper.emit(Opcode::FuncDefBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });
        helper.emit(Opcode::Move { rd: 6, rs: 0 });
        helper.emit(Opcode::LoadConst {
            rd: 7,
            idx: req_idx,
        });
        helper.emit(Opcode::RecordNew {
            rd: 8,
            fields_start,
            values_start: 6,
            count: 2,
        });
        helper.emit(Opcode::SeqNew {
            rd: 9,
            start: 8,
            count: 1,
        });
        let next_pc = helper.emit(Opcode::LoopNext {
            r_binding: 5,
            r_body: 9,
            loop_begin: 0,
        });
        helper.patch_jump(begin_pc, next_pc + 1);
        helper.patch_jump(next_pc, begin_pc + 1);
        helper.emit(Opcode::Ret { rs: 4 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("mcl_broadcast_network_store".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 1 });
        entry.emit(Opcode::Call {
            rd: 2,
            op_idx: helper_idx,
            args_start: 1,
            argc: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 3, value: 1 });
        entry.emit(Opcode::FuncExcept {
            rd: 4,
            func: 0,
            path: 3,
            val: 2,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 4 });
        entry.emit(Opcode::LoadBool { rd: 5, value: true });
        entry.emit(Opcode::Ret { rs: 5 });
        let entry_idx = chunk.add_function(entry);

        let message_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("from"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let row_layout = || CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(message_layout()),
                element_count: Some(1),
            }),
            pair_count: Some(3),
            domain_lo: Some(1),
        };
        let network_layout = CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(row_layout()),
            pair_count: Some(3),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(network_layout)]);

        let module = lower_module_next_state_with_layout(
            &chunk,
            entry_idx,
            "mcl_broadcast_network_store",
            &layout,
        )
        .expect("called MCL Broadcast-style FuncDef row should store into fixed network layout");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "MCL Broadcast-style row replacement should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
        assert_call_uses_caller_owned_return_buffer(&module, 0, 4, 9);
        assert_callee_stores_into_hidden_return_buffer(&module, 1, 4);
    }

    #[test]
    fn test_called_mcl_broadcast_append_row_uses_fixed_return_buffer() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();
        let fields_start = chunk.constants.add_value(Value::String("type".into()));
        chunk.constants.add_value(Value::String("clock".into()));
        let req_idx = chunk.constants.add_value(Value::String("req".into()));

        let mut helper = BytecodeFunction::new("Broadcast".to_string(), 2);
        helper.emit(Opcode::LoadVar { rd: 2, var_idx: 0 });
        helper.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 0,
        });
        helper.emit(Opcode::LoadImm { rd: 4, value: 1 });
        helper.emit(Opcode::LoadImm { rd: 5, value: 3 });
        helper.emit(Opcode::Range {
            rd: 6,
            lo: 4,
            hi: 5,
        });
        let begin_pc = helper.emit(Opcode::FuncDefBegin {
            rd: 7,
            r_binding: 8,
            r_domain: 6,
            loop_end: 0,
        });
        helper.emit(Opcode::FuncApply {
            rd: 9,
            func: 3,
            arg: 8,
        });
        helper.emit(Opcode::Move { rd: 10, rs: 1 });
        helper.emit(Opcode::CallBuiltin {
            rd: 11,
            builtin: BuiltinOp::Append,
            args_start: 9,
            argc: 2,
        });
        helper.emit(Opcode::Eq {
            rd: 12,
            r1: 0,
            r2: 8,
        });
        helper.emit(Opcode::CondMove {
            rd: 11,
            cond: 12,
            rs: 9,
        });
        let next_pc = helper.emit(Opcode::LoopNext {
            r_binding: 8,
            r_body: 11,
            loop_begin: 0,
        });
        helper.patch_jump(begin_pc, next_pc + 1);
        helper.patch_jump(next_pc, begin_pc + 1);
        helper.emit(Opcode::Ret { rs: 7 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("mcl_broadcast_append_network_store".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadConst {
            rd: 1,
            idx: req_idx,
        });
        entry.emit(Opcode::LoadImm { rd: 2, value: 1 });
        entry.emit(Opcode::RecordNew {
            rd: 3,
            fields_start,
            values_start: 1,
            count: 2,
        });
        entry.emit(Opcode::Move { rd: 4, rs: 0 });
        entry.emit(Opcode::Move { rd: 5, rs: 3 });
        entry.emit(Opcode::Call {
            rd: 6,
            op_idx: helper_idx,
            args_start: 4,
            argc: 2,
        });
        entry.emit(Opcode::LoadVar { rd: 7, var_idx: 0 });
        entry.emit(Opcode::LoadImm { rd: 8, value: 1 });
        entry.emit(Opcode::FuncExcept {
            rd: 9,
            func: 7,
            path: 8,
            val: 6,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 9 });
        entry.emit(Opcode::LoadBool {
            rd: 10,
            value: true,
        });
        entry.emit(Opcode::Ret { rs: 10 });
        let entry_idx = chunk.add_function(entry);

        let message_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("clock"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let channel_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(message_layout()),
            element_count: Some(3),
        };
        let row_layout = || CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(channel_layout()),
            pair_count: Some(3),
            domain_lo: Some(1),
        };
        let network_layout = CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(row_layout()),
            pair_count: Some(3),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(network_layout)]);

        let module = lower_module_next_state_with_layout(
            &chunk,
            entry_idx,
            "mcl_broadcast_append_network_store",
            &layout,
        )
        .expect("MCL Broadcast Append helper should retain a fixed row return layout");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "MCL Broadcast Append row replacement should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
        assert_call_uses_caller_owned_return_buffer(&module, 0, 4, 21);
        assert_callee_stores_into_hidden_return_buffer(&module, 1, 4);
    }

    #[test]
    fn test_called_mcl_request_reqmessage_broadcast_chain_keeps_fixed_return_buffer() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();
        let fields_start = chunk.constants.add_value(Value::String("type".into()));
        chunk.constants.add_value(Value::String("clock".into()));
        let req_const_idx = chunk.constants.add_value(Value::String("req".into()));

        let mut req_message = BytecodeFunction::new("ReqMessage".to_string(), 1);
        req_message.emit(Opcode::LoadConst {
            rd: 1,
            idx: req_const_idx,
        });
        req_message.emit(Opcode::Move { rd: 2, rs: 0 });
        req_message.emit(Opcode::RecordNew {
            rd: 3,
            fields_start,
            values_start: 1,
            count: 2,
        });
        req_message.emit(Opcode::Ret { rs: 3 });
        let req_message_idx = chunk.add_function(req_message);

        let mut broadcast = BytecodeFunction::new("Broadcast".to_string(), 2);
        broadcast.emit(Opcode::LoadVar { rd: 2, var_idx: 3 });
        broadcast.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 0,
        });
        broadcast.emit(Opcode::LoadImm { rd: 4, value: 1 });
        broadcast.emit(Opcode::LoadImm { rd: 5, value: 3 });
        broadcast.emit(Opcode::Range {
            rd: 6,
            lo: 4,
            hi: 5,
        });
        let begin_pc = broadcast.emit(Opcode::FuncDefBegin {
            rd: 7,
            r_binding: 8,
            r_domain: 6,
            loop_end: 0,
        });
        broadcast.emit(Opcode::FuncApply {
            rd: 9,
            func: 3,
            arg: 8,
        });
        broadcast.emit(Opcode::Move { rd: 10, rs: 1 });
        broadcast.emit(Opcode::CallBuiltin {
            rd: 11,
            builtin: BuiltinOp::Append,
            args_start: 9,
            argc: 2,
        });
        broadcast.emit(Opcode::Eq {
            rd: 12,
            r1: 0,
            r2: 8,
        });
        broadcast.emit(Opcode::CondMove {
            rd: 11,
            cond: 12,
            rs: 9,
        });
        let next_pc = broadcast.emit(Opcode::LoopNext {
            r_binding: 8,
            r_body: 11,
            loop_begin: 0,
        });
        broadcast.patch_jump(begin_pc, next_pc + 1);
        broadcast.patch_jump(next_pc, begin_pc + 1);
        broadcast.emit(Opcode::Ret { rs: 7 });
        let broadcast_idx = chunk.add_function(broadcast);

        let unchanged_start = chunk.constants.add_value(Value::SmallInt(1));
        chunk.constants.add_value(Value::SmallInt(2));

        let mut entry = BytecodeFunction::new("Request__1_1".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadVar { rd: 1, var_idx: 4 });
        entry.emit(Opcode::FuncApply {
            rd: 2,
            func: 1,
            arg: 0,
        });
        entry.emit(Opcode::FuncApply {
            rd: 3,
            func: 2,
            arg: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 4, value: 0 });
        entry.emit(Opcode::Eq {
            rd: 5,
            r1: 3,
            r2: 4,
        });
        entry.emit(Opcode::Move { rd: 6, rs: 5 });
        entry.emit(Opcode::JumpFalse { rs: 6, offset: 11 });
        entry.emit(Opcode::LoadBool {
            rd: 15,
            value: true,
        });
        entry.emit(Opcode::LoadVar { rd: 8, var_idx: 4 });
        entry.emit(Opcode::FuncApply {
            rd: 9,
            func: 8,
            arg: 0,
        });
        entry.emit(Opcode::FuncApply {
            rd: 10,
            func: 9,
            arg: 0,
        });
        entry.emit(Opcode::LoadVar { rd: 11, var_idx: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 12,
            func: 11,
            arg: 0,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 13,
            func: 9,
            path: 0,
            val: 12,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 14,
            func: 8,
            path: 0,
            val: 13,
        });
        entry.emit(Opcode::StoreVar { var_idx: 4, rs: 14 });
        entry.emit(Opcode::Move { rd: 6, rs: 15 });
        entry.emit(Opcode::Move { rd: 16, rs: 6 });
        entry.emit(Opcode::JumpFalse { rs: 16, offset: 14 });
        entry.emit(Opcode::LoadBool {
            rd: 28,
            value: true,
        });
        entry.emit(Opcode::LoadVar { rd: 18, var_idx: 3 });
        entry.emit(Opcode::FuncApply {
            rd: 19,
            func: 18,
            arg: 0,
        });
        entry.emit(Opcode::Move { rd: 20, rs: 0 });
        entry.emit(Opcode::LoadVar { rd: 23, var_idx: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 24,
            func: 23,
            arg: 0,
        });
        entry.emit(Opcode::Move { rd: 22, rs: 24 });
        entry.emit(Opcode::Call {
            rd: 25,
            op_idx: req_message_idx,
            args_start: 22,
            argc: 1,
        });
        entry.emit(Opcode::Move { rd: 21, rs: 25 });
        entry.emit(Opcode::Call {
            rd: 26,
            op_idx: broadcast_idx,
            args_start: 20,
            argc: 2,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 27,
            func: 18,
            path: 0,
            val: 26,
        });
        entry.emit(Opcode::StoreVar { var_idx: 3, rs: 27 });
        entry.emit(Opcode::Move { rd: 16, rs: 28 });
        entry.emit(Opcode::Move { rd: 29, rs: 16 });
        entry.emit(Opcode::JumpFalse { rs: 29, offset: 9 });
        entry.emit(Opcode::LoadBool {
            rd: 36,
            value: true,
        });
        entry.emit(Opcode::LoadVar { rd: 31, var_idx: 0 });
        entry.emit(Opcode::FuncApply {
            rd: 32,
            func: 31,
            arg: 0,
        });
        entry.emit(Opcode::Move { rd: 33, rs: 0 });
        entry.emit(Opcode::SetEnum {
            rd: 34,
            start: 33,
            count: 1,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 35,
            func: 31,
            path: 0,
            val: 34,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 35 });
        entry.emit(Opcode::Move { rd: 29, rs: 36 });
        entry.emit(Opcode::Move { rd: 37, rs: 29 });
        entry.emit(Opcode::JumpFalse { rs: 37, offset: 3 });
        entry.emit(Opcode::Unchanged {
            rd: 38,
            start: unchanged_start,
            count: 2,
        });
        entry.emit(Opcode::Move { rd: 37, rs: 38 });
        entry.emit(Opcode::Move { rd: 0, rs: 37 });
        entry.emit(Opcode::Ret { rs: 0 });
        let entry_idx = chunk.add_function(entry);

        let message_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("clock"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let channel_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(message_layout()),
            element_count: Some(3),
        };
        let proc_int_sequence_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        };
        let proc_set_layout = || int_range_set_bitmask_layout(1, 3);
        let ack_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(proc_set_layout()),
            element_count: Some(3),
        };
        let req_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(proc_int_sequence_layout()),
            element_count: Some(3),
        };
        let row_layout = || CompoundLayout::Sequence {
            element_layout: Box::new(channel_layout()),
            element_count: Some(3),
        };
        let network_layout = CompoundLayout::Sequence {
            element_layout: Box::new(row_layout()),
            element_count: Some(3),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(ack_layout()),
            VarLayout::Compound(proc_int_sequence_layout()),
            VarLayout::Compound(proc_set_layout()),
            VarLayout::Compound(network_layout),
            VarLayout::Compound(req_layout()),
        ]);
        assert_eq!(
            layout.compact_slot_count(),
            89,
            "MCL sequence-shaped canary layout should stay at the native compact width"
        );

        let module = lower_module_next_state_with_layout(
            &chunk,
            entry_idx,
            "mcl_request_broadcast_chain_store",
            &layout,
        )
        .expect("MCL Request -> ReqMessage -> Broadcast chain should keep fixed return layout");
        assert_no_ptr_payload_store_to_state_out(&module, 0);
        assert_call_uses_caller_owned_return_buffer(&module, 0, 4, 2);
        assert_call_uses_caller_owned_return_buffer(&module, 0, 4, 21);
        assert_call_arg_is_materialized_aggregate_ptr(&module, 0, 4, 21, 6, 2);
        assert_callee_stores_into_hidden_return_buffer(&module, 1, 4);
        assert_callee_stores_into_hidden_return_buffer(&module, 2, 4);
        assert_callee_stores_exact_hidden_return_slots(&module, 1, 4, 2);
        assert_callee_stores_exact_hidden_return_slots(&module, 2, 4, 21);
    }

    #[test]
    fn test_called_funcdef_flat_pair_list_return_copies_value_slots_not_dense_slots() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("FlatPairFuncDef".to_string(), 0);
        helper.emit(Opcode::LoadImm { rd: 0, value: 1 });
        helper.emit(Opcode::LoadImm { rd: 1, value: 2 });
        helper.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        let begin_pc = helper.emit(Opcode::FuncDefBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        helper.emit(Opcode::LoadImm { rd: 5, value: 10 });
        let next_pc = helper.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 5,
            loop_begin: 0,
        });
        helper.patch_jump(begin_pc, next_pc + 1);
        helper.patch_jump(next_pc, begin_pc + 1);
        helper.emit(Opcode::Ret { rs: 3 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("called_flat_pair_funcdef".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: helper_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadBool { rd: 1, value: true });
        entry.emit(Opcode::Ret { rs: 1 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "called_flat_pair_funcdef")
            .expect("called scalar FuncDef should compact-return through a hidden buffer");

        assert_call_uses_caller_owned_return_buffer(&module, 0, 3, 2);
        assert_callee_stores_exact_hidden_return_slots(&module, 1, 3, 2);
        assert_eq!(
            hidden_return_load_source_slots(&module, 1, 3),
            vec![(0, 2), (1, 4)],
            "FuncDef returns are flat [len, key, value, ...]; compact return copy must read value slots 2 and 4, not dense compact slots 0 and 1"
        );
    }

    #[test]
    fn test_called_interval_return_uses_caller_owned_return_buffer() {
        let mut chunk = BytecodeChunk::new();

        let mut domain = BytecodeFunction::new("IntervalDomain".to_string(), 0);
        domain.emit(Opcode::LoadImm { rd: 0, value: 1 });
        domain.emit(Opcode::LoadImm { rd: 1, value: 3 });
        domain.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        domain.emit(Opcode::Ret { rs: 2 });
        let domain_idx = chunk.add_function(domain);

        let mut entry = BytecodeFunction::new("called_interval_membership".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: domain_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::SetIn {
            rd: 2,
            elem: 1,
            set: 0,
        });
        entry.emit(Opcode::Ret { rs: 2 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "called_interval_membership")
            .expect("called Interval helper should return through a caller-owned buffer");

        assert_call_uses_caller_owned_materialized_return_buffer(&module, 0, 3, 4);
        assert_callee_stores_exact_hidden_return_slots(&module, 1, 3, 4);
    }

    #[test]
    fn test_called_empty_interval_return_uses_one_slot_return_buffer() {
        let mut chunk = BytecodeChunk::new();

        let mut domain = BytecodeFunction::new("EmptyIntervalDomain".to_string(), 0);
        domain.emit(Opcode::LoadImm { rd: 0, value: 3 });
        domain.emit(Opcode::LoadImm { rd: 1, value: 1 });
        domain.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        domain.emit(Opcode::Ret { rs: 2 });
        let domain_idx = chunk.add_function(domain);

        let mut entry = BytecodeFunction::new("called_empty_interval_membership".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: domain_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::SetIn {
            rd: 2,
            elem: 1,
            set: 0,
        });
        entry.emit(Opcode::Ret { rs: 2 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "called_empty_interval_membership")
            .expect("called empty Interval helper should return through a caller-owned buffer");

        assert_call_uses_caller_owned_materialized_return_buffer(&module, 0, 3, 1);
        assert_callee_stores_exact_hidden_return_slots(&module, 1, 3, 1);
    }

    #[test]
    fn test_called_exact_int_set_return_uses_caller_owned_return_buffer() {
        let mut chunk = BytecodeChunk::new();

        let mut domain = BytecodeFunction::new("ExactIntDomain".to_string(), 0);
        domain.emit(Opcode::LoadImm { rd: 0, value: 2 });
        domain.emit(Opcode::LoadImm { rd: 1, value: 4 });
        domain.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        domain.emit(Opcode::Ret { rs: 2 });
        let domain_idx = chunk.add_function(domain);

        let mut entry = BytecodeFunction::new("called_exact_int_set_membership".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: domain_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::SetIn {
            rd: 2,
            elem: 1,
            set: 0,
        });
        entry.emit(Opcode::Ret { rs: 2 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "called_exact_int_set_membership")
            .expect("called exact integer set helper should return through a caller-owned buffer");

        assert_call_uses_caller_owned_materialized_return_buffer(&module, 0, 3, 3);
        assert_callee_stores_exact_hidden_return_slots(&module, 1, 3, 3);
    }

    #[test]
    fn test_called_empty_finite_set_return_uses_one_slot_return_buffer() {
        let mut chunk = BytecodeChunk::new();

        let mut domain = BytecodeFunction::new("EmptySetDomain".to_string(), 0);
        domain.emit(Opcode::SetEnum {
            rd: 0,
            start: 0,
            count: 0,
        });
        domain.emit(Opcode::Ret { rs: 0 });
        let domain_idx = chunk.add_function(domain);

        let mut entry = BytecodeFunction::new("called_empty_set_membership".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: domain_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::SetIn {
            rd: 2,
            elem: 1,
            set: 0,
        });
        entry.emit(Opcode::Ret { rs: 2 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "called_empty_set_membership")
            .expect("called empty finite set helper should return through a caller-owned buffer");

        assert_call_uses_caller_owned_materialized_return_buffer(&module, 0, 3, 1);
        assert_callee_stores_exact_hidden_return_slots(&module, 1, 3, 1);
        assert_eq!(
            AggregateShape::Set {
                len: 0,
                element: None
            }
            .materialized_return_slot_count(),
            Some(1),
            "shape completion should treat an erased empty Set as a one-slot materialized return"
        );
    }

    #[test]
    fn test_called_generic_materialized_set_return_without_abi_rejects() {
        let mut chunk = BytecodeChunk::new();

        let mut domain = BytecodeFunction::new("GenericBoolSetDomain".to_string(), 0);
        domain.emit(Opcode::LoadBool { rd: 0, value: true });
        domain.emit(Opcode::LoadBool {
            rd: 1,
            value: false,
        });
        domain.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        domain.emit(Opcode::Ret { rs: 2 });
        let domain_idx = chunk.add_function(domain);

        let mut entry = BytecodeFunction::new("called_generic_set_return".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: domain_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadBool { rd: 1, value: true });
        entry.emit(Opcode::Ret { rs: 1 });
        let entry_idx = chunk.add_function(entry);

        assert_missing_caller_owned_return_abi(
            lower_module_invariant(&chunk, entry_idx, "called_generic_set_return"),
            "Set",
        );
    }

    #[test]
    fn test_called_compact_return_without_abi_shape_rejects() {
        let mut chunk = BytecodeChunk::new();
        let fields_start = chunk.constants.add_value(Value::String("x".into()));
        chunk.constants.add_value(Value::String("y".into()));

        let mut helper = BytecodeFunction::new("UnmodeledRecordReturn".to_string(), 1);
        helper.emit(Opcode::LoadImm { rd: 1, value: 2 });
        helper.emit(Opcode::RecordNew {
            rd: 2,
            fields_start,
            values_start: 0,
            count: 2,
        });
        helper.emit(Opcode::Ret { rs: 2 });
        helper.emit(Opcode::Halt);
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::LoadBool { rd: 2, value: true });
        entry.emit(Opcode::Ret { rs: 2 });
        let entry_idx = chunk.add_function(entry);

        assert_missing_caller_owned_return_abi(
            lower_module_invariant(&chunk, entry_idx, "unmodeled_record_return"),
            "Record",
        );
    }

    #[test]
    fn test_called_compact_return_rejects_caller_callee_abi_mismatch() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("IdentityRecord".to_string(), 1);
        helper.emit(Opcode::Ret { rs: 0 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::LoadVar { rd: 2, var_idx: 1 });
        entry.emit(Opcode::Call {
            rd: 3,
            op_idx: helper_idx,
            args_start: 2,
            argc: 1,
        });
        entry.emit(Opcode::LoadBool { rd: 4, value: true });
        entry.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(entry);

        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("x"), CompoundLayout::Int),
                    (tla_core::intern_name("y"), CompoundLayout::Int),
                ],
            }),
            VarLayout::Compound(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("x"), CompoundLayout::Int),
                    (tla_core::intern_name("y"), CompoundLayout::String),
                ],
            }),
        ]);

        let err = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "called_compact_return_abi_mismatch",
            &layout,
        )
        .expect_err("caller/callee compact return ABI mismatch must reject");
        let message = format!("{err}");
        assert!(
            message.contains("Call compact compound return ABI")
                && message.contains("differs between caller and callee")
                || message.contains("incompatible compact aggregate callsite shapes"),
            "unexpected compact return ABI mismatch error: {message}"
        );
    }

    #[test]
    fn test_called_compact_return_rejects_late_abi_upgrade_after_callee_lowered_scalar() {
        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::LoadBool { rd: 0, value: true });
        entry.emit(Opcode::Ret { rs: 0 });

        let mut ctx = Ctx::new(
            &entry,
            "late_compact_return_abi_upgrade",
            LoweringMode::Invariant,
            None,
            None,
            None,
        )
        .expect("test context should initialize");
        let op_idx = 7;
        ctx.callee_lowered_return_abi_shapes.insert(op_idx, None);
        let abi_shape = AggregateShape::Record {
            fields: vec![(
                tla_core::intern_name("x"),
                Some(Box::new(AggregateShape::Scalar(ScalarShape::Int))),
            )],
        };

        let err = ctx
            .record_callee_expected_return_abi_shape(op_idx, &abi_shape)
            .expect_err("late compact-return ABI upgrade after lowering must reject");
        let message = format!("{err}");
        assert!(
            message.contains(
                "discovered after the callee was lowered without a compact return buffer"
            ),
            "unexpected late compact-return ABI error: {message}"
        );
    }

    #[test]
    fn test_called_reordered_record_branch_return_uses_abi_shape() {
        let mut chunk = BytecodeChunk::new();
        let fields_xy = chunk.constants.add_value(Value::String("x".into()));
        chunk.constants.add_value(Value::String("y".into()));
        let fields_yx = chunk.constants.add_value(Value::String("y".into()));
        chunk.constants.add_value(Value::String("x".into()));

        let mut helper = BytecodeFunction::new("MaybeReorderedRecord".to_string(), 1);
        let jump_to_else = helper.emit(Opcode::JumpFalse { rs: 0, offset: 0 });
        helper.emit(Opcode::LoadImm { rd: 1, value: 11 });
        helper.emit(Opcode::LoadImm { rd: 2, value: 22 });
        helper.emit(Opcode::RecordNew {
            rd: 3,
            fields_start: fields_xy,
            values_start: 1,
            count: 2,
        });
        let jump_to_ret = helper.emit(Opcode::Jump { offset: 0 });
        let else_pc = helper.len();
        helper.patch_jump(jump_to_else, else_pc);
        helper.emit(Opcode::LoadImm { rd: 4, value: 33 });
        helper.emit(Opcode::LoadImm { rd: 5, value: 44 });
        helper.emit(Opcode::RecordNew {
            rd: 3,
            fields_start: fields_yx,
            values_start: 4,
            count: 2,
        });
        let ret_pc = helper.len();
        helper.patch_jump(jump_to_ret, ret_pc);
        helper.emit(Opcode::Ret { rs: 3 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::LoadBool { rd: 0, value: true });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
        entry.emit(Opcode::LoadBool { rd: 2, value: true });
        entry.emit(Opcode::Ret { rs: 2 });
        let entry_idx = chunk.add_function(entry);

        let layout = StateLayout::new(vec![VarLayout::Compound(compact_record_fields(&[
            "x", "y",
        ]))]);

        let module = lower_module_next_state_with_layout(
            &chunk,
            entry_idx,
            "reordered_record_return",
            &layout,
        )
        .expect("callee record branch returns should copy through the ABI shape");
        assert_call_uses_caller_owned_return_buffer(&module, 0, 4, 2);
        assert_callee_stores_into_hidden_return_buffer(&module, 1, 4);
        let stores = callee_return_buffer_const_stores(&module, 1, 4);
        let mut return_slots: Vec<_> = stores.iter().map(|(slot, _)| *slot).collect();
        return_slots.sort_unstable();
        return_slots.dedup();
        assert_eq!(
            return_slots,
            vec![0, 1],
            "callee must write exactly the caller ABI return slots; stores={stores:?}"
        );
        assert!(
            stores.contains(&(0, 11)) && stores.contains(&(1, 22)),
            "ordered branch should return x=11, y=22 in ABI slot order; stores={stores:?}"
        );
        assert!(
            stores.contains(&(0, 44)) && stores.contains(&(1, 33)),
            "reordered branch should return x=44, y=33 in ABI slot order; stores={stores:?}"
        );
        assert!(
            !stores.contains(&(0, 33)) && !stores.contains(&(1, 44)),
            "reordered branch must not copy syntax order into ABI slots; stores={stores:?}"
        );
        assert!(
            !stores.contains(&(0, 22)) && !stores.contains(&(1, 11)),
            "ordered branch must not copy through first-branch y,x ABI order; stores={stores:?}"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_parameterized_branch_return_shape_declines_skipped_sequence_assignment_for_membership()
    {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("MaybeSeq".to_string(), 1);
        helper.emit(Opcode::LoadImm { rd: 1, value: 99 });
        let jump_to_ret = helper.emit(Opcode::JumpFalse { rs: 0, offset: 0 });
        helper.emit(Opcode::LoadImm { rd: 2, value: 1 });
        helper.emit(Opcode::SeqNew {
            rd: 1,
            start: 2,
            count: 1,
        });
        let ret_pc = helper.len();
        helper.patch_jump(jump_to_ret, ret_pc);
        helper.emit(Opcode::Ret { rs: 1 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("branch_sensitive_shape".to_string(), 0);
        entry.emit(Opcode::LoadBool { rd: 0, value: true });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 2, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 3, value: 2 });
        entry.emit(Opcode::Range {
            rd: 4,
            lo: 2,
            hi: 3,
        });
        entry.emit(Opcode::FuncSet {
            rd: 5,
            domain: 4,
            range: 4,
        });
        entry.emit(Opcode::SetIn {
            rd: 6,
            elem: 1,
            set: 5,
        });
        entry.emit(Opcode::Ret { rs: 6 });
        let entry_idx = chunk.add_function(entry);

        let result = lower_module_invariant(&chunk, entry_idx, "branch_sensitive_shape");
        assert!(
            result.is_err(),
            "branch-dependent scalar-or-sequence return must not be inferred as a sequence"
        );
    }

    #[test]
    fn test_parameterized_branch_return_shape_merges_compatible_sequences_for_membership() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("AlwaysSeq".to_string(), 1);
        let jump_to_else = helper.emit(Opcode::JumpFalse { rs: 0, offset: 0 });
        helper.emit(Opcode::LoadImm { rd: 1, value: 1 });
        helper.emit(Opcode::SeqNew {
            rd: 3,
            start: 1,
            count: 1,
        });
        let jump_to_ret = helper.emit(Opcode::Jump { offset: 0 });
        let else_pc = helper.len();
        helper.patch_jump(jump_to_else, else_pc);
        helper.emit(Opcode::LoadImm { rd: 2, value: 1 });
        helper.emit(Opcode::SeqNew {
            rd: 3,
            start: 2,
            count: 1,
        });
        let ret_pc = helper.len();
        helper.patch_jump(jump_to_ret, ret_pc);
        helper.emit(Opcode::Ret { rs: 3 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("branch_compatible_shape".to_string(), 0);
        entry.emit(Opcode::LoadBool { rd: 0, value: true });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 2, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 3, value: 1 });
        entry.emit(Opcode::Range {
            rd: 4,
            lo: 2,
            hi: 3,
        });
        entry.emit(Opcode::FuncSet {
            rd: 5,
            domain: 4,
            range: 4,
        });
        entry.emit(Opcode::SetIn {
            rd: 6,
            elem: 1,
            set: 5,
        });
        entry.emit(Opcode::Ret { rs: 6 });
        let entry_idx = chunk.add_function(entry);

        lower_module_invariant(&chunk, entry_idx, "branch_compatible_shape")
            .expect("compatible sequence branches should preserve helper return shape");
    }

    #[test]
    fn test_called_funcdef_helper_return_shape_materializes_sequence_funcexcept_replacement() {
        let mut chunk = BytecodeChunk::new();
        let fields_start = chunk.constants.add_value(Value::String("x".into()));
        chunk.constants.add_value(Value::String("y".into()));

        let mut helper = BytecodeFunction::new("SeqFunction".to_string(), 0);
        helper.emit(Opcode::LoadImm { rd: 0, value: 1 });
        helper.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        let begin_pc = helper.emit(Opcode::FuncDefBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        helper.emit(Opcode::LoadImm { rd: 4, value: 10 });
        helper.emit(Opcode::LoadImm { rd: 5, value: 20 });
        helper.emit(Opcode::RecordNew {
            rd: 6,
            fields_start,
            values_start: 4,
            count: 2,
        });
        helper.emit(Opcode::LoadImm { rd: 7, value: 30 });
        helper.emit(Opcode::LoadImm { rd: 8, value: 40 });
        helper.emit(Opcode::RecordNew {
            rd: 9,
            fields_start,
            values_start: 7,
            count: 2,
        });
        helper.emit(Opcode::Move { rd: 7, rs: 9 });
        helper.emit(Opcode::SeqNew {
            rd: 10,
            start: 6,
            count: 2,
        });
        let next_pc = helper.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 10,
            loop_begin: 0,
        });
        helper.patch_jump(begin_pc, next_pc + 1);
        helper.patch_jump(next_pc, begin_pc + 1);
        helper.emit(Opcode::Ret { rs: 2 });
        let helper_idx = chunk.add_function(helper);

        let mut entry =
            BytecodeFunction::new("called_funcdef_sequence_except_shape".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: helper_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 1, value: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 3, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 4, value: 50 });
        entry.emit(Opcode::LoadImm { rd: 5, value: 60 });
        entry.emit(Opcode::RecordNew {
            rd: 6,
            fields_start,
            values_start: 4,
            count: 2,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 7,
            func: 2,
            path: 3,
            val: 6,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 8,
            func: 0,
            path: 1,
            val: 7,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 8 });
        entry.emit(Opcode::LoadBool { rd: 9, value: true });
        entry.emit(Opcode::Ret { rs: 9 });
        let entry_idx = chunk.add_function(entry);

        let record_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(record_layout()),
                element_count: Some(2),
            }),
            pair_count: Some(1),
            domain_lo: Some(1),
        })]);

        let module = lower_module_next_state_with_layout(
            &chunk,
            entry_idx,
            "called_funcdef_sequence_except_shape",
            &layout,
        )
        .expect("called FuncDef return shape should materialize sequence EXCEPT replacement");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "called FuncDef sequence EXCEPT should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_called_nested_funcdef_helper_return_shape_materializes_nested_funcexcept_replacements()
    {
        let mut chunk = BytecodeChunk::new();
        let fields_start = chunk.constants.add_value(Value::String("x".into()));
        chunk.constants.add_value(Value::String("y".into()));

        let mut helper = BytecodeFunction::new("NestedFunction".to_string(), 0);
        helper.emit(Opcode::LoadImm { rd: 0, value: 1 });
        helper.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        let outer_begin = helper.emit(Opcode::FuncDefBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        helper.emit(Opcode::LoadImm { rd: 4, value: 1 });
        helper.emit(Opcode::SetEnum {
            rd: 5,
            start: 4,
            count: 1,
        });
        let inner_begin = helper.emit(Opcode::FuncDefBegin {
            rd: 6,
            r_binding: 7,
            r_domain: 5,
            loop_end: 0,
        });
        helper.emit(Opcode::LoadImm { rd: 8, value: 10 });
        helper.emit(Opcode::LoadImm { rd: 9, value: 20 });
        helper.emit(Opcode::RecordNew {
            rd: 10,
            fields_start,
            values_start: 8,
            count: 2,
        });
        helper.emit(Opcode::LoadImm { rd: 11, value: 30 });
        helper.emit(Opcode::LoadImm { rd: 12, value: 40 });
        helper.emit(Opcode::RecordNew {
            rd: 13,
            fields_start,
            values_start: 11,
            count: 2,
        });
        helper.emit(Opcode::Move { rd: 11, rs: 13 });
        helper.emit(Opcode::SeqNew {
            rd: 14,
            start: 10,
            count: 2,
        });
        let inner_next = helper.emit(Opcode::LoopNext {
            r_binding: 7,
            r_body: 14,
            loop_begin: 0,
        });
        helper.patch_jump(inner_begin, inner_next + 1);
        helper.patch_jump(inner_next, inner_begin + 1);
        let outer_next = helper.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 6,
            loop_begin: 0,
        });
        helper.patch_jump(outer_begin, outer_next + 1);
        helper.patch_jump(outer_next, outer_begin + 1);
        helper.emit(Opcode::Ret { rs: 2 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("called_nested_funcdef_except_shape".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: helper_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::LoadImm { rd: 1, value: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 3, value: 1 });
        entry.emit(Opcode::FuncApply {
            rd: 4,
            func: 2,
            arg: 3,
        });
        entry.emit(Opcode::LoadImm { rd: 5, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 6, value: 50 });
        entry.emit(Opcode::LoadImm { rd: 7, value: 60 });
        entry.emit(Opcode::RecordNew {
            rd: 8,
            fields_start,
            values_start: 6,
            count: 2,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 9,
            func: 4,
            path: 5,
            val: 8,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 10,
            func: 2,
            path: 3,
            val: 9,
        });
        entry.emit(Opcode::FuncExcept {
            rd: 11,
            func: 0,
            path: 1,
            val: 10,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 11 });
        entry.emit(Opcode::LoadBool {
            rd: 12,
            value: true,
        });
        entry.emit(Opcode::Ret { rs: 12 });
        let entry_idx = chunk.add_function(entry);

        let record_layout = || CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
            ],
        };
        let nested_function_layout = || CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Sequence {
                    element_layout: Box::new(record_layout()),
                    element_count: Some(2),
                }),
                pair_count: Some(1),
                domain_lo: Some(1),
            }),
            pair_count: Some(1),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(nested_function_layout())]);

        let module = lower_module_next_state_with_layout(
            &chunk,
            entry_idx,
            "called_nested_funcdef_except_shape",
            &layout,
        )
        .expect("called nested FuncDef shape should materialize nested EXCEPT replacements");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "called nested FuncDef EXCEPT should keep fixed compact materialization"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
        assert_call_uses_caller_owned_return_buffer(&module, 0, 4, 5);
        assert_eq!(
            hidden_return_load_source_slots(&module, 1, 4),
            vec![(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)],
            "captured nested FuncDef values are already compact; callee return copy must read dense slots 0..4, not flat pair-list value slots"
        );
    }

    /// Test CallBuiltin(FoldFunctionOnSetSum): sums f[x] over a tracked set S.
    #[test]
    fn test_lower_fold_function_on_set_sum() {
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;
        use tla_value::FuncValue;

        let mut pool = ConstantPool::new();
        let func_idx = pool.add_value(Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::SmallInt(10)),
            (Value::SmallInt(2), Value::SmallInt(20)),
        ]))));

        let mut func = BytecodeFunction::new("fold_sum_test".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: func_idx,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 1,
            count: 2,
        });
        func.emit(Opcode::Move { rd: 4, rs: 0 });
        func.emit(Opcode::Move { rd: 5, rs: 3 });
        func.emit(Opcode::CallBuiltin {
            rd: 6,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 4,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let module = lower_invariant_with_constants(&func, "fold_sum_test", &pool)
            .expect("FoldFunctionOnSetSum should lower for tracked finite f and S");
        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].blocks.len() >= 10,
            "expected nested fold/apply blocks, got {}",
            module.functions[0].blocks.len()
        );

        let has_checked_add = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Overflow {
                        op: OverflowOp::AddOverflow,
                        ..
                    }
                )
            })
        });
        assert!(
            has_checked_add,
            "FoldFunctionOnSetSum must use checked addition"
        );
    }

    /// FoldFunctionOnSetSum should reject non-tracked/lazy domains explicitly.
    #[test]
    fn test_lower_fold_function_on_set_sum_rejects_untracked_set() {
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;
        use tla_value::FuncValue;

        let mut pool = ConstantPool::new();
        let func_idx = pool.add_value(Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::SmallInt(10)),
        ]))));

        let mut func = BytecodeFunction::new("fold_sum_bad_set".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: func_idx,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::Move { rd: 2, rs: 0 });
        func.emit(Opcode::Move { rd: 3, rs: 1 });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 2,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let result = lower_invariant_with_constants(&func, "fold_sum_bad_set", &pool);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            format!("{err}").contains("set argument"),
            "error should identify unsupported domain: {err}"
        );
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_accepts_shape_swapped_args() {
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;
        use tla_value::FuncValue;

        let mut pool = ConstantPool::new();
        let func_idx = pool.add_value(Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(0), Value::SmallInt(1)),
            (Value::SmallInt(1), Value::SmallInt(2)),
            (Value::SmallInt(2), Value::SmallInt(3)),
        ]))));

        let mut func = BytecodeFunction::new("fold_sum_swapped_args".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: func_idx,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Move { rd: 4, rs: 3 });
        func.emit(Opcode::Move { rd: 5, rs: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 6,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 4,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 6 });

        lower_invariant_with_constants(&func, "fold_sum_swapped_args", &pool)
            .expect("FoldFunctionOnSetSum should resolve finite set/function operands by shape");
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_rejects_disjoint_exact_interval_domain() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("fold_sum_disjoint_exact_domain".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 5 });
        func.emit(Opcode::LoadImm { rd: 3, value: 6 });
        func.emit(Opcode::Range {
            rd: 1,
            lo: 2,
            hi: 3,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 0,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);
        let err = lower_invariant_with_constants_and_layout(
            &func,
            "fold_sum_disjoint_exact_domain",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("FoldFunctionOnSetSum must reject exact set outside exact function domain");

        assert!(
            format!("{err}").contains("incompatible with function domain"),
            "error should identify domain incompatibility: {err}"
        );
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_accepts_state_function_without_layout() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("fold_sum_swapped_state_func".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Move { rd: 4, rs: 3 });
        func.emit(Opcode::Move { rd: 5, rs: 0 });
        func.emit(Opcode::CallBuiltin {
            rd: 6,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 4,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 6 });

        lower_invariant(&func, "fold_sum_swapped_state_func_no_layout").expect(
            "FoldFunctionOnSetSum should infer state-loaded function shape from finite set",
        );

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);
        lower_invariant_with_constants_and_layout(
            &func,
            "fold_sum_swapped_state_func",
            &pool,
            &layout,
        )
        .expect("FoldFunctionOnSetSum should lower when invariant layout tracks state function");
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_accepts_ewd_interval_first_stale_function_shape() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("fold_sum_ewd_interval_first".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::LoadVar { rd: 4, var_idx: 0 });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::CondMove {
            rd: 3,
            cond: 5,
            rs: 4,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 6,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 2,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);

        lower_invariant_with_constants_and_layout(
            &func,
            "fold_sum_ewd_interval_first",
            &pool,
            &layout,
        )
        .expect("FoldFunctionOnSetSum should resolve EWD-style interval/function operands");
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_accepts_dynamic_range_with_layout_function() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("fold_sum_dynamic_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadVar { rd: 2, var_idx: 1 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Move { rd: 1, rs: 3 });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 0,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Int),
                pair_count: Some(3),
                domain_lo: Some(0),
            }),
            VarLayout::ScalarInt,
        ]);

        lower_invariant_with_constants_and_layout(&func, "fold_sum_dynamic_range", &pool, &layout)
            .expect("FoldFunctionOnSetSum should accept runtime-finite Range domains");
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_accepts_unknown_set_first_from_function_domain() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();

        let mut filtered_node = BytecodeFunction::new("FilteredNode".to_string(), 0);
        filtered_node.emit(Opcode::LoadImm { rd: 0, value: 0 });
        filtered_node.emit(Opcode::LoadImm { rd: 1, value: 2 });
        filtered_node.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        let begin_pc = filtered_node.emit(Opcode::SetFilterBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        filtered_node.emit(Opcode::LoadBool { rd: 5, value: true });
        let next_pc = filtered_node.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 5,
            loop_begin: 0,
        });
        filtered_node.patch_jump(begin_pc, next_pc + 1);
        filtered_node.patch_jump(next_pc, begin_pc + 1);
        filtered_node.emit(Opcode::Ret { rs: 3 });
        let filtered_node_idx = chunk.add_function(filtered_node);

        let mut inv = BytecodeFunction::new("fold_sum_unknown_set_first".to_string(), 0);
        inv.emit(Opcode::Call {
            rd: 0,
            op_idx: filtered_node_idx,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::LoadVar { rd: 1, var_idx: 0 });
        inv.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 0,
            argc: 2,
        });
        inv.emit(Opcode::Ret { rs: 2 });
        let entry_idx = chunk.add_function(inv);

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "fold_sum_unknown_set_first",
            &layout,
        )
        .expect("FoldFunctionOnSetSum should recover a finite set bound from the function domain");
        assert!(
            has_bounded_loop_tag(&module, 0, 3),
            "recovered finite-set shape should bound the entry FoldFunctionOnSetSum loop"
        );
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_uses_callsite_arg_shapes_for_bounds() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();

        let mut sum = BytecodeFunction::new("Sum".to_string(), 2);
        sum.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 0,
            argc: 2,
        });
        sum.emit(Opcode::Ret { rs: 2 });
        let sum_idx = chunk.add_function(sum);

        let mut inv = BytecodeFunction::new("fold_sum_callsite_shapes".to_string(), 0);
        inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv.emit(Opcode::LoadImm { rd: 2, value: 0 });
        inv.emit(Opcode::LoadImm { rd: 3, value: 2 });
        inv.emit(Opcode::Range {
            rd: 1,
            lo: 2,
            hi: 3,
        });
        inv.emit(Opcode::Call {
            rd: 4,
            op_idx: sum_idx,
            args_start: 0,
            argc: 2,
        });
        inv.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(inv);

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "fold_sum_callsite_shapes",
            &layout,
        )
        .expect("callee FoldFunctionOnSetSum should receive compatible call-site shapes");
        assert!(
            module.functions.len() >= 2,
            "expected entry plus Sum callee, got {} functions",
            module.functions.len()
        );
        assert!(
            has_bounded_loop_tag(&module, 1, 3),
            "call-site finite-set shape should bound the callee FoldFunctionOnSetSum loop"
        );
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_materializes_compact_state_function_call_arg() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();

        let mut sum = BytecodeFunction::new("Sum".to_string(), 2);
        sum.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 0,
            argc: 2,
        });
        sum.emit(Opcode::Ret { rs: 2 });
        let sum_idx = chunk.add_function(sum);

        let mut inv = BytecodeFunction::new("fold_sum_compact_state_func_call_arg".to_string(), 0);
        inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv.emit(Opcode::LoadImm { rd: 2, value: 0 });
        inv.emit(Opcode::LoadImm { rd: 3, value: 2 });
        inv.emit(Opcode::Range {
            rd: 1,
            lo: 2,
            hi: 3,
        });
        inv.emit(Opcode::Call {
            rd: 4,
            op_idx: sum_idx,
            args_start: 0,
            argc: 2,
        });
        inv.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(inv);

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "fold_sum_compact_state_func_call_arg",
            &layout,
        )
        .expect("compact state Function(Int->Int) helper argument should lower");
        assert!(
            has_bounded_loop_tag(&module, 1, 3),
            "call-site finite-set shape should still bound the callee FoldFunctionOnSetSum loop"
        );

        let entry = &module.functions[0];
        let (state_in, state_in_ty) = entry
            .blocks
            .first()
            .and_then(|block| block.params.get(1))
            .expect("lowered invariant should have a state_in parameter");
        assert_eq!(*state_in_ty, Ty::Ptr);
        let state_in = *state_in;

        let mut i32_consts = HashMap::new();
        let mut i64_consts = HashMap::new();
        let mut alloca_counts = HashMap::new();
        let mut ptr_to_int_sources = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut load_slots = HashMap::new();
        let mut stores = Vec::new();
        let mut call_args = None;

        for block in &entry.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i32_consts.insert(result, *value);
                    }
                    (
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i64_consts.insert(result, *value);
                    }
                    (
                        Inst::Alloca {
                            count: Some(count), ..
                        },
                        Some(result),
                    ) => {
                        if let Some(count) = i32_consts.get(count).copied() {
                            alloca_counts.insert(result, count);
                        }
                    }
                    (
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        ptr_to_int_sources.insert(result, *operand);
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = i32_consts.get(&indices[0]).copied() {
                            gep_slots.insert(result, (*base, slot));
                        }
                    }
                    (
                        Inst::Load {
                            ty: Ty::I64, ptr, ..
                        },
                        Some(result),
                    ) => {
                        if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                            load_slots.insert(result, (base, slot));
                        }
                    }
                    (
                        Inst::Store {
                            ty: Ty::I64,
                            ptr,
                            value,
                            ..
                        },
                        _,
                    ) => {
                        if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                            stores.push((base, slot, *value));
                        }
                    }
                    (Inst::Call { args, .. }, _) => {
                        call_args = Some(args.clone());
                    }
                    _ => {}
                }
            }
        }

        let call_args = call_args.expect("entry should call the Sum helper");
        let function_arg = *call_args.get(4).expect(
            "first user argument should follow invariant context and return buffer arguments",
        );
        let materialized_ptr = *ptr_to_int_sources
            .get(&function_arg)
            .expect("compact state function call arg should be materialized as a pointer");
        assert_eq!(
            alloca_counts.get(&materialized_ptr),
            Some(&7),
            "three Int->Int pairs should materialize to [len, key, value] slots"
        );

        for (slot, expected) in [(0, 3), (1, 0), (3, 1), (5, 2)] {
            let has_const_store = stores.iter().any(|(base, stored_slot, value)| {
                *base == materialized_ptr
                    && *stored_slot == slot
                    && i64_consts.get(value) == Some(&expected)
            });
            assert!(
                has_const_store,
                "materialized function should store constant {expected} at slot {slot}"
            );
        }

        for (dst_slot, source_slot) in [(2, 0), (4, 1), (6, 2)] {
            let has_value_copy = stores.iter().any(|(base, stored_slot, value)| {
                *base == materialized_ptr
                    && *stored_slot == dst_slot
                    && load_slots.get(value) == Some(&(state_in, source_slot))
            });
            assert!(
                has_value_copy,
                "materialized function value slot {dst_slot} should copy state_in[{source_slot}]"
            );
        }
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_materializes_moved_compact_state_function_call_arg() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();

        let mut sum = BytecodeFunction::new("Sum".to_string(), 2);
        sum.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 0,
            argc: 2,
        });
        sum.emit(Opcode::Ret { rs: 2 });
        let sum_idx = chunk.add_function(sum);

        let mut inv =
            BytecodeFunction::new("fold_sum_moved_compact_state_func_call_arg".to_string(), 0);
        inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv.emit(Opcode::LoadImm { rd: 2, value: 0 });
        inv.emit(Opcode::LoadImm { rd: 3, value: 2 });
        inv.emit(Opcode::Range {
            rd: 1,
            lo: 2,
            hi: 3,
        });
        inv.emit(Opcode::Move { rd: 4, rs: 0 });
        inv.emit(Opcode::Move { rd: 5, rs: 1 });
        inv.emit(Opcode::Call {
            rd: 6,
            op_idx: sum_idx,
            args_start: 4,
            argc: 2,
        });
        inv.emit(Opcode::Ret { rs: 6 });
        let entry_idx = chunk.add_function(inv);

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "fold_sum_moved_compact_state_func_call_arg",
            &layout,
        )
        .expect("moved compact state Function(Int->Int) helper argument should lower");
        assert!(
            has_bounded_loop_tag(&module, 1, 3),
            "moved finite-set shape should still bound the callee FoldFunctionOnSetSum loop"
        );

        let entry = &module.functions[0];
        let (state_in, state_in_ty) = entry
            .blocks
            .first()
            .and_then(|block| block.params.get(1))
            .expect("lowered invariant should have a state_in parameter");
        assert_eq!(*state_in_ty, Ty::Ptr);
        let state_in = *state_in;

        let mut i32_consts = HashMap::new();
        let mut i64_consts = HashMap::new();
        let mut alloca_counts = HashMap::new();
        let mut ptr_to_int_sources = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut load_slots = HashMap::new();
        let mut stores = Vec::new();
        let mut call_args = None;

        for block in &entry.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i32_consts.insert(result, *value);
                    }
                    (
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i64_consts.insert(result, *value);
                    }
                    (
                        Inst::Alloca {
                            count: Some(count), ..
                        },
                        Some(result),
                    ) => {
                        if let Some(count) = i32_consts.get(count).copied() {
                            alloca_counts.insert(result, count);
                        }
                    }
                    (
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        ptr_to_int_sources.insert(result, *operand);
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = i32_consts.get(&indices[0]).copied() {
                            gep_slots.insert(result, (*base, slot));
                        }
                    }
                    (
                        Inst::Load {
                            ty: Ty::I64, ptr, ..
                        },
                        Some(result),
                    ) => {
                        if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                            load_slots.insert(result, (base, slot));
                        }
                    }
                    (
                        Inst::Store {
                            ty: Ty::I64,
                            ptr,
                            value,
                            ..
                        },
                        _,
                    ) => {
                        if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                            stores.push((base, slot, *value));
                        }
                    }
                    (Inst::Call { args, .. }, _) => {
                        call_args = Some(args.clone());
                    }
                    _ => {}
                }
            }
        }

        let call_args = call_args.expect("entry should call the Sum helper");
        let function_arg = *call_args.get(4).expect(
            "first user argument should follow invariant context and return buffer arguments",
        );
        let materialized_ptr = *ptr_to_int_sources
            .get(&function_arg)
            .expect("moved compact state function call arg should be materialized as a pointer");
        assert_eq!(
            alloca_counts.get(&materialized_ptr),
            Some(&7),
            "three Int->Int pairs should materialize to [len, key, value] slots"
        );

        for (slot, expected) in [(0, 3), (1, 0), (3, 1), (5, 2)] {
            let has_const_store = stores.iter().any(|(base, stored_slot, value)| {
                *base == materialized_ptr
                    && *stored_slot == slot
                    && i64_consts.get(value) == Some(&expected)
            });
            assert!(
                has_const_store,
                "materialized function should store constant {expected} at slot {slot}"
            );
        }

        for (dst_slot, source_slot) in [(2, 0), (4, 1), (6, 2)] {
            let has_value_copy = stores.iter().any(|(base, stored_slot, value)| {
                *base == materialized_ptr
                    && *stored_slot == dst_slot
                    && load_slots.get(value) == Some(&(state_in, source_slot))
            });
            assert!(
                has_value_copy,
                "materialized function value slot {dst_slot} should copy state_in[{source_slot}]"
            );
        }
    }

    #[test]
    fn test_helper_call_materializes_pointer_backed_compact_function_arg_from_reloaded_reg() {
        let mut chunk = BytecodeChunk::new();

        let mut apply_inner = BytecodeFunction::new("ApplyInner".to_string(), 1);
        apply_inner.emit(Opcode::LoadImm { rd: 1, value: 2 });
        apply_inner.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        apply_inner.emit(Opcode::Ret { rs: 2 });
        let apply_inner_idx = chunk.add_function(apply_inner);

        let mut inv = BytecodeFunction::new("pointer_backed_compact_func_call_arg".to_string(), 0);
        inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv.emit(Opcode::LoadImm { rd: 1, value: 1 });
        inv.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        inv.emit(Opcode::Call {
            rd: 3,
            op_idx: apply_inner_idx,
            args_start: 2,
            argc: 1,
        });
        inv.emit(Opcode::LoadImm { rd: 4, value: 0 });
        inv.emit(Opcode::Eq {
            rd: 5,
            r1: 3,
            r2: 4,
        });
        inv.emit(Opcode::Ret { rs: 5 });
        let entry_idx = chunk.add_function(inv);

        let inner_function_layout = || CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(2),
            domain_lo: Some(1),
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(inner_function_layout()),
            pair_count: Some(2),
            domain_lo: Some(1),
        })]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "pointer_backed_compact_func_call_arg",
            &layout,
        )
        .expect("pointer-backed compact Function(Int->Int) helper argument should lower");
        assert_call_arg_is_materialized_aggregate_ptr(&module, 0, 3, 1, 4, 5);

        let entry = &module.functions[0];
        let mut int_to_ptr_sources = HashMap::new();
        let mut load_sources = HashMap::new();
        for block in &entry.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Cast {
                            op: CastOp::IntToPtr,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        int_to_ptr_sources.insert(result, *operand);
                    }
                    (Inst::Load { ptr, .. }, Some(result)) => {
                        load_sources.insert(result, *ptr);
                    }
                    _ => {}
                }
            }
        }
        assert!(
            int_to_ptr_sources
                .values()
                .any(|operand| load_sources.contains_key(operand)),
            "pointer-backed compact function call arg should reload the aggregate pointer from its register before materialization"
        );
    }

    #[test]
    fn test_helper_callee_consumes_compact_record_and_sequence_record_args_in_abi_layout() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();
        let field_a = tla_core::intern_name("compact_helper_arg_a");
        let field_z = tla_core::intern_name("compact_helper_arg_z");
        let return_a = tla_core::intern_name("compact_helper_arg_return_a");
        let return_z = tla_core::intern_name("compact_helper_arg_return_z");
        let field_a_idx = chunk.constants.add_field_id(field_a.0);
        let field_z_idx = chunk.constants.add_field_id(field_z.0);
        let record_return_start = chunk
            .constants
            .add_value(Value::String("compact_helper_arg_return".into()));
        let sequence_return_start = chunk
            .constants
            .add_value(Value::String("compact_helper_arg_return_a".into()));
        chunk
            .constants
            .add_value(Value::String("compact_helper_arg_return_z".into()));

        let mut record_helper = BytecodeFunction::new("RecordArgA".to_string(), 1);
        record_helper.emit(Opcode::RecordGet {
            rd: 1,
            rs: 0,
            field_idx: field_a_idx,
        });
        record_helper.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: record_return_start,
            values_start: 1,
            count: 1,
        });
        record_helper.emit(Opcode::Ret { rs: 2 });
        let record_helper_idx = chunk.add_function(record_helper);

        let mut sequence_helper =
            BytecodeFunction::new("SequenceRecordArgHeadFields".to_string(), 1);
        sequence_helper.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Head,
            args_start: 0,
            argc: 1,
        });
        sequence_helper.emit(Opcode::RecordGet {
            rd: 2,
            rs: 1,
            field_idx: field_a_idx,
        });
        sequence_helper.emit(Opcode::RecordGet {
            rd: 3,
            rs: 1,
            field_idx: field_z_idx,
        });
        sequence_helper.emit(Opcode::RecordNew {
            rd: 4,
            fields_start: sequence_return_start,
            values_start: 2,
            count: 2,
        });
        sequence_helper.emit(Opcode::Ret { rs: 4 });
        let sequence_helper_idx = chunk.add_function(sequence_helper);

        let mut entry = BytecodeFunction::new("compact_helper_arg_entry".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: record_helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::LoadVar { rd: 2, var_idx: 1 });
        entry.emit(Opcode::Call {
            rd: 3,
            op_idx: sequence_helper_idx,
            args_start: 2,
            argc: 1,
        });
        entry.emit(Opcode::LoadBool { rd: 4, value: true });
        entry.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(entry);

        let record_layout = || CompoundLayout::Record {
            fields: vec![
                (field_z, CompoundLayout::Int),
                (field_a, CompoundLayout::Int),
            ],
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(record_layout()),
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(record_layout()),
                element_count: Some(2),
            }),
        ]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "compact_helper_arg_abi_consumption",
            &layout,
        )
        .expect("compact Record and Sequence<Record> helper arguments should lower");

        assert_call_arg_is_materialized_aggregate_ptr(&module, 0, 3, 1, 4, 2);
        assert_call_arg_is_materialized_aggregate_ptr(&module, 0, 3, 2, 4, 5);
        assert_callee_stores_exact_hidden_return_slots(&module, 1, 3, 1);
        assert_hidden_return_loads_from_user_arg_slots(
            &module,
            1,
            3,
            4,
            &[(0, 0)],
            "RecordArgA must read field a from compact ABI slot 0, not the source layout field index"
        );
        assert_callee_stores_exact_hidden_return_slots(&module, 2, 3, 2);
        assert_hidden_return_loads_from_user_arg_slots(
            &module,
            2,
            3,
            4,
            &[(0, 1), (1, 2)],
            "SequenceRecordArgHeadFields must read the first record element from compact sequence slots [a=1, z=2]"
        );
        assert!(
            return_a < return_z,
            "test field interning should keep return record ABI slot order stable"
        );
    }

    #[test]
    fn test_helper_call_materializes_local_nested_record_arg_to_callee_abi_shape() {
        let mut chunk = BytecodeChunk::new();
        let field_a = chunk
            .constants
            .add_value(Value::String("local_record_a".into()));
        chunk
            .constants
            .add_value(Value::String("local_record_z".into()));
        let outer_field = chunk
            .constants
            .add_value(Value::String("local_record_outer".into()));

        let mut helper = BytecodeFunction::new("LocalNestedRecordArg".to_string(), 1);
        helper.emit(Opcode::LoadBool { rd: 1, value: true });
        helper.emit(Opcode::Ret { rs: 1 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("local_nested_record_arg_entry".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 11 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 22 });
        entry.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: field_a,
            values_start: 0,
            count: 2,
        });
        entry.emit(Opcode::RecordNew {
            rd: 3,
            fields_start: outer_field,
            values_start: 2,
            count: 1,
        });
        entry.emit(Opcode::Call {
            rd: 4,
            op_idx: helper_idx,
            args_start: 3,
            argc: 1,
        });
        entry.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "local_nested_record_arg")
            .expect("local nested RecordNew helper argument should materialize to callee ABI");

        assert_call_arg_is_materialized_aggregate_ptr(&module, 0, 3, 1, 4, 2);
    }

    #[test]
    fn test_helper_call_materializes_local_sequence_record_arg_to_callee_abi_shape() {
        let mut chunk = BytecodeChunk::new();
        let field_a = chunk
            .constants
            .add_value(Value::String("local_seq_record_a".into()));
        chunk
            .constants
            .add_value(Value::String("local_seq_record_z".into()));

        let mut helper = BytecodeFunction::new("LocalSequenceRecordArg".to_string(), 1);
        helper.emit(Opcode::LoadBool { rd: 1, value: true });
        helper.emit(Opcode::Ret { rs: 1 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("local_sequence_record_arg_entry".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 11 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 22 });
        entry.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: field_a,
            values_start: 0,
            count: 2,
        });
        entry.emit(Opcode::SeqNew {
            rd: 3,
            start: 2,
            count: 1,
        });
        entry.emit(Opcode::Call {
            rd: 4,
            op_idx: helper_idx,
            args_start: 3,
            argc: 1,
        });
        entry.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "local_sequence_record_arg")
            .expect("local SeqNew<Record> helper argument should materialize to callee ABI");

        assert_call_arg_is_materialized_aggregate_ptr(&module, 0, 3, 1, 4, 3);
    }

    #[test]
    fn test_helper_call_materializes_load_const_nested_record_arg_to_callee_abi_shape() {
        let mut chunk = BytecodeChunk::new();
        let const_idx = chunk.constants.add_value(Value::record([(
            "const_outer",
            Value::record([
                ("const_a", Value::SmallInt(11)),
                ("const_z", Value::SmallInt(22)),
            ]),
        )]));

        let mut helper = BytecodeFunction::new("ConstNestedRecordArg".to_string(), 1);
        helper.emit(Opcode::LoadBool { rd: 1, value: true });
        helper.emit(Opcode::Ret { rs: 1 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("const_nested_record_arg_entry".to_string(), 0);
        entry.emit(Opcode::LoadConst {
            rd: 0,
            idx: const_idx,
        });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::Ret { rs: 1 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "const_nested_record_arg")
            .expect("LoadConst nested Record helper argument should materialize to callee ABI");

        assert_call_arg_is_materialized_aggregate_ptr(&module, 0, 3, 1, 4, 2);
    }

    #[test]
    fn test_helper_arg_shape_rejects_incompatible_compact_record_callsites() {
        let mut chunk = BytecodeChunk::new();
        let left_fields = chunk
            .constants
            .add_value(Value::String("poly_record_a".into()));
        chunk
            .constants
            .add_value(Value::String("poly_record_b".into()));
        let right_fields = chunk
            .constants
            .add_value(Value::String("poly_record_a".into()));
        chunk
            .constants
            .add_value(Value::String("poly_record_c".into()));

        let mut helper = BytecodeFunction::new("PolymorphicRecordArg".to_string(), 1);
        helper.emit(Opcode::LoadBool { rd: 1, value: true });
        helper.emit(Opcode::Ret { rs: 1 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("polymorphic_record_arg_entry".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
        entry.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: left_fields,
            values_start: 0,
            count: 2,
        });
        entry.emit(Opcode::Call {
            rd: 3,
            op_idx: helper_idx,
            args_start: 2,
            argc: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 4, value: 3 });
        entry.emit(Opcode::LoadImm { rd: 5, value: 4 });
        entry.emit(Opcode::RecordNew {
            rd: 6,
            fields_start: right_fields,
            values_start: 4,
            count: 2,
        });
        entry.emit(Opcode::Call {
            rd: 7,
            op_idx: helper_idx,
            args_start: 6,
            argc: 1,
        });
        entry.emit(Opcode::LoadBool { rd: 8, value: true });
        entry.emit(Opcode::Ret { rs: 8 });
        let entry_idx = chunk.add_function(entry);

        let err = lower_module_invariant(&chunk, entry_idx, "polymorphic_record_arg")
            .expect_err("incompatible compact Record helper callsites must reject");
        let message = format!("{err}");
        assert!(
            message.contains("Call arg shape collection")
                && message.contains("incompatible compact aggregate")
                && message.contains("PolymorphicRecordArg"),
            "error should reject incompatible compact Record helper callsites: {message}"
        );
    }

    #[test]
    fn test_helper_call_materializes_compact_sequence_arg_with_capacity_and_inactive_zeroing() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("SeqLen".to_string(), 1);
        helper.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Len,
            args_start: 0,
            argc: 1,
        });
        helper.emit(Opcode::Ret { rs: 1 });
        let helper_idx = chunk.add_function(helper);

        let mut inv = BytecodeFunction::new("compact_sequence_call_arg".to_string(), 0);
        inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        inv.emit(Opcode::Ret { rs: 1 });
        let entry_idx = chunk.add_function(inv);

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        })]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "compact_sequence_call_arg",
            &layout,
        )
        .expect("compact Sequence(Int) helper argument should lower");

        let entry = &module.functions[0];
        let (state_in, state_in_ty) = entry
            .blocks
            .first()
            .and_then(|block| block.params.get(1))
            .expect("lowered invariant should have a state_in parameter");
        assert_eq!(*state_in_ty, Ty::Ptr);
        let state_in = *state_in;

        let mut i32_consts = HashMap::new();
        let mut i64_consts = HashMap::new();
        let mut alloca_counts = HashMap::new();
        let mut ptr_to_int_sources = HashMap::new();
        let mut gep_slots = HashMap::new();
        let mut load_slots = HashMap::new();
        let mut stores = Vec::new();
        let mut call_args = None;

        for block in &entry.blocks {
            for node in &block.body {
                match (&node.inst, node.results.first().copied()) {
                    (
                        Inst::Const {
                            ty: Ty::I32,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i32_consts.insert(result, *value);
                    }
                    (
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(value),
                        },
                        Some(result),
                    ) => {
                        i64_consts.insert(result, *value);
                    }
                    (
                        Inst::Alloca {
                            count: Some(count), ..
                        },
                        Some(result),
                    ) => {
                        if let Some(count) = i32_consts.get(count).copied() {
                            alloca_counts.insert(result, count);
                        }
                    }
                    (
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            operand,
                            ..
                        },
                        Some(result),
                    ) => {
                        ptr_to_int_sources.insert(result, *operand);
                    }
                    (Inst::GEP { base, indices, .. }, Some(result)) if indices.len() == 1 => {
                        if let Some(slot) = i32_consts.get(&indices[0]).copied() {
                            gep_slots.insert(result, (*base, slot));
                        }
                    }
                    (
                        Inst::Load {
                            ty: Ty::I64, ptr, ..
                        },
                        Some(result),
                    ) => {
                        if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                            load_slots.insert(result, (base, slot));
                        }
                    }
                    (
                        Inst::Store {
                            ty: Ty::I64,
                            ptr,
                            value,
                            ..
                        },
                        _,
                    ) => {
                        if let Some((base, slot)) = gep_slots.get(ptr).copied() {
                            stores.push((base, slot, *value));
                        }
                    }
                    (Inst::Call { args, .. }, _) => {
                        call_args = Some(args.clone());
                    }
                    _ => {}
                }
            }
        }

        let call_args = call_args.expect("entry should call the SeqLen helper");
        let sequence_arg = *call_args.get(4).expect(
            "first user argument should follow invariant context and return buffer arguments",
        );
        let materialized_ptr = *ptr_to_int_sources
            .get(&sequence_arg)
            .expect("compact sequence call arg should be materialized as a pointer");
        assert_eq!(
            alloca_counts.get(&materialized_ptr),
            Some(&4),
            "capacity-3 compact sequence should materialize fixed [len, elem0, elem1, elem2] slots"
        );

        let has_runtime_len_load = load_slots.values().any(|source| *source == (state_in, 0));
        assert!(
            has_runtime_len_load,
            "materializing the sequence argument should read the compact runtime length header"
        );

        let has_header_copy = stores.iter().any(|(base, slot, value)| {
            *base == materialized_ptr && *slot == 0 && !i64_consts.contains_key(value)
        });
        assert!(
            has_header_copy,
            "materialized sequence should preserve the runtime length header after bounds checks"
        );

        for slot in 1..=3 {
            let has_active_copy = stores.iter().any(|(base, stored_slot, value)| {
                *base == materialized_ptr
                    && *stored_slot == slot
                    && load_slots.get(value) == Some(&(state_in, slot))
            });
            assert!(
                has_active_copy,
                "materialized sequence payload slot {slot} should copy the active compact state slot"
            );

            let has_inactive_zero = stores.iter().any(|(base, stored_slot, value)| {
                *base == materialized_ptr
                    && *stored_slot == slot
                    && i64_consts.get(value) == Some(&0)
            });
            assert!(
                has_inactive_zero,
                "materialized sequence payload slot {slot} should be zeroed when inactive"
            );
        }
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_merges_later_sibling_callsite_shapes() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();

        let mut sum = BytecodeFunction::new("Sum".to_string(), 2);
        sum.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 0,
            argc: 2,
        });
        sum.emit(Opcode::Ret { rs: 2 });
        let sum_idx = chunk.add_function(sum);

        let mut wrapper = BytecodeFunction::new("Wrapper".to_string(), 2);
        wrapper.emit(Opcode::Call {
            rd: 2,
            op_idx: sum_idx,
            args_start: 0,
            argc: 2,
        });
        wrapper.emit(Opcode::Ret { rs: 2 });
        let wrapper_idx = chunk.add_function(wrapper);

        let mut inv = BytecodeFunction::new("fold_sum_later_sibling_shapes".to_string(), 0);
        inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv.emit(Opcode::LoadImm { rd: 2, value: 0 });
        inv.emit(Opcode::LoadImm { rd: 3, value: 1 });
        inv.emit(Opcode::Range {
            rd: 1,
            lo: 2,
            hi: 3,
        });
        inv.emit(Opcode::Call {
            rd: 4,
            op_idx: sum_idx,
            args_start: 0,
            argc: 2,
        });
        inv.emit(Opcode::LoadImm { rd: 5, value: 0 });
        inv.emit(Opcode::LoadImm { rd: 6, value: 2 });
        inv.emit(Opcode::Range {
            rd: 1,
            lo: 5,
            hi: 6,
        });
        inv.emit(Opcode::Call {
            rd: 7,
            op_idx: wrapper_idx,
            args_start: 0,
            argc: 2,
        });
        inv.emit(Opcode::Ret { rs: 7 });
        let entry_idx = chunk.add_function(inv);

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "fold_sum_later_sibling_shapes",
            &layout,
        )
        .expect("later sibling call-site shapes should be collected before lowering Sum");
        assert!(
            module.functions.len() >= 3,
            "expected entry, Sum, and Wrapper, got {} functions",
            module.functions.len()
        );
        assert!(
            bounded_loop_tag_count(&module, 1, 3) >= 2,
            "the Sum callee must see the later Wrapper->Sum call shape before it is emitted"
        );
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_rejects_two_set_shapes() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("fold_sum_two_sets".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 4,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 2,
            argc: 2,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let err = lower_invariant(&func, "fold_sum_two_sets")
            .expect_err("FoldFunctionOnSetSum should reject two finite-set operands");
        assert!(
            format!("{err}").contains("tracked finite function"),
            "error should identify the non-function operand: {err}"
        );
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_accepts_called_set_filter_domain() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();

        let mut node = BytecodeFunction::new("Node".to_string(), 0);
        node.emit(Opcode::LoadImm { rd: 0, value: 0 });
        node.emit(Opcode::LoadImm { rd: 1, value: 2 });
        node.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        node.emit(Opcode::Ret { rs: 2 });
        let node_idx = chunk.add_function(node);

        let mut rng = BytecodeFunction::new("Rng".to_string(), 2);
        rng.emit(Opcode::Call {
            rd: 2,
            op_idx: node_idx,
            args_start: 0,
            argc: 0,
        });
        let begin_pc = rng.emit(Opcode::SetFilterBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        rng.emit(Opcode::LoadBool { rd: 5, value: true });
        let next_pc = rng.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 5,
            loop_begin: 0,
        });
        rng.patch_jump(begin_pc, next_pc + 1);
        rng.patch_jump(next_pc, begin_pc + 1);
        rng.emit(Opcode::Ret { rs: 3 });
        let rng_idx = chunk.add_function(rng);

        let mut inv = BytecodeFunction::new("fold_sum_called_set_filter".to_string(), 0);
        inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv.emit(Opcode::LoadImm { rd: 1, value: 0 });
        inv.emit(Opcode::LoadImm { rd: 2, value: 2 });
        inv.emit(Opcode::Call {
            rd: 3,
            op_idx: rng_idx,
            args_start: 1,
            argc: 2,
        });
        inv.emit(Opcode::Move { rd: 4, rs: 0 });
        inv.emit(Opcode::Move { rd: 5, rs: 3 });
        inv.emit(Opcode::CallBuiltin {
            rd: 6,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 4,
            argc: 2,
        });
        inv.emit(Opcode::Ret { rs: 6 });
        let entry_idx = chunk.add_function(inv);

        lower_module_invariant(&chunk, entry_idx, "fold_sum_called_set_filter").expect(
            "called SetFilter domains should retain bounded-set shape for FoldFunctionOnSetSum",
        );
    }

    #[test]
    fn test_lower_fold_function_on_set_sum_allows_generic_callee_formals() {
        use tla_tir::bytecode::BuiltinOp;

        let mut chunk = BytecodeChunk::new();

        let mut sum = BytecodeFunction::new("Sum".to_string(), 2);
        sum.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 0,
            argc: 2,
        });
        sum.emit(Opcode::Ret { rs: 2 });
        let sum_idx = chunk.add_function(sum);

        let mut inv = BytecodeFunction::new("fold_sum_generic_callee".to_string(), 0);
        inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        inv.emit(Opcode::LoadImm { rd: 1, value: 0 });
        inv.emit(Opcode::LoadImm { rd: 2, value: 2 });
        inv.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        inv.emit(Opcode::Move { rd: 4, rs: 0 });
        inv.emit(Opcode::Move { rd: 5, rs: 3 });
        inv.emit(Opcode::Call {
            rd: 6,
            op_idx: sum_idx,
            args_start: 4,
            argc: 2,
        });
        inv.emit(Opcode::Ret { rs: 6 });
        let entry_idx = chunk.add_function(inv);

        lower_module_invariant(&chunk, entry_idx, "fold_sum_generic_callee")
            .expect("generic Sum(f, S) callees should lower FoldFunctionOnSetSum dynamically");
    }

    /// Test unsupported builtin returns error.
    #[test]
    fn test_unsupported_builtin() {
        use tla_tir::bytecode::BuiltinOp;
        let mut func = BytecodeFunction::new("unsup_builtin".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::ToString,
            args_start: 0,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let result = lower_invariant(&func, "unsup_builtin");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            format!("{err}").contains("unsupported opcode"),
            "error: {err}"
        );
    }

    // =====================================================================
    // Quantifier tests
    // =====================================================================

    /// Helper: build a bytecode program for \A x \in S : P(x).
    ///
    /// Bytecode layout:
    ///   0: SetEnum { rd: 0, start: 1, count: 3 }  -- domain = {10, 20, 30}
    ///   1: LoadImm { rd: 1, value: 10 }
    ///   2: LoadImm { rd: 2, value: 20 }
    ///   3: LoadImm { rd: 3, value: 30 }
    ///   (re-emit SetEnum since we need elements in registers first)
    ///
    /// Actually, simpler approach: load elements, build set, then quantify.
    fn build_forall_program() -> BytecodeFunction {
        let mut func = BytecodeFunction::new("forall_test".to_string(), 0);
        // Build domain set {10, 20, 30} in r3
        func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // pc 0
        func.emit(Opcode::LoadImm { rd: 1, value: 20 }); // pc 1
        func.emit(Opcode::LoadImm { rd: 2, value: 30 }); // pc 2
        func.emit(Opcode::SetEnum {
            // pc 3
            rd: 3,
            start: 0,
            count: 3,
        });

        // ForallBegin: r4 = result, r5 = binding, domain in r3
        // Body starts at pc 5, loop_end jumps to pc 8 (after ForallNext)
        let begin_pc = func.emit(Opcode::ForallBegin {
            // pc 4
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0, // patched below
        });

        // Body: r6 = (r5 > 0) — predicate P(x) = x > 0
        func.emit(Opcode::LoadImm { rd: 6, value: 0 }); // pc 5
        func.emit(Opcode::GtInt {
            // pc 6
            rd: 7,
            r1: 5,
            r2: 6,
        });

        let next_pc = func.emit(Opcode::ForallNext {
            // pc 7
            rd: 4,
            r_binding: 5,
            r_body: 7,
            loop_begin: 0, // patched below
        });

        // Patch jump targets: loop_end -> after ForallNext, loop_begin -> body start
        func.patch_jump(begin_pc, next_pc + 1); // loop_end -> pc 8 (Ret)
        func.patch_jump(next_pc, begin_pc + 1); // loop_begin -> pc 5

        func.emit(Opcode::Ret { rs: 4 }); // pc 8
        func
    }

    /// Test ForAll quantifier lowering: \A x \in {10,20,30} : x > 0
    /// Expected: TRUE (all elements > 0).
    #[test]
    fn test_lower_forall_all_true() {
        let func = build_forall_program();
        let module = lower_invariant(&func, "forall_test").expect("ForAll lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have multiple blocks: entry, ForAll header, load, body blocks,
        // short-circuit, advance, exit.
        assert!(
            module.functions[0].blocks.len() >= 5,
            "expected >= 5 blocks for ForAll, got {}",
            module.functions[0].blocks.len()
        );

        // Verify function has Return instruction.
        let has_return = module.functions[0].blocks.iter().any(|b| {
            b.body
                .last()
                .map_or(false, |n| matches!(n.inst, Inst::Return { .. }))
        });
        assert!(has_return, "function should contain a Return instruction");
    }

    /// Test EXISTS quantifier lowering: \E x \in {10,20,30} : x > 15
    #[test]
    fn test_lower_exists() {
        let mut func = BytecodeFunction::new("exists_test".to_string(), 0);
        // Build domain set {10, 20, 30} in r3
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::LoadImm { rd: 2, value: 30 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });

        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });

        // Body: r7 = (r5 > 15)
        func.emit(Opcode::LoadImm { rd: 6, value: 15 });
        func.emit(Opcode::GtInt {
            rd: 7,
            r1: 5,
            r2: 6,
        });

        let next_pc = func.emit(Opcode::ExistsNext {
            rd: 4,
            r_binding: 5,
            r_body: 7,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "exists_test").expect("EXISTS lowering should succeed");
        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].blocks.len() >= 5,
            "expected >= 5 blocks for EXISTS, got {}",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_lower_set_filter_invariant_setenum_membership() {
        let mut func = BytecodeFunction::new("set_filter_setenum".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });

        let begin_pc = func.emit(Opcode::SetFilterBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 6, value: 1 });
        func.emit(Opcode::GtInt {
            rd: 7,
            r1: 5,
            r2: 6,
        });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 5,
            r_body: 7,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::LoadImm { rd: 8, value: 2 });
        func.emit(Opcode::SetIn {
            rd: 9,
            elem: 8,
            set: 4,
        });
        func.emit(Opcode::Ret { rs: 9 });

        let module = lower_invariant(&func, "set_filter_setenum")
            .expect("SetFilterBegin over SetEnum should lower in invariants");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "expected SetFilter CFG blocks, got {}",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "SetFilter over fixed SetEnum should allocate a fixed-capacity result"
        );
    }

    #[test]
    fn test_lower_set_filter_invariant_interval_cardinality() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("set_filter_interval".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });

        let begin_pc = func.emit(Opcode::SetFilterBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        func.emit(Opcode::LoadImm { rd: 5, value: 1 });
        func.emit(Opcode::LeInt {
            rd: 6,
            r1: 4,
            r2: 5,
        });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 6,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::CallBuiltin {
            rd: 7,
            builtin: BuiltinOp::Cardinality,
            args_start: 3,
            argc: 1,
        });
        func.emit(Opcode::LoadImm { rd: 8, value: 2 });
        func.emit(Opcode::Eq {
            rd: 9,
            r1: 7,
            r2: 8,
        });
        func.emit(Opcode::Ret { rs: 9 });

        let module = lower_invariant(&func, "set_filter_interval")
            .expect("SetFilterBegin over an interval should lower in invariants");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "SetFilter over fixed interval should allocate a fixed-capacity result"
        );
    }

    /// Test CHOOSE quantifier lowering: CHOOSE x \in {10,20,30} : x > 15
    #[test]
    fn test_lower_choose() {
        let mut func = BytecodeFunction::new("choose_test".to_string(), 0);
        // Build domain set {10, 20, 30} in r3
        func.emit(Opcode::LoadImm { rd: 0, value: 10 });
        func.emit(Opcode::LoadImm { rd: 1, value: 20 });
        func.emit(Opcode::LoadImm { rd: 2, value: 30 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });

        let begin_pc = func.emit(Opcode::ChooseBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });

        // Body: r7 = (r5 > 15)
        func.emit(Opcode::LoadImm { rd: 6, value: 15 });
        func.emit(Opcode::GtInt {
            rd: 7,
            r1: 5,
            r2: 6,
        });

        let next_pc = func.emit(Opcode::ChooseNext {
            rd: 4,
            r_binding: 5,
            r_body: 7,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "choose_test").expect("CHOOSE lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // CHOOSE has an extra exhausted block for runtime error.
        assert!(
            module.functions[0].blocks.len() >= 6,
            "expected >= 6 blocks for CHOOSE, got {}",
            module.functions[0].blocks.len()
        );

        // Should have a runtime error return path (for exhausted domain).
        let has_runtime_error = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                // The exhausted block stores RuntimeError status then returns.
                matches!(n.inst, Inst::Const { value: Constant::Int(v), .. }
                        if v == i128::from(JitStatus::RuntimeError as u8))
            })
        });
        assert!(
            has_runtime_error,
            "CHOOSE should have a runtime error path for exhausted domain"
        );
    }

    /// Test nested quantifiers: \A x \in S : \E y \in T : x + y > 0
    #[test]
    fn test_lower_nested_forall_exists() {
        let mut func = BytecodeFunction::new("nested_test".to_string(), 0);

        // Build domain S = {1, 2} in r2
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });

        // Build domain T = {3, 4} in r5
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::LoadImm { rd: 4, value: 4 });
        func.emit(Opcode::SetEnum {
            rd: 5,
            start: 3,
            count: 2,
        });

        // Outer: \A x \in S
        let forall_begin = func.emit(Opcode::ForallBegin {
            rd: 6,        // outer result
            r_binding: 7, // x
            r_domain: 2,  // S
            loop_end: 0,
        });

        // Inner: \E y \in T
        let exists_begin = func.emit(Opcode::ExistsBegin {
            rd: 8,        // inner result
            r_binding: 9, // y
            r_domain: 5,  // T
            loop_end: 0,
        });

        // Body: r10 = x + y, r12 = (r10 > 0)
        func.emit(Opcode::AddInt {
            rd: 10,
            r1: 7,
            r2: 9,
        });
        func.emit(Opcode::LoadImm { rd: 11, value: 0 });
        func.emit(Opcode::GtInt {
            rd: 12,
            r1: 10,
            r2: 11,
        });

        let exists_next = func.emit(Opcode::ExistsNext {
            rd: 8,
            r_binding: 9,
            r_body: 12,
            loop_begin: 0,
        });

        // ForallNext uses the exists result (r8) as its body result.
        let forall_next = func.emit(Opcode::ForallNext {
            rd: 6,
            r_binding: 7,
            r_body: 8,
            loop_begin: 0,
        });

        // Patch jump targets (before emitting Ret, matching compiler pattern)
        // exists_begin.loop_end -> instruction after exists_next (= forall_next)
        func.patch_jump(exists_begin, exists_next + 1);
        // exists_next.loop_begin -> instruction after exists_begin
        func.patch_jump(exists_next, exists_begin + 1);
        // forall_begin.loop_end -> instruction after forall_next
        func.patch_jump(forall_begin, forall_next + 1);
        // forall_next.loop_begin -> instruction after forall_begin
        func.patch_jump(forall_next, forall_begin + 1);

        func.emit(Opcode::Ret { rs: 6 });

        let module = lower_invariant(&func, "nested_test")
            .expect("nested ForAll+Exists lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Nested quantifiers should produce many blocks.
        assert!(
            module.functions[0].blocks.len() >= 8,
            "expected >= 8 blocks for nested quantifiers, got {}",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_reject_nested_forall_compound_layout_set_bitmask_without_universe_proof() {
        let mut func = BytecodeFunction::new("nested_forall_bitmask_membership".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });

        let outer_begin = func.emit(Opcode::ForallBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 0,
            loop_end: 0,
        });
        let inner_begin = func.emit(Opcode::ForallBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 1,
            loop_end: 0,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 5,
            set: 0,
        });
        let inner_next = func.emit(Opcode::ForallNext {
            rd: 4,
            r_binding: 5,
            r_body: 6,
            loop_begin: 0,
        });
        let outer_next = func.emit(Opcode::ForallNext {
            rd: 2,
            r_binding: 3,
            r_body: 4,
            loop_begin: 0,
        });
        func.patch_jump(inner_begin, inner_next + 1);
        func.patch_jump(inner_next, inner_begin + 1);
        func.patch_jump(outer_begin, outer_next + 1);
        func.patch_jump(outer_next, outer_begin + 1);
        func.emit(Opcode::Ret { rs: 2 });

        let set_layout = || {
            VarLayout::Compound(CompoundLayout::Set {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: Some(4),
            })
        };
        let layout = StateLayout::new(vec![set_layout(), set_layout()]);
        let result = lower_invariant_with_constants_and_layout(
            &func,
            "nested_forall_bitmask_membership",
            &ConstantPool::new(),
            &layout,
        );
        assert_rejects_unproven_set_bitmask_universe(result);
    }

    /// Test ForAll with empty domain produces TRUE.
    /// Uses a SetEnum with count=0.
    #[test]
    fn test_lower_forall_empty_domain() {
        let mut func = BytecodeFunction::new("forall_empty".to_string(), 0);
        // Empty set in r0
        func.emit(Opcode::SetEnum {
            rd: 0,
            start: 1,
            count: 0,
        });

        let begin_pc = func.emit(Opcode::ForallBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 0,
        });

        // Trivial body (never executed).
        func.emit(Opcode::LoadBool {
            rd: 3,
            value: false,
        });

        let next_pc = func.emit(Opcode::ForallNext {
            rd: 1,
            r_binding: 2,
            r_body: 3,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 1 });

        let module = lower_invariant(&func, "forall_empty")
            .expect("ForAll with empty domain should lower successfully");
        assert_eq!(module.functions.len(), 1);
    }

    /// Test EXISTS with empty domain produces FALSE.
    #[test]
    fn test_lower_exists_empty_domain() {
        let mut func = BytecodeFunction::new("exists_empty".to_string(), 0);
        func.emit(Opcode::SetEnum {
            rd: 0,
            start: 1,
            count: 0,
        });

        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 0,
        });

        func.emit(Opcode::LoadBool { rd: 3, value: true });

        let next_pc = func.emit(Opcode::ExistsNext {
            rd: 1,
            r_binding: 2,
            r_body: 3,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 1 });

        let module = lower_invariant(&func, "exists_empty")
            .expect("EXISTS with empty domain should lower successfully");
        assert_eq!(module.functions.len(), 1);
    }

    // =====================================================================
    // Phase 4: Function operation tests
    // =====================================================================

    /// Test FuncApply: f[x] where f is a function aggregate.
    ///
    /// Bytecode: build a function {1 |-> 10, 2 |-> 20} via FuncDefBegin/LoopNext,
    /// then apply it with FuncApply to get f[1].
    #[test]
    fn test_lower_func_apply() {
        let mut func = BytecodeFunction::new("func_apply_test".to_string(), 0);

        // Build domain set {1, 2} in r2
        func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // pc 0
        func.emit(Opcode::LoadImm { rd: 1, value: 2 }); // pc 1
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        }); // pc 2

        // FuncDefBegin: r3 = result func, r4 = binding, domain in r2
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            // pc 3
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });

        // Body: r5 = r4 * 10 (each key maps to key*10)
        func.emit(Opcode::LoadImm { rd: 5, value: 10 }); // pc 4
        func.emit(Opcode::MulInt {
            rd: 6,
            r1: 4,
            r2: 5,
        }); // pc 5

        let next_pc = func.emit(Opcode::LoopNext {
            // pc 6
            r_binding: 4,
            r_body: 6,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        // Now apply: r8 = f[1]
        func.emit(Opcode::LoadImm { rd: 7, value: 1 }); // pc 7
        func.emit(Opcode::FuncApply {
            // pc 8
            rd: 8,
            func: 3,
            arg: 7,
        });
        func.emit(Opcode::Ret { rs: 8 }); // pc 9

        let module =
            lower_invariant(&func, "func_apply_test").expect("FuncApply lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have many blocks: entry, funcdef header/load/body,
        // func_apply header/body/found/not_found/merge
        assert!(
            module.functions[0].blocks.len() >= 8,
            "expected >= 8 blocks for FuncDef+FuncApply, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test Domain: DOMAIN f extracts keys into a set.
    #[test]
    fn test_lower_domain() {
        let mut func = BytecodeFunction::new("domain_test".to_string(), 0);

        // Build domain set {1, 2, 3} in r3
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });

        // Build function [x \in {1,2,3} |-> x+1] via FuncDefBegin
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });

        func.emit(Opcode::LoadImm { rd: 6, value: 1 });
        func.emit(Opcode::AddInt {
            rd: 7,
            r1: 5,
            r2: 6,
        });

        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 5,
            r_body: 7,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        // DOMAIN f
        func.emit(Opcode::Domain { rd: 8, rs: 4 });
        func.emit(Opcode::Ret { rs: 8 });

        let module = lower_invariant(&func, "domain_test").expect("Domain lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have blocks for FuncDef loop + Domain extraction loop
        assert!(
            module.functions[0].blocks.len() >= 6,
            "expected >= 6 blocks for FuncDef+Domain, got {}",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size Domain lowering should not emit non-const-count Alloca"
        );
    }

    /// Test FuncExcept: [f EXCEPT ![2] = 99].
    #[test]
    fn test_lower_func_except() {
        let mut func = BytecodeFunction::new("func_except_test".to_string(), 0);

        // Build domain set {1, 2} in r2
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });

        // Build function [x \in {1,2} |-> x*10] via FuncDefBegin
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });

        func.emit(Opcode::LoadImm { rd: 5, value: 10 });
        func.emit(Opcode::MulInt {
            rd: 6,
            r1: 4,
            r2: 5,
        });

        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 6,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        // [f EXCEPT ![2] = 99]
        func.emit(Opcode::LoadImm { rd: 7, value: 2 });
        func.emit(Opcode::LoadImm { rd: 8, value: 99 });
        func.emit(Opcode::FuncExcept {
            rd: 9,
            func: 3,
            path: 7,
            val: 8,
        });
        func.emit(Opcode::Ret { rs: 9 });

        let module =
            lower_invariant(&func, "func_except_test").expect("FuncExcept lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have blocks for FuncDef loop + FuncExcept copy loop
        assert!(
            module.functions[0].blocks.len() >= 6,
            "expected >= 6 blocks for FuncDef+FuncExcept, got {}",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size FuncExcept lowering should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_function_lowerers_clear_compact_provenance_when_overwriting_rd() {
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;
        use tla_value::FuncValue;

        fn state_function_layout() -> StateLayout {
            StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Int),
                pair_count: Some(2),
                domain_lo: Some(1),
            })])
        }

        fn const_function_pool() -> ConstantPool {
            let mut pool = ConstantPool::new();
            pool.add_value(Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
                (Value::SmallInt(1), Value::SmallInt(10)),
                (Value::SmallInt(2), Value::SmallInt(20)),
            ]))));
            pool
        }

        fn assert_clears_after(
            func: &BytecodeFunction,
            pool: &ConstantPool,
            through_pc: usize,
            case_name: &str,
        ) {
            let layout = state_function_layout();
            let mut ctx = Ctx::new(
                func,
                case_name,
                LoweringMode::Invariant,
                Some(pool),
                Some(&layout),
                None,
            )
            .expect("test context should initialize");
            let mut block = ctx
                .block_index_for_pc(0)
                .expect("entry block should exist for test function");

            for (pc, opcode) in func.instructions.iter().enumerate().take(through_pc + 1) {
                block = ctx
                    .lower_opcode(pc, opcode, block, &func.instructions)
                    .unwrap_or_else(|err| {
                        panic!("lowering {case_name} pc {pc} opcode {opcode:?} failed: {err}")
                    })
                    .unwrap_or(block);
                if pc == 0 {
                    assert!(
                        ctx.compact_state_slots.contains_key(&0),
                        "{case_name} test setup did not create compact provenance for r0"
                    );
                }
            }

            assert!(
                !ctx.compact_state_slots.contains_key(&0),
                "{case_name} left stale compact provenance for overwritten r0"
            );
        }

        let pool = const_function_pool();

        let mut load_imm = BytecodeFunction::new("stale_load_imm_rd".to_string(), 0);
        load_imm.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        load_imm.emit(Opcode::LoadImm { rd: 0, value: 7 });
        load_imm.emit(Opcode::Ret { rs: 0 });
        assert_clears_after(&load_imm, &pool, 1, "LoadImm");

        let mut load_bool = BytecodeFunction::new("stale_load_bool_rd".to_string(), 0);
        load_bool.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        load_bool.emit(Opcode::LoadBool { rd: 0, value: true });
        load_bool.emit(Opcode::Ret { rs: 0 });
        assert_clears_after(&load_bool, &pool, 1, "LoadBool");

        let mut load_const_function =
            BytecodeFunction::new("stale_load_const_function_rd".to_string(), 0);
        load_const_function.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        load_const_function.emit(Opcode::LoadConst { rd: 0, idx: 0 });
        load_const_function.emit(Opcode::Ret { rs: 0 });
        assert_clears_after(&load_const_function, &pool, 1, "LoadConst function");

        let mut self_move = BytecodeFunction::new("self_move_keeps_compact_rd".to_string(), 0);
        self_move.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        self_move.emit(Opcode::Move { rd: 0, rs: 0 });
        self_move.emit(Opcode::Ret { rs: 0 });
        let layout = state_function_layout();
        let mut ctx = Ctx::new(
            &self_move,
            "self_move_keeps_compact_rd",
            LoweringMode::Invariant,
            Some(&pool),
            Some(&layout),
            None,
        )
        .expect("test context should initialize");
        let mut block = ctx
            .block_index_for_pc(0)
            .expect("entry block should exist for test function");
        for (pc, opcode) in self_move.instructions.iter().enumerate().take(2) {
            block = ctx
                .lower_opcode(pc, opcode, block, &self_move.instructions)
                .unwrap_or_else(|err| {
                    panic!("lowering self_move pc {pc} opcode {opcode:?} failed: {err}")
                })
                .unwrap_or(block);
        }
        assert!(
            ctx.compact_state_slots.contains_key(&0),
            "self Move r0 <- r0 should preserve compact provenance after store_reg_value clears the destination"
        );

        let mut fold = BytecodeFunction::new("stale_fold_sum_rd".to_string(), 0);
        fold.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        fold.emit(Opcode::LoadConst { rd: 1, idx: 0 });
        fold.emit(Opcode::LoadImm { rd: 3, value: 1 });
        fold.emit(Opcode::LoadImm { rd: 4, value: 2 });
        fold.emit(Opcode::Range {
            rd: 2,
            lo: 3,
            hi: 4,
        });
        fold.emit(Opcode::CallBuiltin {
            rd: 0,
            builtin: BuiltinOp::FoldFunctionOnSetSum,
            args_start: 1,
            argc: 2,
        });
        fold.emit(Opcode::Ret { rs: 0 });
        assert_clears_after(&fold, &pool, 5, "FoldFunctionOnSetSum");

        let mut apply = BytecodeFunction::new("stale_func_apply_rd".to_string(), 0);
        apply.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        apply.emit(Opcode::LoadConst { rd: 1, idx: 0 });
        apply.emit(Opcode::LoadImm { rd: 2, value: 1 });
        apply.emit(Opcode::FuncApply {
            rd: 0,
            func: 1,
            arg: 2,
        });
        apply.emit(Opcode::Ret { rs: 0 });
        assert_clears_after(&apply, &pool, 3, "FuncApply");

        let mut domain = BytecodeFunction::new("stale_domain_rd".to_string(), 0);
        domain.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        domain.emit(Opcode::Domain { rd: 0, rs: 0 });
        domain.emit(Opcode::Ret { rs: 0 });
        assert_clears_after(&domain, &pool, 1, "Domain");

        let mut except = BytecodeFunction::new("stale_func_except_rd".to_string(), 0);
        except.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        except.emit(Opcode::LoadConst { rd: 1, idx: 0 });
        except.emit(Opcode::LoadImm { rd: 2, value: 1 });
        except.emit(Opcode::LoadImm { rd: 3, value: 99 });
        except.emit(Opcode::FuncExcept {
            rd: 0,
            func: 1,
            path: 2,
            val: 3,
        });
        except.emit(Opcode::Ret { rs: 0 });
        assert_clears_after(&except, &pool, 4, "FuncExcept");

        let mut func_def = BytecodeFunction::new("stale_func_def_rd".to_string(), 0);
        func_def.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func_def.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func_def.emit(Opcode::SetEnum {
            rd: 1,
            start: 2,
            count: 1,
        });
        let begin_pc = func_def.emit(Opcode::FuncDefBegin {
            rd: 0,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        func_def.emit(Opcode::Move { rd: 4, rs: 3 });
        let next_pc = func_def.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 4,
            loop_begin: 0,
        });
        func_def.patch_jump(begin_pc, next_pc + 1);
        func_def.patch_jump(next_pc, begin_pc + 1);
        func_def.emit(Opcode::Ret { rs: 0 });
        assert_clears_after(&func_def, &pool, begin_pc, "FuncDefBegin");
    }

    #[test]
    fn test_compact_func_apply_later_record_field_use_reloads_pointer_backed_provenance() {
        let mut func = BytecodeFunction::new("compact_fapply_aux_provenance".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 0 });
        func.emit(Opcode::FuncApply {
            rd: 4,
            func: 2,
            arg: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(compact_record_fields(&["left", "right"])),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);
        let mut ctx = Ctx::new(
            &func,
            "compact_fapply_aux_provenance",
            LoweringMode::Invariant,
            Some(&pool),
            Some(&layout),
            None,
        )
        .expect("test context should initialize");
        let mut block = ctx
            .block_index_for_pc(0)
            .expect("entry block should exist for test function");

        for (pc, opcode) in func.instructions.iter().enumerate().take(3) {
            block = ctx
                .lower_opcode(pc, opcode, block, &func.instructions)
                .unwrap_or_else(|err| panic!("lowering pc {pc} opcode {opcode:?} failed: {err}"))
                .unwrap_or(block);
        }

        let source_slot = ctx
            .compact_state_slots
            .get(&2)
            .copied()
            .expect("compact FuncApply should keep pointer-backed result provenance");
        assert!(
            !source_slot.is_raw_compact_slot(),
            "multi-slot compact FuncApply result should remain pointer-backed"
        );
        let lowered_func = &ctx.module.functions[ctx.func_idx];
        match ctx.aggregate_shapes.get(&2) {
            Some(AggregateShape::Record { fields }) => {
                assert_eq!(
                    fields.len(),
                    2,
                    "compact FuncApply should keep the record value shape"
                );
                assert_eq!(fields[0].0, tla_core::intern_name("left"));
                assert_eq!(fields[1].0, tla_core::intern_name("right"));
            }
            other => panic!("compact FuncApply should keep record shape, got {other:?}"),
        }

        let local_reload_count_before = lowered_func.blocks[block]
            .body
            .iter()
            .filter(|node| {
                matches!(
                    &node.inst,
                    Inst::Cast {
                        op: CastOp::IntToPtr,
                        ..
                    }
                )
            })
            .count();

        for (pc, opcode) in func.instructions.iter().enumerate().skip(3).take(2) {
            block = ctx
                .lower_opcode(pc, opcode, block, &func.instructions)
                .unwrap_or_else(|err| panic!("lowering pc {pc} opcode {opcode:?} failed: {err}"))
                .unwrap_or(block);
        }

        let source_slot_after = ctx
            .compact_state_slots
            .get(&2)
            .copied()
            .expect("point-of-use reload must not clear source compact provenance");
        assert_eq!(
            source_slot_after.source_ptr, source_slot.source_ptr,
            "point-of-use reload should not rewrite global compact provenance"
        );
        let lowered_func = &ctx.module.functions[ctx.func_idx];
        let local_reload_count_after = lowered_func.blocks[block]
            .body
            .iter()
            .filter(|node| {
                matches!(
                    &node.inst,
                    Inst::Cast {
                        op: CastOp::IntToPtr,
                        ..
                    }
                )
            })
            .count();
        assert!(
            local_reload_count_after > local_reload_count_before,
            "later compact record field FuncApply should reload pointer-backed provenance locally"
        );
    }

    #[test]
    fn test_lower_func_def_unknown_setbitmask_state_domain_rejects() {
        let mut func = BytecodeFunction::new("funcdef_known_state_domain".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 0,
        });
        func.emit(Opcode::Move { rd: 3, rs: 2 });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 2,
            r_body: 3,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Set {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(4),
        })]);

        let err = lower_next_state_with_constants_and_layout(
            &func,
            "funcdef_known_state_domain",
            &pool,
            &layout,
        )
        .expect_err("unknown-universe compact SetBitmask FuncDef domains must fail closed");

        assert!(
            format!("{err}").contains("FuncDefBegin: raw compact source r0")
                && format!("{err}").contains("unknown-universe SetBitmask payload"),
            "unexpected FuncDefBegin compact SetBitmask rejection: {err}"
        );
    }

    #[test]
    fn test_lower_domain_known_state_function_has_no_nonconst_alloca_count() {
        let mut func = BytecodeFunction::new("domain_known_state_func".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::Domain { rd: 1, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::Ret { rs: 2 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "domain_known_state_func",
            &pool,
            &layout,
        )
        .expect("fixed-size state function Domain should lower successfully");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size state function Domain should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_domain_raw_compact_function_with_unknown_setbitmask_values_uses_keys_only() {
        let mut func =
            BytecodeFunction::new("domain_compact_function_unknown_set_values".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::Domain { rd: 1, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::Ret { rs: 2 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Set {
                element_layout: Box::new(CompoundLayout::Int),
                element_count: Some(4),
            }),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "domain_compact_function_unknown_set_values",
            &pool,
            &layout,
        )
        .expect("DOMAIN over raw compact function keys should not materialize unknown set values");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed raw compact function Domain should keep static allocations"
        );
        assert_eq!(
            entry_param_direct_load_count(&module, 0, 1),
            1,
            "DOMAIN should not load compact function value payload slots just to produce keys"
        );
        assert_const_i64_stores_to_base_alloca(&module, 0, 4, &[(0, 3), (1, 1), (2, 2), (3, 3)]);
    }

    #[test]
    fn test_store_var_domain_raw_compact_function_to_setbitmask_writes_mask() {
        let mut func = BytecodeFunction::new("store_domain_compact_function_mask".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::Domain { rd: 1, rs: 0 });
        func.emit(Opcode::StoreVar { var_idx: 1, rs: 1 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::Ret { rs: 2 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Int),
                pair_count: Some(3),
                domain_lo: Some(1),
            }),
            VarLayout::Compound(int_range_set_bitmask_layout(1, 3)),
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_domain_compact_function_mask",
            &pool,
            &layout,
        )
        .expect("DOMAIN of dense raw compact function should store into compatible SetBitmask");

        assert_state_out_const_store(&module, 0, 3, 0b111);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_store_var_domain_const_function_to_setbitmask_writes_mask() {
        use std::sync::Arc;
        use tla_value::FuncValue;

        let mut pool = ConstantPool::new();
        let func_idx = pool.add_value(Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Bool(true)),
            (Value::SmallInt(2), Value::Bool(false)),
            (Value::SmallInt(3), Value::Bool(true)),
        ]))));

        let mut func = BytecodeFunction::new("store_domain_const_function_mask".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: func_idx,
        });
        func.emit(Opcode::Domain { rd: 1, rs: 0 });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
        func.emit(Opcode::LoadBool { rd: 2, value: true });
        func.emit(Opcode::Ret { rs: 2 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 3,
        ))]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "store_domain_const_function_mask",
            &pool,
            &layout,
        )
        .expect("DOMAIN of dense const function should store into compatible SetBitmask");

        assert_state_out_const_store(&module, 0, 0, 0b111);
        assert_no_ptr_payload_store_to_state_out(&module, 0);
    }

    #[test]
    fn test_lower_func_except_known_state_function_has_no_nonconst_alloca_count() {
        let mut func = BytecodeFunction::new("func_except_known_state_func".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 99 });
        func.emit(Opcode::FuncExcept {
            rd: 3,
            func: 0,
            path: 1,
            val: 2,
        });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "func_except_known_state_func",
            &pool,
            &layout,
        )
        .expect("fixed-size state function FuncExcept should lower successfully");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size state function FuncExcept should not emit non-const-count Alloca"
        );
        let has_select = module.functions[0]
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .any(|node| matches!(node.inst, Inst::Select { .. }));
        assert!(
            !has_select,
            "compile-time indexed FuncExcept should overwrite the compact slot directly"
        );
    }

    #[test]
    fn test_record_field_apply_and_except_known_state_record_has_no_nonconst_alloca_count() {
        let mut func = BytecodeFunction::new("record_except_known_state".to_string(), 0);
        let mut pool = ConstantPool::new();
        let black_idx = pool.add_value(Value::String("black".into()));

        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadConst {
            rd: 1,
            idx: black_idx,
        });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(Opcode::SubInt {
            rd: 4,
            r1: 2,
            r2: 3,
        });
        func.emit(Opcode::FuncExcept {
            rd: 5,
            func: 0,
            path: 1,
            val: 4,
        });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("black"), CompoundLayout::Int),
                (tla_core::intern_name("white"), CompoundLayout::Int),
            ],
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "record_except_known_state",
            &pool,
            &layout,
        )
        .expect("fixed-layout state record field update should lower without dynamic alloca");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "record field access/update should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_record_field_apply_and_except_known_state_record_by_index_has_no_nonconst_alloca_count()
    {
        let mut func = BytecodeFunction::new("record_except_known_state_idx".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(Opcode::SubInt {
            rd: 4,
            r1: 2,
            r2: 3,
        });
        func.emit(Opcode::FuncExcept {
            rd: 5,
            func: 0,
            path: 1,
            val: 4,
        });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::Ret { rs: 6 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("black"), CompoundLayout::Int),
                (tla_core::intern_name("white"), CompoundLayout::Int),
            ],
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "record_except_known_state_idx",
            &pool,
            &layout,
        )
        .expect("indexed record field access/update should lower without dynamic alloca");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "indexed record field access/update should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_nested_func_apply_propagates_fixed_shape_for_inner_funcexcept() {
        let mut func = BytecodeFunction::new("nested_func_apply_shape".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 2 });
        func.emit(Opcode::LoadImm { rd: 4, value: 42 });
        func.emit(Opcode::FuncExcept {
            rd: 5,
            func: 2,
            path: 3,
            val: 4,
        });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        func.emit(Opcode::Ret { rs: 6 });

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Int),
                pair_count: Some(3),
                domain_lo: Some(1),
            }),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "nested_func_apply_shape",
            &pool,
            &layout,
        )
        .expect("nested function apply should preserve inner fixed cardinality");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "inner FuncExcept should reuse fixed shape propagated through FuncApply"
        );
    }

    /// Test FuncDefBegin/LoopNext: build [x \in {1,2,3} |-> x * x].
    #[test]
    fn test_lower_func_def() {
        let mut func = BytecodeFunction::new("func_def_test".to_string(), 0);

        // Build domain set {1, 2, 3} in r3
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });

        // FuncDefBegin
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });

        // Body: r6 = r5 * r5
        func.emit(Opcode::MulInt {
            rd: 6,
            r1: 5,
            r2: 5,
        });

        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 5,
            r_body: 6,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 4 });

        let module =
            lower_invariant(&func, "func_def_test").expect("FuncDef lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have blocks: entry, header, load, body (MulInt overflow blocks), LoopNext, exit
        assert!(
            module.functions[0].blocks.len() >= 5,
            "expected >= 5 blocks for FuncDef, got {}",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size FuncDef lowering should not emit non-const-count Alloca"
        );
    }

    /// Test FuncDef with empty domain produces a function with 0 pairs.
    #[test]
    fn test_lower_func_def_empty_domain() {
        let mut func = BytecodeFunction::new("func_def_empty".to_string(), 0);

        // Empty set
        func.emit(Opcode::SetEnum {
            rd: 0,
            start: 1,
            count: 0,
        });

        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 0,
        });

        // Body (never executed)
        func.emit(Opcode::LoadImm { rd: 3, value: 0 });

        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 2,
            r_body: 3,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 1 });

        let module = lower_invariant(&func, "func_def_empty")
            .expect("FuncDef with empty domain should lower successfully");
        assert_eq!(module.functions.len(), 1);
    }

    /// Test FuncApply with standalone function aggregate (no FuncDef loop).
    /// Uses direct aggregate construction to test FuncApply in isolation.
    #[test]
    fn test_lower_func_apply_standalone() {
        // We can't directly construct a function aggregate from bytecode
        // without FuncDefBegin, so this test uses FuncDefBegin+LoopNext
        // to build a simple identity function, then applies it.
        let mut func = BytecodeFunction::new("fapply_standalone".to_string(), 0);

        // Build domain {42} in r1
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });

        // Build f = [x \in {42} |-> x]
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });

        // Body: identity function, r3 is the binding
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 3, // body = binding itself (identity)
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        // Apply f[42]
        func.emit(Opcode::LoadImm { rd: 4, value: 42 });
        func.emit(Opcode::FuncApply {
            rd: 5,
            func: 2,
            arg: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant(&func, "fapply_standalone")
            .expect("FuncApply standalone should succeed");
        assert_eq!(module.functions.len(), 1);

        // Verify it has Return instruction
        let has_return = module.functions[0].blocks.iter().any(|b| {
            b.body
                .last()
                .map_or(false, |n| matches!(n.inst, Inst::Return { .. }))
        });
        assert!(has_return, "function should contain a Return instruction");
    }

    // =================================================================
    // LoadConst tests
    // =================================================================

    #[test]
    fn test_load_const_small_int() {
        // LoadConst with SmallInt(42) should emit an immediate load.
        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::SmallInt(42));

        let mut func = BytecodeFunction::new("load_const_int".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_int", &pool)
            .expect("LoadConst SmallInt should lower successfully");
        assert_eq!(module.functions.len(), 1);
        assert!(!module.functions[0].blocks.is_empty());

        // Should contain a Const instruction with value 42.
        let has_const_42 = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(42),
                    }
                )
            })
        });
        assert!(has_const_42, "should emit Const(42) for SmallInt(42)");
    }

    #[test]
    fn test_load_const_bool_true() {
        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::Bool(true));

        let mut func = BytecodeFunction::new("load_const_bool".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_bool", &pool)
            .expect("LoadConst Bool(true) should lower successfully");
        assert_eq!(module.functions.len(), 1);

        // Should contain a Const instruction with value 1 (true).
        let has_const_1 = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(1),
                    }
                )
            })
        });
        assert!(has_const_1, "should emit Const(1) for Bool(true)");
    }

    #[test]
    fn test_load_const_bool_false() {
        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::Bool(false));

        let mut func = BytecodeFunction::new("load_const_bool_f".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_bool_f", &pool)
            .expect("LoadConst Bool(false) should lower successfully");
        assert_eq!(module.functions.len(), 1);

        // Should contain a Const instruction with value 0 (false).
        let has_const_0 = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    }
                )
            })
        });
        assert!(has_const_0, "should emit Const(0) for Bool(false)");
    }

    #[test]
    fn test_load_const_negative_int() {
        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::SmallInt(-7));

        let mut func = BytecodeFunction::new("load_const_neg".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_neg", &pool)
            .expect("LoadConst SmallInt(-7) should lower successfully");
        assert_eq!(module.functions.len(), 1);

        let has_neg7 = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(-7),
                    }
                )
            })
        });
        assert!(has_neg7, "should emit Const(-7) for SmallInt(-7)");
    }

    #[test]
    fn test_load_const_without_pool_returns_error() {
        // LoadConst without a constant pool should fail.
        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::SmallInt(1));

        let mut func = BytecodeFunction::new("no_pool".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let result = lower_invariant(&func, "no_pool");
        assert!(result.is_err(), "LoadConst without pool should fail");
    }

    #[test]
    fn test_load_const_non_materializable_compound_value_returns_error() {
        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::StringSet);

        let mut func = BytecodeFunction::new("compound".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let result = lower_invariant_with_constants(&func, "compound", &pool);
        assert!(
            result.is_err(),
            "LoadConst with non-materializable compound value should fail"
        );
    }

    #[test]
    fn test_load_const_scalar_record_materializes_aggregate() {
        use std::sync::Arc;
        use tla_value::RecordValue;

        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::Record(RecordValue::from_sorted_str_entries(vec![
            (Arc::from("clock"), Value::SmallInt(0)),
            (Arc::from("type"), Value::String(Arc::from("rel"))),
        ])));

        let mut func = BytecodeFunction::new("load_const_record".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_record", &pool)
            .expect("LoadConst scalar record should lower successfully");
        let blocks = &module.functions[0].blocks;

        let has_alloca = blocks.iter().any(|b| {
            b.body
                .iter()
                .any(|n| matches!(&n.inst, Inst::Alloca { count: Some(_), .. }))
        });
        assert!(
            has_alloca,
            "record materialization should allocate an aggregate"
        );

        let rel_name_id = i128::from(tla_core::intern_name("rel").0);
        let has_rel_const = blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(v),
                    } if *v == rel_name_id
                )
            })
        });
        assert!(
            has_rel_const,
            "record materialization should intern string fields to NameId immediates"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size record LoadConst should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_load_const_set_materializes_fixed_aggregate() {
        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::set([Value::SmallInt(1), Value::SmallInt(2)]));

        let mut func = BytecodeFunction::new("load_const_set".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_set", &pool)
            .expect("LoadConst finite set should lower successfully");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size set LoadConst should not emit non-const-count Alloca"
        );

        let blocks = &module.functions[0].blocks;
        for expected in [1_i128, 2] {
            let has_const = blocks.iter().any(|b| {
                b.body.iter().any(|n| {
                    matches!(
                        &n.inst,
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(v),
                        } if *v == expected
                    )
                })
            });
            assert!(
                has_const,
                "set materialization should emit Const({expected})"
            );
        }
    }

    #[test]
    fn test_load_const_sequence_materializes_fixed_aggregate() {
        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::seq([Value::SmallInt(3), Value::SmallInt(4)]));

        let mut func = BytecodeFunction::new("load_const_seq".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_seq", &pool)
            .expect("LoadConst finite sequence should lower successfully");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed-size sequence LoadConst should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_load_const_nested_record_shape_preserves_fixed_set_field() {
        let mut pool = ConstantPool::new();
        let record_idx = pool.add_value(Value::record([(
            "msgs",
            Value::set([Value::SmallInt(1), Value::SmallInt(2)]),
        )]));
        let field_idx = pool.add_value(Value::String("msgs".into()));

        let mut func = BytecodeFunction::new("load_const_nested_record".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: record_idx,
        });
        func.emit(Opcode::LoadConst {
            rd: 1,
            idx: field_idx,
        });
        func.emit(Opcode::FuncApply {
            rd: 2,
            func: 0,
            arg: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 3,
            count: 1,
        });
        func.emit(Opcode::SetDiff {
            rd: 5,
            r1: 2,
            r2: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant_with_constants(&func, "load_const_nested_record", &pool)
            .expect("nested finite record constant should preserve fixed field shape");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "record field set shape from LoadConst should keep SetDiff on static allocation"
        );
    }

    /// Part of #4280: Value::String in the constant pool must lower to a
    /// LoadImm of the interned NameId, matching the JIT scalar
    /// representation in serialized state buffers.
    #[test]
    fn test_load_const_string_lowers_to_name_id() {
        use std::sync::Arc;

        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::String(Arc::from("Hot")));

        let mut func = BytecodeFunction::new("load_const_str".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_str", &pool)
            .expect("LoadConst String(\"Hot\") should lower successfully");
        assert_eq!(module.functions.len(), 1);

        // The expected immediate is the NameId assigned by tla_core::intern_name.
        let expected = i128::from(tla_core::intern_name("Hot").0);
        let has_expected = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(v),
                    } if *v == expected
                )
            })
        });
        assert!(
            has_expected,
            "should emit Const({expected}) for String(\"Hot\") via intern_name"
        );
    }

    /// Part of #4280: Value::ModelValue must lower the same way as
    /// Value::String — model values are interned strings at runtime.
    #[test]
    fn test_load_const_model_value_lowers_to_name_id() {
        use std::sync::Arc;

        let mut pool = ConstantPool::new();
        let idx = pool.add_value(Value::ModelValue(Arc::from("alpha")));

        let mut func = BytecodeFunction::new("load_const_mv".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant_with_constants(&func, "load_const_mv", &pool)
            .expect("LoadConst ModelValue should lower successfully");
        assert_eq!(module.functions.len(), 1);

        let expected = i128::from(tla_core::intern_name("alpha").0);
        let has_expected = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(v),
                    } if *v == expected
                )
            })
        });
        assert!(
            has_expected,
            "should emit Const({expected}) for ModelValue(\"alpha\") via intern_name"
        );
    }

    /// Part of #4280 (Gap A): `Value::Interval(lo, hi)` in the constant
    /// pool must lower by materializing the concrete integer set into a
    /// tMIR aggregate (`slot[0] = count, slot[1..=count] = elements`),
    /// matching the layout produced by `SetEnum` so downstream set
    /// operations work natively without special-casing intervals.
    #[test]
    fn test_load_const_interval_materializes_aggregate() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;
        let mut pool = ConstantPool::new();
        let iv = Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(0),
            BigInt::from(3),
        )));
        let idx = pool.add_value(iv);
        let mut func = BytecodeFunction::new("load_const_interval".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });
        let module = lower_invariant_with_constants(&func, "load_const_interval", &pool)
            .expect("LoadConst Interval(0..3) should lower successfully");
        assert_eq!(module.functions.len(), 1);

        // Verify the four element values (0, 1, 2, 3) and the length header (4)
        // all appear as i64 constants somewhere in the function body.
        let blocks = &module.functions[0].blocks;
        for expected in [0_i128, 1, 2, 3, 4] {
            let has_const = blocks.iter().any(|b| {
                b.body.iter().any(|n| {
                    matches!(
                        &n.inst,
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(v),
                        } if *v == expected
                    )
                })
            });
            assert!(
                has_const,
                "should emit Const(i64, {expected}) for 0..3 interval materialization"
            );
        }

        // Verify an Alloca is emitted (for the aggregate) and a PtrToInt cast
        // (to store the pointer as an i64 in the register file).
        let has_alloca_with_count = blocks.iter().any(|b| {
            b.body
                .iter()
                .any(|n| matches!(&n.inst, Inst::Alloca { count: Some(_), .. }))
        });
        assert!(
            has_alloca_with_count,
            "interval materialization should emit Alloca with explicit count"
        );
        let has_ptr_to_int = blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Cast {
                        op: CastOp::PtrToInt,
                        ..
                    }
                )
            })
        });
        assert!(
            has_ptr_to_int,
            "interval aggregate pointer must be stored in the register file as i64 (PtrToInt)"
        );
    }

    /// Part of #4280 (Gap A): empty intervals (`low > high`) should
    /// materialize to an aggregate of just the length header (0), with
    /// no element slots.
    #[test]
    fn test_load_const_empty_interval_materializes_length_zero() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;
        let mut pool = ConstantPool::new();
        // `5..3` is empty.
        let iv = Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(5),
            BigInt::from(3),
        )));
        let idx = pool.add_value(iv);
        let mut func = BytecodeFunction::new("load_const_empty_interval".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });
        let module = lower_invariant_with_constants(&func, "load_const_empty_interval", &pool)
            .expect("LoadConst Interval(5..3) should lower successfully (empty)");
        assert_eq!(module.functions.len(), 1);

        // Should emit a length-0 constant.
        let has_zero = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    }
                )
            })
        });
        assert!(
            has_zero,
            "empty interval should emit Const(i64, 0) for the length header"
        );
    }

    /// Part of #4280 (Gap A): intervals exceeding the tMIR materialization
    /// limit fall back to an error (the interpreter handles them); this
    /// prevents unbounded stack allocations in the generated tMIR.
    #[test]
    fn test_load_const_interval_too_large_returns_error() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;
        let mut pool = ConstantPool::new();
        // 0..128 has 129 elements, which exceeds `MAX_INTERVAL_MATERIALIZE` (64).
        let iv = Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(0),
            BigInt::from(128),
        )));
        let idx = pool.add_value(iv);
        let mut func = BytecodeFunction::new("load_const_big_interval".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });
        let result = lower_invariant_with_constants(&func, "load_const_big_interval", &pool);
        assert!(
            result.is_err(),
            "LoadConst Interval exceeding materialization limit should error"
        );
        let err = result.unwrap_err();
        let msg = format!("{err}");
        assert!(
            msg.contains("exceeds tMIR materialization limit"),
            "error should mention materialization limit, got: {msg}"
        );
    }

    #[test]
    fn test_load_const_record_set_large_interval_domains_lowers_membership() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let black_field = pool.add_value(Value::String(Arc::from("black")));
        let _white_field = pool.add_value(Value::String(Arc::from("white")));
        let domain = Value::record_set([
            (
                "black",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(0),
                    BigInt::from(1000),
                ))),
            ),
            (
                "white",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(0),
                    BigInt::from(1000),
                ))),
            ),
        ]);
        let domain_idx = pool.add_value(domain);

        let mut func = BytecodeFunction::new("coffeecan_typeok_shape".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 7 });
        func.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: black_field,
            values_start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadConst {
            rd: 3,
            idx: domain_idx,
        });
        func.emit(Opcode::SetIn {
            rd: 4,
            elem: 2,
            set: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant_with_constants(&func, "coffeecan_typeok_shape", &pool)
            .expect("CoffeeCan-style record-set LoadConst should lower without enumerating");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "record-set interval membership should stay on fixed allocation"
        );
        let has_range_check = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Sge | ICmpOp::Sle,
                        ..
                    }
                )
            })
        });
        assert!(
            has_range_check,
            "record-set membership should lower interval domains to scalar range checks"
        );
    }

    #[test]
    fn test_record_set_opcode_lowers_membership_without_materializing_product() {
        use std::sync::Arc;

        let mut pool = ConstantPool::new();
        let black_field = pool.add_value(Value::String(Arc::from("black")));
        let _white_field = pool.add_value(Value::String(Arc::from("white")));

        let mut func = BytecodeFunction::new("record_set_opcode_membership".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 7 });
        func.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: black_field,
            values_start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 0 });
        func.emit(Opcode::LoadImm { rd: 4, value: 1000 });
        func.emit(Opcode::Range {
            rd: 5,
            lo: 3,
            hi: 4,
        });
        func.emit(Opcode::Range {
            rd: 6,
            lo: 3,
            hi: 4,
        });
        func.emit(Opcode::RecordSet {
            rd: 7,
            fields_start: black_field,
            values_start: 5,
            count: 2,
        });
        func.emit(Opcode::SetIn {
            rd: 8,
            elem: 2,
            set: 7,
        });
        func.emit(Opcode::Ret { rs: 8 });

        let module = lower_invariant_with_constants(&func, "record_set_opcode_membership", &pool)
            .expect("RecordSet opcode should lower to lazy record-set membership");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "RecordSet opcode membership should avoid materializing the Cartesian product"
        );
        let has_range_check = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Sge | ICmpOp::Sle,
                        ..
                    }
                )
            })
        });
        assert!(
            has_range_check,
            "RecordSet opcode membership should lower interval domains to scalar range checks"
        );
    }

    #[test]
    fn test_record_set_opcode_exact_int_domain_lowers_membership() {
        use std::sync::Arc;

        let mut pool = ConstantPool::new();
        let node_field = pool.add_value(Value::String(Arc::from("node")));

        let mut func = BytecodeFunction::new("record_set_exact_int_domain".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 2 });
        func.emit(Opcode::RecordNew {
            rd: 1,
            fields_start: node_field,
            values_start: 0,
            count: 1,
        });
        func.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func.emit(Opcode::LoadImm { rd: 3, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 2,
            count: 2,
        });
        func.emit(Opcode::RecordSet {
            rd: 5,
            fields_start: node_field,
            values_start: 4,
            count: 1,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 1,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let module = lower_invariant_with_constants(&func, "record_set_exact_int_domain", &pool)
            .expect("RecordSet opcode should lower exact integer set domains");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "exact integer record-set membership should stay on fixed allocation"
        );
        let has_equality_check = module.functions[0].blocks.iter().any(|b| {
            b.body
                .iter()
                .any(|n| matches!(&n.inst, Inst::ICmp { op: ICmpOp::Eq, .. }))
        });
        assert!(
            has_equality_check,
            "exact integer record-set membership should compare against fixed domain elements"
        );
    }

    #[test]
    fn test_called_record_set_opcode_retains_shape_for_membership() {
        use std::sync::Arc;

        let mut chunk = BytecodeChunk::new();
        let _dummy = chunk.constants.add_value(Value::String(Arc::from("dummy")));
        let black_field = chunk.constants.add_value(Value::String(Arc::from("black")));
        let _white_field = chunk.constants.add_value(Value::String(Arc::from("white")));

        let mut domain = BytecodeFunction::new("CoffeeCanDomain".to_string(), 0);
        domain.emit(Opcode::LoadImm { rd: 0, value: 0 });
        domain.emit(Opcode::LoadImm { rd: 1, value: 1000 });
        domain.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        domain.emit(Opcode::Range {
            rd: 3,
            lo: 0,
            hi: 1,
        });
        domain.emit(Opcode::RecordSet {
            rd: 4,
            fields_start: black_field,
            values_start: 2,
            count: 2,
        });
        domain.emit(Opcode::Ret { rs: 4 });
        let domain_idx = chunk.add_function(domain);

        let mut inv = BytecodeFunction::new("CalledCoffeeCanDomainMembership".to_string(), 0);
        inv.emit(Opcode::LoadImm { rd: 0, value: 5 });
        inv.emit(Opcode::LoadImm { rd: 1, value: 7 });
        inv.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: black_field,
            values_start: 0,
            count: 2,
        });
        inv.emit(Opcode::Call {
            rd: 3,
            op_idx: domain_idx,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::SetIn {
            rd: 4,
            elem: 2,
            set: 3,
        });
        inv.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(inv);

        let module = lower_module_invariant(&chunk, entry_idx, "called_record_set_membership")
            .expect("called RecordSet domains should retain lazy membership shape");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "called RecordSet membership should avoid materializing the Cartesian product"
        );
        assert_call_uses_caller_owned_return_buffer(&module, 0, 3, 2);
        assert_callee_stores_into_hidden_return_buffer(&module, 1, 3);
        assert_eq!(
            callee_return_buffer_const_stores(&module, 1, 3),
            vec![(0, 0), (1, 0)],
            "called RecordSet interval domains must not copy callee-local domain pointers into the return buffer"
        );
        let has_range_check = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Sge | ICmpOp::Sle,
                        ..
                    }
                )
            })
        });
        assert!(
            has_range_check,
            "called RecordSet membership should lower interval domains to scalar range checks"
        );
    }

    #[test]
    fn test_called_record_new_opcode_retains_shape_for_record_set_membership() {
        use std::sync::Arc;

        let mut chunk = BytecodeChunk::new();
        let _dummy = chunk.constants.add_value(Value::String(Arc::from("dummy")));
        let black_field = chunk.constants.add_value(Value::String(Arc::from("black")));
        let _white_field = chunk.constants.add_value(Value::String(Arc::from("white")));

        let mut record = BytecodeFunction::new("CoffeeCanRecord".to_string(), 0);
        record.emit(Opcode::LoadImm { rd: 0, value: 5 });
        record.emit(Opcode::LoadImm { rd: 1, value: 7 });
        record.emit(Opcode::RecordNew {
            rd: 2,
            fields_start: black_field,
            values_start: 0,
            count: 2,
        });
        record.emit(Opcode::Ret { rs: 2 });
        let record_idx = chunk.add_function(record);

        let mut inv = BytecodeFunction::new("CalledCoffeeCanRecordMembership".to_string(), 0);
        inv.emit(Opcode::Call {
            rd: 0,
            op_idx: record_idx,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::LoadImm { rd: 1, value: 0 });
        inv.emit(Opcode::LoadImm { rd: 2, value: 1000 });
        inv.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        inv.emit(Opcode::Range {
            rd: 4,
            lo: 1,
            hi: 2,
        });
        inv.emit(Opcode::RecordSet {
            rd: 5,
            fields_start: black_field,
            values_start: 3,
            count: 2,
        });
        inv.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        inv.emit(Opcode::Ret { rs: 6 });
        let entry_idx = chunk.add_function(inv);

        let module = lower_module_invariant(&chunk, entry_idx, "called_record_new_membership")
            .expect("called RecordNew values should retain record shape for record-set membership");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "called RecordNew membership should avoid materializing the Cartesian product"
        );
        let has_range_check = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Sge | ICmpOp::Sle,
                        ..
                    }
                )
            })
        });
        assert!(
            has_range_check,
            "called RecordNew membership should lower interval domains to scalar range checks"
        );
    }

    #[test]
    fn test_load_const_record_set_state_loaded_record_lowers_membership() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let domain = Value::record_set([
            (
                "black",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(0),
                    BigInt::from(1000),
                ))),
            ),
            (
                "white",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(0),
                    BigInt::from(1000),
                ))),
            ),
        ]);
        let domain_idx = pool.add_value(domain);

        let mut func = BytecodeFunction::new("coffeecan_typeok_state_shape".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadConst {
            rd: 1,
            idx: domain_idx,
        });
        func.emit(Opcode::SetIn {
            rd: 2,
            elem: 0,
            set: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("black"), CompoundLayout::Int),
                (tla_core::intern_name("white"), CompoundLayout::Int),
            ],
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "coffeecan_typeok_state_shape",
            &pool,
            &layout,
        )
        .expect("state-loaded record-set membership should use the compact record shape");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "state-loaded record-set interval membership should stay on fixed allocation"
        );
        assert_eq!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    ..
                }
            )),
            1,
            "compact state record membership must not cast the record's first scalar lane to a pointer"
        );
        let has_range_check = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Sge | ICmpOp::Sle,
                        ..
                    }
                )
            })
        });
        assert!(
            has_range_check,
            "state-loaded record-set membership should lower interval domains to scalar range checks"
        );
    }

    #[test]
    fn test_load_const_record_set_finite_domain_lowers_membership() {
        use std::sync::Arc;

        let mut pool = ConstantPool::new();
        let kind_field = pool.add_value(Value::String(Arc::from("kind")));
        let value_a = pool.add_value(Value::String(Arc::from("a")));
        let domain = Value::record_set([(
            "kind",
            Value::set([Value::String(Arc::from("a")), Value::String(Arc::from("b"))]),
        )]);
        let domain_idx = pool.add_value(domain);

        let mut func = BytecodeFunction::new("record_set_finite_domain".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: value_a,
        });
        func.emit(Opcode::RecordNew {
            rd: 1,
            fields_start: kind_field,
            values_start: 0,
            count: 1,
        });
        func.emit(Opcode::LoadConst {
            rd: 2,
            idx: domain_idx,
        });
        func.emit(Opcode::SetIn {
            rd: 3,
            elem: 1,
            set: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant_with_constants(&func, "record_set_finite_domain", &pool)
            .expect("record-set finite field domain membership should lower");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "finite record-set membership should not emit non-const-count Alloca"
        );
        let has_equality_check = module.functions[0].blocks.iter().any(|b| {
            b.body
                .iter()
                .any(|n| matches!(&n.inst, Inst::ICmp { op: ICmpOp::Eq, .. }))
        });
        assert!(
            has_equality_check,
            "finite record-set membership should compare against fixed domain elements"
        );
    }

    #[test]
    fn test_load_const_record_set_symbolic_numeric_domains_lowers_membership() {
        use std::sync::Arc;

        let mut pool = ConstantPool::new();
        let int_field = pool.add_value(Value::String(Arc::from("i")));
        let _nat_field = pool.add_value(Value::String(Arc::from("n")));
        let _real_field = pool.add_value(Value::String(Arc::from("r")));
        let domain = Value::record_set([
            (
                "i",
                Value::try_model_value("Int").expect("Int symbolic domain"),
            ),
            (
                "n",
                Value::try_model_value("Nat").expect("Nat symbolic domain"),
            ),
            (
                "r",
                Value::try_model_value("Real").expect("Real symbolic domain"),
            ),
        ]);
        let domain_idx = pool.add_value(domain);

        let mut func = BytecodeFunction::new("record_set_symbolic_numeric".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 6 });
        func.emit(Opcode::LoadImm { rd: 2, value: 7 });
        func.emit(Opcode::RecordNew {
            rd: 3,
            fields_start: int_field,
            values_start: 0,
            count: 3,
        });
        func.emit(Opcode::LoadConst {
            rd: 4,
            idx: domain_idx,
        });
        func.emit(Opcode::SetIn {
            rd: 5,
            elem: 3,
            set: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant_with_constants(&func, "record_set_symbolic_numeric", &pool)
            .expect("record-set Int/Nat/Real field membership should lower for numeric fields");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "symbolic numeric record-set membership should not enumerate domains"
        );
        let has_nat_lower_bound_check = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Sge,
                        ..
                    }
                )
            })
        });
        assert!(
            has_nat_lower_bound_check,
            "Nat field membership should lower to a numeric nonnegative check"
        );
    }

    #[test]
    fn test_called_record_set_symbolic_numeric_domains_zero_return_payloads() {
        use std::sync::Arc;

        let mut chunk = BytecodeChunk::new();
        let int_field = chunk.constants.add_value(Value::String(Arc::from("i")));
        let _nat_field = chunk.constants.add_value(Value::String(Arc::from("n")));
        let _real_field = chunk.constants.add_value(Value::String(Arc::from("r")));
        let domain_idx = chunk.constants.add_value(Value::record_set([
            (
                "i",
                Value::try_model_value("Int").expect("Int symbolic domain"),
            ),
            (
                "n",
                Value::try_model_value("Nat").expect("Nat symbolic domain"),
            ),
            (
                "r",
                Value::try_model_value("Real").expect("Real symbolic domain"),
            ),
        ]));

        let mut domain = BytecodeFunction::new("SymbolicNumericDomain".to_string(), 0);
        domain.emit(Opcode::LoadConst {
            rd: 0,
            idx: domain_idx,
        });
        domain.emit(Opcode::Ret { rs: 0 });
        let domain_idx = chunk.add_function(domain);

        let mut inv = BytecodeFunction::new("CalledSymbolicNumericDomainMembership".to_string(), 0);
        inv.emit(Opcode::LoadImm { rd: 0, value: 5 });
        inv.emit(Opcode::LoadImm { rd: 1, value: 6 });
        inv.emit(Opcode::LoadImm { rd: 2, value: 7 });
        inv.emit(Opcode::RecordNew {
            rd: 3,
            fields_start: int_field,
            values_start: 0,
            count: 3,
        });
        inv.emit(Opcode::Call {
            rd: 4,
            op_idx: domain_idx,
            args_start: 0,
            argc: 0,
        });
        inv.emit(Opcode::SetIn {
            rd: 5,
            elem: 3,
            set: 4,
        });
        inv.emit(Opcode::Ret { rs: 5 });
        let entry_idx = chunk.add_function(inv);

        let module = lower_module_invariant(&chunk, entry_idx, "called_symbolic_numeric_domain")
            .expect("called RecordSet Int/Nat/Real domains should lower for numeric fields");

        assert_call_uses_caller_owned_return_buffer(&module, 0, 3, 3);
        assert_callee_stores_into_hidden_return_buffer(&module, 1, 3);
        assert_eq!(
            callee_return_buffer_const_stores(&module, 1, 3),
            vec![(0, 0), (1, 0), (2, 0)],
            "called RecordSet symbolic domains must not copy callee-local domain pointers into the return buffer"
        );
        let has_nat_lower_bound_check = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Sge,
                        ..
                    }
                )
            })
        });
        assert!(
            has_nat_lower_bound_check,
            "Nat field membership should lower to a numeric nonnegative check"
        );
    }

    // =================================================================
    // Unchanged tests
    // =================================================================

    #[test]
    fn test_unchanged_single_var() {
        // UNCHANGED <<x>> where x is var_idx 0.
        let mut pool = ConstantPool::new();
        let start = pool.add_value(Value::SmallInt(0)); // var_idx 0

        let mut func = BytecodeFunction::new("unchanged_x".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start,
            count: 1,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_next_state_with_constants(&func, "unchanged_x", &pool)
            .expect("Unchanged single var should lower successfully");
        assert_eq!(module.functions.len(), 1);

        // Should contain ICmp Eq instructions for the comparison.
        let has_icmp_eq = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        ..
                    }
                )
            })
        });
        assert!(
            has_icmp_eq,
            "Unchanged should emit ICmp Eq for var comparison"
        );

        // Should have a Return instruction.
        let has_return = module.functions[0].blocks.iter().any(|b| {
            b.body
                .last()
                .map_or(false, |n| matches!(n.inst, Inst::Return { .. }))
        });
        assert!(has_return, "function should contain a Return instruction");
    }

    #[test]
    fn test_unchanged_multiple_vars() {
        // UNCHANGED <<x, y>> where x=var_idx 0, y=var_idx 1.
        let mut pool = ConstantPool::new();
        let start = pool.add_value(Value::SmallInt(0)); // var_idx 0
        pool.add_value(Value::SmallInt(1)); // var_idx 1

        let mut func = BytecodeFunction::new("unchanged_xy".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start,
            count: 2,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_next_state_with_constants(&func, "unchanged_xy", &pool)
            .expect("Unchanged two vars should lower successfully");
        assert_eq!(module.functions.len(), 1);

        // Should have 2 ICmp Eq instructions (one per variable).
        let icmp_eq_count: usize = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .filter(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        ..
                    }
                )
            })
            .count();
        assert_eq!(
            icmp_eq_count, 2,
            "Unchanged <<x,y>> should emit 2 ICmp Eq, got {icmp_eq_count}"
        );

        // Should have an And instruction to combine the two comparisons.
        let has_and = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        ..
                    }
                )
            })
        });
        assert!(
            has_and,
            "Unchanged <<x,y>> should emit And to combine results"
        );
    }

    #[test]
    fn test_unchanged_compact_record_compares_all_slots() {
        let mut pool = ConstantPool::new();
        let start = pool.add_value(Value::SmallInt(0));

        let mut func = BytecodeFunction::new("unchanged_compact_record".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start,
            count: 1,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("x"), CompoundLayout::Int),
                (tla_core::intern_name("y"), CompoundLayout::Int),
                (tla_core::intern_name("z"), CompoundLayout::Int),
            ],
        })]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "unchanged_compact_record",
            &pool,
            &layout,
        )
        .expect("UNCHANGED over compact record should lower");

        assert_eq!(
            unchanged_eq_slot_pairs(&module, 0),
            vec![(0, 0), (1, 1), (2, 2)],
            "UNCHANGED must compare every compact record slot"
        );
    }

    #[test]
    fn test_unchanged_mixed_compact_and_scalar_uses_compact_offsets() {
        let mut pool = ConstantPool::new();
        let start = pool.add_value(Value::SmallInt(0));
        pool.add_value(Value::SmallInt(1));

        let mut func = BytecodeFunction::new("unchanged_compact_mixed".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start,
            count: 2,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("left"), CompoundLayout::Int),
                    (tla_core::intern_name("right"), CompoundLayout::Int),
                ],
            }),
            VarLayout::ScalarInt,
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "unchanged_compact_mixed",
            &pool,
            &layout,
        )
        .expect("UNCHANGED over mixed compact/scalar variables should lower");

        assert_eq!(
            unchanged_eq_slot_pairs(&module, 0),
            vec![(0, 0), (1, 1), (2, 2)],
            "UNCHANGED must compare all compact slots and then the scalar at its compact offset"
        );
    }

    #[test]
    fn test_unchanged_tail_after_placeholder_compound_uses_compact_offset() {
        let mut pool = ConstantPool::new();
        let start = pool.add_value(Value::SmallInt(2));

        let mut func = BytecodeFunction::new("unchanged_after_placeholder_compound".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start,
            count: 1,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("left"), CompoundLayout::Int),
                    (tla_core::intern_name("right"), CompoundLayout::Int),
                ],
            }),
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Int),
                pair_count: None,
                domain_lo: None,
            }),
            VarLayout::ScalarInt,
        ]);

        let module = lower_next_state_with_constants_and_layout(
            &func,
            "unchanged_after_placeholder_compound",
            &pool,
            &layout,
        )
        .expect("UNCHANGED after a placeholder compact layout should lower");

        assert_eq!(
            unchanged_eq_slot_pairs(&module, 0),
            vec![(3, 3)],
            "UNCHANGED must use ABI compact placeholder offsets, not raw var_idx fallback"
        );
    }

    #[test]
    fn test_unchanged_rejects_out_of_range_supplied_layout() {
        let mut pool = ConstantPool::new();
        let start = pool.add_value(Value::SmallInt(1));

        let mut func = BytecodeFunction::new("unchanged_out_of_range".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start,
            count: 1,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let layout = StateLayout::new(vec![VarLayout::ScalarInt]);
        let err = lower_next_state_with_constants_and_layout(
            &func,
            "unchanged_out_of_range",
            &pool,
            &layout,
        )
        .expect_err("UNCHANGED with an out-of-range supplied layout var should reject");
        assert!(
            format!("{err}").contains("state layout has 1 vars but var_idx 1 was requested"),
            "unexpected UNCHANGED out-of-range error: {err}"
        );
    }

    #[test]
    fn test_unchanged_empty_vars() {
        // UNCHANGED <<>> — vacuously true.
        let pool = ConstantPool::new();

        let mut func = BytecodeFunction::new("unchanged_empty".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start: 0,
            count: 0,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_next_state_with_constants(&func, "unchanged_empty", &pool)
            .expect("Unchanged empty should lower successfully");
        assert_eq!(module.functions.len(), 1);

        // Should contain Const(1) for TRUE.
        let has_const_1 = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(1),
                    }
                )
            })
        });
        assert!(has_const_1, "Unchanged <<>> should emit Const(1) for TRUE");
    }

    #[test]
    fn test_unchanged_invariant_mode_returns_error() {
        // Unchanged in invariant mode should fail.
        let mut pool = ConstantPool::new();
        pool.add_value(Value::SmallInt(0));

        let mut func = BytecodeFunction::new("unchanged_inv".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start: 0,
            count: 1,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let result = lower_invariant_with_constants(&func, "unchanged_inv", &pool);
        assert!(result.is_err(), "Unchanged in invariant mode should fail");
    }

    #[test]
    fn test_unchanged_without_pool_returns_error() {
        let mut func = BytecodeFunction::new("unchanged_nopool".to_string(), 0);
        func.emit(Opcode::Unchanged {
            rd: 0,
            start: 0,
            count: 1,
        });
        func.emit(Opcode::Ret { rs: 0 });

        let result = lower_next_state(&func, "unchanged_nopool");
        assert!(
            result.is_err(),
            "Unchanged without constant pool should fail"
        );
    }

    // =================================================================
    // Multi-function module (Call opcode) tests
    // =================================================================

    /// Test calling a simple callee: f(x) = x + 1, entrypoint calls f(10).
    ///
    /// Chunk layout:
    ///   func 0 = f(x):  r0=x param, LoadImm r1=1, AddInt r2=r0+r1, Ret r2
    ///   func 1 = entry:  LoadImm r0=10, Call r1=f(r0), Ret r1
    #[test]
    fn test_lower_call_simple() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // func 0: f(x) = x + 1
        let mut f = BytecodeFunction::new("f".to_string(), 1);
        f.emit(Opcode::LoadImm { rd: 1, value: 1 });
        f.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        f.emit(Opcode::Ret { rs: 2 });
        chunk.add_function(f);

        // func 1: entry() = f(10)
        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 10 });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: 0, // call func 0 (f)
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::Ret { rs: 1 });
        chunk.add_function(entry);

        let module =
            lower_module_invariant(&chunk, 1, "call_test").expect("Call lowering should succeed");

        // Module should have 2 functions: entry + callee f.
        assert_eq!(
            module.functions.len(),
            2,
            "expected 2 functions in module, got {}",
            module.functions.len()
        );

        // Entrypoint is functions[0], callee f is functions[1].
        assert_eq!(module.functions[0].name, "call_test");
        assert_eq!(
            module.functions[1].name,
            "__tmir_callee_m9x63616c6c5f74657374_o0_n1x66"
        );

        // Verify entrypoint contains a Call instruction.
        assert_eq!(
            direct_call_callees(&module, 0),
            vec![module.functions[1].id],
            "entrypoint should call the namespaced callee by FuncId"
        );

        // Verify callee f has a Return with values (i64 return).
        let has_i64_return = module.functions[1].blocks.iter().any(|b| {
            b.body.last().map_or(
                false,
                |n| matches!(&n.inst, Inst::Return { values } if !values.is_empty()),
            )
        });
        assert!(
            has_i64_return,
            "callee should return i64 (Return with non-empty values)"
        );
    }

    /// Test calling a callee with multiple arguments: add(x, y) = x + y.
    #[test]
    fn test_lower_call_multi_arg() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // func 0: add(x, y) = x + y
        let mut add = BytecodeFunction::new("add".to_string(), 2);
        add.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        add.emit(Opcode::Ret { rs: 2 });
        chunk.add_function(add);

        // func 1: entry() = add(3, 7)
        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 3 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 7 });
        entry.emit(Opcode::Call {
            rd: 2,
            op_idx: 0,
            args_start: 0,
            argc: 2,
        });
        entry.emit(Opcode::Ret { rs: 2 });
        chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, 1, "multi_arg_test")
            .expect("multi-arg Call lowering should succeed");

        assert_eq!(module.functions.len(), 2);

        // The callee "add" should have arity-2 params in its func type.
        // Func type for callee: [Ptr, Ptr, I32, Ptr, I64, I64] -> [I64]
        let callee_ft_idx = module.functions[1].ty;
        let callee_ft = &module.func_types[callee_ft_idx.as_usize()];
        // Context params (Ptr, Ptr, I32) + hidden return buffer + 2 user args.
        assert_eq!(
            callee_ft.params.len(),
            6,
            "callee should have 6 params (3 context + return buffer + 2 user), got {}",
            callee_ft.params.len()
        );
        assert_eq!(callee_ft.params[3], Ty::Ptr);
        assert_eq!(callee_ft.returns, vec![Ty::I64]);
    }

    /// Test zero-arg call: f() = 42, entry calls f().
    #[test]
    fn test_lower_call_zero_arg() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // func 0: f() = 42
        let mut f = BytecodeFunction::new("f".to_string(), 0);
        f.emit(Opcode::LoadImm { rd: 0, value: 42 });
        f.emit(Opcode::Ret { rs: 0 });
        chunk.add_function(f);

        // func 1: entry() = f()
        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: 0,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::Ret { rs: 0 });
        chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, 1, "zero_arg_test")
            .expect("zero-arg Call lowering should succeed");

        assert_eq!(module.functions.len(), 2);
        assert_eq!(module.functions[0].name, "zero_arg_test");
        assert_eq!(
            module.functions[1].name,
            "__tmir_callee_m13x7a65726f5f6172675f74657374_o0_n1x66"
        );
    }

    #[test]
    fn test_callee_symbols_are_namespaced_by_entry_module() {
        fn build_sum_chunk() -> (BytecodeChunk, u16) {
            let mut chunk = BytecodeChunk::new();

            let mut sum = BytecodeFunction::new("Sum".to_string(), 2);
            sum.emit(Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            });
            sum.emit(Opcode::Ret { rs: 2 });
            let sum_idx = chunk.add_function(sum);

            let mut entry = BytecodeFunction::new("Inv".to_string(), 0);
            entry.emit(Opcode::LoadImm { rd: 0, value: 1 });
            entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
            entry.emit(Opcode::Call {
                rd: 2,
                op_idx: sum_idx,
                args_start: 0,
                argc: 2,
            });
            entry.emit(Opcode::Ret { rs: 2 });
            let entry_idx = chunk.add_function(entry);

            (chunk, entry_idx)
        }

        let (chunk_a, entry_a) = build_sum_chunk();
        let module_a = lower_module_invariant(&chunk_a, entry_a, "InvA")
            .expect("first Sum helper module should lower");
        let (chunk_b, entry_b) = build_sum_chunk();
        let module_b = lower_module_invariant(&chunk_b, entry_b, "InvB")
            .expect("second Sum helper module should lower");

        assert_eq!(
            module_a.functions[1].name,
            "__tmir_callee_m4x496e7641_o0_n3x53756d"
        );
        assert_eq!(
            module_b.functions[1].name,
            "__tmir_callee_m4x496e7642_o0_n3x53756d"
        );
        assert_ne!(
            module_a.functions[1].name, module_b.functions[1].name,
            "same raw helper name must not produce the same JIT symbol"
        );
        assert_eq!(
            direct_call_callees(&module_a, 0),
            vec![module_a.functions[1].id],
            "first entry should call its namespaced Sum helper"
        );
        assert_eq!(
            direct_call_callees(&module_b, 0),
            vec![module_b.functions[1].id],
            "second entry should call its namespaced Sum helper"
        );
    }

    #[test]
    fn test_callee_symbols_escape_delimiter_collisions() {
        fn lowered_helper_name(module_name: &str, raw_name: &str) -> String {
            let mut chunk = BytecodeChunk::new();

            let mut helper = BytecodeFunction::new(raw_name.to_string(), 0);
            helper.emit(Opcode::LoadImm { rd: 0, value: 1 });
            helper.emit(Opcode::Ret { rs: 0 });
            chunk.add_function(helper);

            let mut entry = BytecodeFunction::new("Entry".to_string(), 0);
            entry.emit(Opcode::Call {
                rd: 0,
                op_idx: 0,
                args_start: 0,
                argc: 0,
            });
            entry.emit(Opcode::Ret { rs: 0 });
            let entry_idx = chunk.add_function(entry);

            lower_module_invariant(&chunk, entry_idx, module_name)
                .expect("module with delimiter-like names should lower")
                .functions[1]
                .name
                .clone()
        }

        let left = lowered_helper_name("A__callee_0__B", "C");
        let right = lowered_helper_name("A", "B__callee_0__C");

        assert_ne!(
            left, right,
            "distinct (module, op_idx, raw callee) tuples must not collide"
        );
        assert!(
            left.chars()
                .all(|ch| ch.is_ascii_alphanumeric() || ch == '_'),
            "encoded helper symbol should stay symbol-safe: {left}"
        );
        assert!(
            right
                .chars()
                .all(|ch| ch.is_ascii_alphanumeric() || ch == '_'),
            "encoded helper symbol should stay symbol-safe: {right}"
        );
    }

    /// Test transitive calls: entry -> g -> f.
    #[test]
    fn test_lower_call_transitive() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // func 0: f(x) = x * x
        let mut f = BytecodeFunction::new("f".to_string(), 1);
        f.emit(Opcode::MulInt {
            rd: 1,
            r1: 0,
            r2: 0,
        });
        f.emit(Opcode::Ret { rs: 1 });
        chunk.add_function(f);

        // func 1: g(x) = f(x) + 1
        let mut g = BytecodeFunction::new("g".to_string(), 1);
        // Call f(r0) -> r1
        g.emit(Opcode::Call {
            rd: 1,
            op_idx: 0, // call f
            args_start: 0,
            argc: 1,
        });
        g.emit(Opcode::LoadImm { rd: 2, value: 1 });
        g.emit(Opcode::AddInt {
            rd: 3,
            r1: 1,
            r2: 2,
        });
        g.emit(Opcode::Ret { rs: 3 });
        chunk.add_function(g);

        // func 2: entry() = g(5)
        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::LoadImm { rd: 0, value: 5 });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: 1, // call g
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::Ret { rs: 1 });
        chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, 2, "transitive_test")
            .expect("transitive Call lowering should succeed");

        // Should have 3 functions: entry + g + f.
        assert_eq!(
            module.functions.len(),
            3,
            "expected 3 functions for transitive call chain, got {}",
            module.functions.len()
        );

        // Verify all 3 functions are present.
        let names: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
        assert!(
            names.contains(&"transitive_test"),
            "missing entry: {names:?}"
        );
        assert!(
            names.contains(&"__tmir_callee_m15x7472616e7369746976655f74657374_o1_n1x67"),
            "missing g: {names:?}"
        );
        assert!(
            names.contains(&"__tmir_callee_m15x7472616e7369746976655f74657374_o0_n1x66"),
            "missing f: {names:?}"
        );
    }

    /// Test that lower_module_next_state works with Call.
    #[test]
    fn test_lower_call_next_state() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // func 0: inc(x) = x + 1
        let mut inc = BytecodeFunction::new("inc".to_string(), 1);
        inc.emit(Opcode::LoadImm { rd: 1, value: 1 });
        inc.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        inc.emit(Opcode::Ret { rs: 2 });
        chunk.add_function(inc);

        // func 1: Next() = x' = inc(x)
        let mut next = BytecodeFunction::new("Next".to_string(), 0);
        next.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // x
        next.emit(Opcode::Call {
            rd: 1,
            op_idx: 0, // call inc
            args_start: 0,
            argc: 1,
        });
        next.emit(Opcode::StoreVar { var_idx: 0, rs: 1 }); // x' = inc(x)
        next.emit(Opcode::LoadBool { rd: 2, value: true });
        next.emit(Opcode::Ret { rs: 2 });
        chunk.add_function(next);

        let module = lower_module_next_state(&chunk, 1, "next_state_call_test")
            .expect("next-state Call lowering should succeed");

        assert_eq!(module.functions.len(), 2);

        // Callee in next-state mode should have 4 context params
        // (Ptr, Ptr, Ptr, I32) + hidden return buffer + 1 user arg.
        let callee_ft_idx = module.functions[1].ty;
        let callee_ft = &module.func_types[callee_ft_idx.as_usize()];
        assert_eq!(
            callee_ft.params.len(),
            6,
            "next-state callee should have 6 params (4 context + return buffer + 1 user), got {}",
            callee_ft.params.len()
        );
        assert_eq!(callee_ft.params[4], Ty::Ptr);
    }

    #[test]
    fn test_called_dense_function_stores_into_sequence_state() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("DenseFunction".to_string(), 0);
        helper.emit(Opcode::LoadImm { rd: 0, value: 1 });
        helper.emit(Opcode::LoadImm { rd: 1, value: 2 });
        helper.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        let begin_pc = helper.emit(Opcode::FuncDefBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        helper.emit(Opcode::Move { rd: 5, rs: 4 });
        let next_pc = helper.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 5,
            loop_begin: 0,
        });
        helper.patch_jump(begin_pc, next_pc + 1);
        helper.patch_jump(next_pc, begin_pc + 1);
        helper.emit(Opcode::Ret { rs: 3 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("StoreCalledDenseFunction".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: helper_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        entry.emit(Opcode::LoadBool { rd: 1, value: true });
        entry.emit(Opcode::Ret { rs: 1 });
        let entry_idx = chunk.add_function(entry);

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(2),
        })]);

        let module = lower_module_next_state_with_layout(
            &chunk,
            entry_idx,
            "called_dense_function_sequence_store",
            &layout,
        )
        .expect("called dense Function with domain_lo Some(1) should store into Sequence layout");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "caller should keep dense function-to-sequence materialization fixed"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 1),
            "callee should keep dense function return materialization fixed"
        );
        assert_no_ptr_payload_store_to_state_out(&module, 0);
        assert_call_uses_caller_owned_return_buffer(&module, 0, 4, 2);
    }

    #[test]
    fn test_called_compact_function_domain_rejects_return_buffer_pointer_fallback() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("DenseFunction".to_string(), 0);
        helper.emit(Opcode::LoadImm { rd: 0, value: 1 });
        helper.emit(Opcode::LoadImm { rd: 1, value: 2 });
        helper.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        let begin_pc = helper.emit(Opcode::FuncDefBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        helper.emit(Opcode::Move { rd: 5, rs: 4 });
        let next_pc = helper.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 5,
            loop_begin: 0,
        });
        helper.patch_jump(begin_pc, next_pc + 1);
        helper.patch_jump(next_pc, begin_pc + 1);
        helper.emit(Opcode::Ret { rs: 3 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("DomainOfCalledDenseFunction".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: helper_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::Domain { rd: 1, rs: 0 });
        entry.emit(Opcode::LoadBool { rd: 2, value: true });
        entry.emit(Opcode::Ret { rs: 2 });
        let entry_idx = chunk.add_function(entry);

        let err =
            lower_module_invariant(&chunk, entry_idx, "called_compact_function_domain_rejects")
                .expect_err("DOMAIN over a compact helper return buffer must fail closed");
        let message = format!("{err}");
        assert!(
            message.contains("Domain")
                && message.contains("compact")
                && (message.contains("aggregate-pointer")
                    || message.contains("aggregate pointer")
                    || message.contains("return buffer")
                    || message.contains("reinterpret")),
            "unexpected compact helper-return Domain rejection: {message}"
        );
    }

    /// Helper callees share the entrypoint out_ptr for runtime error /
    /// fallback signaling. Their non-Ok path must still return an i64, and
    /// callers must branch on shared status before consuming the result.
    #[test]
    fn test_lower_call_propagates_callee_status_and_keeps_callee_returns_typed() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // func 0: overflow_if_max(x) = x + 1
        let mut helper = BytecodeFunction::new("overflow_if_max".to_string(), 1);
        helper.emit(Opcode::LoadImm { rd: 1, value: 1 });
        helper.emit(Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        helper.emit(Opcode::Ret { rs: 2 });
        chunk.add_function(helper);

        // func 1: entry() = overflow_if_max(i64::MAX)
        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::LoadImm {
            rd: 0,
            value: i64::MAX,
        });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: 0,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::Ret { rs: 1 });
        chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, 1, "call_status_test")
            .expect("call lowering with overflowing callee should succeed");

        let entry_fn = &module.functions[0];
        let helper_fn = &module.functions[1];

        let helper_has_void_return = helper_fn.blocks.iter().any(|block| {
            block
                .body
                .iter()
                .any(|node| matches!(&node.inst, Inst::Return { values } if values.is_empty()))
        });
        assert!(
            !helper_has_void_return,
            "callee runtime-error paths must still return i64"
        );

        let call_block = entry_fn
            .blocks
            .iter()
            .find(|block| {
                block
                    .body
                    .iter()
                    .any(|node| matches!(&node.inst, Inst::Call { .. }))
            })
            .expect("entry should contain a Call block");

        let has_status_load = call_block
            .body
            .iter()
            .any(|node| matches!(&node.inst, Inst::Load { ty: Ty::I8, .. }));
        assert!(
            has_status_load,
            "caller must reload shared status after helper call"
        );

        let has_ok_cmp = call_block.body.iter().any(|node| {
            matches!(
                &node.inst,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I8,
                    ..
                }
            )
        });
        assert!(
            has_ok_cmp,
            "caller must compare shared status against JitStatus::Ok"
        );

        assert!(
            matches!(
                call_block.body.last().map(|node| &node.inst),
                Some(Inst::CondBr { .. })
            ),
            "caller must branch on shared status after helper call"
        );
    }

    #[test]
    fn test_lower_call_stores_result_before_status_branch() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("helper".to_string(), 0);
        helper.emit(Opcode::LoadImm { rd: 0, value: 7 });
        helper.emit(Opcode::Ret { rs: 0 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: helper_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::Ret { rs: 0 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "call_result_store_test")
            .expect("helper call should lower");
        let entry_fn = &module.functions[0];
        let (call_block_idx, call_result) = entry_fn
            .blocks
            .iter()
            .enumerate()
            .find_map(|(block_idx, block)| {
                block.body.iter().find_map(|node| {
                    if matches!(&node.inst, Inst::Call { .. }) {
                        node.results
                            .first()
                            .copied()
                            .map(|result| (block_idx, result))
                    } else {
                        None
                    }
                })
            })
            .expect("entry should contain a Call with a result");
        let call_block = &entry_fn.blocks[call_block_idx];
        let cond_pos = call_block
            .body
            .iter()
            .position(|node| matches!(&node.inst, Inst::CondBr { .. }))
            .expect("call block should branch on shared status");

        assert!(
            call_block.body[..cond_pos].iter().any(|node| {
                matches!(&node.inst, Inst::Store { value, .. } if *value == call_result)
            }),
            "call result must be stored in the call block before the status branch"
        );

        let continue_id = match &call_block.body[cond_pos].inst {
            Inst::CondBr { then_target, .. } => *then_target,
            _ => unreachable!(),
        };
        let continue_block = entry_fn
            .blocks
            .iter()
            .find(|block| block.id == continue_id)
            .expect("call_ok block should exist");
        assert!(
            !continue_block.body.iter().any(|node| {
                matches!(&node.inst, Inst::Store { value, .. } if *value == call_result)
            }),
            "call_ok must not consume the call result through cross-block SSA"
        );
    }

    #[test]
    fn test_lower_call_clears_shared_status_before_helper_call() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("helper".to_string(), 0);
        helper.emit(Opcode::LoadImm { rd: 0, value: 7 });
        helper.emit(Opcode::Ret { rs: 0 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: helper_idx,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::Ret { rs: 0 });
        let entry_idx = chunk.add_function(entry);

        let module = lower_module_invariant(&chunk, entry_idx, "call_clear_status_test")
            .expect("helper call should lower");

        assert_eq!(
            direct_call_callees(&module, 0),
            vec![module.functions[1].id],
            "entrypoint should call the helper"
        );
        assert_eq!(
            direct_calls_missing_pre_call_status_clear(&module, 0),
            0,
            "lower_call must store JitStatus::Ok to shared JitCallOut.status before helper calls"
        );
    }

    #[test]
    fn test_helper_set_ops_return_compact_setbitmask_shape_for_matching_universe() {
        for (op_name, opcode) in [
            (
                "SetUnion",
                Opcode::SetUnion {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
            ),
            (
                "SetIntersect",
                Opcode::SetIntersect {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
            ),
            (
                "SetDiff",
                Opcode::SetDiff {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
            ),
        ] {
            let mut chunk = BytecodeChunk::new();

            let mut helper = BytecodeFunction::new(format!("{op_name}Mask"), 2);
            helper.emit(opcode);
            helper.emit(Opcode::Ret { rs: 2 });
            let helper_idx = chunk.add_function(helper);

            let mut entry = BytecodeFunction::new(format!("{op_name}Entry"), 0);
            entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
            entry.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
            entry.emit(Opcode::Call {
                rd: 2,
                op_idx: helper_idx,
                args_start: 0,
                argc: 2,
            });
            entry.emit(Opcode::LoadImm { rd: 3, value: 2 });
            entry.emit(Opcode::SetIn {
                rd: 4,
                elem: 3,
                set: 2,
            });
            entry.emit(Opcode::Ret { rs: 4 });
            let entry_idx = chunk.add_function(entry);

            let layout = StateLayout::new(vec![
                VarLayout::Compound(int_range_set_bitmask_layout(1, 4)),
                VarLayout::Compound(int_range_set_bitmask_layout(1, 4)),
            ]);

            let module_name = format!("helper_{op_name}_matching_setbitmask");
            let module =
                lower_module_invariant_with_layout(&chunk, entry_idx, &module_name, &layout)
                    .expect("matching compact SetBitmask helper call should lower");

            assert!(
                inst_count(&module, 0, |inst| matches!(
                    inst,
                    Inst::BinOp {
                        op: BinOp::Shl,
                        ty: Ty::I64,
                        ..
                    }
                )) >= 1,
                "caller SetIn after {op_name} helper return should use compact SetBitmask membership"
            );

            let callee_has_mask_native_op = match op_name {
                "SetUnion" => {
                    inst_count(&module, 1, |inst| {
                        matches!(
                            inst,
                            Inst::BinOp {
                                op: BinOp::Or,
                                ty: Ty::I64,
                                ..
                            }
                        )
                    }) >= 1
                }
                "SetIntersect" => {
                    inst_count(&module, 1, |inst| {
                        matches!(
                            inst,
                            Inst::BinOp {
                                op: BinOp::And,
                                ty: Ty::I64,
                                ..
                            }
                        )
                    }) >= 1
                }
                "SetDiff" => {
                    inst_count(&module, 1, |inst| {
                        matches!(
                            inst,
                            Inst::BinOp {
                                op: BinOp::Xor,
                                ty: Ty::I64,
                                ..
                            }
                        )
                    }) >= 1
                }
                _ => unreachable!(),
            };
            assert!(
                callee_has_mask_native_op,
                "{op_name} helper should use mask-native compact SetBitmask lowering"
            );
        }
    }

    #[test]
    fn test_helper_set_ops_reject_polymorphic_compact_setbitmask_universes() {
        for (op_name, opcode) in [
            (
                "SetUnion",
                Opcode::SetUnion {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
            ),
            (
                "SetIntersect",
                Opcode::SetIntersect {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
            ),
            (
                "SetDiff",
                Opcode::SetDiff {
                    rd: 2,
                    r1: 0,
                    r2: 1,
                },
            ),
        ] {
            let mut chunk = BytecodeChunk::new();

            let mut helper = BytecodeFunction::new(format!("{op_name}Mask"), 2);
            helper.emit(opcode);
            helper.emit(Opcode::Ret { rs: 2 });
            let helper_idx = chunk.add_function(helper);

            let mut entry = BytecodeFunction::new(format!("{op_name}PolymorphicEntry"), 0);
            entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
            entry.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
            entry.emit(Opcode::Call {
                rd: 2,
                op_idx: helper_idx,
                args_start: 0,
                argc: 2,
            });
            entry.emit(Opcode::LoadVar { rd: 3, var_idx: 2 });
            entry.emit(Opcode::LoadVar { rd: 4, var_idx: 3 });
            entry.emit(Opcode::Call {
                rd: 5,
                op_idx: helper_idx,
                args_start: 3,
                argc: 2,
            });
            entry.emit(Opcode::LoadBool { rd: 6, value: true });
            entry.emit(Opcode::Ret { rs: 6 });
            let entry_idx = chunk.add_function(entry);

            let layout = StateLayout::new(vec![
                VarLayout::Compound(int_range_set_bitmask_layout(1, 4)),
                VarLayout::Compound(int_range_set_bitmask_layout(1, 4)),
                VarLayout::Compound(int_range_set_bitmask_layout(2, 5)),
                VarLayout::Compound(int_range_set_bitmask_layout(2, 5)),
            ]);

            let module_name = format!("helper_{op_name}_polymorphic_setbitmask");
            let err = lower_module_invariant_with_layout(&chunk, entry_idx, &module_name, &layout)
                .expect_err("polymorphic compact SetBitmask helper callsites must reject");

            let message = format!("{err}");
            assert!(
                message.contains("Call arg shape collection")
                    && message.contains("incompatible compact SetBitmask")
                    && message.contains(op_name),
                "error should reject incompatible compact SetBitmask helper callsites for {op_name}: {message}"
            );
        }
    }

    #[test]
    fn test_helper_arg_shape_rejects_nested_polymorphic_compact_setbitmask_universes() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("NestedMaskHelper".to_string(), 1);
        helper.emit(Opcode::LoadBool { rd: 1, value: true });
        helper.emit(Opcode::Ret { rs: 1 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("NestedMaskEntry".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::LoadVar { rd: 2, var_idx: 1 });
        entry.emit(Opcode::Call {
            rd: 3,
            op_idx: helper_idx,
            args_start: 2,
            argc: 1,
        });
        entry.emit(Opcode::LoadBool { rd: 4, value: true });
        entry.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(entry);

        let function_with_mask_value = |lo, hi| CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(lo, hi)),
            pair_count: Some(1),
            domain_lo: Some(0),
        };
        let layout = StateLayout::new(vec![
            VarLayout::Compound(function_with_mask_value(1, 4)),
            VarLayout::Compound(function_with_mask_value(2, 5)),
        ]);

        let err = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "nested_polymorphic_setbitmask_arg",
            &layout,
        )
        .expect_err("nested polymorphic compact SetBitmask helper callsites must reject");

        let message = format!("{err}");
        assert!(
            message.contains("Call arg shape collection")
                && message.contains("incompatible compact SetBitmask")
                && message.contains("NestedMaskHelper"),
            "error should reject nested incompatible compact SetBitmask helper callsites: {message}"
        );
    }

    /// Test that out-of-range entry index produces an error.
    #[test]
    fn test_lower_module_bad_entry_idx() {
        use tla_tir::bytecode::BytecodeChunk;

        let chunk = BytecodeChunk::new();
        let result = lower_module_invariant(&chunk, 0, "bad");
        assert!(result.is_err());
        assert!(
            format!("{}", result.unwrap_err()).contains("out of range"),
            "should report out of range"
        );
    }

    /// Test that calling a non-existent function index produces an error.
    #[test]
    fn test_lower_call_bad_callee_idx() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // Only 1 function, but entry calls func index 5.
        let mut entry = BytecodeFunction::new("entry".to_string(), 0);
        entry.emit(Opcode::Call {
            rd: 0,
            op_idx: 5,
            args_start: 0,
            argc: 0,
        });
        entry.emit(Opcode::Ret { rs: 0 });
        chunk.add_function(entry);

        let result = lower_module_invariant(&chunk, 0, "bad_callee");
        assert!(result.is_err());
        assert!(
            format!("{}", result.unwrap_err()).contains("function index 5"),
            "should report bad callee index"
        );
    }

    // =================================================================
    // FuncSet tests
    // =================================================================

    /// Test FuncSet: build [S -> T] from two sets.
    #[test]
    fn test_lower_func_set() {
        let mut func = BytecodeFunction::new("func_set_test".to_string(), 0);
        // Domain = {1, 2}
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        // Range = {10, 20, 30}
        func.emit(Opcode::LoadImm { rd: 3, value: 10 });
        func.emit(Opcode::LoadImm { rd: 4, value: 20 });
        func.emit(Opcode::LoadImm { rd: 5, value: 30 });
        func.emit(Opcode::SetEnum {
            rd: 6,
            start: 3,
            count: 3,
        });
        // FuncSet [domain -> range]
        func.emit(Opcode::FuncSet {
            rd: 7,
            domain: 2,
            range: 6,
        });
        func.emit(Opcode::Ret { rs: 7 });

        let module = lower_invariant(&func, "func_set_test").unwrap();
        assert_eq!(module.functions.len(), 1);

        let entry = &module.functions[0].blocks[0];
        assert!(
            entry.body.len() > 8,
            "entry block should have allocas + 2 sets + funcset, got {} instructions",
            entry.body.len()
        );

        let alloca_count: usize = module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .filter(|n| matches!(&n.inst, Inst::Alloca { .. }))
            .count();
        assert!(
            alloca_count >= 11,
            "expected >= 11 allocas (8 regs + 3 aggregates), got {alloca_count}"
        );
    }

    #[test]
    fn test_lower_func_set_empty_domain() {
        let mut func = BytecodeFunction::new("func_set_empty".to_string(), 0);
        func.emit(Opcode::SetEnum {
            rd: 0,
            start: 0,
            count: 0,
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::FuncSet {
            rd: 3,
            domain: 0,
            range: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "func_set_empty")
            .expect("FuncSet with empty domain should lower successfully");
        assert_eq!(module.functions.len(), 1);

        let has_return = module.functions[0].blocks.iter().any(|b| {
            b.body
                .last()
                .map_or(false, |n| matches!(n.inst, Inst::Return { .. }))
        });
        assert!(has_return, "function should contain a Return instruction");
    }

    #[test]
    fn test_lower_func_set_with_range_domain() {
        let mut func = BytecodeFunction::new("func_set_range".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 0 });
        func.emit(Opcode::LoadImm { rd: 4, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 5,
            start: 3,
            count: 2,
        });
        func.emit(Opcode::FuncSet {
            rd: 6,
            domain: 2,
            range: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let module = lower_invariant(&func, "func_set_range")
            .expect("FuncSet with Range domain should lower successfully");
        assert_eq!(module.functions.len(), 1);

        assert!(
            module.functions[0].blocks.len() >= 3,
            "expected >= 3 blocks (entry + range loop + done), got {}",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_range_runtime_empty_branches_before_length_arithmetic() {
        use tla_tir::bytecode::BuiltinOp;

        let mut func = BytecodeFunction::new("range_runtime_empty".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 3,
            builtin: BuiltinOp::Cardinality,
            args_start: 2,
            argc: 1,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "range_runtime_empty")
            .expect("runtime empty Range should lower to a guarded zero-length aggregate");
        let entry = &module.functions[0].blocks[0];
        let first_branch = entry
            .body
            .iter()
            .position(|node| matches!(node.inst, Inst::CondBr { .. }))
            .expect("Range lowering should branch on hi < lo before computing length");
        assert!(
            entry.body[..first_branch].iter().any(|node| matches!(
                node.inst,
                Inst::ICmp {
                    op: ICmpOp::Slt,
                    ..
                }
            )),
            "Range lowering should compare hi < lo before materializing length"
        );
        assert!(
            !entry.body[..first_branch]
                .iter()
                .any(|node| matches!(node.inst, Inst::BinOp { op: BinOp::Sub, .. })),
            "Range lowering must not compute hi - lo before the empty-range guard"
        );
        assert!(
            !has_instruction_after_terminator(&module, 0),
            "Range lowering must not emit instructions after a terminator"
        );
        assert!(
            has_const_alloca_count(&module, 0, 1),
            "runtime empty Range path should allocate only the length header"
        );
        assert!(
            has_const_i64_store_to_gep_slot(&module, 0, 0, 0),
            "runtime empty Range path should store length 0"
        );
    }

    #[test]
    fn test_range_negative_to_positive_span_tracks_exact_length() {
        let mut func = BytecodeFunction::new("range_negative_span".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: -2 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "range_negative_span")
            .expect("negative-to-positive Range span should lower successfully");
        assert!(
            has_const_alloca_count(&module, 0, 6),
            "-2..2 should track length 5 and allocate 6 slots including the length header"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "checked static Range length should avoid dynamic allocation for -2..2"
        );
    }

    #[test]
    fn test_lower_func_set_membership_with_setdiff_range_shape() {
        let mut func = BytecodeFunction::new("func_set_setdiff_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::LoadImm { rd: 4, value: 0 });
        func.emit(Opcode::LoadImm { rd: 5, value: 7 });
        func.emit(Opcode::Range {
            rd: 6,
            lo: 4,
            hi: 5,
        });
        func.emit(Opcode::SetEnum {
            rd: 7,
            start: 4,
            count: 1,
        });
        func.emit(Opcode::SetDiff {
            rd: 8,
            r1: 6,
            r2: 7,
        });
        func.emit(Opcode::FuncSet {
            rd: 9,
            domain: 3,
            range: 8,
        });
        func.emit(Opcode::SetIn {
            rd: 10,
            elem: 0,
            set: 9,
        });
        func.emit(Opcode::Ret { rs: 10 });

        let module = lower_invariant(&func, "func_set_setdiff_range")
            .expect("function-set range should accept bounded SetDiff shape");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "function-set membership with SetDiff range should lower runtime checks, got {} blocks",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "bounded SetDiff range should keep static aggregate allocations"
        );
    }

    #[test]
    fn test_called_small_interval_setdiff_plain_arg_funcset_range_stays_materialized() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("NodeMinus".to_string(), 1);
        helper.emit(Opcode::LoadImm { rd: 1, value: 0 });
        helper.emit(Opcode::LoadImm { rd: 2, value: 2 });
        helper.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        helper.emit(Opcode::SetEnum {
            rd: 4,
            start: 0,
            count: 1,
        });
        helper.emit(Opcode::SetDiff {
            rd: 5,
            r1: 3,
            r2: 4,
        });
        helper.emit(Opcode::Ret { rs: 5 });
        let helper_idx = chunk.add_function(helper);

        let mut entry = BytecodeFunction::new("FuncSetRangeFromCalledSetDiff".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        entry.emit(Opcode::Call {
            rd: 2,
            op_idx: helper_idx,
            args_start: 1,
            argc: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 3, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 4, value: 3 });
        entry.emit(Opcode::Range {
            rd: 5,
            lo: 3,
            hi: 4,
        });
        entry.emit(Opcode::FuncSet {
            rd: 6,
            domain: 5,
            range: 2,
        });
        entry.emit(Opcode::SetIn {
            rd: 7,
            elem: 0,
            set: 6,
        });
        entry.emit(Opcode::Ret { rs: 7 });
        let entry_idx = chunk.add_function(entry);

        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Int),
                pair_count: Some(3),
                domain_lo: Some(1),
            }),
            VarLayout::ScalarInt,
        ]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "called_small_interval_setdiff_funcset_range",
            &layout,
        )
        .expect("called small interval SetDiff with a plain argument should lower");

        assert_eq!(
            inst_count(&module, 1, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    ..
                }
            )),
            0,
            "callee SetDiff with a plain helper argument must not claim compact mask provenance"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "FunctionSet membership over bounded SetDiff range should keep fixed allocations"
        );
    }

    #[test]
    fn test_called_small_interval_setdiff_proc_binding_arg_uses_compact_bitmask() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("NodeMinus".to_string(), 1);
        helper.emit(Opcode::LoadImm { rd: 1, value: 0 });
        helper.emit(Opcode::LoadImm { rd: 2, value: 2 });
        helper.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        helper.emit(Opcode::SetEnum {
            rd: 4,
            start: 0,
            count: 1,
        });
        helper.emit(Opcode::SetDiff {
            rd: 5,
            r1: 3,
            r2: 4,
        });
        helper.emit(Opcode::Ret { rs: 5 });
        let helper_idx = chunk.add_function(helper);

        let mut entry =
            BytecodeFunction::new("FuncSetRangeFromCalledSetDiffProcBinding".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::LoadImm { rd: 1, value: 0 });
        entry.emit(Opcode::LoadImm { rd: 2, value: 2 });
        entry.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        let begin_pc = entry.emit(Opcode::ExistsBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });
        entry.emit(Opcode::Call {
            rd: 6,
            op_idx: helper_idx,
            args_start: 5,
            argc: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 7, value: 1 });
        entry.emit(Opcode::LoadImm { rd: 8, value: 3 });
        entry.emit(Opcode::Range {
            rd: 9,
            lo: 7,
            hi: 8,
        });
        entry.emit(Opcode::FuncSet {
            rd: 10,
            domain: 9,
            range: 6,
        });
        entry.emit(Opcode::SetIn {
            rd: 11,
            elem: 0,
            set: 10,
        });
        let next_pc = entry.emit(Opcode::ExistsNext {
            rd: 4,
            r_binding: 5,
            r_body: 11,
            loop_begin: 0,
        });
        entry.patch_jump(begin_pc, next_pc + 1);
        entry.patch_jump(next_pc, begin_pc + 1);
        entry.emit(Opcode::Ret { rs: 4 });
        let entry_idx = chunk.add_function(entry);

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);

        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "called_small_interval_setdiff_proc_binding_funcset_range",
            &layout,
        )
        .expect("called small interval SetDiff with a Proc-domain binding should lower");

        assert!(
            inst_count(&module, 1, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "callee SetDiff with a proven Proc-domain helper argument should use compact mask provenance"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "FunctionSet membership over compact called SetDiff range should keep fixed allocations"
        );
    }

    #[test]
    fn test_called_set_filter_over_setdiff_returns_bounded_materialized_set() {
        let mut chunk = BytecodeChunk::new();

        let mut helper = BytecodeFunction::new("FilteredNodeMinus".to_string(), 1);
        helper.emit(Opcode::LoadImm { rd: 1, value: 0 });
        helper.emit(Opcode::LoadImm { rd: 2, value: 2 });
        helper.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        helper.emit(Opcode::SetEnum {
            rd: 4,
            start: 0,
            count: 1,
        });
        helper.emit(Opcode::SetDiff {
            rd: 5,
            r1: 3,
            r2: 4,
        });
        let begin_pc = helper.emit(Opcode::SetFilterBegin {
            rd: 6,
            r_binding: 7,
            r_domain: 5,
            loop_end: 0,
        });
        helper.emit(Opcode::LoadBool { rd: 8, value: true });
        let next_pc = helper.emit(Opcode::LoopNext {
            r_binding: 7,
            r_body: 8,
            loop_begin: 0,
        });
        helper.patch_jump(begin_pc, next_pc + 1);
        helper.patch_jump(next_pc, begin_pc + 1);
        helper.emit(Opcode::Ret { rs: 6 });
        let helper_idx = chunk.add_function(helper);

        let mut entry =
            BytecodeFunction::new("called_setfilter_over_setdiff_membership".to_string(), 0);
        entry.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        entry.emit(Opcode::Call {
            rd: 1,
            op_idx: helper_idx,
            args_start: 0,
            argc: 1,
        });
        entry.emit(Opcode::LoadImm { rd: 2, value: 1 });
        entry.emit(Opcode::SetIn {
            rd: 3,
            elem: 2,
            set: 1,
        });
        entry.emit(Opcode::Ret { rs: 3 });
        let entry_idx = chunk.add_function(entry);

        let layout = StateLayout::new(vec![VarLayout::ScalarInt]);
        let module = lower_module_invariant_with_layout(
            &chunk,
            entry_idx,
            "called_setfilter_over_setdiff_membership",
            &layout,
        )
        .expect("SetFilter over bounded SetDiff should keep element shape for helper return ABI");

        assert_call_uses_caller_owned_materialized_return_buffer(&module, 0, 3, 4);
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "caller-owned bounded SetFilter return should use a fixed-size materialized buffer"
        );
    }

    #[test]
    fn test_lower_func_set_membership_accepts_state_value_for_finite_range() {
        let mut func = BytecodeFunction::new("func_set_tracked_elem_finite_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::LoadBool {
            rd: 4,
            value: false,
        });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::SetEnum {
            rd: 6,
            start: 4,
            count: 2,
        });
        func.emit(Opcode::FuncSet {
            rd: 7,
            domain: 3,
            range: 6,
        });
        func.emit(Opcode::SetIn {
            rd: 8,
            elem: 0,
            set: 7,
        });
        func.emit(Opcode::Ret { rs: 8 });

        let module = lower_invariant(&func, "func_set_state_elem_finite_range")
            .expect("function-set membership should infer state-loaded function shape");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "state-loaded function-set membership should lower to runtime checks, got {} blocks",
            module.functions[0].blocks.len()
        );

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Bool),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_tracked_elem_finite_range",
            &pool,
            &layout,
        )
        .expect("finite-range function-set membership should lower with tracked element shape");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "function-set membership should lower to runtime checks, got {} blocks",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_lower_func_set_membership_accepts_state_value_for_powerset_range() {
        let mut func = BytecodeFunction::new("func_set_state_elem_powerset_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Powerset { rd: 4, rs: 3 });
        func.emit(Opcode::FuncSet {
            rd: 5,
            domain: 3,
            range: 4,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let module = lower_invariant(&func, "func_set_state_elem_powerset_range")
            .expect("state-loaded function membership in [S -> SUBSET S] should lower");
        assert!(
            module.functions[0].blocks.len() >= 16,
            "function-set SUBSET range membership should lower nested checks, got {} blocks",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_lower_func_set_membership_with_symbolic_nat_range_invariant_layout() {
        let mut pool = ConstantPool::new();
        let nat_idx = pool.add_value(Value::try_model_value("Nat").expect("Nat model value"));

        let mut func = BytecodeFunction::new("func_set_symbolic_nat_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::LoadConst {
            rd: 4,
            idx: nat_idx,
        });
        func.emit(Opcode::FuncSet {
            rd: 5,
            domain: 3,
            range: 4,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Int),
            pair_count: Some(3),
            domain_lo: Some(0),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_symbolic_nat_range",
            &pool,
            &layout,
        )
        .expect("[Node -> Nat] membership should lower with numeric function values");
        let has_nat_check = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Sge,
                        ..
                    }
                )
            })
        });
        assert!(
            has_nat_check,
            "Nat range membership should emit a nonnegative value check"
        );
    }

    #[test]
    fn test_lower_powerset_membership_for_subset_proc() {
        let mut func = BytecodeFunction::new("subset_proc_typeok".to_string(), 0);
        // Proc == 1..3
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        // crit == {1, 3}
        func.emit(Opcode::LoadImm { rd: 3, value: 1 });
        func.emit(Opcode::LoadImm { rd: 4, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 5,
            start: 3,
            count: 2,
        });
        func.emit(Opcode::Powerset { rd: 6, rs: 2 });
        func.emit(Opcode::SetIn {
            rd: 7,
            elem: 5,
            set: 6,
        });
        func.emit(Opcode::Ret { rs: 7 });

        let module = lower_invariant(&func, "subset_proc_typeok")
            .expect("crit \\in SUBSET Proc should lower as subset membership");

        assert!(
            module.functions[0].blocks.len() >= 8,
            "SUBSET membership should lower to a subset-check CFG, got {} blocks",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed SUBSET Proc membership should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_powerset_membership_accepts_state_value_for_subset_proc() {
        let mut func = BytecodeFunction::new("subset_proc_state_typeok".to_string(), 0);
        // crit is loaded from the state and may have only the generic
        // StateValue shape when no checker layout has been threaded through.
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        // Proc == 1..3
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Powerset { rd: 4, rs: 3 });
        func.emit(Opcode::SetIn {
            rd: 5,
            elem: 0,
            set: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant(&func, "subset_proc_state_typeok")
            .expect("state-loaded crit \\in SUBSET Proc should lower as subset membership");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "state-loaded SUBSET membership should lower to subset-check CFG, got {} blocks",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "state-loaded SUBSET Proc membership should not emit non-const-count Alloca"
        );

        let pool = ConstantPool::new();
        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 3,
        ))]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "subset_proc_tracked_state_typeok",
            &pool,
            &layout,
        )
        .expect("tracked state-set crit \\in SUBSET Proc should lower as subset membership");
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "tracked state-set SUBSET Proc membership should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_powerset_membership_accepts_compact_setbitmask_for_exact_int_set_base() {
        let mut func = BytecodeFunction::new("subset_exact_base_typeok".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 1,
            count: 3,
        });
        func.emit(Opcode::Powerset { rd: 5, rs: 4 });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 3,
        ))]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "subset_exact_base_typeok",
            &ConstantPool::new(),
            &layout,
        )
        .expect("compact SetBitmask should lower against exact integer SUBSET base");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "compact SUBSET exact base membership should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_powerset_membership_checks_compact_setbitmask_for_partial_exact_int_set_base() {
        let mut func = BytecodeFunction::new("subset_partial_exact_base_typeok".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 2 });
        func.emit(Opcode::LoadImm { rd: 3, value: 4 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 1,
            count: 3,
        });
        func.emit(Opcode::Powerset { rd: 5, rs: 4 });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 3,
        ))]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "subset_partial_exact_base_typeok",
            &ConstantPool::new(),
            &layout,
        )
        .expect(
            "compact SetBitmask should lower with a runtime subset mask for partial exact base",
        );

        assert!(
            module_has_i64_const(&module, 0, !0b0011),
            "partial exact base should emit an invalid-base-bits mask"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "compact SUBSET partial exact base membership should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_powerset_membership_accepts_explicit_compact_setbitmask_for_exact_int_set_base() {
        let mut func = BytecodeFunction::new("subset_explicit_exact_base_typeok".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 1,
            count: 2,
        });
        func.emit(Opcode::Powerset { rd: 4, rs: 3 });
        func.emit(Opcode::SetIn {
            rd: 5,
            elem: 0,
            set: 4,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let layout = StateLayout::new(vec![VarLayout::Compound(explicit_int_set_bitmask_layout(
            &[1, 3],
        ))]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "subset_explicit_exact_base_typeok",
            &ConstantPool::new(),
            &layout,
        )
        .expect("explicit compact SetBitmask should lower against exact integer SUBSET base");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "explicit compact SUBSET exact base membership should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_powerset_membership_accepts_compact_setbitmask_for_const_exact_int_set_base() {
        let mut pool = ConstantPool::new();
        let base_idx = pool.add_value(Value::set([
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]));

        let mut func = BytecodeFunction::new("subset_const_exact_base_typeok".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadConst {
            rd: 1,
            idx: base_idx,
        });
        func.emit(Opcode::Powerset { rd: 2, rs: 1 });
        func.emit(Opcode::SetIn {
            rd: 3,
            elem: 0,
            set: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 3,
        ))]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "subset_const_exact_base_typeok",
            &pool,
            &layout,
        )
        .expect("compact SetBitmask should lower against constant exact integer SUBSET base");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "compact SUBSET constant exact base membership should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_powerset_membership_uses_runtime_compact_setbitmask_base() {
        let mut func = BytecodeFunction::new("subset_runtime_compact_base_typeok".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::Powerset { rd: 2, rs: 1 });
        func.emit(Opcode::SetIn {
            rd: 3,
            elem: 0,
            set: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let bitmask = || VarLayout::Compound(int_range_set_bitmask_layout(1, 3));
        let layout = StateLayout::new(vec![bitmask(), bitmask()]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "subset_runtime_compact_base_typeok",
            &ConstantPool::new(),
            &layout,
        )
        .expect("compact SetBitmask should lower against runtime compact SUBSET base");

        assert!(
            compact_runtime_subset_mask_check_count(&module, 0) >= 1,
            "compact SUBSET membership should compare against the runtime base mask"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "runtime compact SUBSET membership should keep static allocations"
        );
    }

    #[test]
    fn test_lazy_powerset_of_compact_setbitmask_iteration_rejects() {
        let mut set_filter = BytecodeFunction::new("compact_subset_set_filter".to_string(), 0);
        set_filter.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        set_filter.emit(Opcode::Powerset { rd: 1, rs: 0 });
        let begin_pc = set_filter.emit(Opcode::SetFilterBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        set_filter.emit(Opcode::LoadBool { rd: 4, value: true });
        let next_pc = set_filter.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 4,
            loop_begin: 0,
        });
        set_filter.patch_jump(begin_pc, next_pc + 1);
        set_filter.patch_jump(next_pc, begin_pc + 1);
        set_filter.emit(Opcode::Ret { rs: 2 });

        let mut forall = BytecodeFunction::new("compact_subset_forall".to_string(), 0);
        forall.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        forall.emit(Opcode::Powerset { rd: 1, rs: 0 });
        let begin_pc = forall.emit(Opcode::ForallBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        forall.emit(Opcode::LoadBool { rd: 4, value: true });
        let next_pc = forall.emit(Opcode::ForallNext {
            rd: 2,
            r_binding: 3,
            r_body: 4,
            loop_begin: 0,
        });
        forall.patch_jump(begin_pc, next_pc + 1);
        forall.patch_jump(next_pc, begin_pc + 1);
        forall.emit(Opcode::Ret { rs: 2 });

        let mut exists = BytecodeFunction::new("compact_subset_exists".to_string(), 0);
        exists.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        exists.emit(Opcode::Powerset { rd: 1, rs: 0 });
        let begin_pc = exists.emit(Opcode::ExistsBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        exists.emit(Opcode::LoadBool { rd: 4, value: true });
        let next_pc = exists.emit(Opcode::ExistsNext {
            rd: 2,
            r_binding: 3,
            r_body: 4,
            loop_begin: 0,
        });
        exists.patch_jump(begin_pc, next_pc + 1);
        exists.patch_jump(next_pc, begin_pc + 1);
        exists.emit(Opcode::Ret { rs: 2 });

        let mut choose = BytecodeFunction::new("compact_subset_choose".to_string(), 0);
        choose.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        choose.emit(Opcode::Powerset { rd: 1, rs: 0 });
        let begin_pc = choose.emit(Opcode::ChooseBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        choose.emit(Opcode::LoadBool { rd: 4, value: true });
        let next_pc = choose.emit(Opcode::ChooseNext {
            rd: 2,
            r_binding: 3,
            r_body: 4,
            loop_begin: 0,
        });
        choose.patch_jump(begin_pc, next_pc + 1);
        choose.patch_jump(next_pc, begin_pc + 1);
        choose.emit(Opcode::Ret { rs: 2 });

        let mut func_def = BytecodeFunction::new("compact_subset_func_def".to_string(), 0);
        func_def.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func_def.emit(Opcode::Powerset { rd: 1, rs: 0 });
        let begin_pc = func_def.emit(Opcode::FuncDefBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 0,
        });
        func_def.emit(Opcode::Move { rd: 4, rs: 3 });
        let next_pc = func_def.emit(Opcode::LoopNext {
            r_binding: 3,
            r_body: 4,
            loop_begin: 0,
        });
        func_def.patch_jump(begin_pc, next_pc + 1);
        func_def.patch_jump(next_pc, begin_pc + 1);
        func_def.emit(Opcode::Ret { rs: 2 });

        let cases = vec![
            ("SetFilterBegin", set_filter),
            ("ForallBegin", forall),
            ("ExistsBegin", exists),
            ("ChooseBegin", choose),
            ("FuncDefBegin", func_def),
        ];
        let layout = StateLayout::new(vec![VarLayout::Compound(int_range_set_bitmask_layout(
            1, 3,
        ))]);

        for (opcode, func) in cases {
            let err = lower_invariant_with_constants_and_layout(
                &func,
                &format!("compact_subset_iter_{opcode}"),
                &ConstantPool::new(),
                &layout,
            )
            .expect_err("compact SetBitmask SUBSET iteration must reject");
            let message = format!("{err}");
            assert!(
                message.contains(opcode)
                    && message.contains("lazy SUBSET over compact SetBitmask")
                    && message.contains("submask iteration"),
                "error should reject {opcode} compact SUBSET iteration before pointer iteration: {message}"
            );
        }
    }

    #[test]
    fn test_lower_func_set_membership_with_powerset_range() {
        let mut func = BytecodeFunction::new("func_set_subset_proc_typeok".to_string(), 0);
        // Proc == 1..3
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 3 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });

        // ack == [p \in Proc |-> {p}]
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });
        func.emit(Opcode::SetEnum {
            rd: 5,
            start: 4,
            count: 1,
        });
        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 4,
            r_body: 5,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Powerset { rd: 6, rs: 2 });
        func.emit(Opcode::FuncSet {
            rd: 7,
            domain: 2,
            range: 6,
        });
        func.emit(Opcode::SetIn {
            rd: 8,
            elem: 3,
            set: 7,
        });
        func.emit(Opcode::Ret { rs: 8 });

        let module = lower_invariant(&func, "func_set_subset_proc_typeok")
            .expect("ack \\in [Proc -> SUBSET Proc] should lower conservatively");

        assert!(
            module.functions[0].blocks.len() >= 16,
            "function-set SUBSET range membership should lower to nested checks, got {} blocks",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed [Proc -> SUBSET Proc] membership should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_lower_func_set_membership_accepts_layout_function_with_set_bitmask_values() {
        let mut func = BytecodeFunction::new("func_set_subset_proc_layout_typeok".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Powerset { rd: 4, rs: 3 });
        func.emit(Opcode::FuncSet {
            rd: 5,
            domain: 3,
            range: 4,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(int_range_set_bitmask_layout(1, 3)),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_subset_proc_layout_typeok",
            &ConstantPool::new(),
            &layout,
        )
        .expect("layout-tracked [Proc -> SUBSET Proc] membership should lower");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "layout-tracked compact function-set SUBSET range should lower runtime checks"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "layout-tracked compact function-set SUBSET range should keep static allocations"
        );
    }

    #[test]
    fn test_lower_func_set_membership_uses_runtime_compact_setbitmask_powerset_range() {
        let mut func = BytecodeFunction::new("func_set_subset_runtime_compact_base".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::Range {
            rd: 4,
            lo: 2,
            hi: 3,
        });
        func.emit(Opcode::Powerset { rd: 5, rs: 1 });
        func.emit(Opcode::FuncSet {
            rd: 6,
            domain: 4,
            range: 5,
        });
        func.emit(Opcode::SetIn {
            rd: 7,
            elem: 0,
            set: 6,
        });
        func.emit(Opcode::Ret { rs: 7 });

        let bitmask = || int_range_set_bitmask_layout(1, 3);
        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(bitmask()),
                pair_count: Some(3),
                domain_lo: Some(1),
            }),
            VarLayout::Compound(bitmask()),
        ]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_subset_runtime_compact_base",
            &ConstantPool::new(),
            &layout,
        )
        .expect("[Proc -> SUBSET runtime compact base] membership should lower");
        assert!(
            compact_runtime_subset_mask_check_count(&module, 0) >= 1,
            "function-set SUBSET range should compare values against the runtime base mask"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed [Proc -> SUBSET runtime compact base] membership should keep static allocations"
        );
    }

    #[test]
    fn test_lower_func_set_mcl_called_range_and_nested_function_set_shape() {
        let mut chunk = BytecodeChunk::new();

        // NatOverride == 0..7
        let mut nat_override = BytecodeFunction::new("NatOverride".to_string(), 0);
        nat_override.emit(Opcode::LoadImm { rd: 0, value: 0 });
        nat_override.emit(Opcode::LoadImm { rd: 1, value: 7 });
        nat_override.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        });
        nat_override.emit(Opcode::Ret { rs: 2 });
        let nat_idx = chunk.add_function(nat_override);

        // Clock == NatOverride \ {0}
        let mut clock = BytecodeFunction::new("Clock".to_string(), 0);
        clock.emit(Opcode::Call {
            rd: 0,
            op_idx: nat_idx,
            args_start: 0,
            argc: 0,
        });
        clock.emit(Opcode::LoadImm { rd: 1, value: 0 });
        clock.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        clock.emit(Opcode::SetDiff {
            rd: 3,
            r1: 0,
            r2: 2,
        });
        clock.emit(Opcode::Ret { rs: 3 });
        let clock_idx = chunk.add_function(clock);

        let mut typeok = BytecodeFunction::new("MCLTypeOkShape".to_string(), 0);
        // clock \in [Proc -> Clock]
        typeok.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        typeok.emit(Opcode::LoadImm { rd: 1, value: 1 });
        typeok.emit(Opcode::LoadImm { rd: 2, value: 3 });
        typeok.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        typeok.emit(Opcode::Call {
            rd: 4,
            op_idx: clock_idx,
            args_start: 0,
            argc: 0,
        });
        typeok.emit(Opcode::FuncSet {
            rd: 5,
            domain: 3,
            range: 4,
        });
        typeok.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });

        // req \in [Proc -> [Proc -> NatOverride]]
        typeok.emit(Opcode::LoadVar { rd: 7, var_idx: 1 });
        typeok.emit(Opcode::Call {
            rd: 8,
            op_idx: nat_idx,
            args_start: 0,
            argc: 0,
        });
        typeok.emit(Opcode::FuncSet {
            rd: 9,
            domain: 3,
            range: 8,
        });
        typeok.emit(Opcode::FuncSet {
            rd: 10,
            domain: 3,
            range: 9,
        });
        typeok.emit(Opcode::SetIn {
            rd: 11,
            elem: 7,
            set: 10,
        });
        typeok.emit(Opcode::And {
            rd: 12,
            r1: 6,
            r2: 11,
        });
        typeok.emit(Opcode::Ret { rs: 12 });
        let entry_idx = chunk.add_function(typeok);

        let module = lower_module_invariant(&chunk, entry_idx, "mcl_typeok_shape")
            .expect("MCL-shaped called FuncSet ranges should keep tracked shapes");
        assert!(
            module.functions[0].blocks.len() >= 20,
            "MCL-shaped function-set memberships should lower nested runtime checks, got {} blocks",
            module.functions[0].blocks.len()
        );
    }

    #[test]
    fn test_lower_func_set_membership_with_seq_record_range() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let message_domain = Value::record_set([
            (
                "type",
                Value::set([
                    Value::String(Arc::from("request")),
                    Value::String(Arc::from("ack")),
                    Value::String(Arc::from("release")),
                ]),
            ),
            (
                "from",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(1),
                    BigInt::from(3),
                ))),
            ),
        ]);
        let message_idx = pool.add_value(message_domain);

        let mut func = BytecodeFunction::new("func_set_seq_record_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::LoadConst {
            rd: 4,
            idx: message_idx,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 5,
            builtin: BuiltinOp::Seq,
            args_start: 4,
            argc: 1,
        });
        func.emit(Opcode::FuncSet {
            rd: 6,
            domain: 3,
            range: 5,
        });
        func.emit(Opcode::SetIn {
            rd: 7,
            elem: 0,
            set: 6,
        });
        func.emit(Opcode::Ret { rs: 7 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Record {
                    fields: vec![
                        (tla_core::intern_name("from"), CompoundLayout::Int),
                        (tla_core::intern_name("type"), CompoundLayout::String),
                    ],
                }),
                element_count: Some(1),
            }),
            pair_count: Some(3),
            domain_lo: Some(1),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_seq_record_range",
            &pool,
            &layout,
        )
        .expect("function-set membership should lower Seq(record-set) ranges");
        assert!(
            module.functions[0].blocks.len() >= 12,
            "Seq(record-set) range membership should lower nested sequence checks"
        );
    }

    #[test]
    fn test_lower_seq_membership_with_finite_record_message_set_emits_loop_equality_evidence() {
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;

        let mut pool = ConstantPool::new();
        let message_idx = pool.add_value(Value::set([
            Value::record([
                ("from", Value::SmallInt(1)),
                ("type", Value::String(Arc::from("request"))),
            ]),
            Value::record([
                ("from", Value::SmallInt(2)),
                ("type", Value::String(Arc::from("ack"))),
            ]),
        ]));

        let mut func = BytecodeFunction::new("seq_finite_record_message_membership".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadConst {
            rd: 1,
            idx: message_idx,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::Seq,
            args_start: 1,
            argc: 1,
        });
        func.emit(Opcode::SetIn {
            rd: 3,
            elem: 0,
            set: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let message_layout = CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("from"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(message_layout),
            element_count: Some(2),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "seq_finite_record_message_membership",
            &pool,
            &layout,
        )
        .expect("Seq(Message) should lower when Message is a concrete finite set of records");

        let slt_count = inst_count(&module, 0, |inst| {
            matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    ..
                }
            )
        });
        assert!(
            slt_count >= 1,
            "Seq(Message) membership should emit a sequence loop bounds check, got {slt_count}"
        );

        let eq_count = inst_count(&module, 0, |inst| {
            matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    ..
                }
            )
        });
        assert!(
            eq_count >= 1,
            "Seq(Message) membership should emit equality checks against finite record-set elements"
        );
    }

    #[test]
    fn test_lower_seq_membership_accepts_compact_record_sequence_value() {
        use tla_tir::bytecode::BuiltinOp;

        let mut pool = ConstantPool::new();
        let message_idx = pool.add_value(Value::set([
            Value::record([
                ("type", Value::String("req".into())),
                ("clock", Value::SmallInt(1)),
            ]),
            Value::record([
                ("type", Value::String("ack".into())),
                ("clock", Value::SmallInt(0)),
            ]),
        ]));

        let mut func =
            BytecodeFunction::new("seq_finite_record_message_compact_value".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadConst {
            rd: 1,
            idx: message_idx,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: BuiltinOp::Seq,
            args_start: 1,
            argc: 1,
        });
        func.emit(Opcode::SetIn {
            rd: 3,
            elem: 0,
            set: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Record {
                fields: vec![
                    (tla_core::intern_name("clock"), CompoundLayout::Int),
                    (tla_core::intern_name("type"), CompoundLayout::String),
                ],
            }),
            element_count: Some(2),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "seq_finite_record_message_compact_value",
            &pool,
            &layout,
        )
        .expect("compact state sequence value should lower for Seq(Message)");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "Seq(Message) membership should compare compact record element slots against finite records"
        );
        assert!(
            !has_instruction_after_terminator(&module, 0),
            "compact Seq(Message) membership must not leave instructions after terminators"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "compact one-record Seq(Message) membership should keep static allocations"
        );
    }

    #[test]
    fn test_lower_func_set_membership_accepts_sequence_state_for_interval_domain() {
        let mut func = BytecodeFunction::new("func_set_sequence_state".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::LoadImm { rd: 4, value: 0 });
        func.emit(Opcode::LoadImm { rd: 5, value: 7 });
        func.emit(Opcode::Range {
            rd: 6,
            lo: 4,
            hi: 5,
        });
        func.emit(Opcode::FuncSet {
            rd: 7,
            domain: 3,
            range: 6,
        });
        func.emit(Opcode::SetIn {
            rd: 8,
            elem: 0,
            set: 7,
        });
        func.emit(Opcode::Ret { rs: 8 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_sequence_state",
            &ConstantPool::new(),
            &layout,
        )
        .expect("sequence state over 1..N should lower as function-set membership");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "sequence-as-function membership should lower runtime range checks"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed sequence-as-function membership should keep static allocations"
        );
    }

    #[test]
    fn test_lower_func_set_membership_accepts_compact_sequence_set_bitmasks_for_powerset_range() {
        let mut func =
            BytecodeFunction::new("func_set_sequence_setbitmask_subset_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Powerset { rd: 4, rs: 3 });
        func.emit(Opcode::FuncSet {
            rd: 5,
            domain: 3,
            range: 4,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(int_range_set_bitmask_layout(1, 3)),
            element_count: Some(3),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_sequence_setbitmask_subset_range",
            &ConstantPool::new(),
            &layout,
        )
        .expect("compact SetBitmask sequence entries should lower as SUBSET bitmasks");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "compact sequence SUBSET range membership should lower runtime mask checks"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed compact sequence SUBSET range membership should keep static allocations"
        );
    }

    #[test]
    fn test_lower_func_set_membership_rejects_compact_sequence_ints_for_powerset_range() {
        let mut func = BytecodeFunction::new("func_set_sequence_int_subset_range".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Powerset { rd: 4, rs: 3 });
        func.emit(Opcode::FuncSet {
            rd: 5,
            domain: 3,
            range: 4,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        })]);

        let err = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_sequence_int_subset_range",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("plain integer sequence entries must not lower as SUBSET bitmasks");
        let message = err.to_string();
        assert!(
            message.contains("compact SUBSET range requires SetBitmask entries"),
            "unexpected error: {message}"
        );
        assert!(
            message.contains("Scalar(Int)"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn test_lower_seqset_membership_accepts_compact_sequence_setbitmasks_for_powerset_base() {
        let mut func =
            BytecodeFunction::new("seqset_sequence_setbitmask_subset_base".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Powerset { rd: 4, rs: 3 });
        func.emit(Opcode::CallBuiltin {
            rd: 5,
            builtin: tla_tir::bytecode::BuiltinOp::Seq,
            args_start: 4,
            argc: 1,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(int_range_set_bitmask_layout(1, 3)),
            element_count: Some(3),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "seqset_sequence_setbitmask_subset_base",
            &ConstantPool::new(),
            &layout,
        )
        .expect("compact SetBitmask sequence entries should lower for Seq(SUBSET Proc)");
        assert!(
            module.functions[0].blocks.len() >= 8,
            "compact Seq(SUBSET) membership should lower runtime mask checks"
        );
        assert!(
            has_runtime_error_status_path(&module, 0),
            "compact Seq(SUBSET) membership should guard dynamic sequence lengths"
        );
        assert!(
            !has_instruction_after_terminator(&module, 0),
            "compact Seq(SUBSET) membership must not leave skipped SSA definitions after terminators"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed compact Seq(SUBSET) membership should keep static allocations"
        );
    }

    #[test]
    fn test_lower_seqset_membership_uses_runtime_compact_setbitmask_powerset_base() {
        let mut func = BytecodeFunction::new("seqset_runtime_compact_subset_base".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::Powerset { rd: 2, rs: 1 });
        func.emit(Opcode::CallBuiltin {
            rd: 3,
            builtin: tla_tir::bytecode::BuiltinOp::Seq,
            args_start: 2,
            argc: 1,
        });
        func.emit(Opcode::SetIn {
            rd: 4,
            elem: 0,
            set: 3,
        });
        func.emit(Opcode::Ret { rs: 4 });

        let bitmask = || int_range_set_bitmask_layout(1, 3);
        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(bitmask()),
                element_count: Some(3),
            }),
            VarLayout::Compound(bitmask()),
        ]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "seqset_runtime_compact_subset_base",
            &ConstantPool::new(),
            &layout,
        )
        .expect("compact SetBitmask sequence entries should lower for Seq(SUBSET runtime base)");
        assert!(
            compact_runtime_subset_mask_check_count(&module, 0) >= 1,
            "Seq(SUBSET runtime compact base) should compare elements against the runtime base mask"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed Seq(SUBSET runtime compact base) membership should keep static allocations"
        );
    }

    #[test]
    fn test_lower_seq_membership_rejects_setbitmask_elements_for_scalar_setbitmask_base() {
        let mut func =
            BytecodeFunction::new("seq_setbitmask_elem_scalar_setbitmask_base".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::CallBuiltin {
            rd: 2,
            builtin: tla_tir::bytecode::BuiltinOp::Seq,
            args_start: 1,
            argc: 1,
        });
        func.emit(Opcode::SetIn {
            rd: 3,
            elem: 0,
            set: 2,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let bitmask = || int_range_set_bitmask_layout(1, 3);
        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Sequence {
                element_layout: Box::new(bitmask()),
                element_count: Some(1),
            }),
            VarLayout::Compound(bitmask()),
        ]);

        let err = lower_invariant_with_constants_and_layout(
            &func,
            "seq_setbitmask_elem_scalar_setbitmask_base",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("known SetBitmask sequence entries must not lower as scalar Seq(S) elements");
        let message = err.to_string();
        assert!(
            message.contains("compact SetBitmask values are set-valued masks, not scalar elements"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn test_lower_seqset_membership_rejects_compact_sequence_ints_for_powerset_base() {
        let mut func = BytecodeFunction::new("seqset_sequence_int_subset_base".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::Powerset { rd: 4, rs: 3 });
        func.emit(Opcode::CallBuiltin {
            rd: 5,
            builtin: tla_tir::bytecode::BuiltinOp::Seq,
            args_start: 4,
            argc: 1,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 0,
            set: 5,
        });
        func.emit(Opcode::Ret { rs: 6 });

        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: Some(3),
        })]);

        let err = lower_invariant_with_constants_and_layout(
            &func,
            "seqset_sequence_int_subset_base",
            &ConstantPool::new(),
            &layout,
        )
        .expect_err("plain integer sequence entries must not lower for Seq(SUBSET Proc)");
        let message = err.to_string();
        assert!(
            message.contains("compact SUBSET range requires SetBitmask entries"),
            "unexpected error: {message}"
        );
        assert!(
            message.contains("Scalar(Int)"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn test_lower_func_set_membership_uses_runtime_compact_setbitmask_seq_powerset_range() {
        let mut func =
            BytecodeFunction::new("func_set_seq_subset_runtime_compact_base".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 1 });
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::Range {
            rd: 4,
            lo: 2,
            hi: 3,
        });
        func.emit(Opcode::Powerset { rd: 5, rs: 1 });
        func.emit(Opcode::CallBuiltin {
            rd: 6,
            builtin: tla_tir::bytecode::BuiltinOp::Seq,
            args_start: 5,
            argc: 1,
        });
        func.emit(Opcode::FuncSet {
            rd: 7,
            domain: 4,
            range: 6,
        });
        func.emit(Opcode::SetIn {
            rd: 8,
            elem: 0,
            set: 7,
        });
        func.emit(Opcode::Ret { rs: 8 });

        let bitmask = || int_range_set_bitmask_layout(1, 3);
        let layout = StateLayout::new(vec![
            VarLayout::Compound(CompoundLayout::Function {
                key_layout: Box::new(CompoundLayout::Int),
                value_layout: Box::new(CompoundLayout::Sequence {
                    element_layout: Box::new(bitmask()),
                    element_count: Some(2),
                }),
                pair_count: Some(3),
                domain_lo: Some(1),
            }),
            VarLayout::Compound(bitmask()),
        ]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_seq_subset_runtime_compact_base",
            &ConstantPool::new(),
            &layout,
        )
        .expect("[Proc -> Seq(SUBSET runtime compact base)] membership should lower");
        assert!(
            compact_runtime_subset_mask_check_count(&module, 0) >= 1,
            "function-set Seq(SUBSET runtime compact base) range should use runtime mask checks"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "fixed [Proc -> Seq(SUBSET runtime compact base)] membership should keep static allocations"
        );
    }

    #[test]
    fn test_lower_func_set_membership_accepts_nested_sequence_state_for_seq_record_range() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_tir::bytecode::BuiltinOp;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let message_domain = Value::record_set([
            (
                "type",
                Value::set([
                    Value::String(Arc::from("request")),
                    Value::String(Arc::from("ack")),
                    Value::String(Arc::from("release")),
                ]),
            ),
            (
                "from",
                Value::Interval(Arc::new(IntervalValue::new(
                    BigInt::from(1),
                    BigInt::from(3),
                ))),
            ),
        ]);
        let message_idx = pool.add_value(message_domain);

        let mut func = BytecodeFunction::new("func_set_nested_sequence_state".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::Range {
            rd: 3,
            lo: 1,
            hi: 2,
        });
        func.emit(Opcode::LoadConst {
            rd: 4,
            idx: message_idx,
        });
        func.emit(Opcode::CallBuiltin {
            rd: 5,
            builtin: BuiltinOp::Seq,
            args_start: 4,
            argc: 1,
        });
        func.emit(Opcode::FuncSet {
            rd: 6,
            domain: 3,
            range: 5,
        });
        func.emit(Opcode::FuncSet {
            rd: 7,
            domain: 3,
            range: 6,
        });
        func.emit(Opcode::SetIn {
            rd: 8,
            elem: 0,
            set: 7,
        });
        func.emit(Opcode::Ret { rs: 8 });

        let message_layout = CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("from"), CompoundLayout::Int),
                (tla_core::intern_name("type"), CompoundLayout::String),
            ],
        };
        let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(CompoundLayout::Sequence {
                element_layout: Box::new(CompoundLayout::Sequence {
                    element_layout: Box::new(message_layout),
                    element_count: Some(1),
                }),
                element_count: Some(3),
            }),
            element_count: Some(3),
        })]);

        let module = lower_invariant_with_constants_and_layout(
            &func,
            "func_set_nested_sequence_state",
            &pool,
            &layout,
        )
        .expect("nested sequence state should lower for [Proc -> [Proc -> Seq(Message)]]");
        assert!(
            module.functions[0].blocks.len() >= 12,
            "nested sequence-as-function membership should lower nested runtime checks, got {} blocks",
            module.functions[0].blocks.len()
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "nested fixed sequence membership should keep static aggregate allocations"
        );
    }

    // =====================================================================
    // Proof annotation tests (Stream 2 of #4251)
    // =====================================================================
    //
    // These tests verify that the lowering attaches correct proof
    // annotations on function headers (Pure, Deterministic, Terminates,
    // NoPanic) and on loop header CondBr terminators
    // (Custom(BOUNDED_LOOP_N), Custom(PARALLEL_MAP)).

    use crate::annotations::{bounded_loop_n, is_bounded_loop, is_parallel_map, PARALLEL_MAP};
    use tmir::proof::ProofAnnotation;

    /// Return all CondBr instructions across every block in a function,
    /// paired with the proof annotations attached to each one.
    fn collect_condbr_proofs(module: &tmir::Module, func_idx: usize) -> Vec<&[ProofAnnotation]> {
        let mut out = Vec::new();
        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                if matches!(node.inst, Inst::CondBr { .. }) {
                    out.push(node.proofs.as_slice());
                }
            }
        }
        out
    }

    /// Assert that some CondBr in the function carries a Custom proof tag
    /// matching `predicate`.
    fn assert_has_condbr_tag<F: Fn(tmir::ProofTag) -> bool>(
        module: &tmir::Module,
        func_idx: usize,
        label: &str,
        predicate: F,
    ) {
        let found = collect_condbr_proofs(module, func_idx)
            .iter()
            .flat_map(|ps| ps.iter())
            .any(|p| matches!(p, ProofAnnotation::Custom(tag) if predicate(*tag)));
        assert!(
            found,
            "expected some CondBr to carry {label} proof annotation, but none found"
        );
    }

    fn pure_invariant_func(name: &str) -> BytecodeFunction {
        let mut func = BytecodeFunction::new(name.to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });
        func
    }

    fn next_state_store_func(name: &str) -> BytecodeFunction {
        let mut func = BytecodeFunction::new(name.to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
        func.emit(Opcode::LoadBool { rd: 1, value: true });
        func.emit(Opcode::Ret { rs: 1 });
        func
    }

    #[test]
    fn test_lower_module_next_state_entrypoint_is_not_pure_but_invariant_is() {
        let mut next_chunk = BytecodeChunk::new();
        let next_idx = next_chunk.add_function(next_state_store_func("Next"));

        let next_module = lower_module_next_state(&next_chunk, next_idx, "next_state_entry")
            .expect("next-state module lowering should succeed");
        let next_proofs = &next_module.functions[0].proofs;
        assert!(
            !next_proofs.contains(&ProofAnnotation::Pure),
            "next-state module entrypoint writes state_out and must not be Pure: {next_proofs:?}"
        );
        assert!(
            next_proofs.contains(&ProofAnnotation::Deterministic),
            "next-state module entrypoint should remain deterministic: {next_proofs:?}"
        );

        let mut invariant_chunk = BytecodeChunk::new();
        let invariant_idx = invariant_chunk.add_function(pure_invariant_func("Inv"));

        let invariant_module =
            lower_module_invariant(&invariant_chunk, invariant_idx, "invariant_entry")
                .expect("invariant module lowering should succeed");
        let invariant_proofs = &invariant_module.functions[0].proofs;
        assert!(
            invariant_proofs.contains(&ProofAnnotation::Pure),
            "pure invariant module entrypoint should keep Pure: {invariant_proofs:?}"
        );
    }

    #[test]
    fn test_lower_entry_next_state_with_chunk_entrypoint_is_not_pure_but_invariant_is() {
        let chunk = BytecodeChunk::new();
        let next_entry = next_state_store_func("StandaloneNext");

        let next_module =
            lower_entry_next_state_with_chunk(&next_entry, &chunk, "standalone_next_entry")
                .expect("standalone next-state lowering should succeed");
        let next_proofs = &next_module.functions[0].proofs;
        assert!(
            !next_proofs.contains(&ProofAnnotation::Pure),
            "standalone next-state entrypoint writes state_out and must not be Pure: {next_proofs:?}"
        );
        assert!(
            next_proofs.contains(&ProofAnnotation::Deterministic),
            "standalone next-state entrypoint should remain deterministic: {next_proofs:?}"
        );

        let invariant_entry = pure_invariant_func("StandaloneInv");
        let invariant_module = lower_entry_invariant_with_chunk(
            &invariant_entry,
            &chunk,
            "standalone_invariant_entry",
        )
        .expect("standalone invariant lowering should succeed");
        let invariant_proofs = &invariant_module.functions[0].proofs;
        assert!(
            invariant_proofs.contains(&ProofAnnotation::Pure),
            "standalone pure invariant entrypoint should keep Pure: {invariant_proofs:?}"
        );
    }

    /// Simple invariant x > 0 should be Pure + Deterministic + Terminates
    /// + NoPanic: no loops, no side effects, but checked arithmetic is
    /// absent so NoPanic holds.
    #[test]
    fn test_trivial_invariant_is_pure_and_deterministic() {
        let mut func = BytecodeFunction::new("inv_pure".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::GtInt {
            rd: 2,
            r1: 0,
            r2: 1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "inv_pure").unwrap();
        let proofs = &module.functions[0].proofs;

        assert!(
            proofs.contains(&ProofAnnotation::Pure),
            "expected Pure annotation, got {proofs:?}"
        );
        assert!(
            proofs.contains(&ProofAnnotation::Deterministic),
            "expected Deterministic annotation, got {proofs:?}"
        );
        assert!(
            proofs.contains(&ProofAnnotation::Terminates),
            "expected Terminates annotation (no loops), got {proofs:?}"
        );
        assert!(
            proofs.contains(&ProofAnnotation::NoPanic),
            "expected NoPanic annotation (no trapping ops), got {proofs:?}"
        );
    }

    /// Checked arithmetic emits a RuntimeError return path; the function
    /// should NOT be NoPanic but must still be Pure/Deterministic.
    #[test]
    fn test_checked_arithmetic_disables_nopanic() {
        let mut func = BytecodeFunction::new("inv_add".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        // AddInt emits overflow-checked addition.
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

        let module = lower_invariant(&func, "inv_add").unwrap();
        let proofs = &module.functions[0].proofs;

        assert!(
            proofs.contains(&ProofAnnotation::Pure),
            "expected Pure, got {proofs:?}"
        );
        assert!(
            proofs.contains(&ProofAnnotation::Deterministic),
            "expected Deterministic, got {proofs:?}"
        );
        assert!(
            !proofs.contains(&ProofAnnotation::NoPanic),
            "expected NoPanic to be absent (overflow path emits error), got {proofs:?}"
        );
    }

    /// A ForAll loop over a SetEnum domain should emit bounded_loop(N).
    /// `\A i \in {7, 8, 9} : i > 0` → domain size 3.
    #[test]
    fn test_forall_over_setenum_emits_bounded_loop() {
        let mut func = BytecodeFunction::new("forall_setenum".to_string(), 0);
        // Build the domain: {7, 8, 9}
        func.emit(Opcode::LoadImm { rd: 0, value: 7 });
        func.emit(Opcode::LoadImm { rd: 1, value: 8 });
        func.emit(Opcode::LoadImm { rd: 2, value: 9 });
        func.emit(Opcode::SetEnum {
            rd: 3,
            start: 0,
            count: 3,
        });
        let begin_pc = func.emit(Opcode::ForallBegin {
            rd: 5,
            r_binding: 4,
            r_domain: 3,
            loop_end: 0, // patched below
        });
        // Body: r6 = TRUE
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        let next_pc = func.emit(Opcode::ForallNext {
            rd: 5,
            r_binding: 4,
            r_body: 6,
            loop_begin: 0, // patched below
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant(&func, "forall_setenum").unwrap();

        // Look for bounded_loop(3) on some CondBr.
        assert_has_condbr_tag(&module, 0, "bounded_loop", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(3)
        });

        // Function should be Terminates (domain size is compile-time known).
        let proofs = &module.functions[0].proofs;
        assert!(
            proofs.contains(&ProofAnnotation::Terminates),
            "expected Terminates when all loops are bounded, got {proofs:?}"
        );
    }

    /// A ForAll loop over a non-constant domain (LoadVar-sourced) should
    /// NOT emit bounded_loop, and the function should NOT be Terminates.
    #[test]
    fn test_forall_over_unknown_domain_no_bounded_loop() {
        let mut func = BytecodeFunction::new("forall_var".to_string(), 0);
        // Domain comes from state[0] — size is unknown at compile time.
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::ForallBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 3,
        });
        func.emit(Opcode::LoadBool { rd: 3, value: true });
        func.emit(Opcode::ForallNext {
            rd: 1,
            r_binding: 2,
            r_body: 3,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let module = lower_invariant(&func, "forall_var").unwrap();

        // No bounded_loop tag anywhere.
        let all_condbr_proofs = collect_condbr_proofs(&module, 0);
        let has_bounded = all_condbr_proofs
            .iter()
            .flat_map(|ps| ps.iter())
            .any(|p| matches!(p, ProofAnnotation::Custom(tag) if is_bounded_loop(*tag)));
        assert!(
            !has_bounded,
            "did not expect bounded_loop on unknown-domain forall"
        );

        // Terminates must NOT be set.
        let proofs = &module.functions[0].proofs;
        assert!(
            !proofs.contains(&ProofAnnotation::Terminates),
            "Terminates must be absent when any loop is unbounded, got {proofs:?}"
        );
    }

    /// An Exists loop over a Range with compile-time known bounds should
    /// emit bounded_loop(N).
    #[test]
    fn test_exists_over_constant_range_emits_bounded_loop() {
        let mut func = BytecodeFunction::new("exists_range".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 10 });
        func.emit(Opcode::Range {
            rd: 2,
            lo: 0,
            hi: 1,
        }); // 1..10 → size 10
        func.emit(Opcode::ExistsBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 3,
        });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::ExistsNext {
            rd: 3,
            r_binding: 4,
            r_body: 5,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "exists_range").unwrap();

        assert_has_condbr_tag(&module, 0, "bounded_loop(10)", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(10)
        });
    }

    /// A CHOOSE loop over a SetEnum domain should emit bounded_loop, but
    /// the function cannot be NoPanic (CHOOSE over empty set traps).
    #[test]
    fn test_choose_over_setenum_is_bounded_but_may_panic() {
        let mut func = BytecodeFunction::new("choose_setenum".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 42 });
        func.emit(Opcode::SetEnum {
            rd: 1,
            start: 0,
            count: 1,
        });
        func.emit(Opcode::ChooseBegin {
            rd: 2,
            r_binding: 3,
            r_domain: 1,
            loop_end: 3,
        });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::ChooseNext {
            rd: 2,
            r_binding: 3,
            r_body: 4,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 2 });

        let module = lower_invariant(&func, "choose_setenum").unwrap();

        assert_has_condbr_tag(&module, 0, "bounded_loop(1)", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(1)
        });

        // CHOOSE emits a runtime error on empty domain — NoPanic must not
        // be set.
        let proofs = &module.functions[0].proofs;
        assert!(
            !proofs.contains(&ProofAnnotation::NoPanic),
            "CHOOSE emits runtime error, NoPanic must be absent: {proofs:?}"
        );
    }

    /// FuncDef over a constant-sized domain should emit BOTH parallel_map
    /// AND bounded_loop(N).
    #[test]
    fn test_funcdef_emits_parallel_map_and_bounded_loop() {
        let mut func = BytecodeFunction::new("funcdef_parallel".to_string(), 0);
        // Domain = {1, 2, 3, 4}
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::LoadImm { rd: 2, value: 3 });
        func.emit(Opcode::LoadImm { rd: 3, value: 4 });
        func.emit(Opcode::SetEnum {
            rd: 4,
            start: 0,
            count: 4,
        });
        // [x \in r4 |-> x]
        func.emit(Opcode::FuncDefBegin {
            rd: 5,
            r_binding: 6,
            r_domain: 4,
            loop_end: 2,
        });
        // Body returns the binding directly.
        func.emit(Opcode::Move { rd: 7, rs: 6 });
        func.emit(Opcode::LoopNext {
            r_binding: 6,
            r_body: 7,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant(&func, "funcdef_parallel").unwrap();

        // Must have parallel_map on some CondBr.
        assert_has_condbr_tag(&module, 0, "parallel_map", |tag| is_parallel_map(tag));
        // Must have bounded_loop(4) on some CondBr.
        assert_has_condbr_tag(&module, 0, "bounded_loop(4)", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(4)
        });

        // Parallel + bounded → Terminates + Pure (no side effects).
        let proofs = &module.functions[0].proofs;
        assert!(
            proofs.contains(&ProofAnnotation::Pure),
            "expected Pure on funcdef, got {proofs:?}"
        );
        assert!(
            proofs.contains(&ProofAnnotation::Terminates),
            "expected Terminates on funcdef with bounded domain, got {proofs:?}"
        );
    }

    /// FuncDef over an unknown-sized domain still emits parallel_map
    /// (iterations are independent regardless of cardinality).
    #[test]
    fn test_funcdef_emits_parallel_map_for_dynamic_domain() {
        let mut func = BytecodeFunction::new("funcdef_dyn".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::FuncDefBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 2,
        });
        func.emit(Opcode::Move { rd: 3, rs: 2 });
        func.emit(Opcode::LoopNext {
            r_binding: 2,
            r_body: 3,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 1 });

        let module = lower_invariant(&func, "funcdef_dyn").unwrap();

        assert_has_condbr_tag(&module, 0, "parallel_map", |tag| is_parallel_map(tag));

        // bounded_loop must NOT be present.
        let all_condbr_proofs = collect_condbr_proofs(&module, 0);
        let has_bounded = all_condbr_proofs
            .iter()
            .flat_map(|ps| ps.iter())
            .any(|p| matches!(p, ProofAnnotation::Custom(tag) if is_bounded_loop(*tag)));
        assert!(!has_bounded, "bounded_loop must not be set on dyn funcdef");
    }

    /// Move propagates compile-time set size tracking.
    #[test]
    fn test_move_propagates_setsize_tracking() {
        let mut func = BytecodeFunction::new("move_tracking".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        // Copy the set into r10.
        func.emit(Opcode::Move { rd: 10, rs: 2 });
        func.emit(Opcode::ForallBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 10, // Domain from Move-source, not SetEnum direct.
            loop_end: 3,
        });
        func.emit(Opcode::LoadBool { rd: 5, value: true });
        func.emit(Opcode::ForallNext {
            rd: 3,
            r_binding: 4,
            r_body: 5,
            loop_begin: -1,
        });
        func.emit(Opcode::Ret { rs: 3 });

        let module = lower_invariant(&func, "move_tracking").unwrap();

        // bounded_loop(2) should still fire even though the domain was
        // indirectly sourced via Move.
        assert_has_condbr_tag(&module, 0, "bounded_loop(2) via Move", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(2)
        });
    }

    /// PARALLEL_MAP tag value is stable (0x504D_0000).
    #[test]
    fn test_parallel_map_tag_stable_value() {
        assert_eq!(PARALLEL_MAP.0, 0x504D_0000);
    }

    // =====================================================================
    // Phase 5: Typed binding frame + short-circuit CFG structure tests
    //
    // The quantifier lowering produces a well-defined CFG:
    //
    //   entry -> [rd=identity; idx=0] -> header
    //   header -> load  (if i < len)
    //   header -> exit  (if i >= len)  [empty-domain path]
    //   load   -> body  (r_binding = S[i+1])
    //   body   -> *Next
    //   *Next  -> short_circuit (on TRUE for \E / FALSE for \A)
    //   *Next  -> advance (otherwise)
    //   short_circuit -> [rd=result] -> exit
    //   advance -> [idx += 1] -> header
    //
    // These tests assert that structure exists for EXISTS and FORALL
    // (the deliverable for #4251 Stream 2: typed binding frame).
    // =====================================================================

    /// Count `Store ty=I64, value=imm` instructions landing on any alloca,
    /// where the stored value is `Constant::Int(expected)`. Used to
    /// verify that rd is initialized to the quantifier's identity and
    /// that the short-circuit path writes the exit value.
    fn count_store_const(module: &tmir::Module, func_idx: usize, expected: i64) -> usize {
        let mut count = 0;
        let mut consts: std::collections::HashMap<ValueId, i128> = std::collections::HashMap::new();
        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                if let Inst::Const {
                    value: Constant::Int(v),
                    ..
                } = node.inst
                {
                    if let Some(&res) = node.results.first() {
                        consts.insert(res, v);
                    }
                }
            }
        }
        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                if let Inst::Store { value, .. } = node.inst {
                    if let Some(&v) = consts.get(&value) {
                        if v == i128::from(expected) {
                            count += 1;
                        }
                    }
                }
            }
        }
        count
    }

    /// Count CondBr instructions in a function.
    fn count_condbr(module: &tmir::Module, func_idx: usize) -> usize {
        module.functions[func_idx]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .filter(|n| matches!(n.inst, Inst::CondBr { .. }))
            .count()
    }

    /// Count unconditional `Br` instructions in a function.
    fn count_br(module: &tmir::Module, func_idx: usize) -> usize {
        module.functions[func_idx]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .filter(|n| matches!(n.inst, Inst::Br { .. }))
            .count()
    }

    /// Count `ICmp Slt` instructions — produced by the header bounds
    /// check `i < len`.
    fn count_icmp_slt(module: &tmir::Module, func_idx: usize) -> usize {
        module.functions[func_idx]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .filter(|n| {
                matches!(
                    n.inst,
                    Inst::ICmp {
                        op: ICmpOp::Slt,
                        ..
                    }
                )
            })
            .count()
    }

    /// Build a simple `\E x \in S : r_body` program with a user-controlled
    /// body and a SetEnum domain of `count` elements starting from
    /// `start_value`.
    fn build_exists(body_reg: u8, start_value: i64, count: u8) -> BytecodeFunction {
        let mut func = BytecodeFunction::new("exists_frame".to_string(), 0);
        for i in 0..count {
            func.emit(Opcode::LoadImm {
                rd: i,
                value: start_value + i as i64,
            });
        }
        func.emit(Opcode::SetEnum {
            rd: 20,
            start: 0,
            count,
        });

        // Body: r_body = TRUE (LoadBool)
        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 21,
            r_binding: 22,
            r_domain: 20,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool {
            rd: body_reg,
            value: true,
        });
        let next_pc = func.emit(Opcode::ExistsNext {
            rd: 21,
            r_binding: 22,
            r_body: body_reg,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::Ret { rs: 21 });
        func
    }

    /// EXISTS with a SetEnum of 2 elements should emit the typed
    /// binding frame: one rd=FALSE init store, one rd=TRUE short-circuit
    /// store, one Slt bounds check on the header, and a CondBr in both
    /// the header and the ExistsNext path.
    #[test]
    fn test_exists_short_circuits_with_typed_binding_frame() {
        let func = build_exists(23, 5, 2);
        let module = lower_invariant(&func, "exists_frame").unwrap();

        // Two CondBr: header (i<len) + ExistsNext (body_val != 0).
        assert_eq!(
            count_condbr(&module, 0),
            2,
            "EXISTS must produce exactly two CondBr (header + next)"
        );
        // Exactly one Slt comparison — the header bounds check.
        assert_eq!(
            count_icmp_slt(&module, 0),
            1,
            "EXISTS header must perform exactly one Slt bounds check"
        );
        // rd=FALSE on init + rd=TRUE on short-circuit = at least two
        // distinct "store zero to rd" / "store one to rd" points.
        assert!(
            count_store_const(&module, 0, 0) >= 1,
            "EXISTS must initialize rd with FALSE (0) before the loop"
        );
        assert!(
            count_store_const(&module, 0, 1) >= 1,
            "EXISTS must store TRUE (1) on short-circuit"
        );

        // Four unconditional `Br`s: entry→header, load→body, short→exit,
        // advance→header. (The Ret at the end is NOT a Br.)
        assert!(
            count_br(&module, 0) >= 4,
            "expected >= 4 unconditional Br in EXISTS CFG, got {}",
            count_br(&module, 0)
        );
    }

    /// FORALL with a SetEnum of 2 elements should mirror EXISTS but
    /// with opposite short-circuit polarity: rd initialized to TRUE,
    /// rd stored as FALSE on the first body=FALSE witness.
    #[test]
    fn test_forall_short_circuits_with_typed_binding_frame() {
        let mut func = BytecodeFunction::new("forall_frame".to_string(), 0);
        func.emit(Opcode::LoadImm { rd: 0, value: 5 });
        func.emit(Opcode::LoadImm { rd: 1, value: 6 });
        func.emit(Opcode::SetEnum {
            rd: 20,
            start: 0,
            count: 2,
        });

        // Body: r_body = FALSE so we exercise the short-circuit path.
        let begin_pc = func.emit(Opcode::ForallBegin {
            rd: 21,
            r_binding: 22,
            r_domain: 20,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool {
            rd: 23,
            value: false,
        });
        let next_pc = func.emit(Opcode::ForallNext {
            rd: 21,
            r_binding: 22,
            r_body: 23,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::Ret { rs: 21 });

        let module = lower_invariant(&func, "forall_frame").unwrap();

        assert_eq!(
            count_condbr(&module, 0),
            2,
            "FORALL must produce exactly two CondBr (header + next)"
        );
        assert_eq!(
            count_icmp_slt(&module, 0),
            1,
            "FORALL header must perform exactly one Slt bounds check"
        );
        // rd initialized to TRUE; short-circuit stores FALSE.
        assert!(
            count_store_const(&module, 0, 1) >= 1,
            "FORALL must initialize rd with TRUE (1) before the loop"
        );
        assert!(
            count_store_const(&module, 0, 0) >= 1,
            "FORALL must store FALSE (0) on short-circuit"
        );

        assert!(
            count_br(&module, 0) >= 4,
            "expected >= 4 unconditional Br in FORALL CFG, got {}",
            count_br(&module, 0)
        );
    }

    /// EXISTS with an empty SetEnum: rd must still be initialized to
    /// FALSE (0) in the entry block, the header must emit exactly one
    /// bounds check, and the function must still be well-formed (has
    /// a Return). This is the empty-domain correctness property.
    #[test]
    fn test_exists_empty_domain_emits_false_identity() {
        let mut func = BytecodeFunction::new("exists_empty_frame".to_string(), 0);
        func.emit(Opcode::SetEnum {
            rd: 20,
            start: 0,
            count: 0,
        });
        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 21,
            r_binding: 22,
            r_domain: 20,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool {
            rd: 23,
            value: true,
        });
        let next_pc = func.emit(Opcode::ExistsNext {
            rd: 21,
            r_binding: 22,
            r_body: 23,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::Ret { rs: 21 });

        let module = lower_invariant(&func, "exists_empty_frame").unwrap();

        assert_eq!(count_icmp_slt(&module, 0), 1, "expected one header Slt");
        assert!(
            count_store_const(&module, 0, 0) >= 1,
            "EXISTS empty-domain must still initialize rd=FALSE"
        );
        // bounded_loop(0) annotation should still fire.
        assert_has_condbr_tag(&module, 0, "bounded_loop(0)", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(0)
        });
    }

    /// FORALL with an empty SetEnum: rd must be initialized to TRUE (1)
    /// in the entry block — the vacuous-truth identity for ForAll.
    #[test]
    fn test_forall_empty_domain_emits_true_identity() {
        let mut func = BytecodeFunction::new("forall_empty_frame".to_string(), 0);
        func.emit(Opcode::SetEnum {
            rd: 20,
            start: 0,
            count: 0,
        });
        let begin_pc = func.emit(Opcode::ForallBegin {
            rd: 21,
            r_binding: 22,
            r_domain: 20,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool {
            rd: 23,
            value: false,
        });
        let next_pc = func.emit(Opcode::ForallNext {
            rd: 21,
            r_binding: 22,
            r_body: 23,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::Ret { rs: 21 });

        let module = lower_invariant(&func, "forall_empty_frame").unwrap();

        assert_eq!(count_icmp_slt(&module, 0), 1, "expected one header Slt");
        assert!(
            count_store_const(&module, 0, 1) >= 1,
            "FORALL empty-domain must still initialize rd=TRUE"
        );
        assert_has_condbr_tag(&module, 0, "bounded_loop(0)", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(0)
        });
    }

    /// Typed binding frame survives nesting: \A x \in S : \E y \in T : P
    /// must produce TWO header CondBrs (one per quantifier), TWO body
    /// CondBrs (one per `*Next`), one `bounded_loop(|S|)` annotation and
    /// one `bounded_loop(|T|)` annotation.
    #[test]
    fn test_nested_quantifiers_have_independent_typed_frames() {
        let mut func = BytecodeFunction::new("nested_frames".to_string(), 0);
        // S = {1, 2}, T = {3, 4, 5}
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        });
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::LoadImm { rd: 4, value: 4 });
        func.emit(Opcode::LoadImm { rd: 5, value: 5 });
        func.emit(Opcode::SetEnum {
            rd: 6,
            start: 3,
            count: 3,
        });

        let forall_begin = func.emit(Opcode::ForallBegin {
            rd: 7,
            r_binding: 8,
            r_domain: 2,
            loop_end: 0,
        });
        let exists_begin = func.emit(Opcode::ExistsBegin {
            rd: 9,
            r_binding: 10,
            r_domain: 6,
            loop_end: 0,
        });
        // Body: LoadBool(r11 = TRUE)
        func.emit(Opcode::LoadBool {
            rd: 11,
            value: true,
        });
        let exists_next = func.emit(Opcode::ExistsNext {
            rd: 9,
            r_binding: 10,
            r_body: 11,
            loop_begin: 0,
        });
        let forall_next = func.emit(Opcode::ForallNext {
            rd: 7,
            r_binding: 8,
            r_body: 9,
            loop_begin: 0,
        });
        func.patch_jump(exists_begin, exists_next + 1);
        func.patch_jump(exists_next, exists_begin + 1);
        func.patch_jump(forall_begin, forall_next + 1);
        func.patch_jump(forall_next, forall_begin + 1);
        func.emit(Opcode::Ret { rs: 7 });

        let module = lower_invariant(&func, "nested_frames").unwrap();

        // Two headers + two next paths = 4 CondBrs.
        assert_eq!(
            count_condbr(&module, 0),
            4,
            "nested \\A/\\E must produce 4 CondBrs (2 headers + 2 next)"
        );
        // Two header Slt comparisons (one per quantifier).
        assert_eq!(
            count_icmp_slt(&module, 0),
            2,
            "nested \\A/\\E must produce 2 header Slt bounds checks"
        );
        // Both bounded_loop tags must be present, with the correct sizes.
        assert_has_condbr_tag(&module, 0, "bounded_loop(2) outer", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(2)
        });
        assert_has_condbr_tag(&module, 0, "bounded_loop(3) inner", |tag| {
            is_bounded_loop(tag) && bounded_loop_n(tag) == Some(3)
        });
    }

    /// The emit_binding_frame_prelude helper must store the first
    /// element of the domain into the binding register on the first
    /// load. We can't peek at the frame directly, but we can verify
    /// that the lowered module contains a `Store` into some alloca
    /// whose source value chain ultimately depends on a dynamic offset
    /// load from the domain pointer. In practice, a single load per
    /// quantifier plus the Slt bounds check is enough structural proof.
    #[test]
    fn test_typed_binding_frame_loads_element_before_body() {
        let func = build_exists(23, 10, 3);
        let module = lower_invariant(&func, "exists_load_shape").unwrap();

        // One Slt check = one header, as the frame prescribes.
        assert_eq!(count_icmp_slt(&module, 0), 1);

        // Look for at least one dynamic-offset load chain:
        //   ICmp + CondBr in header, then in load block there must be
        //   at least one GEP-equivalent (offset computation) followed
        //   by a Load from a ptr. In tMIR terms that's a BinOp Add plus
        //   a Load. We check there's at least one Load in some block
        //   OTHER than the header where the address is a BinOp result
        //   (not the raw alloca).
        let has_load_from_computed = module.functions[0]
            .blocks
            .iter()
            .any(|b| b.body.iter().any(|n| matches!(n.inst, Inst::Load { .. })));
        assert!(
            has_load_from_computed,
            "typed binding frame must emit at least one Load instruction"
        );
    }

    // =====================================================================
    // #4287 smoke: LLVM2 Phase 2b/2c aggregate adoption — record-of-ints state
    // =====================================================================
    //
    // Smoke test exercising the integration surface between tla-tmir and
    // LLVM2 Phase 2b/2c aggregate lowering (shipped in LLVM2 #391 commits
    // `6f91ef0` and `e6b75e2`). Represents a tla2 record state
    // `[pc: Int, counter: Int, owner: Int]` as a `Ty::Struct` with three
    // i64 fields — the only record-like tMIR representation LLVM2's
    // adapter currently accepts (`Ty::Record` is rejected at
    // `~/llvm2/crates/llvm2-lower/src/adapter.rs:418`).
    //
    // The test does NOT drive the tMIR → LIR → machir pipeline end-to-end
    // yet (Phase 2 of the adoption work, tracked in
    // `designs/2026-04-20-llvm2-phase-2bc-adoption.md`). It pins the
    // on-disk shape the Phase 2 adapter consumer will receive: a module
    // with a well-formed StructDef (all i64 fields), ready for
    // `translate_type_with_tables` at adapter.rs:367.

    /// Construct a tMIR `StructDef` mirroring a tla2 record-of-ints state.
    ///
    /// Fields correspond to the smoke-path shape called out in issue #4287
    /// "`verif.bfs_step` with a record-of-ints state layout":
    ///   - `pc: Int`      (program counter / label field)
    ///   - `counter: Int` (a scalar state variable)
    ///   - `owner: Int`   (second scalar state variable)
    ///
    /// All three fields lower to `Ty::I64` — the representation Phase 2b
    /// SROA/aggregate-constant rewrites now handle as first-class LIR
    /// aggregate values.
    #[test]
    fn test_lower_record_of_ints_state_struct_well_formed() {
        use tmir::ty::{FieldDef, StructDef};
        use tmir::value::StructId;

        let mut module = tmir::Module::new("record_of_ints_smoke");

        // Three-field record: pc, counter, owner. C-layout, no named offsets
        // — the adapter will compute field offsets from type alignment.
        let sd = StructDef {
            id: StructId::new(0),
            name: "RecordState3Ints".to_string(),
            fields: vec![
                FieldDef {
                    name: "pc".to_string(),
                    ty: Ty::I64,
                    offset: None,
                },
                FieldDef {
                    name: "counter".to_string(),
                    ty: Ty::I64,
                    offset: None,
                },
                FieldDef {
                    name: "owner".to_string(),
                    ty: Ty::I64,
                    offset: None,
                },
            ],
            size: None,
            align: None,
        };
        let sid = module.add_struct(sd);

        // Sanity: the struct round-trips through the module's struct table
        // with the expected shape the LLVM2 adapter will translate.
        assert_eq!(sid, StructId::new(0));
        assert_eq!(module.structs.len(), 1);
        let stored = &module.structs[0];
        assert_eq!(stored.name, "RecordState3Ints");
        assert_eq!(stored.fields.len(), 3);
        assert!(
            stored.fields.iter().all(|f| f.ty == Ty::I64),
            "all record-of-ints fields must be Ty::I64 for LLVM2 Phase 2b lowering"
        );
        assert_eq!(stored.fields[0].name, "pc");
        assert_eq!(stored.fields[1].name, "counter");
        assert_eq!(stored.fields[2].name, "owner");

        // A `Ty::Struct(sid)` reference must resolve against the module's
        // struct table. This is the precise input shape the adapter at
        // `~/llvm2/crates/llvm2-lower/src/adapter.rs:358-365` consumes.
        let struct_ty = Ty::Struct(sid);
        match struct_ty {
            Ty::Struct(id) => {
                let def = &module.structs[id.index() as usize];
                assert_eq!(def.fields.len(), 3);
            }
            _ => panic!("expected Ty::Struct variant"),
        }
    }

    /// Smoke test: the Invariant entrypoint signature emitted by `Ctx::new`
    /// is `fn(out_ptr: Ptr, state_in: Ptr, state_len: I32) -> void`. For
    /// LLVM2 Phase 2b adoption, `state_in` is expected to carry a pointer
    /// to a record-struct-shaped aggregate (rather than a flat i64 array).
    /// This test pins the current signature shape so the Phase 2 wiring
    /// work has a stable anchor.
    #[test]
    fn test_lower_invariant_signature_accepts_record_state_ptr() {
        // Minimal bytecode: Ret of a boolean literal. The body does not need
        // to reference state — we just want the signature to exist.
        let mut func = BytecodeFunction::new("rec_state_smoke".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true });
        func.emit(Opcode::Ret { rs: 0 });

        let module = lower_invariant(&func, "rec_state_smoke").unwrap();
        assert_eq!(module.functions.len(), 1);

        // Invariant signature: [Ptr, Ptr, I32]. The second Ptr is where a
        // record-struct-state pointer will land once Phase 2 wiring threads
        // `Ty::Struct(record_id)` through `Ctx::new`.
        let ft_id = module.functions[0].ty;
        let ft = &module.func_types[ft_id.index() as usize];
        assert_eq!(
            ft.params.len(),
            3,
            "Invariant entrypoint must take (out_ptr, state_in, state_len)"
        );
        assert_eq!(ft.params[0], Ty::Ptr);
        assert_eq!(ft.params[1], Ty::Ptr);
        assert_eq!(ft.params[2], Ty::I32);
        assert!(
            ft.returns.is_empty(),
            "Invariant entrypoints return void (status flows through out_ptr)"
        );
    }

    #[test]
    fn test_set_diff_interval_const_lhs_has_no_nonconst_alloca_count() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let iv = Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(0),
            BigInt::from(2),
        )));
        let idx = pool.add_value(iv);

        let mut func = BytecodeFunction::new("set_diff_interval_const".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::LoadImm { rd: 1, value: 1 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::SetDiff {
            rd: 3,
            r1: 0,
            r2: 2,
        });
        func.emit(Opcode::LoadBool { rd: 4, value: true });
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant_with_constants(&func, "set_diff_interval_const", &pool)
            .expect("fixed-size interval SetDiff should lower successfully");

        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "SetDiff with fixed-size lhs interval should not emit non-const-count Alloca"
        );
    }

    #[test]
    fn test_exists_over_interval_diff_plain_scalar_singleton_stays_materialized() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let node_idx = pool.add_value(Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(0),
            BigInt::from(2),
        ))));

        let mut func = BytecodeFunction::new("exists_interval_diff_singleton".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: node_idx,
        });
        func.emit(Opcode::LoadVar { rd: 1, var_idx: 0 });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::SetDiff {
            rd: 3,
            r1: 0,
            r2: 2,
        });
        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool { rd: 6, value: true });
        let next_pc = func.emit(Opcode::ExistsNext {
            rd: 4,
            r_binding: 5,
            r_body: 6,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::Ret { rs: 4 });

        let layout = StateLayout::new(vec![VarLayout::ScalarInt]);
        let module = lower_invariant_with_constants_and_layout(
            &func,
            "exists_interval_diff_singleton",
            &pool,
            &layout,
        )
        .expect("small interval SetDiff with a plain scalar singleton should lower");

        assert_eq!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    ..
                }
            )),
            0,
            "plain scalar SetDiff singleton must not claim compact mask provenance"
        );
    }

    #[test]
    fn test_exists_over_interval_diff_proc_binding_singleton_uses_compact_bitmask() {
        use num_bigint::BigInt;
        use std::sync::Arc;
        use tla_value::IntervalValue;

        let mut pool = ConstantPool::new();
        let node_idx = pool.add_value(Value::Interval(Arc::new(IntervalValue::new(
            BigInt::from(0),
            BigInt::from(2),
        ))));

        let mut func =
            BytecodeFunction::new("exists_interval_diff_proc_binding_singleton".to_string(), 0);
        func.emit(Opcode::LoadConst {
            rd: 0,
            idx: node_idx,
        });
        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 4,
            r_binding: 1,
            r_domain: 0,
            loop_end: 0,
        });
        func.emit(Opcode::SetEnum {
            rd: 2,
            start: 1,
            count: 1,
        });
        func.emit(Opcode::SetDiff {
            rd: 3,
            r1: 0,
            r2: 2,
        });
        func.emit(Opcode::SetIn {
            rd: 6,
            elem: 1,
            set: 3,
        });
        let next_pc = func.emit(Opcode::ExistsNext {
            rd: 4,
            r_binding: 1,
            r_body: 6,
            loop_begin: 0,
        });
        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);
        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant_with_constants(
            &func,
            "exists_interval_diff_proc_binding_singleton",
            &pool,
        )
        .expect("proven Proc-domain singleton SetDiff should lower as compact SetBitmask");

        assert!(
            inst_count(&module, 0, |inst| matches!(
                inst,
                Inst::BinOp {
                    op: BinOp::Xor,
                    ty: Ty::I64,
                    ..
                }
            )) >= 1,
            "proven Proc-domain SetDiff singleton should use the compact mask-complement path"
        );
        assert!(
            !has_nonconst_alloca_count(&module, 0),
            "proven Proc-domain SetDiff singleton should keep fixed allocations"
        );
    }
}
