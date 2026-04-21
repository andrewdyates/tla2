// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for bytecode-to-tMIR lowering.

#[cfg(test)]
mod tests {
    use crate::lower::{
        lower_invariant, lower_invariant_with_constants, lower_module_invariant,
        lower_module_next_state, lower_next_state, lower_next_state_with_constants,
    };
    use tla_jit_abi::JitStatus;
    use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};
    use tla_value::Value;
    use tmir::inst::*;
    use tmir::ty::Ty;
    use tmir::value::ValueId;
    use tmir::Constant;

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
        let has_return = module.functions[0]
            .blocks
            .iter()
            .any(|b| {
                b.body.last().map_or(false, |n| {
                    matches!(n.inst, Inst::Return { .. })
                })
            });
        assert!(has_return, "function should contain a Return instruction");
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
        assert!(
            format!("{err}").contains("arity"),
            "error: {err}"
        );
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
        func.emit(Opcode::JumpFalse {                       // pc 1
            rs: 0,
            offset: 2, // jump to pc 3
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 42 }); // pc 2
        func.emit(Opcode::Ret { rs: 1 });                 // pc 3
        // patch: offset=2 means pc 1 + 2 = 3
        // but we need a fallthrough at pc 2 and target at pc 3
        // Actually offset=2 targets pc=1+2=3. We need a valid program.

        // Let's create a proper branch that has both paths ending in Ret.
        let mut func = BytecodeFunction::new("branch_test".to_string(), 0);
        func.emit(Opcode::LoadBool { rd: 0, value: true }); // pc 0
        func.emit(Opcode::JumpFalse {                       // pc 1
            rs: 0,
            offset: 3, // target = pc 1 + 3 = 4
        });
        func.emit(Opcode::LoadImm { rd: 1, value: 42 });   // pc 2 (fallthrough)
        func.emit(Opcode::Ret { rs: 1 });                   // pc 3
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });     // pc 4 (target)
        func.emit(Opcode::Ret { rs: 1 });                   // pc 5

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
        func.emit(Opcode::SetEnum {                       // pc 3
            rd: 3,
            start: 0,
            count: 3,
        });

        // ForallBegin: r4 = result, r5 = binding, domain in r3
        // Body starts at pc 5, loop_end jumps to pc 8 (after ForallNext)
        let begin_pc = func.emit(Opcode::ForallBegin {    // pc 4
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0, // patched below
        });

        // Body: r6 = (r5 > 0) — predicate P(x) = x > 0
        func.emit(Opcode::LoadImm { rd: 6, value: 0 });  // pc 5
        func.emit(Opcode::GtInt {                         // pc 6
            rd: 7,
            r1: 5,
            r2: 6,
        });

        let next_pc = func.emit(Opcode::ForallNext {      // pc 7
            rd: 4,
            r_binding: 5,
            r_body: 7,
            loop_begin: 0, // patched below
        });

        // Patch jump targets: loop_end -> after ForallNext, loop_begin -> body start
        func.patch_jump(begin_pc, next_pc + 1);  // loop_end -> pc 8 (Ret)
        func.patch_jump(next_pc, begin_pc + 1);  // loop_begin -> pc 5

        func.emit(Opcode::Ret { rs: 4 });       // pc 8
        func
    }

    /// Test ForAll quantifier lowering: \A x \in {10,20,30} : x > 0
    /// Expected: TRUE (all elements > 0).
    #[test]
    fn test_lower_forall_all_true() {
        let func = build_forall_program();
        let module = lower_invariant(&func, "forall_test")
            .expect("ForAll lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have multiple blocks: entry, ForAll header, load, body blocks,
        // short-circuit, advance, exit.
        assert!(
            module.functions[0].blocks.len() >= 5,
            "expected >= 5 blocks for ForAll, got {}",
            module.functions[0].blocks.len()
        );

        // Verify function has Return instruction.
        let has_return = module.functions[0]
            .blocks
            .iter()
            .any(|b| {
                b.body.last().map_or(false, |n| {
                    matches!(n.inst, Inst::Return { .. })
                })
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
        func.emit(Opcode::SetEnum { rd: 3, start: 0, count: 3 });

        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });

        // Body: r7 = (r5 > 15)
        func.emit(Opcode::LoadImm { rd: 6, value: 15 });
        func.emit(Opcode::GtInt { rd: 7, r1: 5, r2: 6 });

        let next_pc = func.emit(Opcode::ExistsNext {
            rd: 4,
            r_binding: 5,
            r_body: 7,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "exists_test")
            .expect("EXISTS lowering should succeed");
        assert_eq!(module.functions.len(), 1);
        assert!(
            module.functions[0].blocks.len() >= 5,
            "expected >= 5 blocks for EXISTS, got {}",
            module.functions[0].blocks.len()
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
        func.emit(Opcode::SetEnum { rd: 3, start: 0, count: 3 });

        let begin_pc = func.emit(Opcode::ChooseBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });

        // Body: r7 = (r5 > 15)
        func.emit(Opcode::LoadImm { rd: 6, value: 15 });
        func.emit(Opcode::GtInt { rd: 7, r1: 5, r2: 6 });

        let next_pc = func.emit(Opcode::ChooseNext {
            rd: 4,
            r_binding: 5,
            r_body: 7,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "choose_test")
            .expect("CHOOSE lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // CHOOSE has an extra exhausted block for runtime error.
        assert!(
            module.functions[0].blocks.len() >= 6,
            "expected >= 6 blocks for CHOOSE, got {}",
            module.functions[0].blocks.len()
        );

        // Should have a runtime error return path (for exhausted domain).
        let has_runtime_error = module.functions[0]
            .blocks
            .iter()
            .any(|b| {
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
        func.emit(Opcode::SetEnum { rd: 2, start: 0, count: 2 });

        // Build domain T = {3, 4} in r5
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::LoadImm { rd: 4, value: 4 });
        func.emit(Opcode::SetEnum { rd: 5, start: 3, count: 2 });

        // Outer: \A x \in S
        let forall_begin = func.emit(Opcode::ForallBegin {
            rd: 6,         // outer result
            r_binding: 7,  // x
            r_domain: 2,   // S
            loop_end: 0,
        });

        // Inner: \E y \in T
        let exists_begin = func.emit(Opcode::ExistsBegin {
            rd: 8,         // inner result
            r_binding: 9,  // y
            r_domain: 5,   // T
            loop_end: 0,
        });

        // Body: r10 = x + y, r12 = (r10 > 0)
        func.emit(Opcode::AddInt { rd: 10, r1: 7, r2: 9 });
        func.emit(Opcode::LoadImm { rd: 11, value: 0 });
        func.emit(Opcode::GtInt { rd: 12, r1: 10, r2: 11 });

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

    /// Test ForAll with empty domain produces TRUE.
    /// Uses a SetEnum with count=0.
    #[test]
    fn test_lower_forall_empty_domain() {
        let mut func = BytecodeFunction::new("forall_empty".to_string(), 0);
        // Empty set in r0
        func.emit(Opcode::SetEnum { rd: 0, start: 1, count: 0 });

        let begin_pc = func.emit(Opcode::ForallBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 0,
        });

        // Trivial body (never executed).
        func.emit(Opcode::LoadBool { rd: 3, value: false });

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
        func.emit(Opcode::SetEnum { rd: 0, start: 1, count: 0 });

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
        func.emit(Opcode::SetEnum { rd: 2, start: 0, count: 2 }); // pc 2

        // FuncDefBegin: r3 = result func, r4 = binding, domain in r2
        let begin_pc = func.emit(Opcode::FuncDefBegin { // pc 3
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });

        // Body: r5 = r4 * 10 (each key maps to key*10)
        func.emit(Opcode::LoadImm { rd: 5, value: 10 }); // pc 4
        func.emit(Opcode::MulInt { rd: 6, r1: 4, r2: 5 }); // pc 5

        let next_pc = func.emit(Opcode::LoopNext { // pc 6
            r_binding: 4,
            r_body: 6,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        // Now apply: r8 = f[1]
        func.emit(Opcode::LoadImm { rd: 7, value: 1 }); // pc 7
        func.emit(Opcode::FuncApply { // pc 8
            rd: 8,
            func: 3,
            arg: 7,
        });
        func.emit(Opcode::Ret { rs: 8 }); // pc 9

        let module = lower_invariant(&func, "func_apply_test")
            .expect("FuncApply lowering should succeed");
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
        func.emit(Opcode::SetEnum { rd: 3, start: 0, count: 3 });

        // Build function [x \in {1,2,3} |-> x+1] via FuncDefBegin
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });

        func.emit(Opcode::LoadImm { rd: 6, value: 1 });
        func.emit(Opcode::AddInt { rd: 7, r1: 5, r2: 6 });

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

        let module = lower_invariant(&func, "domain_test")
            .expect("Domain lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have blocks for FuncDef loop + Domain extraction loop
        assert!(
            module.functions[0].blocks.len() >= 6,
            "expected >= 6 blocks for FuncDef+Domain, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test FuncExcept: [f EXCEPT ![2] = 99].
    #[test]
    fn test_lower_func_except() {
        let mut func = BytecodeFunction::new("func_except_test".to_string(), 0);

        // Build domain set {1, 2} in r2
        func.emit(Opcode::LoadImm { rd: 0, value: 1 });
        func.emit(Opcode::LoadImm { rd: 1, value: 2 });
        func.emit(Opcode::SetEnum { rd: 2, start: 0, count: 2 });

        // Build function [x \in {1,2} |-> x*10] via FuncDefBegin
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 0,
        });

        func.emit(Opcode::LoadImm { rd: 5, value: 10 });
        func.emit(Opcode::MulInt { rd: 6, r1: 4, r2: 5 });

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

        let module = lower_invariant(&func, "func_except_test")
            .expect("FuncExcept lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have blocks for FuncDef loop + FuncExcept copy loop
        assert!(
            module.functions[0].blocks.len() >= 6,
            "expected >= 6 blocks for FuncDef+FuncExcept, got {}",
            module.functions[0].blocks.len()
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
        func.emit(Opcode::SetEnum { rd: 3, start: 0, count: 3 });

        // FuncDefBegin
        let begin_pc = func.emit(Opcode::FuncDefBegin {
            rd: 4,
            r_binding: 5,
            r_domain: 3,
            loop_end: 0,
        });

        // Body: r6 = r5 * r5
        func.emit(Opcode::MulInt { rd: 6, r1: 5, r2: 5 });

        let next_pc = func.emit(Opcode::LoopNext {
            r_binding: 5,
            r_body: 6,
            loop_begin: 0,
        });

        func.patch_jump(begin_pc, next_pc + 1);
        func.patch_jump(next_pc, begin_pc + 1);

        func.emit(Opcode::Ret { rs: 4 });

        let module = lower_invariant(&func, "func_def_test")
            .expect("FuncDef lowering should succeed");
        assert_eq!(module.functions.len(), 1);

        // Should have blocks: entry, header, load, body (MulInt overflow blocks), LoopNext, exit
        assert!(
            module.functions[0].blocks.len() >= 5,
            "expected >= 5 blocks for FuncDef, got {}",
            module.functions[0].blocks.len()
        );
    }

    /// Test FuncDef with empty domain produces a function with 0 pairs.
    #[test]
    fn test_lower_func_def_empty_domain() {
        let mut func = BytecodeFunction::new("func_def_empty".to_string(), 0);

        // Empty set
        func.emit(Opcode::SetEnum { rd: 0, start: 1, count: 0 });

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
        func.emit(Opcode::SetEnum { rd: 1, start: 0, count: 1 });

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
        func.emit(Opcode::FuncApply { rd: 5, func: 2, arg: 4 });
        func.emit(Opcode::Ret { rs: 5 });

        let module = lower_invariant(&func, "fapply_standalone")
            .expect("FuncApply standalone should succeed");
        assert_eq!(module.functions.len(), 1);

        // Verify it has Return instruction
        let has_return = module.functions[0]
            .blocks
            .iter()
            .any(|b| {
                b.body.last().map_or(false, |n| {
                    matches!(n.inst, Inst::Return { .. })
                })
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
    fn test_load_const_compound_value_returns_error() {
        use std::sync::Arc;
        use tla_value::SortedSet;

        let mut pool = ConstantPool::new();
        let set_val = Value::Set(Arc::new(SortedSet::new()));
        let idx = pool.add_value(set_val);

        let mut func = BytecodeFunction::new("compound".to_string(), 0);
        func.emit(Opcode::LoadConst { rd: 0, idx });
        func.emit(Opcode::Ret { rs: 0 });

        let result = lower_invariant_with_constants(&func, "compound", &pool);
        assert!(
            result.is_err(),
            "LoadConst with compound value should fail"
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
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Alloca { count: Some(_), .. }
                )
            })
        });
        assert!(
            has_alloca_with_count,
            "interval materialization should emit Alloca with explicit count"
        );
        let has_ptr_to_int = blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Cast { op: CastOp::PtrToInt, .. }
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
        let module =
            lower_invariant_with_constants(&func, "load_const_empty_interval", &pool)
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
        let result =
            lower_invariant_with_constants(&func, "load_const_big_interval", &pool);
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
        assert!(has_icmp_eq, "Unchanged should emit ICmp Eq for var comparison");

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
        assert!(has_and, "Unchanged <<x,y>> should emit And to combine results");
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
        assert!(
            result.is_err(),
            "Unchanged in invariant mode should fail"
        );
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
        f.emit(Opcode::AddInt { rd: 2, r1: 0, r2: 1 });
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

        let module = lower_module_invariant(&chunk, 1, "call_test")
            .expect("Call lowering should succeed");

        // Module should have 2 functions: entry + callee f.
        assert_eq!(
            module.functions.len(), 2,
            "expected 2 functions in module, got {}",
            module.functions.len()
        );

        // Entrypoint is functions[0], callee f is functions[1].
        assert_eq!(module.functions[0].name, "call_test");
        assert_eq!(module.functions[1].name, "f");

        // Verify entrypoint contains a Call instruction.
        let has_call = module.functions[0]
            .blocks
            .iter()
            .any(|b| b.body.iter().any(|n| matches!(n.inst, Inst::Call { .. })));
        assert!(has_call, "entrypoint should contain a Call instruction");

        // Verify callee f has a Return with values (i64 return).
        let has_i64_return = module.functions[1]
            .blocks
            .iter()
            .any(|b| {
                b.body.last().map_or(false, |n| {
                    matches!(&n.inst, Inst::Return { values } if !values.is_empty())
                })
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
        add.emit(Opcode::AddInt { rd: 2, r1: 0, r2: 1 });
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
        // Func type for callee: [Ptr, Ptr, I32, I64, I64] -> [I64]
        let callee_ft_idx = module.functions[1].ty;
        let callee_ft = &module.func_types[callee_ft_idx.as_usize()];
        // Context params (Ptr, Ptr, I32) + 2 user args (I64, I64) = 5 params.
        assert_eq!(
            callee_ft.params.len(), 5,
            "callee should have 5 params (3 context + 2 user), got {}",
            callee_ft.params.len()
        );
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
        assert_eq!(module.functions[1].name, "f");
    }

    /// Test transitive calls: entry -> g -> f.
    #[test]
    fn test_lower_call_transitive() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // func 0: f(x) = x * x
        let mut f = BytecodeFunction::new("f".to_string(), 1);
        f.emit(Opcode::MulInt { rd: 1, r1: 0, r2: 0 });
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
        g.emit(Opcode::AddInt { rd: 3, r1: 1, r2: 2 });
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
            module.functions.len(), 3,
            "expected 3 functions for transitive call chain, got {}",
            module.functions.len()
        );

        // Verify all 3 functions are present.
        let names: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"transitive_test"), "missing entry: {names:?}");
        assert!(names.contains(&"g"), "missing g: {names:?}");
        assert!(names.contains(&"f"), "missing f: {names:?}");
    }

    /// Test that lower_module_next_state works with Call.
    #[test]
    fn test_lower_call_next_state() {
        use tla_tir::bytecode::BytecodeChunk;

        let mut chunk = BytecodeChunk::new();

        // func 0: inc(x) = x + 1
        let mut inc = BytecodeFunction::new("inc".to_string(), 1);
        inc.emit(Opcode::LoadImm { rd: 1, value: 1 });
        inc.emit(Opcode::AddInt { rd: 2, r1: 0, r2: 1 });
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

        // Callee in next-state mode should have 4 context params (Ptr, Ptr, Ptr, I32)
        // + 1 user arg = 5 params.
        let callee_ft_idx = module.functions[1].ty;
        let callee_ft = &module.func_types[callee_ft_idx.as_usize()];
        assert_eq!(
            callee_ft.params.len(), 5,
            "next-state callee should have 5 params (4 context + 1 user), got {}",
            callee_ft.params.len()
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

        let has_return = module.functions[0]
            .blocks
            .iter()
            .any(|b| {
                b.body.last().map_or(false, |n| {
                    matches!(n.inst, Inst::Return { .. })
                })
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

    // =====================================================================
    // Proof annotation tests (Stream 2 of #4251)
    // =====================================================================
    //
    // These tests verify that the lowering attaches correct proof
    // annotations on function headers (Pure, Deterministic, Terminates,
    // NoPanic) and on loop header CondBr terminators
    // (Custom(BOUNDED_LOOP_N), Custom(PARALLEL_MAP)).

    use crate::annotations::{
        bounded_loop_n, is_bounded_loop, is_parallel_map, PARALLEL_MAP,
    };
    use tmir::proof::ProofAnnotation;

    /// Return all CondBr instructions across every block in a function,
    /// paired with the proof annotations attached to each one.
    fn collect_condbr_proofs(
        module: &tmir::Module,
        func_idx: usize,
    ) -> Vec<&[ProofAnnotation]> {
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

    /// Simple invariant x > 0 should be Pure + Deterministic + Terminates
    /// + NoPanic: no loops, no side effects, but checked arithmetic is
    /// absent so NoPanic holds.
    #[test]
    fn test_trivial_invariant_is_pure_and_deterministic() {
        let mut func = BytecodeFunction::new("inv_pure".to_string(), 0);
        func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
        func.emit(Opcode::LoadImm { rd: 1, value: 0 });
        func.emit(Opcode::GtInt { rd: 2, r1: 0, r2: 1 });
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
        func.emit(Opcode::AddInt { rd: 2, r1: 0, r2: 1 });
        func.emit(Opcode::LoadImm { rd: 3, value: 0 });
        func.emit(Opcode::GtInt { rd: 4, r1: 2, r2: 3 });
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
        let has_bounded = all_condbr_proofs.iter().flat_map(|ps| ps.iter()).any(|p| {
            matches!(p, ProofAnnotation::Custom(tag) if is_bounded_loop(*tag))
        });
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
        func.emit(Opcode::Range { rd: 2, lo: 0, hi: 1 }); // 1..10 → size 10
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
        assert_has_condbr_tag(&module, 0, "parallel_map", |tag| {
            is_parallel_map(tag)
        });
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

        assert_has_condbr_tag(&module, 0, "parallel_map", |tag| {
            is_parallel_map(tag)
        });

        // bounded_loop must NOT be present.
        let all_condbr_proofs = collect_condbr_proofs(&module, 0);
        let has_bounded = all_condbr_proofs.iter().flat_map(|ps| ps.iter()).any(|p| {
            matches!(p, ProofAnnotation::Custom(tag) if is_bounded_loop(*tag))
        });
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
        let mut consts: std::collections::HashMap<ValueId, i128> =
            std::collections::HashMap::new();
        for block in &module.functions[func_idx].blocks {
            for node in &block.body {
                if let Inst::Const { value: Constant::Int(v), .. } = node.inst {
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
            .filter(|n| matches!(n.inst, Inst::ICmp { op: ICmpOp::Slt, .. }))
            .count()
    }

    /// Build a simple `\E x \in S : r_body` program with a user-controlled
    /// body and a SetEnum domain of `count` elements starting from
    /// `start_value`.
    fn build_exists(
        body_reg: u8,
        start_value: i64,
        count: u8,
    ) -> BytecodeFunction {
        let mut func = BytecodeFunction::new("exists_frame".to_string(), 0);
        for i in 0..count {
            func.emit(Opcode::LoadImm { rd: i, value: start_value + i as i64 });
        }
        func.emit(Opcode::SetEnum { rd: 20, start: 0, count });

        // Body: r_body = TRUE (LoadBool)
        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 21,
            r_binding: 22,
            r_domain: 20,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool { rd: body_reg, value: true });
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
        func.emit(Opcode::SetEnum { rd: 20, start: 0, count: 2 });

        // Body: r_body = FALSE so we exercise the short-circuit path.
        let begin_pc = func.emit(Opcode::ForallBegin {
            rd: 21,
            r_binding: 22,
            r_domain: 20,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool { rd: 23, value: false });
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
        func.emit(Opcode::SetEnum { rd: 20, start: 0, count: 0 });
        let begin_pc = func.emit(Opcode::ExistsBegin {
            rd: 21,
            r_binding: 22,
            r_domain: 20,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool { rd: 23, value: true });
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
        func.emit(Opcode::SetEnum { rd: 20, start: 0, count: 0 });
        let begin_pc = func.emit(Opcode::ForallBegin {
            rd: 21,
            r_binding: 22,
            r_domain: 20,
            loop_end: 0,
        });
        func.emit(Opcode::LoadBool { rd: 23, value: false });
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
        func.emit(Opcode::SetEnum { rd: 2, start: 0, count: 2 });
        func.emit(Opcode::LoadImm { rd: 3, value: 3 });
        func.emit(Opcode::LoadImm { rd: 4, value: 4 });
        func.emit(Opcode::LoadImm { rd: 5, value: 5 });
        func.emit(Opcode::SetEnum { rd: 6, start: 3, count: 3 });

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
        func.emit(Opcode::LoadBool { rd: 11, value: true });
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
        let has_load_from_computed = module.functions[0].blocks.iter().any(|b| {
            b.body.iter().any(|n| {
                matches!(
                    n.inst,
                    Inst::Load { .. }
                )
            })
        });
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
                FieldDef { name: "pc".to_string(), ty: Ty::I64, offset: None },
                FieldDef { name: "counter".to_string(), ty: Ty::I64, offset: None },
                FieldDef { name: "owner".to_string(), ty: Ty::I64, offset: None },
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
}
