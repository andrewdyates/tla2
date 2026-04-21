// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

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
    use tla_jit::abi::JitStatus;
    use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};
    use tla_value::Value;
    use tmir::inst::*;
    use tmir::ty::Ty;
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
}
