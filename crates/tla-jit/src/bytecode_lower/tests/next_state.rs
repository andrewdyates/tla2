// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for JIT-compiled next-state relations (compile_next_state).

use super::compile_and_run_next_state;
use crate::abi::JitStatus;
use crate::bytecode_lower::eligibility::{check_eligibility, check_next_state_eligibility};
use crate::bytecode_lower::BytecodeLowerer;
use tla_tir::bytecode::{BytecodeFunction, Opcode};

/// x' = x + 1 (single variable increment)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_increment() {
    let mut func = BytecodeFunction::new("increment".to_string(), 2);
    // r0 = state[0] (x)
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    // r1 = 1
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    // r2 = r0 + r1
    func.emit(Opcode::AddInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    // state_out[0] = r2 (x' = x + 1)
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
    // return TRUE (action enabled)
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    func.emit(Opcode::Ret { rs: 0 });

    let state_in = [10i64];
    let (out, state_out) = compile_and_run_next_state(&func, &state_in);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1); // TRUE
    assert_eq!(state_out[0], 11); // x' = 10 + 1
}

/// x' = y, y' = x (two-variable swap)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_swap() {
    let mut func = BytecodeFunction::new("swap".to_string(), 3);
    // r0 = state[0] (x)
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    // r1 = state[1] (y)
    func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
    // state_out[0] = r1 (x' = y)
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
    // state_out[1] = r0 (y' = x)
    func.emit(Opcode::StoreVar { var_idx: 1, rs: 0 });
    // return TRUE
    func.emit(Opcode::LoadBool { rd: 2, value: true });
    func.emit(Opcode::Ret { rs: 2 });

    let state_in = [3i64, 7];
    let (out, state_out) = compile_and_run_next_state(&func, &state_in);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1); // TRUE
    assert_eq!(state_out[0], 7); // x' = y = 7
    assert_eq!(state_out[1], 3); // y' = x = 3
}

/// Conditional: if x > 5 then x' = x - 1, return TRUE, else return FALSE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_conditional() {
    let mut func = BytecodeFunction::new("conditional".to_string(), 3);
    // r0 = state[0] (x)
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    // r1 = 5
    func.emit(Opcode::LoadImm { rd: 1, value: 5 });
    // r2 = (x > 5)
    func.emit(Opcode::GtInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    // if r2 == false, jump +4 to the FALSE branch
    func.emit(Opcode::JumpFalse { rs: 2, offset: 4 });
    // TRUE branch: x' = x - 1
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::SubInt {
        rd: 3,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 3 });
    func.emit(Opcode::Ret { rs: 2 }); // return TRUE (r2 = 1)
                                      // FALSE branch: return FALSE
    func.emit(Opcode::LoadBool {
        rd: 3,
        value: false,
    });
    func.emit(Opcode::Ret { rs: 3 });

    // Test with x = 10 (enabled)
    let state_in = [10i64];
    let (out, state_out) = compile_and_run_next_state(&func, &state_in);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1); // TRUE: action enabled
    assert_eq!(state_out[0], 9); // x' = 10 - 1

    // Test with x = 3 (disabled)
    let state_in = [3i64];
    let (out, _state_out) = compile_and_run_next_state(&func, &state_in);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0); // FALSE: action disabled
}

/// Multiple variables: x' = x + y, y' = y * 2
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_multiple_vars() {
    let mut func = BytecodeFunction::new("multi_var".to_string(), 4);
    // r0 = state[0] (x)
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    // r1 = state[1] (y)
    func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
    // r2 = x + y
    func.emit(Opcode::AddInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    // r3 = 2
    func.emit(Opcode::LoadImm { rd: 3, value: 2 });
    // r4 = y * 2
    func.emit(Opcode::MulInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    // state_out[0] = r2 (x' = x + y)
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
    // state_out[1] = r4 (y' = y * 2)
    func.emit(Opcode::StoreVar { var_idx: 1, rs: 4 });
    // return TRUE
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    func.emit(Opcode::Ret { rs: 0 });

    let state_in = [5i64, 3];
    let (out, state_out) = compile_and_run_next_state(&func, &state_in);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1); // TRUE
    assert_eq!(state_out[0], 8); // x' = 5 + 3
    assert_eq!(state_out[1], 6); // y' = 3 * 2
}

/// Verify that check_next_state_eligibility allows StoreVar but check_eligibility rejects it.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_eligibility_allows_store_var() {
    let mut func = BytecodeFunction::new("nxt_eligible".to_string(), 1);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
    func.emit(Opcode::LoadBool { rd: 1, value: true });
    func.emit(Opcode::Ret { rs: 1 });

    // Invariant eligibility rejects StoreVar
    assert!(check_eligibility(&func).is_err());
    // Next-state eligibility accepts StoreVar
    assert!(check_next_state_eligibility(&func).is_ok());
}

/// Verify that Call opcode is ineligible for next-state compilation too.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_call_eligible_with_fallback() {
    // Call is now JIT-eligible (emits FallbackNeeded at runtime).
    // Part of #3909 Phase 2.
    let mut func = BytecodeFunction::new("nxt_call".to_string(), 1);
    func.emit(Opcode::Call {
        rd: 0,
        op_idx: 0,
        args_start: 1,
        argc: 0,
    });
    func.emit(Opcode::Ret { rs: 0 });

    assert!(check_next_state_eligibility(&func).is_ok());

    let mut lowerer = BytecodeLowerer::new().unwrap();
    assert!(lowerer.try_compile_next_state(&func).unwrap().is_some());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_ineligible_empty() {
    // Empty functions remain ineligible.
    let func = BytecodeFunction::new("nxt_empty".to_string(), 0);
    assert!(check_next_state_eligibility(&func).is_err());

    let mut lowerer = BytecodeLowerer::new().unwrap();
    assert!(lowerer.try_compile_next_state(&func).unwrap().is_none());
}

// =============================================================================
// UNCHANGED opcode tests
// =============================================================================

use crate::bytecode_lower::UnchangedVarMap;

/// Helper: compile a next-state function with unchanged var map and execute it.
fn compile_and_run_next_state_with_unchanged(
    func: &BytecodeFunction,
    state_in: &[i64],
    unchanged: &UnchangedVarMap,
) -> (crate::abi::JitCallOut, Vec<i64>) {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_next_state_with_unchanged(func, unchanged)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = crate::abi::JitCallOut::default();
    let mut state_out = vec![0i64; state_in.len()];
    unsafe {
        jit_fn(
            &mut out,
            state_in.as_ptr(),
            state_out.as_mut_ptr(),
            state_in.len() as u32,
        );
    }
    (out, state_out)
}

/// UNCHANGED x — single variable, same values in both states.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_single_var_equal() {
    // Build: state_out[0] = state_in[0], r1 = UNCHANGED(var 0), return r1
    let mut func = BytecodeFunction::new("unchanged_single".to_string(), 1);
    // Load x from current state
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    // Store x' = x (write same value to output)
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
    // Check UNCHANGED x: start=0 (const pool idx), count=1
    func.emit(Opcode::Unchanged {
        rd: 1,
        start: 0,
        count: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let mut unchanged = UnchangedVarMap::new();
    unchanged.insert(0, vec![0]); // const idx 0 → var_idx [0]

    let state_in = [42i64];
    let (out, state_out) = compile_and_run_next_state_with_unchanged(&func, &state_in, &unchanged);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "UNCHANGED x should be TRUE when x' == x");
    assert_eq!(state_out[0], 42);
}

/// UNCHANGED x — single variable, different values → FALSE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_single_var_different() {
    // Build: state_out[0] = state_in[0] + 1, r1 = UNCHANGED(var 0), return r1
    let mut func = BytecodeFunction::new("unchanged_diff".to_string(), 2);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::AddInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 }); // x' = x + 1
    func.emit(Opcode::Unchanged {
        rd: 0,
        start: 0,
        count: 1,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let mut unchanged = UnchangedVarMap::new();
    unchanged.insert(0, vec![0]);

    let state_in = [10i64];
    let (out, _) = compile_and_run_next_state_with_unchanged(&func, &state_in, &unchanged);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "UNCHANGED x should be FALSE when x' != x");
}

/// UNCHANGED <<x, y>> — two variables, both unchanged.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_two_vars_both_equal() {
    let mut func = BytecodeFunction::new("unchanged_two".to_string(), 2);
    // Copy both variables to output unchanged
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
    func.emit(Opcode::StoreVar { var_idx: 1, rs: 1 });
    // Check UNCHANGED <<x, y>>
    func.emit(Opcode::Unchanged {
        rd: 2,
        start: 5, // arbitrary const pool idx
        count: 2,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let mut unchanged = UnchangedVarMap::new();
    unchanged.insert(5, vec![0, 1]); // vars 0 and 1

    let state_in = [100i64, 200];
    let (out, state_out) = compile_and_run_next_state_with_unchanged(&func, &state_in, &unchanged);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "UNCHANGED <<x, y>> should be TRUE when both unchanged"
    );
    assert_eq!(state_out, [100, 200]);
}

/// UNCHANGED <<x, y>> — two variables, one changed → FALSE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_two_vars_one_changed() {
    let mut func = BytecodeFunction::new("unchanged_partial".to_string(), 2);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
    // x' = x (unchanged)
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 0 });
    // y' = y + 1 (changed!)
    func.emit(Opcode::LoadImm { rd: 2, value: 1 });
    func.emit(Opcode::AddInt {
        rd: 2,
        r1: 1,
        r2: 2,
    });
    func.emit(Opcode::StoreVar { var_idx: 1, rs: 2 });
    // Check UNCHANGED <<x, y>>
    func.emit(Opcode::Unchanged {
        rd: 0,
        start: 10,
        count: 2,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let mut unchanged = UnchangedVarMap::new();
    unchanged.insert(10, vec![0, 1]);

    let state_in = [5i64, 8];
    let (out, _) = compile_and_run_next_state_with_unchanged(&func, &state_in, &unchanged);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "UNCHANGED <<x, y>> should be FALSE when y changed"
    );
}

// =============================================================================
// ForallBegin with model value / string domains in next-state context
// Part of #3958: enable action JIT for real specs with ForallBegin quantifiers
// =============================================================================

/// Action with ForallBegin over a set of model values from the constant pool.
///
/// Models the pattern: `\A proc \in Proc : x[proc]' = x[proc] + 1`
/// where Proc = {p1, p2} is a set of model values.
///
/// In real TLA+ specs, `\A proc \in Proc : ...` appears in action bodies
/// to apply the same update to all processes. The domain is a constant
/// set of model values loaded via LoadConst.
///
/// This test verifies that:
/// 1. collect_quantifier_domains_from_bytecode extracts ModelValue elements
/// 2. The ForallBegin/ForallNext compiles correctly in next-state context
/// 3. The action produces the correct result
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_forall_with_model_value_domain() {
    use super::compile_and_run_next_state_with_constants;
    use std::sync::Arc;

    // Build constant pool with a set of model values: {"p1", "p2"}
    let mut constants = tla_tir::bytecode::ConstantPool::new();
    let set = tla_value::Value::Set(Arc::new(tla_value::SortedSet::from_iter(vec![
        tla_value::Value::ModelValue(Arc::from("mv_proc_a")),
        tla_value::Value::ModelValue(Arc::from("mv_proc_b")),
    ])));
    let set_idx = constants.add_value(set);

    // Get the interned NameId values for comparison
    let name_a = tla_core::intern_name("mv_proc_a").0 as i64;
    let name_b = tla_core::intern_name("mv_proc_b").0 as i64;

    // Build action bytecode:
    //   r0 = LoadConst set_idx  (the {p1, p2} set)
    //   ForallBegin rd=r1 r_binding=r2 r_domain=r0 loop_end=+4
    //     r3 = (r2 == name_a)   ; check if binding matches first proc
    //   ForallNext rd=r1 r_binding=r2 r_body=r3 loop_begin=-2
    //   ; r1 = FALSE if any binding is NOT name_a (which is true for name_b)
    //   ; At this point, r1 tells us if ALL procs == name_a
    //   StoreVar var_idx=0 rs=r1  ; x' = result of forall
    //   LoadBool r4 true
    //   Ret r4
    let mut func = BytecodeFunction::new("forall_action".to_string(), 4);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: set_idx,
    }); // PC 0: r0 = {p1, p2}
    func.emit(Opcode::LoadImm {
        rd: 3,
        value: name_a,
    }); // PC 1: r3 = interned "mv_proc_a"
    func.emit(Opcode::ForallBegin {
        // PC 2
        rd: 1,
        r_binding: 2,
        r_domain: 0,
        loop_end: 3, // exit at PC 5
    });
    func.emit(Opcode::Eq {
        rd: 4,
        r1: 2,
        r2: 3,
    }); // PC 3: body: r4 = (binding == name_a)
    func.emit(Opcode::ForallNext {
        // PC 4
        rd: 1,
        r_binding: 2,
        r_body: 4,
        loop_begin: -1, // back to PC 3
    });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 }); // PC 5: x' = forall result
    func.emit(Opcode::LoadBool { rd: 0, value: true }); // PC 6
    func.emit(Opcode::Ret { rs: 0 }); // PC 7

    let state_in = [0i64]; // x = 0 (doesn't matter, overwritten)
    let (out, state_out) = compile_and_run_next_state_with_constants(&func, &state_in, &constants);

    assert_eq!(
        out.status,
        JitStatus::Ok,
        "action should compile and run successfully"
    );
    assert_eq!(out.value, 1, "action should be enabled");
    // ForAll proc \in {p1, p2}: proc == p1
    // p1 == p1 → TRUE, p2 == p1 → FALSE
    // ForAll over {TRUE, FALSE} → FALSE
    assert_eq!(
        state_out[0], 0,
        "forall should be FALSE (not all procs == p1)"
    );
}

/// Action with ForallBegin over a set of strings from the constant pool.
///
/// Similar to model values but with Value::String elements.
/// Verifies that string interning in domain extraction matches
/// the LoadConst/String path in scalar_ops.rs.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_forall_with_string_domain() {
    use super::compile_and_run_next_state_with_constants;
    use std::sync::Arc;

    let mut constants = tla_tir::bytecode::ConstantPool::new();
    let set = tla_value::Value::Set(Arc::new(tla_value::SortedSet::from_iter(vec![
        tla_value::Value::String(Arc::from("str_alpha")),
        tla_value::Value::String(Arc::from("str_beta")),
    ])));
    let set_idx = constants.add_value(set);

    let name_alpha = tla_core::intern_name("str_alpha").0 as i64;

    // Forall over {"alpha", "beta"}: check if binding == "alpha"
    // Result: FALSE (beta != alpha)
    let mut func = BytecodeFunction::new("forall_string".to_string(), 4);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: set_idx,
    });
    func.emit(Opcode::LoadImm {
        rd: 3,
        value: name_alpha,
    });
    func.emit(Opcode::ForallBegin {
        rd: 1,
        r_binding: 2,
        r_domain: 0,
        loop_end: 3,
    });
    func.emit(Opcode::Eq {
        rd: 4,
        r1: 2,
        r2: 3,
    });
    func.emit(Opcode::ForallNext {
        rd: 1,
        r_binding: 2,
        r_body: 4,
        loop_begin: -1,
    });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    func.emit(Opcode::Ret { rs: 0 });

    let state_in = [0i64];
    let (out, state_out) = compile_and_run_next_state_with_constants(&func, &state_in, &constants);

    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1);
    assert_eq!(
        state_out[0], 0,
        "forall should be FALSE (not all strings == alpha)"
    );
}

/// Action with ForallBegin over integer constant set: verifies existing path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_forall_with_integer_domain() {
    use super::compile_and_run_next_state_with_constants;
    use std::sync::Arc;

    let mut constants = tla_tir::bytecode::ConstantPool::new();
    let set = tla_value::Value::Set(Arc::new(tla_value::SortedSet::from_iter(vec![
        tla_value::Value::SmallInt(1),
        tla_value::Value::SmallInt(2),
        tla_value::Value::SmallInt(3),
    ])));
    let set_idx = constants.add_value(set);

    // Forall over {1, 2, 3}: check if binding > 0
    // Result: TRUE (all elements > 0)
    let mut func = BytecodeFunction::new("forall_int".to_string(), 4);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: set_idx,
    });
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    func.emit(Opcode::ForallBegin {
        rd: 1,
        r_binding: 2,
        r_domain: 0,
        loop_end: 3,
    });
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 2,
        r2: 3,
    }); // binding > 0
    func.emit(Opcode::ForallNext {
        rd: 1,
        r_binding: 2,
        r_body: 4,
        loop_begin: -1,
    });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    func.emit(Opcode::Ret { rs: 0 });

    let state_in = [0i64];
    let (out, state_out) = compile_and_run_next_state_with_constants(&func, &state_in, &constants);

    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1);
    assert_eq!(state_out[0], 1, "forall should be TRUE (all elements > 0)");
}

/// Verify ExistsBegin is correctly rejected in next-state context.
/// This prevents missing successor states from nondeterministic choice.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_exists_begin_rejected() {
    use crate::bytecode_lower::eligibility::check_next_state_eligibility;

    let mut func = BytecodeFunction::new("exists_action".to_string(), 3);
    func.emit(Opcode::LoadImm { rd: 0, value: 0 });
    func.emit(Opcode::ExistsBegin {
        rd: 1,
        r_binding: 2,
        r_domain: 0,
        loop_end: 3,
    });
    func.emit(Opcode::Move { rd: 3, rs: 2 });
    func.emit(Opcode::ExistsNext {
        rd: 1,
        r_binding: 2,
        r_body: 3,
        loop_begin: -1,
    });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 1 });
    func.emit(Opcode::Ret { rs: 1 });

    let err = check_next_state_eligibility(&func).unwrap_err();
    assert!(
        err.contains("ExistsBegin"),
        "ExistsBegin should be rejected in next-state context, got: {err}"
    );
}

/// Verify that Unchanged is rejected in invariant mode but accepted in next-state mode.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_eligibility() {
    let mut func = BytecodeFunction::new("unch_elig".to_string(), 0);
    func.emit(Opcode::Unchanged {
        rd: 0,
        start: 0,
        count: 1,
    });
    func.emit(Opcode::Ret { rs: 0 });

    // Unchanged is now eligible in invariant mode (emits FallbackNeeded)
    // and natively handled in next-state mode. Part of #3909 Phase 2.
    assert!(
        check_eligibility(&func).is_ok(),
        "Unchanged should be eligible in invariant mode (emits FallbackNeeded)"
    );
    assert!(
        check_next_state_eligibility(&func).is_ok(),
        "Unchanged should be eligible in next-state mode"
    );
}
