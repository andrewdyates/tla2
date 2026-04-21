// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for quantifier loop compilation (ForallBegin/Next, ExistsBegin/Next, ChooseBegin/Next).

use crate::abi::{JitCallOut, JitStatus};
use crate::bytecode_lower::BytecodeLowerer;
use crate::bytecode_lower::QuantifierDomains;
use tla_tir::bytecode::{BytecodeFunction, Opcode};

/// Helper: compile a bytecode function with quantifier domains and execute it.
fn compile_and_run_with_domains(
    func: &BytecodeFunction,
    domains: &QuantifierDomains,
    state: &[i64],
) -> JitCallOut {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant_with_domains(func, domains)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    out
}

/// Build a forall-over-domain bytecode function:
///   ForallBegin(rd=0, r_binding=1, r_domain=2, loop_end=+4)
///   <body: r3 = r1 > 0>
///   ForallNext(rd=0, r_binding=1, r_body=3, loop_begin=-2)
///   Ret(rs=0)
fn make_forall_positive_func() -> BytecodeFunction {
    let mut func = BytecodeFunction::new("forall_positive".to_string(), 3);
    // PC 0: ForallBegin — loop_end targets PC 4 (offset +4, but we only have 4 instructions total, so +3 to land on Ret)
    // Actually: PC 0 + 3 = PC 3 which is Ret
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 3,
    });
    // PC 1: body — check if binding > 0
    func.emit(Opcode::GtInt {
        rd: 3,
        r1: 1,
        r2: 2, // r2 will be repurposed as loop index (0-based), but we need a zero constant
    });
    // Actually, r2 is repurposed as loop counter, so using it for comparison is wrong.
    // Let's use LoadImm instead for the comparison value.
    // Rewrite: simpler body that just checks r_binding (r1) > 0
    // We need a register with 0 to compare against. Use LoadImm.
    let mut func = BytecodeFunction::new("forall_positive".to_string(), 4);
    // PC 0: ForallBegin
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    // PC 1: load constant 0 into r3
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    // PC 2: body — r4 = r1 > r3 (binding > 0)
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    // PC 3: ForallNext — loop_begin targets PC 1 (offset -2)
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    // PC 4: Ret
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_all_positive() {
    let func = make_forall_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, 3, 4, 5]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "forall x in {{1..5}}: x > 0 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_not_all_positive() {
    let func = make_forall_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, -1, 4, 5]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "forall x in {{1,2,-1,4,5}}: x > 0 should be FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_empty_domain() {
    let func = make_forall_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "forall over empty domain should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_single_true() {
    let func = make_forall_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![42]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "forall x in {{42}}: x > 0 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_single_false() {
    let func = make_forall_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![-5]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "forall x in {{-5}}: x > 0 should be FALSE");
}

/// Build an exists-over-domain bytecode function:
///   ExistsBegin(rd=0, r_binding=1, r_domain=2, loop_end=+4)
///   LoadImm(r3, 0)
///   body: r4 = r1 > r3
///   ExistsNext(rd=0, r_binding=1, r_body=4, loop_begin=-2)
///   Ret(rs=0)
fn make_exists_positive_func() -> BytecodeFunction {
    let mut func = BytecodeFunction::new("exists_positive".to_string(), 4);
    // PC 0: ExistsBegin
    func.emit(Opcode::ExistsBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    // PC 1: load constant 0 into r3
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    // PC 2: body — r4 = r1 > r3 (binding > 0)
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    // PC 3: ExistsNext — loop_begin targets PC 1 (offset -2)
    func.emit(Opcode::ExistsNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    // PC 4: Ret
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_found() {
    let func = make_exists_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![-3, -2, 1, -4]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "exists x in {{-3,-2,1,-4}}: x > 0 should be TRUE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_not_found() {
    let func = make_exists_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![-3, -2, -1, -4]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "exists x in {{-3,-2,-1,-4}}: x > 0 should be FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_empty_domain() {
    let func = make_exists_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "exists over empty domain should be FALSE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_all_true() {
    let func = make_exists_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, 3]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "exists x in {{1,2,3}}: x > 0 should be TRUE (short-circuit on first)"
    );
}

// =============================================================================
// CHOOSE quantifier tests
// =============================================================================

/// Build a choose-over-domain bytecode function:
///   CHOOSE x \in S : x > 0
///
///   ChooseBegin(rd=0, r_binding=1, r_domain=2, loop_end=+4)
///   LoadImm(r3, 0)
///   body: r4 = r1 > r3
///   ChooseNext(rd=0, r_binding=1, r_body=4, loop_begin=-2)
///   Ret(rs=0)
fn make_choose_positive_func() -> BytecodeFunction {
    let mut func = BytecodeFunction::new("choose_positive".to_string(), 4);
    // PC 0: ChooseBegin
    func.emit(Opcode::ChooseBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    // PC 1: load constant 0 into r3
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    // PC 2: body — r4 = r1 > r3 (binding > 0)
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    // PC 3: ChooseNext — loop_begin targets PC 1 (offset -2)
    func.emit(Opcode::ChooseNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    // PC 4: Ret
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_finds_first_match() {
    let func = make_choose_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![-3, -2, 7, 10]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 7,
        "CHOOSE x in {{-3,-2,7,10}}: x > 0 should return 7 (first match)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_first_element_matches() {
    let func = make_choose_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![5, -1, -2]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 5,
        "CHOOSE x in {{5,-1,-2}}: x > 0 should return 5 (first element)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_last_element_matches() {
    let func = make_choose_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![-3, -2, -1, 42]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 42,
        "CHOOSE x in {{-3,-2,-1,42}}: x > 0 should return 42 (last element)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_single_matching_element() {
    let func = make_choose_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![99]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 99, "CHOOSE x in {{99}}: x > 0 should return 99");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_empty_domain_runtime_error() {
    let func = make_choose_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(
        out.status,
        JitStatus::RuntimeError,
        "CHOOSE over empty domain should be a RuntimeError"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_no_match_runtime_error() {
    let func = make_choose_positive_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![-5, -3, -1, 0]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(
        out.status,
        JitStatus::RuntimeError,
        "CHOOSE with no matching element should be a RuntimeError"
    );
}

// =============================================================================
// Range-based quantifier tests (ForAll/Exists over Range opcode)
// =============================================================================

/// Helper: compile a bytecode function (no pre-materialized domains needed for
/// Range-based quantifiers) and execute it with the given state array.
fn compile_and_run_range(func: &BytecodeFunction, state: &[i64]) -> JitCallOut {
    // Use compile_invariant (empty domains). Range opcodes populate the
    // range tracker during lowering, so no pre-materialized array needed.
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant(func)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    out
}

/// Build: \A x \in lo..hi : x > 0
///
///   LoadImm(r3, <lo>)        -- PC 0
///   LoadImm(r4, <hi>)        -- PC 1
///   Range(rd=2, lo=3, hi=4)  -- PC 2: creates virtual range set in r2
///   ForallBegin(rd=0, r_binding=1, r_domain=2, loop_end=+4) -- PC 3
///   LoadImm(r5, 0)           -- PC 4
///   GtInt(r6, r1, r5)        -- PC 5: body: r6 = r1 > 0
///   ForallNext(rd=0, r_binding=1, r_body=6, loop_begin=-2)  -- PC 6
///   Ret(rs=0)                -- PC 7
fn make_range_forall_func(lo: i64, hi: i64) -> BytecodeFunction {
    let mut func = BytecodeFunction::new("range_forall_positive".to_string(), 6);
    func.emit(Opcode::LoadImm { rd: 3, value: lo });
    func.emit(Opcode::LoadImm { rd: 4, value: hi });
    func.emit(Opcode::Range {
        rd: 2,
        lo: 3,
        hi: 4,
    });
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    func.emit(Opcode::LoadImm { rd: 5, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 6,
        r1: 1,
        r2: 5,
    });
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 6,
        loop_begin: -2,
    });
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_forall_all_positive() {
    // \A x \in 1..5 : x > 0 -- TRUE
    let func = make_range_forall_func(1, 5);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "forall x in 1..5 : x > 0 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_forall_includes_zero() {
    // \A x \in 0..3 : x > 0 -- FALSE (0 is not > 0)
    let func = make_range_forall_func(0, 3);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "forall x in 0..3 : x > 0 should be FALSE (0 fails)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_forall_negative_range() {
    // \A x \in -2..2 : x > 0 -- FALSE (-2, -1, 0 fail)
    let func = make_range_forall_func(-2, 2);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "forall x in -2..2 : x > 0 should be FALSE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_forall_single_element() {
    // \A x \in 5..5 : x > 0 -- TRUE (only element is 5)
    let func = make_range_forall_func(5, 5);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "forall x in 5..5 : x > 0 should be TRUE (single element)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_forall_empty_range() {
    // \A x \in 5..3 : x > 0 -- TRUE (empty domain, vacuously true)
    let func = make_range_forall_func(5, 3);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "forall over empty range (5..3) should be TRUE"
    );
}

/// Build: \E x \in lo..hi : x > 0
fn make_range_exists_func(lo: i64, hi: i64) -> BytecodeFunction {
    let mut func = BytecodeFunction::new("range_exists_positive".to_string(), 6);
    func.emit(Opcode::LoadImm { rd: 3, value: lo });
    func.emit(Opcode::LoadImm { rd: 4, value: hi });
    func.emit(Opcode::Range {
        rd: 2,
        lo: 3,
        hi: 4,
    });
    func.emit(Opcode::ExistsBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    func.emit(Opcode::LoadImm { rd: 5, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 6,
        r1: 1,
        r2: 5,
    });
    func.emit(Opcode::ExistsNext {
        rd: 0,
        r_binding: 1,
        r_body: 6,
        loop_begin: -2,
    });
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_exists_found() {
    // \E x \in -2..2 : x > 0 -- TRUE (1, 2 are > 0)
    let func = make_range_exists_func(-2, 2);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "exists x in -2..2 : x > 0 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_exists_not_found() {
    // \E x \in -5..-1 : x > 0 -- FALSE (all negative)
    let func = make_range_exists_func(-5, -1);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "exists x in -5..-1 : x > 0 should be FALSE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_exists_empty_range() {
    // \E x \in 5..3 : x > 0 -- FALSE (empty domain)
    let func = make_range_exists_func(5, 3);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "exists over empty range (5..3) should be FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_exists_single_element_true() {
    // \E x \in 1..1 : x > 0 -- TRUE
    let func = make_range_exists_func(1, 1);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "exists x in 1..1 : x > 0 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_exists_single_element_false() {
    // \E x \in -1..-1 : x > 0 -- FALSE
    let func = make_range_exists_func(-1, -1);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "exists x in -1..-1 : x > 0 should be FALSE");
}

// =============================================================================
// Conjunction early-exit tests (ForAll with body = a /\ b)
// =============================================================================

/// Build: \A x \in domain : (x > 0) /\ (x < 10)
///
/// Bytecode:
///   ForallBegin(rd=0, r_binding=1, r_domain=2, loop_end=+7) -- PC 0
///   LoadImm(r3, 0)           -- PC 1
///   GtInt(r4, r1, r3)        -- PC 2: r4 = x > 0
///   LoadImm(r5, 10)          -- PC 3
///   LtInt(r6, r1, r5)        -- PC 4: r6 = x < 10
///   And(r7, r4, r6)          -- PC 5: r7 = r4 /\ r6
///   ForallNext(rd=0, r_binding=1, r_body=7, loop_begin=-5) -- PC 6
///   Ret(rs=0)                -- PC 7
fn make_forall_conjunction_func() -> BytecodeFunction {
    let mut func = BytecodeFunction::new("forall_conjunction".to_string(), 7);
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 7,
    });
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    func.emit(Opcode::LoadImm { rd: 5, value: 10 });
    func.emit(Opcode::LtInt {
        rd: 6,
        r1: 1,
        r2: 5,
    });
    func.emit(Opcode::And {
        rd: 7,
        r1: 4,
        r2: 6,
    });
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 7,
        loop_begin: -5,
    });
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_conjunction_all_pass() {
    // \A x \in {1,2,3,4,5} : (x > 0) /\ (x < 10) -- TRUE
    let func = make_forall_conjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, 3, 4, 5]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "forall x in {{1..5}}: x > 0 /\\ x < 10 should be TRUE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_conjunction_first_conjunct_fails() {
    // \A x \in {1,2,-1,4,5} : (x > 0) /\ (x < 10) -- FALSE (-1 fails first conjunct)
    let func = make_forall_conjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, -1, 4, 5]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "forall with -1 failing x > 0 conjunct should be FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_conjunction_second_conjunct_fails() {
    // \A x \in {1,2,15,4,5} : (x > 0) /\ (x < 10) -- FALSE (15 fails second conjunct)
    let func = make_forall_conjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, 15, 4, 5]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "forall with 15 failing x < 10 conjunct should be FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_conjunction_both_conjuncts_fail() {
    // \A x \in {1,-5,20} : (x > 0) /\ (x < 10) -- FALSE (-5 fails both)
    let func = make_forall_conjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, -5, 20]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "forall with elements failing both conjuncts should be FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_conjunction_single_element_pass() {
    let func = make_forall_conjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![5]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "single element 5 passes both conjuncts");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_conjunction_empty_domain() {
    let func = make_forall_conjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "forall conjunction over empty domain should be TRUE"
    );
}

// =============================================================================
// Disjunction early-exit tests (Exists with body = a \/ b)
// =============================================================================

/// Build: \E x \in domain : (x > 5) \/ (x < -5)
///
/// Bytecode:
///   ExistsBegin(rd=0, r_binding=1, r_domain=2, loop_end=+7) -- PC 0
///   LoadImm(r3, 5)           -- PC 1
///   GtInt(r4, r1, r3)        -- PC 2: r4 = x > 5
///   LoadImm(r5, -5)          -- PC 3
///   LtInt(r6, r1, r5)        -- PC 4: r6 = x < -5
///   Or(r7, r4, r6)           -- PC 5: r7 = r4 \/ r6
///   ExistsNext(rd=0, r_binding=1, r_body=7, loop_begin=-5)  -- PC 6
///   Ret(rs=0)                -- PC 7
fn make_exists_disjunction_func() -> BytecodeFunction {
    let mut func = BytecodeFunction::new("exists_disjunction".to_string(), 7);
    func.emit(Opcode::ExistsBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 7,
    });
    func.emit(Opcode::LoadImm { rd: 3, value: 5 });
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    func.emit(Opcode::LoadImm { rd: 5, value: -5 });
    func.emit(Opcode::LtInt {
        rd: 6,
        r1: 1,
        r2: 5,
    });
    func.emit(Opcode::Or {
        rd: 7,
        r1: 4,
        r2: 6,
    });
    func.emit(Opcode::ExistsNext {
        rd: 0,
        r_binding: 1,
        r_body: 7,
        loop_begin: -5,
    });
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_disjunction_first_disjunct_true() {
    // \E x \in {0,1,10} : x > 5 \/ x < -5 -- TRUE (10 > 5)
    let func = make_exists_disjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![0, 1, 10]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "exists with 10 > 5 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_disjunction_second_disjunct_true() {
    // \E x \in {0,1,-10} : x > 5 \/ x < -5 -- TRUE (-10 < -5)
    let func = make_exists_disjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![0, 1, -10]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "exists with -10 < -5 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_disjunction_none_true() {
    // \E x \in {0,1,2,-1,-2} : x > 5 \/ x < -5 -- FALSE (all in [-2, 2])
    let func = make_exists_disjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![0, 1, 2, -1, -2]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "exists with no extreme values should be FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_disjunction_both_disjuncts_could_be_true() {
    // \E x \in {-10, 10} : x > 5 \/ x < -5 -- TRUE (both elements satisfy one disjunct)
    let func = make_exists_disjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![-10, 10]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "exists with both elements satisfying a disjunct should be TRUE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_disjunction_empty_domain() {
    let func = make_exists_disjunction_func();
    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![]);
    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "exists disjunction over empty domain should be FALSE"
    );
}

// =============================================================================
// Range + conjunction/disjunction combined tests
// =============================================================================

/// Build: \A x \in lo..hi : (x > 0) /\ (x < 100)
fn make_range_forall_conjunction_func(lo: i64, hi: i64) -> BytecodeFunction {
    let mut func = BytecodeFunction::new("range_forall_conj".to_string(), 9);
    func.emit(Opcode::LoadImm { rd: 3, value: lo });
    func.emit(Opcode::LoadImm { rd: 4, value: hi });
    func.emit(Opcode::Range {
        rd: 2,
        lo: 3,
        hi: 4,
    });
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 7,
    });
    func.emit(Opcode::LoadImm { rd: 5, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 6,
        r1: 1,
        r2: 5,
    });
    func.emit(Opcode::LoadImm { rd: 7, value: 100 });
    func.emit(Opcode::LtInt {
        rd: 8,
        r1: 1,
        r2: 7,
    });
    func.emit(Opcode::And {
        rd: 9,
        r1: 6,
        r2: 8,
    });
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 9,
        loop_begin: -5,
    });
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_forall_conjunction_pass() {
    // \A x \in 1..50 : (x > 0) /\ (x < 100) -- TRUE
    let func = make_range_forall_conjunction_func(1, 50);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "forall x in 1..50 : x > 0 /\\ x < 100 should be TRUE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_forall_conjunction_fail() {
    // \A x \in 0..50 : (x > 0) /\ (x < 100) -- FALSE (0 fails x > 0)
    let func = make_range_forall_conjunction_func(0, 50);
    let out = compile_and_run_range(&func, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "forall x in 0..50 : x > 0 /\\ x < 100 should be FALSE"
    );
}

// =============================================================================
// State-loaded domain fallback tests (LoadVar-produced domain → FallbackNeeded)
// =============================================================================

/// Build a forall whose domain is loaded from a state variable (LoadVar),
/// NOT from SetEnum, Range, or LoadConst. The JIT cannot materialize this
/// domain at compile time, so it should emit FallbackNeeded.
///
///   LoadVar(rd=2, var_idx=0)   -- PC 0: load set from state[0] (opaque compound)
///   ForallBegin(rd=0, r_binding=1, r_domain=2, loop_end=+4) -- PC 1
///   LoadImm(r3, 0)             -- PC 2
///   GtInt(r4, r1, r3)          -- PC 3: body: r4 = x > 0
///   ForallNext(rd=0, r_binding=1, r_body=4, loop_begin=-2) -- PC 4
///   Ret(rs=0)                  -- PC 5
fn make_forall_state_loaded_domain_func() -> BytecodeFunction {
    let mut func = BytecodeFunction::new("forall_state_loaded".to_string(), 4);
    // PC 0: Load domain set from state variable 0 (opaque — not in QuantifierDomains)
    func.emit(Opcode::LoadVar { rd: 2, var_idx: 0 });
    // PC 1: ForallBegin — r_domain=2 has no pre-materialized domain
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    // PC 2: body
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    // PC 4: ForallNext
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    // PC 5: Ret
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_state_loaded_domain_emits_fallback() {
    // When the domain register comes from LoadVar (state-loaded set),
    // the JIT cannot materialize the domain. It should compile successfully
    // and return FallbackNeeded at runtime so the interpreter handles it.
    let func = make_forall_state_loaded_domain_func();
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    // Compile with empty domains — register 2 is not in the map
    let jit_fn = lowerer
        .compile_invariant_with_domains(&func, &QuantifierDomains::new())
        .expect("compilation should succeed (not error out)")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    // Provide a dummy state array (LoadVar reads from it, but we only care
    // about the JIT status, not the actual value)
    let state = [0i64; 4];
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    assert!(
        out.needs_fallback(),
        "state-loaded quantifier domain should produce FallbackNeeded, got {:?}",
        out.status
    );
}

/// Same as above but for ExistsBegin — verify the fallback works for both
/// quantifier kinds.
fn make_exists_state_loaded_domain_func() -> BytecodeFunction {
    let mut func = BytecodeFunction::new("exists_state_loaded".to_string(), 4);
    func.emit(Opcode::LoadVar { rd: 2, var_idx: 0 });
    func.emit(Opcode::ExistsBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    func.emit(Opcode::ExistsNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_state_loaded_domain_emits_fallback() {
    let func = make_exists_state_loaded_domain_func();
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant_with_domains(&func, &QuantifierDomains::new())
        .expect("compilation should succeed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    let state = [0i64; 4];
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    assert!(
        out.needs_fallback(),
        "state-loaded exists domain should produce FallbackNeeded, got {:?}",
        out.status
    );
}

/// Test that a ForallBegin with state-loaded domain emits PartialPass
/// (not plain FallbackNeeded) when preceding conjuncts have already been
/// verified by JIT.
///
///   LoadImm(r5, 1)                          -- PC 0: true
///   Ret with value 1  ... simplified:
///
/// Actually, testing PartialPass requires the quantifier to appear after
/// a JumpFalse (which increments conjuncts_passed). This is a more complex
/// bytecode sequence. For the basic test, we verify FallbackNeeded.
/// PartialPass is tested implicitly by the invariant cache integration tests.
fn make_forall_state_loaded_after_conjunct_func() -> BytecodeFunction {
    // Simplified: first conjunct is `state[1] > 0`, checked via JumpFalse.
    // Second conjunct is `\A x \in state[0] : x > 0` (state-loaded domain).
    //
    // PC 0: LoadVar(r5, 1)       — load state[1]
    // PC 1: LoadImm(r6, 0)
    // PC 2: GtInt(r7, r5, r6)    — r7 = state[1] > 0
    // PC 3: JumpFalse(r7, +6)    — if false, jump to PC 9 (return false)
    // PC 4: LoadVar(r2, 0)       — load domain set from state[0]
    // PC 5: ForallBegin(rd=0, r_binding=1, r_domain=2, loop_end=+4)
    // PC 6: LoadImm(r3, 0)
    // PC 7: GtInt(r4, r1, r3)
    // PC 8: ForallNext(rd=0, r_binding=1, r_body=4, loop_begin=-2)
    // PC 9: Ret(rs=0)
    let mut func = BytecodeFunction::new("forall_after_conjunct".to_string(), 7);
    func.emit(Opcode::LoadVar { rd: 5, var_idx: 1 });
    func.emit(Opcode::LoadImm { rd: 6, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 7,
        r1: 5,
        r2: 6,
    });
    func.emit(Opcode::JumpFalse { rs: 7, offset: 6 });
    func.emit(Opcode::LoadVar { rd: 2, var_idx: 0 });
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 1,
        r2: 3,
    });
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    func.emit(Opcode::Ret { rs: 0 });
    func
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_state_loaded_domain_partial_pass() {
    // When the first conjunct passes (state[1] > 0 via JumpFalse) and the
    // second conjunct has a state-loaded domain, the JIT should emit
    // PartialPass (not plain FallbackNeeded) because conjuncts_passed > 0.
    let func = make_forall_state_loaded_after_conjunct_func();
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant_with_domains(&func, &QuantifierDomains::new())
        .expect("compilation should succeed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    // state[0] = opaque set (doesn't matter), state[1] = 5 (> 0, passes first conjunct)
    let state = [0i64, 5, 0, 0];
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    assert!(
        out.is_partial_pass(),
        "state-loaded domain after passing conjunct should produce PartialPass, got {:?}",
        out.status
    );
    assert_eq!(
        out.conjuncts_passed, 1,
        "one conjunct (JumpFalse) should have been verified"
    );
}
