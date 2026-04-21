// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Audit of JIT set membership and quantifier compilation.
//! Part of #3788: JIT set membership and quantifier compilation.
//!
//! # Gap Analysis
//!
//! ## Set Operations (set_ops.rs) — Coverage Summary
//!
//! | Feature                        | Status        | Tests                                        |
//! |-------------------------------|---------------|----------------------------------------------|
//! | SetEnum (enumerated sets)      | IMPLEMENTED   | set_membership.rs: 10 tests                  |
//! | Range (integer interval)       | IMPLEMENTED   | set_membership.rs: 6 tests                   |
//! | SetIn (enum membership)        | IMPLEMENTED   | set_membership.rs: 8 tests (incl. state var) |
//! | SetIn (range membership)       | IMPLEMENTED   | set_membership.rs: 6 tests (incl. boundary)  |
//! | Subseteq (enum vs enum)        | IMPLEMENTED   | set_membership.rs: 3 tests                   |
//! | Subseteq (enum vs range)       | IMPLEMENTED   | set_membership.rs: 2 tests                   |
//! | Subseteq (range vs *)          | UNSUPPORTED   | NEW: test below verifies fallback             |
//! | SetEnum size limit (<=16)      | IMPLEMENTED   | set_membership.rs: 2 tests                   |
//! | \notin                         | NO GAP        | Handled at TIR level as Not(SetIn(...))       |
//! | \subset (proper subset)        | NO GAP        | Handled at syntax/core level, not bytecode    |
//! | SetUnion/Intersect/Diff/etc.   | INELIGIBLE    | set_membership.rs: 1 test + eligibility.rs    |
//!
//! ## Quantifier Loops (quantifier_loops.rs) — Coverage Summary
//!
//! | Feature                        | Status        | Tests                                        |
//! |-------------------------------|---------------|----------------------------------------------|
//! | ForallBegin/ForallNext         | IMPLEMENTED   | quantifier_loops.rs: 5 tests                 |
//! | ExistsBegin/ExistsNext         | IMPLEMENTED   | quantifier_loops.rs: 4 tests                 |
//! | Empty domain (forall)          | IMPLEMENTED   | quantifier_loops.rs: 1 test                  |
//! | Empty domain (exists)          | IMPLEMENTED   | quantifier_loops.rs: 1 test                  |
//! | Nested quantifiers             | SUPPORTED     | NEW: tests below (was UNTESTED)               |
//! | Quantifier + set membership    | SUPPORTED     | NEW: test below (was UNTESTED)                |
//! | ChooseBegin/ChooseNext         | INELIGIBLE    | eligibility.rs: 1 test                       |
//! | SetBuilderBegin/SetFilterBegin | INELIGIBLE    | By design (compound value construction)       |
//!
//! ## Eligibility (eligibility.rs) — Coverage Summary
//!
//! | Feature                        | Status        | Tests                                        |
//! |-------------------------------|---------------|----------------------------------------------|
//! | ForallBegin/ExistsBegin        | ELIGIBLE      | eligibility.rs: 2 tests                      |
//! | ForallNext/ExistsNext          | ELIGIBLE      | eligibility.rs: 2 tests (via Begin tests)     |
//! | SetEnum (count <= 16)          | ELIGIBLE      | eligibility.rs + set_membership.rs            |
//! | SetEnum (count > 16)           | INELIGIBLE    | set_membership.rs: 1 test                    |
//! | SetIn                          | ELIGIBLE      | eligibility.rs: 1 test                       |
//! | Range                          | ELIGIBLE      | set_membership.rs: 1 test                    |
//! | Subseteq                       | ELIGIBLE      | set_membership.rs: 1 test                    |
//! | ChooseBegin                    | INELIGIBLE    | eligibility.rs: 1 test                       |
//!
//! ## Conclusion
//!
//! The JIT compilation of set membership and quantifiers is comprehensive.
//! The architecture is sound: virtual sets avoid materializing set values,
//! and quantifier loops use pre-materialized domain arrays with counted
//! iteration. Three gaps were identified and are addressed by the tests
//! below:
//!
//! 1. **Nested quantifiers** — The QuantifierLoopStack supports nesting but
//!    had no test coverage. Two tests added (forall-in-forall, exists-in-forall).
//!
//! 2. **Quantifier combined with set membership** — A test for
//!    `\E x \in S : x \in T` combines quantifier loop with SetIn expansion.
//!
//! 3. **Subseteq range LHS error** — The error path for Range \subseteq T
//!    had no test coverage. Added a compilation failure test.

use crate::abi::{JitCallOut, JitStatus};
use crate::bytecode_lower::BytecodeLowerer;
use crate::bytecode_lower::QuantifierDomains;
use tla_tir::bytecode::{BytecodeFunction, Opcode};

use super::compile_and_run_no_state;

/// Helper: compile with quantifier domains and run.
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

// =====================================================================
// Gap 1: Nested quantifiers
// =====================================================================

/// Nested forall: \A x \in {1,2,3} : \A y \in {1,2} : x + y > 0
///
/// All domain elements are positive, so x + y > 0 is always true.
/// Expected result: TRUE.
///
/// Bytecode layout:
///   PC 0: ForallBegin(rd=0, r_binding=1, r_domain=2, loop_end=+9)  => exit PC 9
///   PC 1: ForallBegin(rd=3, r_binding=4, r_domain=5, loop_end=+6)  => exit PC 7
///   PC 2: AddInt(rd=6, r1=1, r2=4)      -- x + y
///   PC 3: LoadImm(rd=7, 0)               -- zero constant
///   PC 4: GtInt(rd=8, r1=6, r2=7)        -- x + y > 0
///   PC 5: Move(rd=9, rs=8)               -- body result for inner
///   PC 6: ForallNext(rd=3, r_binding=4, r_body=9, loop_begin=-4)  => body PC 2
///   PC 7: Move(rd=10, rs=3)              -- body result for outer = inner result
///   PC 8: ForallNext(rd=0, r_binding=1, r_body=10, loop_begin=-7) => body PC 1
///   PC 9: Ret(rs=0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_forall_all_true() {
    let mut func = BytecodeFunction::new("nested_forall".to_string(), 10);
    // PC 0: outer ForallBegin — exit at PC 9
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 9,
    });
    // PC 1: inner ForallBegin — exit at PC 7
    func.emit(Opcode::ForallBegin {
        rd: 3,
        r_binding: 4,
        r_domain: 5,
        loop_end: 6,
    });
    // PC 2: x + y
    func.emit(Opcode::AddInt {
        rd: 6,
        r1: 1,
        r2: 4,
    });
    // PC 3: zero constant
    func.emit(Opcode::LoadImm { rd: 7, value: 0 });
    // PC 4: x + y > 0
    func.emit(Opcode::GtInt {
        rd: 8,
        r1: 6,
        r2: 7,
    });
    // PC 5: inner body result
    func.emit(Opcode::Move { rd: 9, rs: 8 });
    // PC 6: inner ForallNext — back to PC 2 (inner body start)
    func.emit(Opcode::ForallNext {
        rd: 3,
        r_binding: 4,
        r_body: 9,
        loop_begin: -4,
    });
    // PC 7: outer body result = inner quantifier result
    func.emit(Opcode::Move { rd: 10, rs: 3 });
    // PC 8: outer ForallNext — back to PC 1 (outer body start = inner ForallBegin)
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 10,
        loop_begin: -7,
    });
    // PC 9: return
    func.emit(Opcode::Ret { rs: 0 });

    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, 3]); // outer domain
    domains.insert(5, vec![1, 2]); // inner domain

    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "\\A x \\in {{1,2,3}} : \\A y \\in {{1,2}} : x + y > 0 should be TRUE"
    );
}

/// Nested forall with inner failure:
/// \A x \in {1, -1} : \A y \in {1, 2} : x + y > 0
///
/// When x = -1, y = 1: x + y = 0, which is NOT > 0.
/// Expected result: FALSE (inner forall short-circuits on x=-1, y has element
/// making x+y <= 0, so outer forall fails).
///
/// Actually x=-1, y=1 gives 0 which is not > 0, and x=-1, y=2 gives 1 which IS > 0.
/// So inner forall for x=-1: P(-1,1) = false => short-circuit => inner = false.
/// Outer forall: inner = false => short-circuit => outer = false.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_forall_inner_fails() {
    let mut func = BytecodeFunction::new("nested_forall_fail".to_string(), 10);
    // Same bytecode structure as test_nested_forall_all_true
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 9,
    });
    func.emit(Opcode::ForallBegin {
        rd: 3,
        r_binding: 4,
        r_domain: 5,
        loop_end: 6,
    });
    func.emit(Opcode::AddInt {
        rd: 6,
        r1: 1,
        r2: 4,
    });
    func.emit(Opcode::LoadImm { rd: 7, value: 0 });
    func.emit(Opcode::GtInt {
        rd: 8,
        r1: 6,
        r2: 7,
    });
    func.emit(Opcode::Move { rd: 9, rs: 8 });
    func.emit(Opcode::ForallNext {
        rd: 3,
        r_binding: 4,
        r_body: 9,
        loop_begin: -4, // back to PC 2 (inner body start)
    });
    func.emit(Opcode::Move { rd: 10, rs: 3 });
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 10,
        loop_begin: -7, // back to PC 1 (outer body start)
    });
    func.emit(Opcode::Ret { rs: 0 });

    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, -1]); // outer: x takes 1 then -1
    domains.insert(5, vec![1, 2]); // inner: y takes 1 then 2

    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "\\A x \\in {{1,-1}} : \\A y \\in {{1,2}} : x + y > 0 should be FALSE"
    );
}

/// Nested exists-in-forall:
/// \A x \in {1, 2, 3} : \E y \in {10, 20} : y > x
///
/// For each x, there exists a y > x (since y=10 > 3). Result: TRUE.
///
/// Bytecode layout:
///   PC 0: ForallBegin(rd=0, r_binding=1, r_domain=2, loop_end=+7)  => exit PC 7
///   PC 1: ExistsBegin(rd=3, r_binding=4, r_domain=5, loop_end=+4)  => exit PC 5
///   PC 2: GtInt(rd=6, r1=4, r2=1)       -- y > x
///   PC 3: Move(rd=7, rs=6)               -- body result for inner
///   PC 4: ExistsNext(rd=3, r_binding=4, r_body=7, loop_begin=-2)   => body PC 2
///   PC 5: Move(rd=8, rs=3)               -- body result for outer
///   PC 6: ForallNext(rd=0, r_binding=1, r_body=8, loop_begin=-5)   => body PC 1
///   PC 7: Ret(rs=0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_exists_in_forall() {
    let mut func = BytecodeFunction::new("exists_in_forall".to_string(), 8);
    // PC 0: outer ForallBegin — exit at PC 7
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 7,
    });
    // PC 1: inner ExistsBegin — exit at PC 5
    func.emit(Opcode::ExistsBegin {
        rd: 3,
        r_binding: 4,
        r_domain: 5,
        loop_end: 4,
    });
    // PC 2: y > x
    func.emit(Opcode::GtInt {
        rd: 6,
        r1: 4,
        r2: 1,
    });
    // PC 3: inner body result
    func.emit(Opcode::Move { rd: 7, rs: 6 });
    // PC 4: inner ExistsNext — back to PC 2 (inner body start)
    func.emit(Opcode::ExistsNext {
        rd: 3,
        r_binding: 4,
        r_body: 7,
        loop_begin: -2,
    });
    // PC 5: outer body result
    func.emit(Opcode::Move { rd: 8, rs: 3 });
    // PC 6: outer ForallNext — back to PC 1 (outer body start)
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 8,
        loop_begin: -5,
    });
    // PC 7: Ret
    func.emit(Opcode::Ret { rs: 0 });

    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, 3]); // outer: x
    domains.insert(5, vec![10, 20]); // inner: y

    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "\\A x \\in {{1,2,3}} : \\E y \\in {{10,20}} : y > x should be TRUE"
    );
}

// =====================================================================
// Gap 2: Quantifier combined with set membership
// =====================================================================

/// \E x \in Domain : x \in TargetSet
///
/// Domain = {1, 5, 10}, TargetSet = {3, 5, 7}
/// x=1: 1 \in {3,5,7} = false
/// x=5: 5 \in {3,5,7} = true => exists short-circuits => TRUE
///
/// Bytecode layout:
///   PC 0: LoadImm(r5, 3)                 -- target set elements
///   PC 1: LoadImm(r6, 5)
///   PC 2: LoadImm(r7, 7)
///   PC 3: SetEnum(rd=8, start=5, count=3) -- r8 = {3, 5, 7}
///   PC 4: ExistsBegin(rd=0, r_binding=1, r_domain=2, loop_end=+4)  => exit PC 8
///   PC 5: SetIn(rd=3, elem=1, set=8)     -- r_binding \in TargetSet
///   PC 6: Move(rd=4, rs=3)
///   PC 7: ExistsNext(rd=0, r_binding=1, r_body=4, loop_begin=-2)   => body PC 5
///   PC 8: Ret(rs=0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_with_set_membership() {
    let mut func = BytecodeFunction::new("exists_set_in".to_string(), 8);
    // PC 0-3: Build target set {3, 5, 7} before the quantifier loop
    func.emit(Opcode::LoadImm { rd: 5, value: 3 });
    func.emit(Opcode::LoadImm { rd: 6, value: 5 });
    func.emit(Opcode::LoadImm { rd: 7, value: 7 });
    func.emit(Opcode::SetEnum {
        rd: 8,
        start: 5,
        count: 3,
    });
    // PC 4: ExistsBegin — exit at PC 8
    func.emit(Opcode::ExistsBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    // PC 5: Body — r_binding \in {3, 5, 7}
    func.emit(Opcode::SetIn {
        rd: 3,
        elem: 1,
        set: 8,
    });
    // PC 6: body result
    func.emit(Opcode::Move { rd: 4, rs: 3 });
    // PC 7: ExistsNext — back to PC 5 (body start)
    func.emit(Opcode::ExistsNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    // PC 8: Ret
    func.emit(Opcode::Ret { rs: 0 });

    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 5, 10]); // domain: {1, 5, 10}

    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "\\E x \\in {{1,5,10}} : x \\in {{3,5,7}} should be TRUE (5 is in both)"
    );
}

/// \E x \in Domain : x \in TargetSet (no overlap)
///
/// Domain = {1, 2, 4}, TargetSet = {3, 5, 7}
/// No overlap => FALSE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_with_set_membership_no_overlap() {
    let mut func = BytecodeFunction::new("exists_set_in_false".to_string(), 8);
    func.emit(Opcode::LoadImm { rd: 5, value: 3 });
    func.emit(Opcode::LoadImm { rd: 6, value: 5 });
    func.emit(Opcode::LoadImm { rd: 7, value: 7 });
    func.emit(Opcode::SetEnum {
        rd: 8,
        start: 5,
        count: 3,
    });
    // PC 4: ExistsBegin — exit at PC 8
    func.emit(Opcode::ExistsBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    func.emit(Opcode::SetIn {
        rd: 3,
        elem: 1,
        set: 8,
    });
    func.emit(Opcode::Move { rd: 4, rs: 3 });
    // PC 7: ExistsNext — back to PC 5 (body start)
    func.emit(Opcode::ExistsNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![1, 2, 4]); // no overlap with {3, 5, 7}

    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "\\E x \\in {{1,2,4}} : x \\in {{3,5,7}} should be FALSE"
    );
}

/// \A x \in Domain : x \in RangeSet
///
/// Domain = {3, 5, 7}, Range = 1..10 => all in range => TRUE.
///
/// Bytecode layout:
///   PC 0: LoadImm(r5, 1)
///   PC 1: LoadImm(r6, 10)
///   PC 2: Range(rd=7, lo=5, hi=6)
///   PC 3: ForallBegin(rd=0, r_binding=1, r_domain=2, loop_end=+4)  => exit PC 7
///   PC 4: SetIn(rd=3, elem=1, set=7)     -- r_binding \in 1..10
///   PC 5: Move(rd=4, rs=3)
///   PC 6: ForallNext(rd=0, r_binding=1, r_body=4, loop_begin=-2)   => body PC 4
///   PC 7: Ret(rs=0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_with_range_membership() {
    let mut func = BytecodeFunction::new("forall_range_in".to_string(), 8);
    // PC 0-2: Build range 1..10
    func.emit(Opcode::LoadImm { rd: 5, value: 1 });
    func.emit(Opcode::LoadImm { rd: 6, value: 10 });
    func.emit(Opcode::Range {
        rd: 7,
        lo: 5,
        hi: 6,
    });
    // PC 3: ForallBegin — exit at PC 7
    func.emit(Opcode::ForallBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    // PC 4: Body — r_binding \in 1..10
    func.emit(Opcode::SetIn {
        rd: 3,
        elem: 1,
        set: 7,
    });
    // PC 5: body result
    func.emit(Opcode::Move { rd: 4, rs: 3 });
    // PC 6: ForallNext — back to PC 4 (body start)
    func.emit(Opcode::ForallNext {
        rd: 0,
        r_binding: 1,
        r_body: 4,
        loop_begin: -2,
    });
    // PC 7: Ret
    func.emit(Opcode::Ret { rs: 0 });

    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![3, 5, 7]); // all in 1..10

    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "\\A x \\in {{3,5,7}} : x \\in 1..10 should be TRUE"
    );
}

// =====================================================================
// Gap 3: Subseteq range LHS graceful fallback
// =====================================================================

/// Subseteq with Range as LHS should compile but emit FallbackNeeded at runtime.
///
/// The JIT Phase A does not support range sets as LHS of \subseteq because
/// it would require enumerating the range or doing lo/hi bounds comparison.
/// Instead of crashing, the lowerer emits FallbackNeeded status so the
/// interpreter handles this case gracefully.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_range_lhs_emits_fallback() {
    let mut func = BytecodeFunction::new("subseteq_range_lhs".to_string(), 0);
    // LHS: range 1..5
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 5 });
    func.emit(Opcode::Range {
        rd: 2,
        lo: 0,
        hi: 1,
    });
    // RHS: range 1..10
    func.emit(Opcode::LoadImm { rd: 3, value: 1 });
    func.emit(Opcode::LoadImm { rd: 4, value: 10 });
    func.emit(Opcode::Range {
        rd: 5,
        lo: 3,
        hi: 4,
    });
    // Subseteq with range LHS
    func.emit(Opcode::Subseteq {
        rd: 6,
        r1: 2,
        r2: 5,
    });
    func.emit(Opcode::Ret { rs: 6 });

    let out = compile_and_run_no_state(&func);
    assert!(
        out.needs_fallback(),
        "Subseteq with range LHS should produce FallbackNeeded status, got: {:?}",
        out.status
    );
}

// =====================================================================
// Correctness: forall short-circuit on first false element
// =====================================================================

/// \A x \in {0, 1, 2} : x > 0
///
/// First element x=0 fails => short-circuit immediately => FALSE.
/// Verifies early exit behavior.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_short_circuit_first_element() {
    let mut func = BytecodeFunction::new("forall_short_circuit".to_string(), 4);
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

    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![0, 1, 2]); // first element fails

    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 0,
        "\\A x \\in {{0,1,2}} : x > 0 should be FALSE (first element fails)"
    );
}

/// \E x \in {5, 3, 1} : x = 5
///
/// First element x=5 matches => short-circuit immediately => TRUE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_short_circuit_first_element() {
    let mut func = BytecodeFunction::new("exists_short_circuit".to_string(), 4);
    func.emit(Opcode::ExistsBegin {
        rd: 0,
        r_binding: 1,
        r_domain: 2,
        loop_end: 4,
    });
    func.emit(Opcode::LoadImm { rd: 3, value: 5 });
    func.emit(Opcode::Eq {
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

    let mut domains = QuantifierDomains::new();
    domains.insert(2, vec![5, 3, 1]); // first element matches

    let out = compile_and_run_with_domains(&func, &domains, &[]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "\\E x \\in {{5,3,1}} : x = 5 should be TRUE (first element matches)"
    );
}
