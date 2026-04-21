// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests verifying z4 SAT/SMT solver integration with TLA2.
//!
//! Tests cover:
//! - TLA+ expression translation to z4 and satisfiability solving
//! - BCP (Boolean Constraint Propagation) via z4's DPLL solver
//! - SAT/UNSAT correctness for known formulas with model validation
//! - Multi-constraint conjunction solving
//!
//! Part of #3743.

use ntest::timeout;
use num_bigint::BigInt;
use tla_core::ast::Expr;
use tla_core::name_intern::NameId;
use tla_core::Spanned;
use tla_z4::{SolveResult, TlaSort, Z4Error, Z4Translator};
use z4_dpll::Executor;
use z4_frontend::parse;

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn bi(n: i64) -> BigInt {
    BigInt::from(n)
}

// ---------------------------------------------------------------------------
// Section 1: TLA+ formula translation to z4 — SAT with model validation
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_tla_formula_x_gt0_and_x_lt5_and_x_eq3_is_sat() {
    // TLA+ formula: x > 0 /\ x < 5 /\ x = 3
    // Expected: SAT with x = 3
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let x_ident = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));

    // x > 0
    let x_gt_0 = spanned(Expr::Gt(
        Box::new(x_ident()),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    // x < 5
    let x_lt_5 = spanned(Expr::Lt(
        Box::new(x_ident()),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    // x = 3
    let x_eq_3 = spanned(Expr::Eq(
        Box::new(x_ident()),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));

    // Conjoin: x > 0 /\ x < 5
    let conj1 = spanned(Expr::And(Box::new(x_gt_0), Box::new(x_lt_5)));
    // Conjoin: (x > 0 /\ x < 5) /\ x = 3
    let formula = spanned(Expr::And(Box::new(conj1), Box::new(x_eq_3)));

    let term = trans.translate_bool(&formula).unwrap();
    trans.assert(term);

    assert!(
        matches!(trans.check_sat(), SolveResult::Sat),
        "x > 0 /\\ x < 5 /\\ x = 3 must be SAT"
    );

    let model = trans.get_model().expect("SAT implies a model");
    assert_eq!(
        model.int_val("x").cloned(),
        Some(bi(3)),
        "model must assign x = 3"
    );
}

#[test]
#[timeout(10_000)]
fn test_tla_formula_x_gt0_and_x_lt0_is_unsat() {
    // TLA+ formula: x > 0 /\ x < 0
    // Expected: UNSAT (no integer satisfies both)
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let x_ident = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));

    let x_gt_0 = spanned(Expr::Gt(
        Box::new(x_ident()),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    let x_lt_0 = spanned(Expr::Lt(
        Box::new(x_ident()),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    let formula = spanned(Expr::And(Box::new(x_gt_0), Box::new(x_lt_0)));

    let term = trans.translate_bool(&formula).unwrap();
    trans.assert(term);

    assert!(
        matches!(trans.check_sat(), SolveResult::Unsat(_)),
        "x > 0 /\\ x < 0 must be UNSAT"
    );
}

// ---------------------------------------------------------------------------
// Section 2: BCP (Boolean Constraint Propagation) via z4's DPLL solver
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_bcp_unit_propagation_pure_boolean() {
    // Unit propagation test: assert individual unit clauses and verify
    // the DPLL solver's BCP engine propagates them correctly.
    //
    // SMT-LIB encoding:
    //   (declare-const a Bool)
    //   (declare-const b Bool)
    //   (assert a)           ; unit clause: a must be true
    //   (assert (or a b))    ; BCP: already satisfied by a=true
    //   (assert (not b))     ; unit clause: b must be false
    //   (check-sat)          ; SAT: a=true, b=false
    let smt2 = "\
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(assert a)
(assert (or a b))
(assert (not b))
(check-sat)
";
    let commands = parse(smt2).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "BCP unit propagation: a=true, b=false must be SAT"
    );
}

#[test]
#[timeout(10_000)]
fn test_bcp_unit_propagation_derives_conflict() {
    // BCP conflict detection: unit clauses force contradictory assignments.
    //
    // SMT-LIB encoding:
    //   (assert a)       ; a = true
    //   (assert (not a)) ; a = false — conflict detected by BCP
    //   Result: UNSAT
    let smt2 = "\
(set-logic QF_UF)
(declare-const a Bool)
(assert a)
(assert (not a))
(check-sat)
";
    let commands = parse(smt2).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "BCP must detect conflict: a AND (not a)"
    );
}

#[test]
#[timeout(10_000)]
fn test_bcp_chain_propagation() {
    // BCP chain: unit propagation cascades through implications.
    //
    // Clauses:
    //   a = true           (unit clause)
    //   a => b  i.e. (or (not a) b)  — BCP forces b = true
    //   b => c  i.e. (or (not b) c)  — BCP forces c = true
    //   (not c)            — contradicts c = true → UNSAT
    let smt2 = "\
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert a)
(assert (or (not a) b))
(assert (or (not b) c))
(assert (not c))
(check-sat)
";
    let commands = parse(smt2).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "BCP chain propagation: a→b→c, (not c) must be UNSAT"
    );
}

#[test]
#[timeout(10_000)]
fn test_bcp_chain_propagation_sat() {
    // Same chain but without the final contradiction — should be SAT.
    //
    // Clauses:
    //   a = true
    //   a => b  → b = true
    //   b => c  → c = true
    //   Result: SAT with a=b=c=true
    let smt2 = "\
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert a)
(assert (or (not a) b))
(assert (or (not b) c))
(check-sat)
";
    let commands = parse(smt2).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "BCP chain without conflict: a→b→c must be SAT"
    );
}

#[test]
#[timeout(10_000)]
fn test_bcp_pigeonhole_3_into_2_is_unsat() {
    // Classic BCP stress test: 3-pigeonhole into 2 holes.
    // Each pigeon must be in exactly one hole; no two pigeons in the same hole.
    // With 3 pigeons and 2 holes, this is unsatisfiable.
    //
    // Variables: p_i_j means "pigeon i is in hole j"
    // Constraints:
    //   Each pigeon in at least one hole: (or p_i_1 p_i_2) for i=1..3
    //   No two pigeons in same hole: (not (and p_i_j p_k_j)) for i<k, j=1..2
    let smt2 = "\
(set-logic QF_UF)
(declare-const p11 Bool)
(declare-const p12 Bool)
(declare-const p21 Bool)
(declare-const p22 Bool)
(declare-const p31 Bool)
(declare-const p32 Bool)
; Each pigeon in at least one hole
(assert (or p11 p12))
(assert (or p21 p22))
(assert (or p31 p32))
; No two pigeons in hole 1
(assert (or (not p11) (not p21)))
(assert (or (not p11) (not p31)))
(assert (or (not p21) (not p31)))
; No two pigeons in hole 2
(assert (or (not p12) (not p22)))
(assert (or (not p12) (not p32)))
(assert (or (not p22) (not p32)))
(check-sat)
";
    let commands = parse(smt2).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "3-pigeonhole into 2 holes must be UNSAT"
    );
}

// ---------------------------------------------------------------------------
// Section 3: SAT/UNSAT correctness for known integer arithmetic formulas
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_sat_two_variable_system_unique_solution() {
    // System of equations with unique solution:
    //   x + y = 10 /\ x - y = 4
    //   Solution: x = 7, y = 3
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    let x = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));
    let y = || spanned(Expr::Ident("y".to_string(), NameId::INVALID));

    // x + y = 10
    let eq1 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Add(Box::new(x()), Box::new(y())))),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));
    // x - y = 4
    let eq2 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Sub(Box::new(x()), Box::new(y())))),
        Box::new(spanned(Expr::Int(BigInt::from(4)))),
    ));

    let t1 = trans.translate_bool(&eq1).unwrap();
    let t2 = trans.translate_bool(&eq2).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().expect("SAT implies a model");
    assert_eq!(model.int_val("x").cloned(), Some(bi(7)));
    assert_eq!(model.int_val("y").cloned(), Some(bi(3)));
}

#[test]
#[timeout(10_000)]
fn test_sat_range_constraint_bounded_variable() {
    // x >= 1 /\ x <= 1 should force x = 1
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let x = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));

    let geq = spanned(Expr::Geq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let leq = spanned(Expr::Leq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));

    let t1 = trans.translate_bool(&geq).unwrap();
    let t2 = trans.translate_bool(&leq).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().expect("SAT implies a model");
    assert_eq!(model.int_val("x").cloned(), Some(bi(1)));
}

#[test]
#[timeout(10_000)]
fn test_unsat_contradictory_equalities() {
    // x = 5 /\ x = 6 — contradictory, must be UNSAT
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let x = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));

    let eq5 = spanned(Expr::Eq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq6 = spanned(Expr::Eq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(6)))),
    ));

    let t1 = trans.translate_bool(&eq5).unwrap();
    let t2 = trans.translate_bool(&eq6).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    assert!(
        matches!(trans.check_sat(), SolveResult::Unsat(_)),
        "x = 5 /\\ x = 6 must be UNSAT"
    );
}

#[test]
#[timeout(10_000)]
fn test_sat_negation_and_disjunction() {
    // ~(x = 0) \/ (x = 1)  and  x = 0
    // The disjunction is satisfied by the right disjunct being false and
    // left being true: but x = 0 means ~(x = 0) is false, so x = 1 must
    // hold — which contradicts x = 0. UNSAT.
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let x = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));

    // ~(x = 0)
    let not_x_eq_0 = spanned(Expr::Not(Box::new(spanned(Expr::Eq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    )))));
    // x = 1
    let x_eq_1 = spanned(Expr::Eq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    // ~(x = 0) \/ (x = 1)
    let disj = spanned(Expr::Or(Box::new(not_x_eq_0), Box::new(x_eq_1)));

    // x = 0
    let x_eq_0 = spanned(Expr::Eq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    // x /= 1 (to block the right disjunct from being satisfied)
    let x_neq_1 = spanned(Expr::Neq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));

    let t_disj = trans.translate_bool(&disj).unwrap();
    let t_eq0 = trans.translate_bool(&x_eq_0).unwrap();
    let t_neq1 = trans.translate_bool(&x_neq_1).unwrap();
    trans.assert(t_disj);
    trans.assert(t_eq0);
    trans.assert(t_neq1);

    assert!(
        matches!(trans.check_sat(), SolveResult::Unsat(_)),
        "(~(x=0) \\/ x=1) /\\ x=0 /\\ x/=1 must be UNSAT"
    );
}

#[test]
#[timeout(10_000)]
fn test_sat_implication_modus_ponens() {
    // p /\ (p => q) should force q = true
    let mut trans = Z4Translator::new();
    trans.declare_var("p", TlaSort::Bool).unwrap();
    trans.declare_var("q", TlaSort::Bool).unwrap();

    let p = || spanned(Expr::Ident("p".to_string(), NameId::INVALID));
    let q = || spanned(Expr::Ident("q".to_string(), NameId::INVALID));

    // p
    let p_true = p();
    // p => q
    let implies = spanned(Expr::Implies(Box::new(p()), Box::new(q())));

    let t_p = trans.translate_bool(&p_true).unwrap();
    let t_impl = trans.translate_bool(&implies).unwrap();
    trans.assert(t_p);
    trans.assert(t_impl);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().expect("SAT implies a model");
    assert_eq!(model.bool_val("p"), Some(true), "p must be true");
    assert_eq!(
        model.bool_val("q"),
        Some(true),
        "q must be true (modus ponens)"
    );
}

// ---------------------------------------------------------------------------
// Section 4: BCP with integer theory (LIA) — z4 DPLL + theory propagation
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_lia_bcp_integer_bounds_sat() {
    // Integer arithmetic with BCP: z4's DPLL solver coordinates with the
    // LIA theory solver to propagate integer bounds.
    //
    //   x > 0 /\ x < 5 /\ x > 3 => x = 4
    let smt2 = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 5))
(assert (> x 3))
(check-sat)
(get-model)
";
    let commands = parse(smt2).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    // Model should contain x = 4 (only integer satisfying 3 < x < 5)
    let model_str = outputs.get(1).expect("get-model output");
    assert!(
        model_str.contains("4"),
        "model should assign x = 4, got: {model_str}"
    );
}

#[test]
#[timeout(10_000)]
fn test_lia_bcp_integer_bounds_unsat() {
    // Integer bounds that leave no valid assignment:
    //   x > 3 /\ x < 5 /\ x /= 4 => UNSAT (no integer in (3, 5) except 4)
    let smt2 = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 3))
(assert (< x 5))
(assert (not (= x 4)))
(check-sat)
";
    let commands = parse(smt2).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "x > 3 /\\ x < 5 /\\ x /= 4 must be UNSAT for integers"
    );
}

#[test]
#[timeout(10_000)]
fn test_lia_multi_variable_propagation() {
    // Multi-variable system where theory propagation narrows domains:
    //   x + y = 5 /\ x >= 3 /\ y >= 3 => UNSAT (x>=3 and y>=3 means x+y>=6)
    let smt2 = "\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 5))
(assert (>= x 3))
(assert (>= y 3))
(check-sat)
";
    let commands = parse(smt2).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "x + y = 5 with x >= 3 and y >= 3 must be UNSAT"
    );
}

// ---------------------------------------------------------------------------
// Section 5: TLA+ translation combined with model validation
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_tla_multi_variable_conjunction_with_arithmetic() {
    // TLA+ formula: x = 2 * 3 /\ y = x + 1
    // (using constant multiplication which is linear)
    // Expected: x = 6, y = 7
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    let x = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));
    let y = || spanned(Expr::Ident("y".to_string(), NameId::INVALID));

    // x = 2 * 3 (constant mul, linear)
    let two_times_three = spanned(Expr::Mul(
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));
    let x_eq = spanned(Expr::Eq(Box::new(x()), Box::new(two_times_three)));

    // y = x + 1
    let x_plus_1 = spanned(Expr::Add(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let y_eq = spanned(Expr::Eq(Box::new(y()), Box::new(x_plus_1)));

    let t1 = trans.translate_bool(&x_eq).unwrap();
    let t2 = trans.translate_bool(&y_eq).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().expect("SAT implies a model");
    assert_eq!(model.int_val("x").cloned(), Some(bi(6)));
    assert_eq!(model.int_val("y").cloned(), Some(bi(7)));
}

#[test]
#[timeout(10_000)]
fn test_tla_boolean_variable_sat() {
    // TLA+ formula: p /\ q /\ (p <=> q)
    // Expected: SAT with p = true, q = true
    let mut trans = Z4Translator::new();
    trans.declare_var("p", TlaSort::Bool).unwrap();
    trans.declare_var("q", TlaSort::Bool).unwrap();

    let p = || spanned(Expr::Ident("p".to_string(), NameId::INVALID));
    let q = || spanned(Expr::Ident("q".to_string(), NameId::INVALID));

    // p <=> q
    let equiv = spanned(Expr::Equiv(Box::new(p()), Box::new(q())));
    // p /\ q
    let conj = spanned(Expr::And(Box::new(p()), Box::new(q())));

    let t1 = trans.translate_bool(&conj).unwrap();
    let t2 = trans.translate_bool(&equiv).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().expect("SAT implies a model");
    assert_eq!(model.bool_val("p"), Some(true));
    assert_eq!(model.bool_val("q"), Some(true));
}

#[test]
#[timeout(10_000)]
fn test_tla_if_then_else_sat() {
    // TLA+ formula: x = IF TRUE THEN 42 ELSE 0
    // Expected: SAT with x = 42
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let x = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));

    let ite = spanned(Expr::If(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Int(BigInt::from(42)))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    let eq = spanned(Expr::Eq(Box::new(x()), Box::new(ite)));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().expect("SAT implies a model");
    assert_eq!(model.int_val("x").cloned(), Some(bi(42)));
}

#[test]
#[timeout(10_000)]
fn test_tla_negation_unsat() {
    // TLA+ formula: x = 5 /\ ~(x = 5)
    // Expected: UNSAT (direct contradiction)
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let x = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));

    let x_eq_5 = spanned(Expr::Eq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let not_x_eq_5 = spanned(Expr::Not(Box::new(spanned(Expr::Eq(
        Box::new(x()),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    )))));

    let t1 = trans.translate_bool(&x_eq_5).unwrap();
    let t2 = trans.translate_bool(&not_x_eq_5).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    assert!(
        matches!(trans.check_sat(), SolveResult::Unsat(_)),
        "x = 5 /\\ ~(x = 5) must be UNSAT"
    );
}

// ---------------------------------------------------------------------------
// Section 6: Error handling — unsupported operations
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_nonlinear_multiplication_rejected() {
    // x * y where both are symbolic should be rejected (QF_LIA is linear only)
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    let x = || spanned(Expr::Ident("x".to_string(), NameId::INVALID));
    let y = || spanned(Expr::Ident("y".to_string(), NameId::INVALID));

    let nonlinear = spanned(Expr::Gt(
        Box::new(spanned(Expr::Mul(Box::new(x()), Box::new(y())))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    let err = trans.translate_bool(&nonlinear).unwrap_err();
    assert!(
        matches!(err, Z4Error::UnsupportedOp(_)),
        "nonlinear x * y must be rejected under QF_LIA, got: {err:?}"
    );
}

#[test]
#[timeout(10_000)]
fn test_unknown_variable_rejected() {
    // Referencing an undeclared variable should produce an error.
    // The translator may return either UnknownVariable or UntranslatableExpr
    // depending on where the unknown variable is encountered (equality
    // dispatch checks sort before looking up the variable).
    let mut trans = Z4Translator::new();

    let undeclared = spanned(Expr::Ident("undeclared_var".to_string(), NameId::INVALID));
    let eq = spanned(Expr::Eq(
        Box::new(undeclared),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    let err = trans.translate_bool(&eq).unwrap_err();
    assert!(
        matches!(
            err,
            Z4Error::UnknownVariable(_) | Z4Error::UntranslatableExpr(_)
        ),
        "undeclared variable must produce an error, got: {err:?}"
    );
}
