// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::Executor;
use crate::executor::model::Model;
use crate::executor_types::{SolveResult, StatValue, Statistics, UnknownReason};
use hashbrown::HashMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use z4_core::term::Symbol;
use z4_core::Sort;
use z4_frontend::sexp::SExpr;
use z4_frontend::{parse, Command};

#[test]
fn test_get_info_name_trims_colon_prefix() {
    let exec = Executor::new();
    assert_eq!(exec.get_info(":name"), "(:name \"z4\")");
}

#[test]
fn test_get_info_reason_unknown_requires_unknown_result() {
    let exec = Executor::new();
    assert_eq!(
        exec.get_info(":reason-unknown"),
        "(error \"no unknown result to explain\")"
    );
}

#[test]
fn test_get_info_reason_unknown_formats_reason() {
    let mut exec = Executor::new();
    exec.last_result = Some(SolveResult::Unknown);
    exec.last_unknown_reason = Some(UnknownReason::MemoryLimit);
    assert_eq!(exec.get_info("reason-unknown"), "(:reason-unknown memout)");
}

#[test]
fn test_get_info_assertion_stack_levels_counts_assertions() {
    let mut exec = Executor::new();
    let a = exec.ctx.terms.mk_var("a", Sort::Bool);
    exec.ctx.assertions.push(a);
    exec.ctx.assertions.push(exec.ctx.terms.mk_not(a));
    assert_eq!(
        exec.get_info(":assertion-stack-levels"),
        "(:assertion-stack-levels 2)"
    );
}

#[test]
fn test_format_statistics_smt2_formats_extra_fields() {
    let mut exec = Executor::new();
    let mut stats = Statistics {
        conflicts: 1,
        decisions: 2,
        ..Default::default()
    };
    stats.extra.insert("foo_bar".to_string(), StatValue::Int(7));
    stats
        .extra
        .insert("time_sec".to_string(), StatValue::Float(1.5));
    stats
        .extra
        .insert("note".to_string(), StatValue::String("hello".to_string()));
    exec.last_statistics = stats;

    let out = exec.get_info(":all-statistics");
    assert!(out.starts_with('('));
    assert!(out.ends_with(')'));
    assert!(out.contains(":conflicts"));
    assert!(out.contains(":decisions"));
    assert!(out.contains(":foo-bar"));
    assert!(out.contains(":time-sec"));
    assert!(out.contains("1.50"));
    assert!(out.contains("\"hello\""));
}

#[test]
fn test_get_option_value_reports_known_and_unknown_options() {
    let mut exec = Executor::new();
    exec.execute(&Command::SetOption(
        ":produce-unsat-cores".to_string(),
        SExpr::True,
    ))
    .unwrap();

    assert_eq!(
        exec.get_option_value(":produce-unsat-cores"),
        "(:produce-unsat-cores true)"
    );
    assert_eq!(
        exec.get_option_value(":does-not-exist"),
        "(error \"unknown option: :does-not-exist\")"
    );
}

#[test]
fn test_get_assertions_empty_and_nonempty() {
    let mut exec = Executor::new();
    assert_eq!(exec.assertions(), "()");

    let a = exec.ctx.terms.mk_var("a", Sort::Bool);
    exec.ctx.assertions.push(a);
    exec.ctx.assertions.push(exec.ctx.terms.mk_not(a));
    assert_eq!(exec.assertions(), "(a\n (not a))");
}

#[test]
fn test_format_term_handles_core_term_forms() {
    let mut exec = Executor::new();

    let a = exec.ctx.terms.mk_var("a", Sort::Bool);
    assert_eq!(exec.format_term(a), "a");

    let let_var = exec.ctx.terms.mk_var("let", Sort::Bool);
    assert_eq!(exec.format_term(let_var), "|let|");

    let int_term = exec.ctx.terms.mk_int(BigInt::from(-7));
    assert_eq!(exec.format_term(int_term), "(- 7)");

    let rat_term = exec
        .ctx
        .terms
        .mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
    assert_eq!(exec.format_term(rat_term), "(/ 3 2)");

    let str_term = exec.ctx.terms.mk_string("hi".to_string());
    assert_eq!(exec.format_term(str_term), "\"hi\"");

    let bv_term = exec.ctx.terms.mk_bitvec(BigInt::from(1), 8);
    assert_eq!(exec.format_term(bv_term), "#x01");

    let not_a = exec.ctx.terms.mk_not(a);
    assert_eq!(exec.format_term(not_a), "(not a)");

    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let ite_term = exec.ctx.terms.mk_ite(a, one, two);
    assert_eq!(exec.format_term(ite_term), "(ite a 1 2)");

    let c = exec.ctx.terms.mk_app(Symbol::named("c"), vec![], Sort::Int);
    assert_eq!(exec.format_term(c), "c");

    let arg1 = exec.ctx.terms.mk_int(BigInt::from(1));
    let arg2 = exec.ctx.terms.mk_int(BigInt::from(2));
    let f_app = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![arg1, arg2], Sort::Int);
    assert_eq!(exec.format_term(f_app), "(f 1 2)");

    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let let_term = exec.ctx.terms.mk_let(vec![("x".to_string(), int_term)], x);
    assert_eq!(exec.format_term(let_term), "(let ((x (- 7))) x)");

    let forall_term = exec.ctx.terms.mk_forall(
        vec![("x".to_string(), Sort::Int)],
        exec.ctx.terms.true_term(),
    );
    assert_eq!(exec.format_term(forall_term), "(forall ((x Int)) true)");

    let exists_term = exec.ctx.terms.mk_exists(
        vec![("y".to_string(), Sort::Bool)],
        exec.ctx.terms.false_term(),
    );
    assert_eq!(exec.format_term(exists_term), "(exists ((y Bool)) false)");
}

#[test]
fn test_get_assignment_requires_produce_assignments() {
    let exec = Executor::new();
    assert_eq!(
        exec.get_assignment(),
        "(error \"assignment generation is not enabled, set :produce-assignments to true\")"
    );
}

#[test]
fn test_get_assignment_sat_model_named_term() {
    let mut exec = Executor::new();
    exec.execute(&Command::SetOption(
        ":produce-assignments".to_string(),
        SExpr::True,
    ))
    .unwrap();

    let cmds = parse(
        r#"
            (set-logic QF_UF)
            (declare-const a Bool)
            (assert (! a :named n1))
        "#,
    )
    .unwrap();
    exec.execute_all(&cmds).unwrap();

    let a = exec.ctx.terms.lookup("a").unwrap();
    let mut term_to_var = HashMap::new();
    term_to_var.insert(a, 0);

    exec.last_result = Some(SolveResult::Sat);
    exec.last_model = Some(Model {
        sat_model: vec![true],
        term_to_var,
        euf_model: None,
        array_model: None,
        lra_model: None,
        lia_model: None,
        bv_model: None,
        fp_model: None,
        string_model: None,
        seq_model: None,
    });

    assert_eq!(exec.get_assignment(), "((n1 true))");
}

#[test]
fn test_get_unsat_core_requires_produce_unsat_cores() {
    let exec = Executor::new();
    assert_eq!(
        exec.unsat_core(),
        "(error \"unsat core generation is not enabled, set :produce-unsat-cores to true\")"
    );
}

#[test]
fn test_get_unsat_core_single_named_assertion() {
    let mut exec = Executor::new();
    exec.execute(&Command::SetOption(
        ":produce-unsat-cores".to_string(),
        SExpr::True,
    ))
    .unwrap();

    let cmds = parse(
        r#"
            (set-logic QF_UF)
            (declare-const a Bool)
            (assert (! a :named n1))
        "#,
    )
    .unwrap();
    exec.execute_all(&cmds).unwrap();

    exec.last_result = Some(SolveResult::Unsat);
    assert_eq!(exec.unsat_core(), "(n1)");
}

#[test]
fn test_get_unsat_assumptions_prefers_minimal_core_if_present() {
    let mut exec = Executor::new();
    let a = exec.ctx.terms.mk_var("a", Sort::Bool);
    let b = exec.ctx.terms.mk_var("b", Sort::Bool);

    exec.last_result = Some(SolveResult::Unsat);
    exec.last_assumptions = Some(vec![a, b]);
    exec.last_assumption_core = Some(vec![b]);

    assert_eq!(exec.unsat_assumptions(), "(b)");
}

#[test]
fn test_get_unsat_assumptions_errors_without_check_sat_assuming() {
    let mut exec = Executor::new();
    exec.last_result = Some(SolveResult::Unsat);
    exec.last_assumptions = None;
    assert_eq!(
        exec.unsat_assumptions(),
        "(error \"no check-sat-assuming has been performed\")"
    );
}
