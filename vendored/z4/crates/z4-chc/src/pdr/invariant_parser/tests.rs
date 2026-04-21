// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::ChcOp;
#[test]
fn parse_define_fun_basic_model_entry() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"
; comment
(define-fun inv ((x Int)) Bool
  (and (>= x 0) (<= x 10)))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).expect("missing inv interpretation");

    assert_eq!(interp.vars, vec![ChcVar::new("x", ChcSort::Int)]);
    assert_eq!(
        interp.formula,
        ChcExpr::and(
            ChcExpr::ge(
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                ChcExpr::int(0)
            ),
            ChcExpr::le(
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                ChcExpr::int(10)
            ),
        )
    );
}

#[test]
fn parse_spacer_wrapper_multiple_definitions() {
    let mut problem = ChcProblem::new();
    let inv0 = problem.declare_predicate("inv0", vec![ChcSort::Int]);
    let inv1 = problem.declare_predicate("inv1", vec![ChcSort::Int]);

    let input = r#"
(
  (define-fun inv0 ((x Int)) Bool (>= x 0))
  (define-fun inv1 ((y Int)) Bool (<= y 10))
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    assert_eq!(
        model.len(),
        2,
        "model should contain exactly 2 predicate interpretations"
    );

    let interp0 = model.get(&inv0).expect("model must contain inv0");
    assert_eq!(interp0.vars, vec![ChcVar::new("x", ChcSort::Int)]);
    assert_eq!(
        interp0.formula,
        ChcExpr::ge(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(0)
        )
    );

    let interp1 = model.get(&inv1).expect("model must contain inv1");
    assert_eq!(interp1.vars, vec![ChcVar::new("y", ChcSort::Int)]);
    assert_eq!(
        interp1.formula,
        ChcExpr::le(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::int(10)
        )
    );
}

#[test]
fn parse_quoted_predicate_and_var_names() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("my inv", vec![ChcSort::Int]);

    let input = r#"(define-fun |my inv| ((|my var| Int)) Bool (>= |my var| 0))"#;
    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    assert_eq!(interp.vars, vec![ChcVar::new("my var", ChcSort::Int)]);
}

#[test]
fn parse_define_fun_skips_unknown_predicates() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"
(define-fun unknown ((x Int)) Bool true)
(define-fun inv ((x Int)) Bool true)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    assert_eq!(model.len(), 1, "only known predicates should be in model");
    let interp = model.get(&inv).expect("model must contain inv");
    assert_eq!(
        interp.formula,
        ChcExpr::Bool(true),
        "inv body should be true"
    );
}

#[test]
fn parse_define_fun_param_count_mismatch_errors() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    let input = r#"(define-fun inv ((x Int)) Bool true)"#;
    let err = InvariantModel::parse_smtlib(input, &problem).unwrap_err();
    assert!(matches!(err, ChcError::Parse(_)));
}

#[test]
fn parse_define_fun_return_type_must_be_bool() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"(define-fun inv ((x Int)) Int 0)"#;
    let err = InvariantModel::parse_smtlib(input, &problem).unwrap_err();
    assert!(matches!(err, ChcError::Parse(_)));
}

#[test]
fn parse_array_sorts_select_store_and_const_arrays() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate(
        "inv",
        vec![
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
            ChcSort::Int,
        ],
    );

    let input = r#"
(define-fun inv ((arr (Array Int Int)) (i Int)) Bool
  (and
(= (select arr i) 0)
(= (store arr i 1) ((as const (Array Int Int)) 0))
  )
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    assert_eq!(interp.vars.len(), 2);
    assert_eq!(
        interp.vars[0].sort,
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
    );
    assert_eq!(interp.vars[1].sort, ChcSort::Int);
}

#[test]
fn parse_nary_distinct_and_chained_comparisons() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    let input = r#"
(define-fun inv ((a Int) (b Int) (c Int)) Bool
  (and
(distinct a b c)
(< a b c)
  )
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model
        .get(&inv)
        .expect("model must contain parsed interpretation for inv");

    assert_eq!(
        interp.vars,
        vec![
            ChcVar::new("a", ChcSort::Int),
            ChcVar::new("b", ChcSort::Int),
            ChcVar::new("c", ChcSort::Int),
        ]
    );

    let atoms = match &interp.formula {
        ChcExpr::Op(ChcOp::And, args) => args.iter().map(|arg| arg.as_ref().clone()).collect(),
        other => vec![other.clone()],
    };

    // distinct(a,b,c) expands to 3 pairwise != constraints.
    // (< a b c) expands to 2 chained < constraints.
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Int));
    let expected_atoms = vec![
        ChcExpr::ne(a.clone(), b.clone()),
        ChcExpr::ne(a.clone(), c.clone()),
        ChcExpr::ne(b.clone(), c.clone()),
        ChcExpr::lt(a, b.clone()),
        ChcExpr::lt(b, c),
    ];
    assert_eq!(
        atoms.len(),
        expected_atoms.len(),
        "expected exactly 5 conjunctive atoms after n-ary expansion"
    );
    for expected in expected_atoms {
        assert!(
            atoms.iter().any(|actual| actual == &expected),
            "missing expanded atom: {expected:?}"
        );
    }
}

#[test]
fn parse_real_division_accepts_explicit_unary_negation() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"
(define-fun inv ((x Int)) Bool
  (= (/ (- 3) 4) (/ -3 4))
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    // Both sides should parse as the same Real(-3,4) after normalization.
    match &interp.formula {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            assert_eq!(args[0].as_ref(), args[1].as_ref());
            assert!(matches!(args[0].as_ref(), ChcExpr::Real(-3, 4)));
        }
        other => panic!("expected equality, got {other:?}"),
    }
}

#[test]
fn parse_let_expressions_substitutes_bindings() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    // Golem-style let bindings
    let input = r#"
(define-fun inv ((x Int) (y Int)) Bool
  (let ((sum (+ x y)))
(let ((bound (<= sum 10)))
  bound)))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    // After substitution: (<= (+ x y) 10)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expected = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
        ChcExpr::int(10),
    );
    assert_eq!(interp.formula, expected);
}

#[test]
fn parse_nested_let_with_multiple_bindings() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"
(define-fun inv ((x Int)) Bool
  (let ((a (+ x 1)) (b (+ x 2)))
(and (>= a 0) (>= b 0))))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    // After substitution: (and (>= (+ x 1) 0) (>= (+ x 2) 0))
    let x = ChcVar::new("x", ChcSort::Int);
    let expected = ChcExpr::and(
        ChcExpr::ge(
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ChcExpr::int(0),
        ),
        ChcExpr::ge(
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
            ChcExpr::int(0),
        ),
    );
    assert_eq!(interp.formula, expected);
}

#[test]
fn parse_unbalanced_parens_errors() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("inv", vec![ChcSort::Int]);

    // Missing closing paren
    let input = r#"(define-fun inv ((x Int)) Bool (>= x 0)"#;
    let err = InvariantModel::parse_smtlib(input, &problem).unwrap_err();
    assert!(matches!(err, ChcError::Parse(_)));
}

#[test]
fn parse_nested_ite() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    // Nested ITE: (ite (>= x 5) 1 (ite (>= x 0) 0 (- 1)))
    // Represents: if x >= 5 then 1 elif x >= 0 then 0 else -1
    let input = r#"
(define-fun inv ((x Int)) Bool
  (>= (ite (>= x 5) 1 (ite (>= x 0) 0 (- 1))) 0))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).expect("model must contain inv");

    assert_eq!(interp.vars, vec![ChcVar::new("x", ChcSort::Int)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let inner_ite = ChcExpr::ite(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::int(0),
        ChcExpr::neg(ChcExpr::int(1)),
    );
    let outer_ite = ChcExpr::ite(
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5)),
        ChcExpr::int(1),
        inner_ite,
    );
    let expected = ChcExpr::ge(outer_ite, ChcExpr::int(0));
    assert_eq!(
        interp.formula, expected,
        "nested ITE structure must be preserved"
    );
}

#[test]
fn parse_implies_binary_operator() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"(define-fun inv ((x Int)) Bool (=> (>= x 0) (<= x 10)))"#;
    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    let x = ChcVar::new("x", ChcSort::Int);
    let expected = ChcExpr::implies(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10)),
    );
    assert_eq!(interp.formula, expected);
}
