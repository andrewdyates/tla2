// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::sexp::parse_sexp;

#[test]
fn test_parse_set_logic() {
    let sexp = parse_sexp("(set-logic QF_LIA)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::SetLogic("QF_LIA".to_string()));
}

#[test]
fn test_parse_declare_fun() {
    let sexp = parse_sexp("(declare-fun x () Int)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::DeclareFun("x".to_string(), vec![], Sort::Simple("Int".to_string()))
    );
}

#[test]
fn test_parse_maximize() {
    let sexp = parse_sexp("(maximize x)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::Maximize(Term::Symbol("x".to_string())));
}

#[test]
fn test_parse_get_objectives() {
    let sexp = parse_sexp("(get-objectives)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::GetObjectives);
}

#[test]
fn test_parse_declare_fun_with_args() {
    let sexp = parse_sexp("(declare-fun f (Int Int) Bool)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::DeclareFun(
            "f".to_string(),
            vec![
                Sort::Simple("Int".to_string()),
                Sort::Simple("Int".to_string())
            ],
            Sort::Simple("Bool".to_string())
        )
    );
}

#[test]
fn test_parse_declare_const() {
    let sexp = parse_sexp("(declare-const y Real)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(
        cmd,
        Command::DeclareConst("y".to_string(), Sort::Simple("Real".to_string()))
    );
}

#[test]
fn test_parse_assert() {
    let sexp = parse_sexp("(assert (> x 0))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::App(name, args)) => {
            assert_eq!(name, ">");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected Assert command"),
    }
}

#[test]
fn test_parse_check_sat() {
    let sexp = parse_sexp("(check-sat)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    assert_eq!(cmd, Command::CheckSat);
}

#[test]
fn test_parse_push_pop() {
    let push = parse_sexp("(push 2)").unwrap();
    assert_eq!(Command::from_sexp(&push).unwrap(), Command::Push(2));

    let pop = parse_sexp("(pop 1)").unwrap();
    assert_eq!(Command::from_sexp(&pop).unwrap(), Command::Pop(1));
}

#[test]
fn test_parse_bitvector_sort() {
    let sexp = parse_sexp("(declare-const bv (_ BitVec 32))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareConst(name, Sort::Indexed(sort_name, indices)) => {
            assert_eq!(name, "bv");
            assert_eq!(sort_name, "BitVec");
            assert_eq!(indices, &vec!["32".to_string()]);
        }
        _ => panic!("Expected DeclareConst with indexed sort"),
    }
}

#[test]
fn test_parse_array_sort() {
    let sexp = parse_sexp("(declare-const arr (Array Int Int))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareConst(name, Sort::Parameterized(sort_name, params)) => {
            assert_eq!(name, "arr");
            assert_eq!(sort_name, "Array");
            assert_eq!(params.len(), 2);
        }
        _ => panic!("Expected DeclareConst with parameterized sort"),
    }
}

#[test]
fn test_parse_let_term() {
    let sexp = parse_sexp("(assert (let ((x 1)) (+ x 2)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Let(bindings, _body)) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
        }
        _ => panic!("Expected Assert with Let term"),
    }
}

#[test]
fn test_parse_forall() {
    let sexp = parse_sexp("(assert (forall ((x Int)) (> x 0)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Forall(bindings, _body)) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
        }
        _ => panic!("Expected Assert with Forall term"),
    }
}

#[test]
fn test_parse_exists() {
    let sexp = parse_sexp("(assert (exists ((x Int)) (> x 0)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Exists(bindings, _body)) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
        }
        _ => panic!("Expected Assert with Exists term"),
    }
}

#[test]
fn test_parse_nested_quantifiers() {
    let sexp = parse_sexp("(assert (forall ((x Int)) (exists ((y Int)) (= (+ x y) 0))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Forall(bindings, body)) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
            assert!(matches!(body.as_ref(), Term::Exists(_, _)));
        }
        _ => panic!("Expected nested Forall/Exists"),
    }
}

#[test]
fn test_parse_forall_multiple_bindings() {
    let sexp = parse_sexp("(assert (forall ((x Int) (y Int)) (>= (+ x y) 0)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Assert(Term::Forall(bindings, _body)) => {
            assert_eq!(bindings.len(), 2);
            assert_eq!(bindings[0].0, "x");
            assert_eq!(bindings[1].0, "y");
        }
        _ => panic!("Expected Forall with multiple bindings"),
    }
}

#[test]
fn test_parse_define_fun_rec() {
    // Factorial function
    let sexp =
        parse_sexp("(define-fun-rec fact ((n Int)) Int (ite (= n 0) 1 (* n (fact (- n 1)))))");
    let cmd = Command::from_sexp(&sexp.unwrap()).unwrap();
    match &cmd {
        Command::DefineFunRec(name, params, ret_sort, _body) => {
            assert_eq!(name, "fact");
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].0, "n");
            assert_eq!(ret_sort, &Sort::Simple("Int".to_string()));
        }
        _ => panic!("Expected DefineFunRec command"),
    }
}

#[test]
fn test_parse_define_fun_rec_multiple_params() {
    let sexp =
        parse_sexp("(define-fun-rec gcd ((a Int) (b Int)) Int (ite (= b 0) a (gcd b (mod a b))))");
    let cmd = Command::from_sexp(&sexp.unwrap()).unwrap();
    match &cmd {
        Command::DefineFunRec(name, params, ret_sort, _body) => {
            assert_eq!(name, "gcd");
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].0, "a");
            assert_eq!(params[1].0, "b");
            assert_eq!(ret_sort, &Sort::Simple("Int".to_string()));
        }
        _ => panic!("Expected DefineFunRec command"),
    }
}

#[test]
fn test_parse_define_funs_rec() {
    // Mutually recursive even/odd functions
    let sexp = parse_sexp(
        "(define-funs-rec ((even ((n Int)) Bool) (odd ((n Int)) Bool)) \
         ((ite (= n 0) true (odd (- n 1))) (ite (= n 0) false (even (- n 1)))))",
    );
    let cmd = Command::from_sexp(&sexp.unwrap()).unwrap();
    match &cmd {
        Command::DefineFunsRec(declarations, bodies) => {
            assert_eq!(declarations.len(), 2);
            assert_eq!(bodies.len(), 2);

            // Check first declaration (even)
            assert_eq!(declarations[0].0, "even");
            assert_eq!(declarations[0].1.len(), 1);
            assert_eq!(declarations[0].1[0].0, "n");
            assert_eq!(declarations[0].2, Sort::Simple("Bool".to_string()));

            // Check second declaration (odd)
            assert_eq!(declarations[1].0, "odd");
            assert_eq!(declarations[1].1.len(), 1);
            assert_eq!(declarations[1].1[0].0, "n");
            assert_eq!(declarations[1].2, Sort::Simple("Bool".to_string()));
        }
        _ => panic!("Expected DefineFunsRec command"),
    }
}

#[test]
fn test_parse_define_funs_rec_mismatch_error() {
    // Mismatched number of declarations and bodies
    let sexp = parse_sexp("(define-funs-rec ((f ((x Int)) Int)) (body1 body2))");
    let result = Command::from_sexp(&sexp.unwrap());
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("number of declarations must match"));
}

#[test]
fn test_parse_declare_datatype_simple() {
    // Simple enumeration type
    let sexp = parse_sexp("(declare-datatype Color ((Red) (Green) (Blue)))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatype(name, datatype_dec) => {
            assert_eq!(name, "Color");
            assert_eq!(datatype_dec.constructors.len(), 3);
            assert_eq!(datatype_dec.constructors[0].name, "Red");
            assert_eq!(datatype_dec.constructors[0].selectors.len(), 0);
            assert_eq!(datatype_dec.constructors[1].name, "Green");
            assert_eq!(datatype_dec.constructors[2].name, "Blue");
        }
        _ => panic!("Expected DeclareDatatype command"),
    }
}

#[test]
fn test_parse_declare_datatype_with_selectors() {
    // Record type with selectors
    let sexp = parse_sexp("(declare-datatype Point ((mk-point (x Int) (y Int))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatype(name, datatype_dec) => {
            assert_eq!(name, "Point");
            assert_eq!(datatype_dec.constructors.len(), 1);
            assert_eq!(datatype_dec.constructors[0].name, "mk-point");
            assert_eq!(datatype_dec.constructors[0].selectors.len(), 2);
            assert_eq!(datatype_dec.constructors[0].selectors[0].name, "x");
            assert_eq!(
                datatype_dec.constructors[0].selectors[0].sort,
                Sort::Simple("Int".to_string())
            );
            assert_eq!(datatype_dec.constructors[0].selectors[1].name, "y");
        }
        _ => panic!("Expected DeclareDatatype command"),
    }
}

#[test]
fn test_parse_declare_datatype_multiple_constructors() {
    // Option-like type
    let sexp = parse_sexp("(declare-datatype Option ((None) (Some (value Int))))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatype(name, datatype_dec) => {
            assert_eq!(name, "Option");
            assert_eq!(datatype_dec.constructors.len(), 2);
            assert_eq!(datatype_dec.constructors[0].name, "None");
            assert_eq!(datatype_dec.constructors[0].selectors.len(), 0);
            assert_eq!(datatype_dec.constructors[1].name, "Some");
            assert_eq!(datatype_dec.constructors[1].selectors.len(), 1);
            assert_eq!(datatype_dec.constructors[1].selectors[0].name, "value");
        }
        _ => panic!("Expected DeclareDatatype command"),
    }
}

#[test]
fn test_parse_declare_datatypes() {
    // Multiple datatypes (potentially mutually recursive)
    let sexp = parse_sexp(
        "(declare-datatypes ((Tree 0) (Forest 0)) \
         (((leaf (val Int)) (node (children Forest))) ((nil) (cons (head Tree) (tail Forest)))))",
    )
    .unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::DeclareDatatypes(sort_decs, datatype_decs) => {
            assert_eq!(sort_decs.len(), 2);
            assert_eq!(datatype_decs.len(), 2);

            // Check sort declarations
            assert_eq!(sort_decs[0].name, "Tree");
            assert_eq!(sort_decs[0].arity, 0);
            assert_eq!(sort_decs[1].name, "Forest");
            assert_eq!(sort_decs[1].arity, 0);

            // Check Tree constructors
            assert_eq!(datatype_decs[0].constructors.len(), 2);
            assert_eq!(datatype_decs[0].constructors[0].name, "leaf");
            assert_eq!(datatype_decs[0].constructors[1].name, "node");

            // Check Forest constructors
            assert_eq!(datatype_decs[1].constructors.len(), 2);
            assert_eq!(datatype_decs[1].constructors[0].name, "nil");
            assert_eq!(datatype_decs[1].constructors[1].name, "cons");
        }
        _ => panic!("Expected DeclareDatatypes command"),
    }
}

#[test]
fn test_parse_declare_datatypes_mismatch_error() {
    // Mismatched number of sort declarations and datatype declarations
    let sexp = parse_sexp("(declare-datatypes ((T 0)) (((a)) ((b))))");
    let result = Command::from_sexp(&sexp.unwrap());
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("number of sort declarations must match"));
}

#[test]
fn test_parse_simplify_basic() {
    let sexp = parse_sexp("(simplify (and true x))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Simplify(Term::App(name, args)) => {
            assert_eq!(name, "and");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected Simplify command"),
    }
}

#[test]
fn test_parse_simplify_constant() {
    let sexp = parse_sexp("(simplify true)").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Simplify(Term::Const(Constant::True)) => {}
        _ => panic!("Expected Simplify command with true constant"),
    }
}

#[test]
fn test_parse_simplify_arithmetic() {
    let sexp = parse_sexp("(simplify (+ 1 2))").unwrap();
    let cmd = Command::from_sexp(&sexp).unwrap();
    match &cmd {
        Command::Simplify(Term::App(name, args)) => {
            assert_eq!(name, "+");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected Simplify command"),
    }
}

// === Deep-nesting stress tests for Term::Drop (#3697) ===
//
// Term::Drop uses iterative drain to avoid stack overflow.
// These tests construct deeply nested Term trees and drop them,
// verifying that the iterative Drop doesn't crash or overflow.

/// Build a deeply nested App chain: (not (not (not ... (not true) ...)))
fn build_deep_app_chain(depth: usize) -> Term {
    let mut term = Term::Const(Constant::True);
    for _ in 0..depth {
        term = Term::App("not".to_string(), vec![term]);
    }
    term
}

#[test]
fn test_term_deep_app_drop_10000() {
    // 10,000-deep App nesting — would overflow with recursive Drop
    let term = build_deep_app_chain(10_000);
    drop(term); // must not stack overflow
}

#[test]
fn test_term_deep_app_drop_100000() {
    // 100,000-deep App nesting — stress test for iterative Drop
    let term = build_deep_app_chain(100_000);
    drop(term);
}

#[test]
fn test_term_deep_let_drop_10000() {
    // 10,000-deep Let nesting: (let ((x true)) (let ((x true)) ...))
    let mut term = Term::Const(Constant::True);
    for i in 0..10_000 {
        let binding = (format!("x{i}"), Term::Const(Constant::False));
        term = Term::Let(vec![binding], Box::new(term));
    }
    drop(term);
}

#[test]
fn test_term_deep_forall_exists_drop_10000() {
    // 5,000 alternating Forall/Exists nesting
    let mut term = Term::Const(Constant::True);
    for i in 0..5_000 {
        let var = (format!("x{i}"), Sort::Simple("Int".to_string()));
        if i % 2 == 0 {
            term = Term::Forall(vec![var], Box::new(term));
        } else {
            term = Term::Exists(vec![var], Box::new(term));
        }
    }
    drop(term);
}

#[test]
fn test_term_deep_annotated_drop_10000() {
    // 10,000-deep Annotated nesting: (! (! (! ... true :named a) :named b) ...)
    let mut term = Term::Const(Constant::True);
    for i in 0..10_000 {
        let attr = (format!("named{i}"), SExpr::Symbol("a".to_string()));
        term = Term::Annotated(Box::new(term), vec![attr]);
    }
    drop(term);
}

#[test]
fn test_term_deep_mixed_nesting_drop() {
    // Mixed nesting: App → Let → Forall → Annotated → App → ...
    let mut term = Term::Const(Constant::True);
    for i in 0..2_500 {
        match i % 4 {
            0 => {
                term = Term::App("f".to_string(), vec![term]);
            }
            1 => {
                let binding = (format!("v{i}"), Term::Const(Constant::False));
                term = Term::Let(vec![binding], Box::new(term));
            }
            2 => {
                let var = (format!("x{i}"), Sort::Simple("Bool".to_string()));
                term = Term::Forall(vec![var], Box::new(term));
            }
            _ => {
                let attr = ("named".to_string(), SExpr::Symbol("a".to_string()));
                term = Term::Annotated(Box::new(term), vec![attr]);
            }
        }
    }
    drop(term); // 10,000 total nesting depth
}

#[test]
fn test_term_deep_app_small_stack() {
    // Run on a restricted 128KB stack to verify iterative Drop works
    // even when the default thread stack is unavailable.
    let result = std::thread::Builder::new()
        .stack_size(128 * 1024) // 128KB — far too small for 10K recursive drops
        .spawn(|| {
            let term = build_deep_app_chain(10_000);
            drop(term);
        })
        .unwrap()
        .join();
    assert!(
        result.is_ok(),
        "iterative Drop must not overflow on 128KB stack"
    );
}
