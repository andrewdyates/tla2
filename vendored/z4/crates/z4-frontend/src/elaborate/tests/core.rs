// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_simple() {
    let input = r#"
            (declare-const x Int)
            (declare-const y Int)
            (assert (= x y))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_forall_preserves_termdata_and_binds_var() {
    let input = r#"
            (assert (forall ((x Int)) (> x 0)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, body) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    let binder_name = vars[0].0.clone();

    let mut names_in_body = Vec::new();
    collect_var_names(&ctx.terms, body, &mut names_in_body);
    assert!(
        names_in_body.contains(&binder_name),
        "Binder {binder_name} not found in body vars: {names_in_body:?}"
    );
}

#[test]
fn test_elaborate_exists_preserves_termdata_and_binds_var() {
    let input = r#"
            (assert (exists ((x Int)) (> x 0)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, body) = match ctx.terms.get(assertion) {
        TermData::Exists(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Exists, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    let binder_name = vars[0].0.clone();

    let mut names_in_body = Vec::new();
    collect_var_names(&ctx.terms, body, &mut names_in_body);
    assert!(
        names_in_body.contains(&binder_name),
        "Binder {binder_name} not found in body vars: {names_in_body:?}"
    );
}

#[test]
fn test_elaborate_nested_quantifiers_preserves_structure() {
    let input = r#"
            (assert (forall ((x Int)) (exists ((y Int)) (= (+ x y) 0))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (outer_vars, outer_body) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };
    assert_eq!(outer_vars.len(), 1);

    match ctx.terms.get(outer_body) {
        TermData::Exists(inner_vars, _, _) => assert_eq!(inner_vars.len(), 1),
        other => panic!("Expected nested TermData::Exists, got {other:?}"),
    }
}

#[test]
fn test_elaborate_forall_with_user_triggers_from_pattern_annotation() {
    let input = r#"
            (declare-fun P (Int) Bool)
            (declare-fun Q (Int) Bool)
            (assert (forall ((x Int))
              (! (=> (P x) (Q x))
                 :pattern ((P x)) )))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, triggers) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, _body, triggers) => (vars, triggers),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1);

    let trigger_term = triggers[0][0];
    let TermData::App(Symbol::Named(sym), args) = ctx.terms.get(trigger_term) else {
        panic!(
            "Expected trigger term to be App, got {:?}",
            ctx.terms.get(trigger_term)
        );
    };
    assert_eq!(sym, "P");
    assert_eq!(args.len(), 1);

    let TermData::Var(var_name, _) = ctx.terms.get(args[0]) else {
        panic!(
            "Expected trigger arg to be bound Var, got {:?}",
            ctx.terms.get(args[0])
        );
    };
    assert_eq!(var_name, &vars[0].0);
}

#[test]
fn test_elaborate_bool_ops() {
    let input = r#"
            (declare-const a Bool)
            (declare-const b Bool)
            (assert (and a b))
            (assert (or a (not b)))
            (assert (=> a b))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 3);
}

#[test]
fn test_elaborate_let() {
    let input = r#"
            (declare-const x Int)
            (assert (let ((y x)) (= y x)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // let (y = x) in (= y x) should simplify to (= x x) = true
    assert_eq!(ctx.assertions.len(), 1);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn test_elaborate_define_fun() {
    let input = r#"
            (define-fun double ((x Int)) Int (+ x x))
            (declare-const a Int)
            (assert (= (double a) (+ a a)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_define_fun_nullary() {
    let input = r#"
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (define-fun my_eq () Bool (= a b))
            (assert my_eq)
            (assert (not (= a b)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn test_push_pop() {
    let input = r#"
            (declare-const x Int)
            (push 1)
            (declare-const y Int)
            (assert (= x y))
            (pop 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 0);
    assert!(ctx.symbols.contains_key("x"));
    assert!(!ctx.symbols.contains_key("y"));
}

#[test]
fn test_redeclare_after_pop_gets_fresh_term_id_6813() {
    let input = r#"
            (push 1)
            (declare-const x Int)
            (pop 1)
            (push 1)
            (declare-const x Int)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut first_x = None;

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
        if first_x.is_none() {
            first_x = ctx.symbols.get("x").and_then(|info| info.term);
        }
    }

    let second_x = ctx
        .symbols
        .get("x")
        .and_then(|info| info.term)
        .expect("x should be declared in the second scope");
    let first_x = first_x.expect("x should be declared in the first scope");

    assert_ne!(
        first_x, second_x,
        "redeclaring x after pop must allocate a fresh internal term id"
    );
}

#[test]
fn test_reserved_symbol_const_rejected() {
    let input = r#"
            (declare-const __z4_internal Int)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, ElaborateError::ReservedSymbol(_)),
        "Expected ReservedSymbol error, got: {err:?}"
    );
}

#[test]
fn test_reserved_symbol_fun_rejected() {
    let input = r#"
            (declare-fun __z4_myfunc (Int) Bool)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_define_fun_rejected() {
    let input = r#"
            (define-fun __z4_helper ((x Int)) Int (+ x 1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_datatype_rejected() {
    let input = r#"
            (declare-datatype __z4_MyDT ((ctor)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_constructor_rejected() {
    let input = r#"
            (declare-datatype MyDT ((__z4_badctor)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_selector_rejected() {
    let input = r#"
            (declare-datatype MyDT ((ctor (__z4_badsel Int))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_normal_symbol_accepted() {
    // Symbols not starting with __z4_ should be accepted
    let input = r#"
            (declare-const _z4_almost Int)
            (declare-fun normal_func (Int) Bool)
            (declare-datatype MyList ((nil) (cons (head Int) (tail MyList))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // All should succeed
    assert!(ctx.symbols.contains_key("_z4_almost"));
    assert!(ctx.symbols.contains_key("normal_func"));
    assert!(ctx.symbols.contains_key("nil"));
    assert!(ctx.symbols.contains_key("cons"));
}

#[test]
fn test_is_reserved_symbol() {
    assert!(is_reserved_symbol("__z4_test"));
    assert!(is_reserved_symbol("__z4_dt_depth_List"));
    assert!(is_reserved_symbol("__z4_"));
    assert!(!is_reserved_symbol("_z4_test"));
    assert!(!is_reserved_symbol("__z3_test"));
    assert!(!is_reserved_symbol("normal"));
}

/// Regression test for #2992: undeclared functions in application position
/// must produce an error, not silently create an App with default Sort::Bool.
#[test]
fn test_undeclared_function_application_rejected() {
    let input = r#"
            (declare-const s Int)
            (assert (= (__field_value s) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                matches!(e, ElaborateError::UndefinedSymbol(ref name) if name == "__field_value"),
                "Expected UndefinedSymbol for __field_value, got: {e:?}"
            );
            found_error = true;
        }
    }
    assert!(
        found_error,
        "Expected UndefinedSymbol error for undeclared function application"
    );
}

/// Declared functions in application position should still work.
#[test]
fn test_declared_function_application_accepted() {
    let input = r#"
            (declare-fun __field_value (Int) Int)
            (declare-const s Int)
            (assert (= (__field_value s) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

/// Unknown indexed identifiers must also be rejected, not silently accepted.
#[test]
fn test_unknown_indexed_identifier_rejected() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ unknown_bv_op 4) x) x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                format!("{e:?}").contains("unknown indexed identifier"),
                "Expected 'unknown indexed identifier' error, got: {e:?}"
            );
            found_error = true;
        }
    }
    assert!(found_error, "Expected error for unknown indexed identifier");
}
