// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::clear_for_test_reset;
use tla_core::ast::{Expr, Substitution};
use tla_core::name_intern::intern_name;
use tla_core::{Span, Spanned};

fn state_var_apply_expr(name: &str, idx: u16, arg: i64) -> Spanned<Expr> {
    let state_var = Spanned::dummy(Expr::StateVar(name.to_string(), idx, intern_name(name)));
    let arg_expr = Spanned::dummy(Expr::Int(arg.into()));
    Spanned::dummy(Expr::FuncApply(Box::new(state_var), Box::new(arg_expr)))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_func_def() {
    // Domain {1, 2} is exactly 1..2, so this becomes a Seq in TLA+ semantics
    let f = eval_str(r"[x \in {1, 2} |-> x * 10]").unwrap();
    // Since domain is {1, 2} = 1..2, this is now a sequence
    let seq = f
        .as_seq()
        .expect("Function with domain 1..n should be a Seq");
    assert_eq!(seq.len(), 2);
    assert_eq!(seq[0], Value::int(10)); // seq[1] in TLA+ = seq[0] in Rust
    assert_eq!(seq[1], Value::int(20)); // seq[2] in TLA+ = seq[1] in Rust

    // Test with non-sequence domain (e.g., {0, 1} - doesn't start at 1)
    let f = eval_str(r"[x \in {0, 1} |-> x * 10]").unwrap();
    let func = f
        .as_func()
        .expect("Function with domain not starting at 1 should be Func");
    assert_eq!(func.apply(&Value::int(0)), Some(&Value::int(0)));
    assert_eq!(func.apply(&Value::int(1)), Some(&Value::int(10)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_multi_variable_func_def_uses_tuple_domain_keys() {
    let f = eval_str(r"[x \in {0, 1}, y \in {2, 3} |-> x * 10 + y]")
        .expect("multi-variable function definition should evaluate");
    let func = f
        .as_func()
        .expect("multi-variable finite-domain function should be a Func");

    assert_eq!(
        func.apply(&Value::tuple([Value::int(0), Value::int(2)])),
        Some(&Value::int(2))
    );
    assert_eq!(
        func.apply(&Value::tuple([Value::int(1), Value::int(3)])),
        Some(&Value::int(13))
    );
    assert_eq!(func.apply(&Value::int(0)), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_except_at_reference() {
    // EXCEPT RHS can reference `@` (old value). This is essential for patterns like:
    //   [f EXCEPT ![i] = @ \\cup {x}]
    // Since domain 1..1 = {1}, which is 1..n, the result is a Seq
    let f = eval_str(r"[ [i \in 1..1 |-> {2}] EXCEPT ![1] = @ \cup {1} ]").unwrap();
    let set = match &f {
        Value::Seq(s) => s[0].as_set().expect("Element should be a set"),
        Value::IntFunc(func) => func.apply(&Value::int(1)).unwrap().as_set().unwrap(),
        Value::Func(func) => func.apply(&Value::int(1)).unwrap().as_set().unwrap(),
        _ => panic!("Expected sequence or function value, got {f:?}"),
    };
    assert_eq!(set.len(), 2);
    assert!(set.contains(&Value::int(1)));
    assert!(set.contains(&Value::int(2)));

    // And for set difference:
    let f = eval_str(r"[ [i \in 1..1 |-> {1, 2}] EXCEPT ![1] = @ \ {1} ]").unwrap();
    let set = match &f {
        Value::Seq(s) => s[0].as_set().expect("Element should be a set"),
        Value::IntFunc(func) => func.apply(&Value::int(1)).unwrap().as_set().unwrap(),
        Value::Func(func) => func.apply(&Value::int(1)).unwrap().as_set().unwrap(),
        _ => panic!("Expected sequence or function value, got {f:?}"),
    };
    assert_eq!(set.len(), 1);
    assert!(set.contains(&Value::int(2)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_except_ignores_out_of_domain_function_update() {
    // Domain {1} = 1..1 is now a sequence with the new semantics
    // EXCEPT ![2] = 3 on a seq of length 1 should be a no-op (index out of bounds)
    let f = eval_str(r"[ [i \in {1} |-> 0] EXCEPT ![2] = 3 ]").unwrap();
    let seq = f.as_seq().expect("Function with domain 1..n should be Seq");
    assert_eq!(seq.len(), 1);
    assert_eq!(seq[0], Value::int(0)); // Unchanged

    // Accessing index 2 on a seq of length 1 should error (IndexOutOfBounds
    // per TLC TupleValue.java:144 — our Seq representation matches TupleValue).
    let err = eval_str(r"([ [i \in {1} |-> 0] EXCEPT ![2] = 3 ])[2]").unwrap_err();
    assert!(matches!(err, EvalError::IndexOutOfBounds { .. }));

    // Test with non-1..n domain (e.g., {0}) which remains a Func
    let f = eval_str(r"[ [i \in {0} |-> 0] EXCEPT ![1] = 3 ]").unwrap();
    let func = f
        .as_func()
        .expect("Function with domain not starting at 1 should be Func");
    assert!(func.domain_contains(&Value::int(0)));
    assert!(!func.domain_contains(&Value::int(1)));
    assert_eq!(func.apply(&Value::int(0)), Some(&Value::int(0)));
    assert_eq!(func.apply(&Value::int(1)), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_except_ignores_missing_record_field_update() {
    let r = eval_str(r"[ [a |-> 1] EXCEPT !.b = 2 ]").unwrap();
    let rec = r.as_record().unwrap();
    assert_eq!(rec.len(), 1);
    assert_eq!(rec.get(&Arc::from("a")), Some(&Value::int(1)));
    assert_eq!(rec.get(&Arc::from("b")), None);

    let err = eval_str(r#"([ [a |-> 1] EXCEPT !.b = 2 ])["b"]"#).unwrap_err();
    assert!(matches!(err, EvalError::NoSuchField { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_except_updates_existing_record_field() {
    let r = eval_str(r"[ [a |-> 1] EXCEPT !.a = 2 ]").unwrap();
    let rec = r.as_record().unwrap();
    assert_eq!(rec.len(), 1);
    assert_eq!(rec.get(&Arc::from("a")), Some(&Value::int(2)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_except_updates_existing_record_string_key() {
    let r = eval_str(r#"[ [a |-> 1] EXCEPT !["a"] = 2 ]"#).unwrap();
    let rec = r.as_record().unwrap();
    assert_eq!(rec.len(), 1);
    assert_eq!(rec.get(&Arc::from("a")), Some(&Value::int(2)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_except_ignores_missing_record_string_key_update() {
    let r = eval_str(r#"[ [a |-> 1] EXCEPT !["b"] = 2 ]"#).unwrap();
    let rec = r.as_record().unwrap();
    assert_eq!(rec.len(), 1);
    assert_eq!(rec.get(&Arc::from("a")), Some(&Value::int(1)));
    assert_eq!(rec.get(&Arc::from("b")), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_except_intfunc_field_access_returns_internal_error() {
    let err = eval_str(r"[ [i \in 2..3 |-> i] EXCEPT !.bad = 0 ]")
        .expect_err("field EXCEPT on IntFunc should reject field access");
    assert!(
        matches!(
            err,
            EvalError::Internal { ref message, .. }
                if message == "Field access on function not supported"
        ),
        "expected IntFunc field EXCEPT to preserve the function-field error, got: {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_func_override_accepts_records_and_sequences() {
    // Records: preserve record value so r.field works.
    let v = eval_str(r#"([dst |-> "a"] @@ [data |-> 15])"#).unwrap();
    assert!(matches!(v, Value::Record(_)));
    let rec = v.as_record().unwrap();
    assert_eq!(rec.get(&Arc::from("data")), Some(&Value::int(15)));
    assert_eq!(rec.get(&Arc::from("dst")), Some(&Value::string("a")));
    assert_eq!(
        eval_str(r#"([dst |-> "a"] @@ [data |-> 15]).data"#).unwrap(),
        Value::int(15)
    );

    // Sequences: @@ should accept tuples/seqs and singleton functions.
    assert_eq!(
        eval_str(r#"(1 :> "a" @@ <<>>)"#).unwrap(),
        Value::seq([Value::string("a")])
    );
    assert_eq!(
        eval_str(r#"(2 :> "x" @@ <<"a", "b", "c">>)"#).unwrap(),
        Value::seq([Value::string("a"), Value::string("x"), Value::string("c")])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_func_apply_fast_path_preserves_not_in_domain() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("f");
    let state = vec![eval_str(r"[i \in {0} |-> i * 10]").expect("function state value")];
    ctx.bind_state_array(&state);

    let expr = state_var_apply_expr("f", 0, 1);
    let err = eval(&ctx, &expr).expect_err("f[2] should be out of domain");
    assert!(matches!(err, EvalError::NotInDomain { .. }));

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_access_func_apply_fast_path_preserves_errors() {
    let err = eval_str(r"([f |-> [i \in {0} |-> i * 10]].f)[1]")
        .expect_err("record field function apply should preserve NotInDomain");
    assert!(matches!(err, EvalError::NotInDomain { .. }));

    let err = eval_str(r"([f |-> [i \in {0} |-> i * 10]].missing)[1]")
        .expect_err("missing record field should preserve NoSuchField");
    assert!(matches!(err, EvalError::NoSuchField { .. }));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_func_apply_respects_call_by_name_fallback() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![
        eval_str(r"[i \in {1} |-> 10]").expect("x function"),
        eval_str(r"[i \in {1} |-> 99]").expect("y function"),
    ];
    ctx.bind_state_array(&state);

    let ctx_with_cbn = ctx.with_call_by_name_subs(vec![Substitution {
        from: Spanned::new("x".to_string(), Span::dummy()),
        to: Spanned::new(
            Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
            Span::dummy(),
        ),
    }]);

    let expr = state_var_apply_expr("x", 0, 1);
    let value = eval(&ctx_with_cbn, &expr).expect("call-by-name fallback should evaluate");
    assert_eq!(value, Value::int(99));

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_func_apply_respects_instance_substitution_fallback() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![
        eval_str(r"[i \in {1} |-> 10]").expect("x function"),
        eval_str(r"[i \in {1} |-> 99]").expect("y function"),
    ];
    ctx.bind_state_array(&state);

    let ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::new("x".to_string(), Span::dummy()),
        to: Spanned::new(
            Expr::Ident("y".to_string(), tla_core::name_intern::NameId::INVALID),
            Span::dummy(),
        ),
    }]);

    let expr = state_var_apply_expr("x", 0, 1);
    let value = eval(&ctx_with_subs, &expr).expect("INSTANCE fallback should evaluate");
    assert_eq!(value, Value::int(99));

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_range_operator() {
    // Range(f) - set of all values in function (image of codomain)
    assert_eq!(
        eval_str(r"Range([x \in {1,2,3} |-> x * 2])").unwrap(),
        Value::set(vec![Value::int(2), Value::int(4), Value::int(6)])
    );

    // Duplicates are collapsed since it's a set
    // Note: [x \in S |-> c] where c is constant is parsed differently,
    // using a record-like constant function syntax. Use x+0 to ensure variable reference.
    assert_eq!(
        eval_str(r"Range([x \in {1,2,3} |-> 1 + 0])").unwrap(),
        Value::set(vec![Value::int(1)])
    );

    // Empty function
    assert_eq!(
        eval_str(r"Range([x \in {} |-> x + 0])").unwrap(),
        Value::empty_set()
    );
}
