// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_string_builtins() {
    let input = r#"
            (declare-const x String)
            (declare-const y String)
            (declare-const i Int)
            (assert (= (str.++ x y) x))
            (assert (= (str.len x) i))
            (assert (= (str.at x i) y))
            (assert (= (str.substr x i i) y))
            (assert (str.contains x y))
            (assert (str.prefixof x y))
            (assert (str.suffixof x y))
            (assert (= (str.indexof x y i) i))
            (assert (= (str.replace x y x) x))
            (assert (= (str.replace_all x y x) x))
            (assert (= (str.to_int x) i))
            (assert (= (str.to.int x) i))
            (assert (= (str.from_int i) x))
            (assert (= (int.to.str i) x))
            (assert (str.< x y))
            (assert (str.<= x y))
            (assert (str.is_digit x))
            (assert (= (str.to_code x) i))
            (assert (= (str.from_code i) x))
            (assert (= (str.replace_re x (str.to_re "a") y) x))
            (assert (= (str.replace_re_all x (str.to_re "a") y) x))
            (assert (= (str.to_lower x) y))
            (assert (= (str.to_upper x) y))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 23);
}

#[test]
fn test_elaborate_str_replace_all_constant_fold() {
    let input = r#"
            (assert (= (str.replace_all "aaba" "a" "c") "ccbc"))
            (assert (= (str.replace_all "aaba" "a" "c") "wrong"))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
    assert!(ctx.terms.is_false(ctx.assertions[1]));
}

#[test]
fn test_elaborate_str_is_digit_sort_mismatch() {
    let input = r#"
            (declare-const n Int)
            (assert (str.is_digit n))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();

    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn test_elaborate_str_is_digit_arity_mismatch() {
    let input = r#"
            (declare-const x String)
            (declare-const y String)
            (assert (str.is_digit x y))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    ctx.process_command(&commands[1]).unwrap();

    let err = ctx.process_command(&commands[2]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::InvalidConstant(_)),
        "expected arity error, got: {err:?}"
    );
}

#[test]
fn test_elaborate_string_builtin_sort_mismatch() {
    let input = r#"
            (assert (= (str.len 0) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let err = ctx.process_command(&commands[0]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn test_elaborate_regex_builtins() {
    let input = r#"
            (declare-const x String)
            (assert (str.in_re x (str.to_re "a")))
            (assert (str.in.re x (str.to.re "a")))
            (assert (str.in_re x (re.* (str.to_re "a"))))
            (assert (str.in_re x (re.+ (str.to_re "a"))))
            (assert (str.in_re x (re.opt (str.to_re "a"))))
            (assert (str.in_re x (re.comp (str.to_re "a"))))
            (assert (str.in_re x (re.++ (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re x (re.union (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re x (re.inter (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re x (re.diff (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re x (re.range "a" "z")))
            (assert (str.in_re x ((_ re.^  3) (str.to_re "a"))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 12);
}

#[test]
fn test_elaborate_str_in_re_sort_mismatch() {
    let input = r#"
            (declare-const x String)
            (assert (str.in_re x x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();

    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn test_elaborate_str_suffixof_sort_mismatch() {
    let input = r#"
            (declare-const n Int)
            (assert (str.suffixof n "a"))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();

    let err = ctx.process_command(&commands[1]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}

#[test]
fn test_elaborate_str_le_sort_mismatch() {
    let input = r#"
            (declare-const n Int)
            (declare-const x String)
            (assert (str.<= n x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    ctx.process_command(&commands[1]).unwrap();

    let err = ctx.process_command(&commands[2]).unwrap_err();
    assert!(
        matches!(err, ElaborateError::SortMismatch { .. }),
        "expected sort mismatch, got: {err:?}"
    );
}
