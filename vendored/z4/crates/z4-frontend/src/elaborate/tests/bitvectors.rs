// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_bitvector() {
    let input = r#"
            (declare-const x (_ BitVec 32))
            (assert (= x #x0000FFFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

/// Test for #924: bitvector numeral syntax (_ bvN w)
/// SMT-LIB 2.6 Section 3.5 defines this as equivalent to #x/#b forms.
#[test]
fn test_elaborate_bv_numeral_syntax_924() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            ; (_ bv255 8) should equal #xFF
            (assert (= (_ bv255 8) #xFF))
            ; (_ bv7 3) should equal #b111
            (assert (= (_ bv7 3) #b111))
            ; (_ bv0 1) should equal #b0
            (assert (= (_ bv0 1) #b0))
            ; (_ bv1 1) should equal #b1
            (assert (= (_ bv1 1) #b1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // Should have 4 assertions (all equivalences)
    assert_eq!(ctx.assertions.len(), 4);
}

#[test]
fn test_elaborate_bv_extract() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ extract 7 4) x) #xF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv_concat() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (concat x y) #x0FF0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv_zero_extend() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ zero_extend 8) x) #x00FF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv_sign_extend() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ sign_extend 8) x) #xFFFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv_rotate() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ rotate_left 2) x) #xAA))
            (assert (= ((_ rotate_right 2) x) #x55))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn test_elaborate_bv_repeat() {
    let input = r#"
            (declare-const x (_ BitVec 4))
            (assert (= ((_ repeat 4) x) #xAAAA))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bvsdiv() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvsdiv x y) #xFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bvsrem() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvsrem x y) #x01))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bvsmod() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvsmod x y) #x02))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bvcomp() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvcomp x y) #b1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv2nat_and_int2bv() {
    let input = r#"
            (assert (= (bv2nat #x0F) 15))
            (assert (= ((_ int2bv 8) (- 1)) #xFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn test_elaborate_bvnand_bvnor_bvxnor() {
    let input = r#"
            (assert (= (bvnand #xFF #xFF) #x00))
            (assert (= (bvnor #x00 #x00) #xFF))
            (assert (= (bvxnor #x0F #x0F) #xFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 3);
}

#[test]
fn test_bv_left_associative_nary_ops() {
    // SMT-LIB 2.6: bvadd, bvmul, bvand, bvor, bvxor are left-associative
    // (bvadd x y z) should desugar to (bvadd (bvadd x y) z)
    let input = r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (declare-const z (_ BitVec 8))
            (assert (= (bvadd x y z) (bvadd (bvadd x y) z)))
            (assert (= (bvmul x y z) (bvmul (bvmul x y) z)))
            (assert (= (bvand x y z) (bvand (bvand x y) z)))
            (assert (= (bvor x y z) (bvor (bvor x y) z)))
            (assert (= (bvxor x y z) (bvxor (bvxor x y) z)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("n-ary BV op should elaborate");
    }

    // 5 assertions, all should parse successfully
    assert_eq!(ctx.assertions.len(), 5);
}

#[test]
fn test_bv_left_associative_4args() {
    // 4-argument case: (bvadd a b c d) => (bvadd (bvadd (bvadd a b) c) d)
    let input = r#"
            (set-logic QF_BV)
            (declare-const a (_ BitVec 8))
            (declare-const b (_ BitVec 8))
            (declare-const c (_ BitVec 8))
            (declare-const d (_ BitVec 8))
            (assert (= (bvadd a b c d) (bvadd (bvadd (bvadd a b) c) d)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("4-arg bvadd should elaborate");
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_bv_binary_still_works() {
    // Binary (2-arg) BV ops should still work as before
    let input = r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvadd x y) (bvor x y)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("binary BV op should still work");
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_bv_nary_rejects_unary() {
    // Even left-associative ops require at least 2 arguments
    let input = r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (assert (= (bvadd x) x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                format!("{e:?}").contains("at least 2 arguments"),
                "Expected 'at least 2 arguments' error, got: {e:?}"
            );
            found_error = true;
        }
    }
    assert!(found_error, "Expected error for unary bvadd");
}
