// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for input validation: single-line Rust expression injection prevention,
//! checker_map config validation.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_single_line_rust_expr_allows_simple_exprs() {
    assert!(validate_single_line_rust_expr("self.x").is_ok());
    assert!(validate_single_line_rust_expr("self.abuse").is_ok());
    assert!(validate_single_line_rust_expr("some_module::value").is_ok());
    assert!(validate_single_line_rust_expr("x.map(|m| m.clone())").is_ok());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_validate_single_line_rust_expr_rejects_injection_primitives() {
    assert!(validate_single_line_rust_expr("").is_err());
    assert!(validate_single_line_rust_expr("self.x\n").is_err());
    assert!(validate_single_line_rust_expr("self.x\r").is_err());
    assert!(validate_single_line_rust_expr("self.x\u{2028}").is_err());
    assert!(validate_single_line_rust_expr("self.x\u{2029}").is_err());
    assert!(validate_single_line_rust_expr("self.x\u{0085}").is_err());
    assert!(validate_single_line_rust_expr("self.x\0").is_err());
    assert!(validate_single_line_rust_expr("self.x\u{001B}").is_err());
    assert!(validate_single_line_rust_expr("self.x\t").is_err());
    assert!(validate_single_line_rust_expr("{ self.x }").is_err());
    assert!(validate_single_line_rust_expr("self.x;").is_err());
    assert!(validate_single_line_rust_expr("self.x // comment").is_err());
    assert!(validate_single_line_rust_expr("self.x /* comment */").is_err());
    assert!(validate_single_line_rust_expr("use crate::x").is_err());
    assert!(validate_single_line_rust_expr("mod x").is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checker_map_validates_rust_type_before_trimming() {
    let checker_map = CheckerMapConfig {
        spec_module: None,
        impls: vec![crate::CheckerMapImpl {
            rust_type: "MyType\n".to_string(),
            fields: std::collections::BTreeMap::from([(
                "count".to_string(),
                "self.count".to_string(),
            )]),
        }],
    };

    let options = CodeGenOptions {
        generate_checker: true,
        checker_map: Some(checker_map),
        ..Default::default()
    };

    assert!(generate_rust(&make_counter_module(), &options).is_err());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checker_map_validates_expr_before_trimming() {
    let checker_map = CheckerMapConfig {
        spec_module: None,
        impls: vec![crate::CheckerMapImpl {
            rust_type: "MyType".to_string(),
            fields: std::collections::BTreeMap::from([(
                "count".to_string(),
                "self.count\n".to_string(),
            )]),
        }],
    };

    let options = CodeGenOptions {
        generate_checker: true,
        checker_map: Some(checker_map),
        ..Default::default()
    };

    assert!(generate_rust(&make_counter_module(), &options).is_err());
}
