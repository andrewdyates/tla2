// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::constructors::*;
use super::types::*;
use crate::span::Span;
use insta::assert_snapshot;

/// Helper to render diagnostic to string (strips ANSI color codes for snapshots)
fn render_to_string(d: &Diagnostic, file_path: &str, source: &str) -> String {
    let mut buf = Vec::new();
    d.render(file_path, source, &mut buf).unwrap();
    let output = String::from_utf8(buf).unwrap();
    // Strip ANSI escape codes for deterministic snapshots
    strip_ansi_codes(&output)
}

/// Strip ANSI escape codes from a string
fn strip_ansi_codes(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\x1b' {
            // Skip the escape sequence: ESC [ ... m
            if chars.peek() == Some(&'[') {
                chars.next(); // consume '['
                              // Skip until we hit 'm'
                while let Some(&nc) = chars.peek() {
                    chars.next();
                    if nc == 'm' {
                        break;
                    }
                }
                continue;
            }
        }
        result.push(c);
    }
    result
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diagnostic_error() {
    let d = Diagnostic::error("test error");
    assert_eq!(d.severity, Severity::Error);
    assert_eq!(d.message, "test error");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diagnostic_with_span() {
    let d = Diagnostic::error("test").with_span("file.tla", 10, 20);
    assert!(d.span.is_some());
    let span = d.span.unwrap();
    assert_eq!(span.file, "file.tla");
    assert_eq!(span.start, 10);
    assert_eq!(span.end, 20);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_diagnostic_render() {
    let source = "---- MODULE Test ----\nVARIABLE x\n====";

    let d = Diagnostic::error("undefined variable")
        .with_span_label("test.tla", 22, 31, "not defined")
        .with_help("Define the variable first");

    let mut buf = Vec::new();
    d.render("test.tla", source, &mut buf).unwrap();
    let output = String::from_utf8(buf).unwrap();

    // Verify the output contains expected content
    assert!(output.contains("undefined variable"));
    assert!(output.contains("not defined"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_error_diagnostic() {
    let d = parse_error_diagnostic("test.tla", "unexpected token", 10, 15);
    assert_eq!(d.severity, Severity::Error);
    assert!(d.message.contains("syntax error"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_undefined_name_diagnostic() {
    let span = Span::new(crate::FileId(0), 10, 15);
    let d = undefined_name_diagnostic("test.tla", "foo", span);
    assert!(d.message.contains("undefined name"));
    assert!(d.help.is_some());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_duplicate_definition_diagnostic() {
    let original = Span::new(crate::FileId(0), 10, 15);
    let duplicate = Span::new(crate::FileId(0), 30, 35);
    let d = duplicate_definition_diagnostic("test.tla", "foo", original, duplicate);
    assert!(d.message.contains("duplicate"));
    assert_eq!(d.labels.len(), 1); // Secondary label for original
}

// ============================================================================
// SNAPSHOT TESTS - Error message format stability
// These tests ensure error messages don't change unexpectedly.
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_parse_error() {
    let source = "---- MODULE Test ----\nVARIABLE x == 1\n====";
    let d = parse_error_diagnostic("test.tla", "expected identifier, found '=='", 33, 35);
    assert_snapshot!(
        "snapshot_parse_error",
        render_to_string(&d, "test.tla", source)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_undefined_name() {
    let source = "---- MODULE Test ----\nInit == foo = 0\n====";
    let span = Span::new(crate::FileId(0), 30, 33); // "foo"
    let d = undefined_name_diagnostic("test.tla", "foo", span);
    assert_snapshot!(
        "snapshot_undefined_name",
        render_to_string(&d, "test.tla", source)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_duplicate_definition() {
    let source = "---- MODULE Test ----\nfoo == 1\nfoo == 2\n====";
    let original = Span::new(crate::FileId(0), 22, 25); // first "foo"
    let duplicate = Span::new(crate::FileId(0), 31, 34); // second "foo"
    let d = duplicate_definition_diagnostic("test.tla", "foo", original, duplicate);
    assert_snapshot!(
        "snapshot_duplicate_definition",
        render_to_string(&d, "test.tla", source)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_arity_mismatch() {
    let source = "---- MODULE Test ----\nOp(x, y) == x + y\nInit == Op(1)\n====";
    let span = Span::new(crate::FileId(0), 48, 53); // "Op(1)"
    let d = arity_mismatch_diagnostic("test.tla", 2, 1, span);
    assert_snapshot!(
        "snapshot_arity_mismatch",
        render_to_string(&d, "test.tla", source)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_type_error() {
    let source = "---- MODULE Test ----\nInit == 1 + \"hello\"\n====";
    let span = Span::new(crate::FileId(0), 30, 42); // "1 + \"hello\""
    let d = type_error_diagnostic("test.tla", "cannot add integer and string", span);
    assert_snapshot!(
        "snapshot_type_error",
        render_to_string(&d, "test.tla", source)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_module_not_found() {
    let source = "---- MODULE Test ----\nEXTENDS Missing\n====";
    let span = Span::new(crate::FileId(0), 30, 37); // "Missing"
    let d = module_not_found_diagnostic("test.tla", "Missing", span);
    assert_snapshot!(
        "snapshot_module_not_found",
        render_to_string(&d, "test.tla", source)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_error_with_help_and_note() {
    let source = "---- MODULE Test ----\nInit == x' = 1\n====";
    let d = Diagnostic::error("primed variable 'x'' in Init")
        .with_span_label("test.tla", 30, 32, "primed variable not allowed here")
        .with_help("Init should not contain primed variables")
        .with_note(
            "Primed variables represent the next-state values and are used in Next, not Init",
        );
    assert_snapshot!(
        "snapshot_error_with_help_and_note",
        render_to_string(&d, "test.tla", source)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn snapshot_multiline_context() {
    let source = r"---- MODULE Test ----
VARIABLE x, y, z

Init ==
    /\ x = 0
    /\ y = undefined_var
    /\ z = 0
====";
    let span = Span::new(crate::FileId(0), 67, 80); // "undefined_var"
    let d = undefined_name_diagnostic("test.tla", "undefined_var", span);
    assert_snapshot!(
        "snapshot_multiline_context",
        render_to_string(&d, "test.tla", source)
    );
}
