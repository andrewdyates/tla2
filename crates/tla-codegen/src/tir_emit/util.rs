// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared naming utilities for TIR code generation.

/// Convert to PascalCase.
///
/// If the result would start with a digit (e.g. `2PCwithBTM`), prefix with `M`
/// to produce a valid Rust identifier (`M2PcwithBtm`).
pub(super) fn to_pascal_case(s: &str) -> String {
    let mut result = String::new();
    let mut capitalize_next = true;
    for c in s.chars() {
        if c == '_' || c == '-' {
            capitalize_next = true;
        } else if capitalize_next {
            result.push(c.to_ascii_uppercase());
            capitalize_next = false;
        } else {
            result.push(c);
        }
    }
    // Rust identifiers cannot start with a digit
    if result.starts_with(|c: char| c.is_ascii_digit()) {
        format!("M{result}")
    } else {
        result
    }
}

/// Convert to snake_case.
pub(super) fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    let mut prev_was_sep = false;
    let mut prev_was_lower_or_digit = false;

    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            if c.is_uppercase() {
                if !result.is_empty() && !prev_was_sep && prev_was_lower_or_digit {
                    result.push('_');
                }
                result.push(c.to_ascii_lowercase());
                prev_was_lower_or_digit = false;
            } else {
                result.push(c.to_ascii_lowercase());
                prev_was_lower_or_digit = true;
            }
            prev_was_sep = false;
        } else if !result.is_empty() && !prev_was_sep {
            result.push('_');
            prev_was_sep = true;
            prev_was_lower_or_digit = false;
        }
    }

    while result.ends_with('_') {
        result.pop();
    }

    if result.is_empty() {
        "_".to_string()
    } else if result.starts_with(|c: char| c.is_ascii_digit()) {
        format!("_{result}")
    } else {
        // Escape Rust reserved keywords with r# prefix
        escape_rust_keyword(&result)
    }
}

/// Escape a name if it conflicts with a Rust keyword.
///
/// Uses the `r#` raw identifier syntax for most keywords.
/// `self`, `Self`, `super`, `crate`, `true`, `false` cannot use `r#` and
/// get an underscore suffix instead.
fn escape_rust_keyword(name: &str) -> String {
    match name {
        // These cannot use r# — append underscore
        "self" | "super" | "crate" | "true" | "false" => format!("{name}_"),
        // Standard keywords: use r# raw identifier
        "as" | "break" | "const" | "continue" | "else" | "enum" | "extern" | "fn" | "for"
        | "if" | "impl" | "in" | "let" | "loop" | "match" | "mod" | "move" | "mut" | "pub"
        | "ref" | "return" | "static" | "struct" | "trait" | "type" | "unsafe" | "use"
        | "where" | "while" | "async" | "await" | "dyn" => format!("r#{name}"),
        // Common Rust built-in names that could clash with macros/prelude
        "matches" | "print" | "println" | "format" | "vec" | "todo" | "panic"
        | "assert" | "debug_assert" | "cfg" | "include" | "concat" | "stringify"
        | "env" | "option_env" | "line" | "column" | "file" | "module_path" => {
            format!("{name}_")
        }
        _ => name.to_string(),
    }
}
