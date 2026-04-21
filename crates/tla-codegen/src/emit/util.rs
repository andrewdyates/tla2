// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::error::CodegenError;

/// Convert to PascalCase
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
    result
}

/// Convert to snake_case
pub(super) fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            result.push('_');
        }
        result.push(c.to_ascii_lowercase());
    }
    result
}

fn validate_single_line_rust_fragment(ctx: &str, s: &str) -> Result<(), CodegenError> {
    let make_err = |reason: String| CodegenError::InvalidRustFragment {
        context: ctx.to_string(),
        reason,
    };

    if s.chars()
        .any(|c| matches!(c, '\n' | '\r' | '\u{0085}' | '\u{2028}' | '\u{2029}'))
    {
        return Err(make_err("must be single-line".to_string()));
    }
    if s.chars().any(|c| c.is_control()) {
        return Err(make_err("must not contain control characters".to_string()));
    }
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return Err(make_err("must be non-empty".to_string()));
    }
    if trimmed.contains('{') || trimmed.contains('}') {
        return Err(make_err("must not contain braces".to_string()));
    }
    if trimmed.contains(';') {
        return Err(make_err("must not contain semicolons".to_string()));
    }
    if trimmed.contains("//") || trimmed.contains("/*") || trimmed.contains("*/") {
        return Err(make_err("must not contain comment markers".to_string()));
    }

    fn is_ident_byte(b: u8) -> bool {
        b == b'_' || b.is_ascii_alphanumeric()
    }

    fn contains_token(s: &str, tok: &[u8]) -> bool {
        let bytes = s.as_bytes();
        if tok.is_empty() || bytes.len() < tok.len() {
            return false;
        }
        for i in 0..=bytes.len() - tok.len() {
            if &bytes[i..i + tok.len()] != tok {
                continue;
            }
            let before_ok = i == 0 || !is_ident_byte(bytes[i - 1]);
            let after_ok = i + tok.len() == bytes.len() || !is_ident_byte(bytes[i + tok.len()]);
            if before_ok && after_ok {
                return true;
            }
        }
        false
    }

    for token in [b"use".as_slice(), b"mod".as_slice()] {
        if contains_token(trimmed, token) {
            let token_str = std::str::from_utf8(token).unwrap_or("<non-utf8>");
            return Err(make_err(format!("must not contain token {token_str:?}")));
        }
    }

    Ok(())
}

pub(super) fn validate_single_line_rust_fragment_trimmed<'a>(
    ctx: &str,
    s: &'a str,
) -> Result<&'a str, CodegenError> {
    validate_single_line_rust_fragment(ctx, s)?;
    Ok(s.trim())
}

pub(super) fn validate_single_line_rust_expr(s: &str) -> Result<(), CodegenError> {
    validate_single_line_rust_fragment("expr", s)?;
    Ok(())
}

pub(super) fn validate_single_line_rust_expr_trimmed(s: &str) -> Result<&str, CodegenError> {
    validate_single_line_rust_expr(s)?;
    Ok(s.trim())
}
