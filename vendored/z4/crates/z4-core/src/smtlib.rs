// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB surface syntax helpers
//!
//! This module provides functions for printing SMT-LIB compatible output.
//! All Z4 crates that emit SMT-LIB text should use these helpers to ensure
//! that output is syntactically valid and round-trips through the parser.
//!
//! Author: Andrew Yates

/// Quote a symbol if it cannot be written as a simple (unquoted) SMT-LIB symbol.
///
/// Returns the symbol wrapped in `|...|` if any of the following hold:
/// - The symbol is empty
/// - The symbol starts with a digit
/// - The symbol is a reserved word (`true`, `false`, keywords, etc.)
/// - The symbol contains characters not allowed in simple symbols
///
/// SMT-LIB quoted symbols cannot contain `|` or `\`. These characters are
/// sanitized to `_` before quoting to ensure valid output (#1841).
///
/// # Examples
/// ```
/// use z4_core::quote_symbol;
///
/// assert_eq!(quote_symbol("x"), "x");
/// assert_eq!(quote_symbol("myVar"), "myVar");
/// assert_eq!(quote_symbol("let"), "|let|");
/// assert_eq!(quote_symbol("123abc"), "|123abc|");
/// assert_eq!(quote_symbol("x y"), "|x y|");
/// assert_eq!(quote_symbol("foo::bar"), "|foo::bar|");
/// assert_eq!(quote_symbol("true"), "|true|");
/// assert_eq!(quote_symbol("false"), "|false|");
/// // Characters invalid in quoted symbols are sanitized
/// assert_eq!(quote_symbol("a|b"), "|a_b|");
/// assert_eq!(quote_symbol(r"a\b"), "|a_b|");
/// ```
pub fn quote_symbol(name: &str) -> String {
    // Reserved words in SMT-LIB that need quoting
    // This includes:
    // - `true` and `false` (dedicated tokens in the lexer)
    // - Core keywords and command names
    const RESERVED: &[&str] = &[
        // Boolean literals (lexer tokens)
        "true",
        "false",
        // Binding keywords
        "let",
        "forall",
        "exists",
        "match",
        "par",
        "_",
        "!",
        "as",
        // Spec constants
        "BINARY",
        "DECIMAL",
        "HEXADECIMAL",
        "NUMERAL",
        "STRING",
        // Commands
        "assert",
        "check-sat",
        "check-sat-assuming",
        "declare-const",
        "declare-datatype",
        "declare-datatypes",
        "declare-fun",
        "declare-sort",
        "define-fun",
        "define-fun-rec",
        "define-funs-rec",
        "define-sort",
        "echo",
        "exit",
        "get-assertions",
        "get-assignment",
        "get-info",
        "get-model",
        "get-option",
        "get-proof",
        "get-unsat-assumptions",
        "get-unsat-core",
        "get-value",
        "pop",
        "push",
        "reset",
        "reset-assertions",
        "set-info",
        "set-logic",
        "set-option",
    ];

    let needs_quoting = name.is_empty()
        || name.starts_with(|c: char| c.is_ascii_digit())
        || RESERVED.contains(&name)
        || name.contains(|c: char| !is_symbol_char(c));

    if needs_quoting {
        // SMT-LIB quoted symbols cannot contain '|' or '\' (#1841).
        // Sanitize these characters to '_' before quoting.
        let sanitized: String = name
            .chars()
            .map(|c| if c == '|' || c == '\\' { '_' } else { c })
            .collect();
        format!("|{sanitized}|")
    } else {
        name.to_string()
    }
}

/// Check if a character is valid in an unquoted SMT-LIB symbol.
///
/// This matches the Z4 lexer's `Token::Symbol` regex:
/// `[a-zA-Z~!@$%^&*_+=<>.?/\-][a-zA-Z0-9~!@$%^&*_+=<>.?/\-]*`
///
/// Note: The first character has additional restrictions (cannot be a digit),
/// which is handled separately in `quote_symbol`.
pub(crate) fn is_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(
            c,
            '+' | '-'
                | '/'
                | '*'
                | '='
                | '%'
                | '?'
                | '!'
                | '.'
                | '$'
                | '_'
                | '~'
                | '&'
                | '^'
                | '<'
                | '>'
                | '@'
        )
}

/// Escape a string's contents for SMT-LIB 2.6 output.
///
/// In SMT-LIB 2.6, the only in-string escape is `""` for a literal `"`.
/// Backslashes are literal characters (not escape characters in the standard),
/// except for `\u{XXXX}` Unicode escapes which we also support.
///
/// # Examples
/// ```
/// use z4_core::escape_string_contents;
///
/// assert_eq!(escape_string_contents("hello"), "hello");
/// assert_eq!(escape_string_contents(r#"say "hi""#), r#"say ""hi"""#);
/// assert_eq!(escape_string_contents(r"path\to\file"), r"path\to\file");
/// ```
pub fn escape_string_contents(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        if c == '"' {
            result.push_str("\"\"");
        } else {
            result.push(c);
        }
    }
    result
}

/// Format a string value as an SMT-LIB 2.6 string literal.
///
/// This escapes the contents and wraps them in double quotes.
/// Uses `""` for literal quotes per SMT-LIB 2.6 standard.
///
/// # Examples
/// ```
/// use z4_core::string_literal;
///
/// assert_eq!(string_literal("hello"), "\"hello\"");
/// assert_eq!(string_literal(r#"say "hi""#), r#""say ""hi""""#);
/// ```
pub fn string_literal(s: &str) -> String {
    format!("\"{}\"", escape_string_contents(s))
}

/// Unescape an SMT-LIB string literal's contents.
///
/// Handles both SMT-LIB 2.6 standard (`""` -> `"`) and legacy backslash
/// escapes (`\\` -> `\`, `\"` -> `"`, `\u{XXXX}`).
/// The input should be the contents without the surrounding quotes.
///
/// # Examples
/// ```
/// use z4_core::unescape_string_contents;
///
/// assert_eq!(unescape_string_contents("hello"), "hello");
/// assert_eq!(unescape_string_contents(r#"say ""hi"""#), r#"say "hi""#);
/// assert_eq!(unescape_string_contents(r#"say \"hi\""#), r#"say "hi""#);
/// assert_eq!(unescape_string_contents(r"path\\to\\file"), r"path\to\file");
/// ```
pub fn unescape_string_contents(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '"' {
            // SMT-LIB 2.6: `""` inside string contents = literal `"`
            if chars.peek() == Some(&'"') {
                chars.next(); // consume second `"`
                result.push('"');
            } else {
                // Stray quote — should not happen in well-formed input
                result.push(c);
            }
        } else if c == '\\' {
            if let Some(&next) = chars.peek() {
                match next {
                    '\\' | '"' => {
                        result.push(next);
                        chars.next();
                    }
                    // SMT-LIB 2.6 unicode escape: \u{XXXX} or \uXXXX
                    'u' => {
                        chars.next(); // consume 'u'
                        if let Some(ch) = parse_unicode_escape(&mut chars) {
                            result.push(ch);
                        } else {
                            // Malformed escape — emit literally
                            result.push('\\');
                            result.push('u');
                        }
                    }
                    // Pass through other backslash sequences unchanged
                    _ => result.push(c),
                }
            } else {
                result.push(c);
            }
        } else {
            result.push(c);
        }
    }
    result
}

/// Parse a unicode escape after `\u` has been consumed.
///
/// Supports two forms per SMT-LIB 2.6:
/// - `\u{XXXX}` — 1 to 6 hex digits in braces (any Unicode code point)
/// - `\uXXXX` — exactly 4 hex digits (BMP only)
fn parse_unicode_escape(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Option<char> {
    if chars.peek() == Some(&'{') {
        chars.next(); // consume '{'
        let mut hex = String::new();
        while let Some(&c) = chars.peek() {
            if c == '}' {
                chars.next(); // consume '}'
                break;
            }
            if c.is_ascii_hexdigit() && hex.len() < 6 {
                hex.push(c);
                chars.next();
            } else {
                return None;
            }
        }
        if hex.is_empty() {
            return None;
        }
        let code = u32::from_str_radix(&hex, 16).ok()?;
        char::from_u32(code)
    } else {
        // \uXXXX — exactly 4 hex digits
        let mut hex = String::with_capacity(4);
        for _ in 0..4 {
            if let Some(&c) = chars.peek() {
                if c.is_ascii_hexdigit() {
                    hex.push(c);
                    chars.next();
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
        let code = u32::from_str_radix(&hex, 16).ok()?;
        char::from_u32(code)
    }
}

#[cfg(test)]
#[path = "smtlib_tests.rs"]
mod tests;
