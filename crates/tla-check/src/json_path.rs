// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared JSON-path formatting utilities.
//!
//! We use a stable `$`-rooted JSONPath-like syntax:
//! - Root: `$`
//! - Object keys: `$.key` (identifier-safe) or `$["not safe"]`
//! - Sequences: `$[0]`

use serde_path_to_error::{Path, Segment};

pub(crate) fn format_json_path(path: &Path) -> String {
    let mut buf = String::from("$");
    for segment in path {
        match segment {
            Segment::Seq { index } => append_json_path_index(&mut buf, *index),
            Segment::Map { key } => append_json_path_key(&mut buf, key),
            Segment::Enum { variant } => append_json_path_key(&mut buf, variant),
            Segment::Unknown => buf.push_str(".?"),
        }
    }
    buf
}

pub(crate) fn append_json_path_index(buf: &mut String, index: usize) {
    use std::fmt::Write;
    buf.push('[');
    write!(buf, "{index}").expect("invariant: String fmt::Write is infallible");
    buf.push(']');
}

pub(crate) fn append_json_path_key(buf: &mut String, key: &str) {
    if is_identifier_safe(key) {
        buf.push('.');
        buf.push_str(key);
        return;
    }

    buf.push('[');
    append_json_string_literal(buf, key);
    buf.push(']');
}

fn append_json_string_literal(buf: &mut String, value: &str) {
    buf.push('"');
    for ch in value.chars() {
        match ch {
            '"' => buf.push_str("\\\""),
            '\\' => buf.push_str("\\\\"),
            '\u{08}' => buf.push_str("\\b"),
            '\u{0C}' => buf.push_str("\\f"),
            '\n' => buf.push_str("\\n"),
            '\r' => buf.push_str("\\r"),
            '\t' => buf.push_str("\\t"),
            ch if ch <= '\u{1F}' => append_json_control_escape(buf, ch as u8),
            ch => buf.push(ch),
        }
    }
    buf.push('"');
}

fn append_json_control_escape(buf: &mut String, byte: u8) {
    const HEX: &[u8; 16] = b"0123456789abcdef";

    buf.push_str("\\u00");
    buf.push(char::from(HEX[(byte >> 4) as usize]));
    buf.push(char::from(HEX[(byte & 0x0f) as usize]));
}

fn is_identifier_safe(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !matches!(first, 'A'..='Z' | 'a'..='z' | '_') {
        return false;
    }
    chars.all(|c| matches!(c, 'A'..='Z' | 'a'..='z' | '0'..='9' | '_'))
}

#[cfg(test)]
mod tests {
    use super::{append_json_path_index, append_json_path_key};

    fn render_key(key: &str) -> String {
        let mut buf = "$".to_string();
        append_json_path_key(&mut buf, key);
        buf
    }

    fn render_index(index: usize) -> String {
        let mut buf = "$".to_string();
        append_json_path_index(&mut buf, index);
        buf
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_bracket_quotes_dot_key() {
        assert_eq!(render_key("a.b"), r#"$["a.b"]"#);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_dot_for_identifier_safe_key() {
        assert_eq!(render_key("abc_123"), "$.abc_123");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_bracket_quotes_empty_key() {
        assert_eq!(render_key(""), r#"$[""]"#);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_bracket_quotes_space_key() {
        assert_eq!(render_key("a b"), r#"$["a b"]"#);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_bracket_quotes_leading_digit_key() {
        assert_eq!(render_key("0abc"), r#"$["0abc"]"#);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_bracket_quotes_quote_key() {
        assert_eq!(render_key("a\"b"), r#"$["a\"b"]"#);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_bracket_quotes_backslash_key() {
        assert_eq!(render_key("a\\b"), r#"$["a\\b"]"#);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_index_brackets_numeric_index() {
        assert_eq!(render_index(42), "$[42]");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_index_brackets_zero_index() {
        assert_eq!(render_index(0), "$[0]");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_index_brackets_max_usize_index() {
        assert_eq!(render_index(usize::MAX), format!("$[{}]", usize::MAX));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_bracket_quotes_newline_key() {
        assert_eq!(render_key("a\nb"), r#"$["a\nb"]"#);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_bracket_quotes_control_key() {
        assert_eq!(render_key("a\u{1f}b"), r#"$["a\u001fb"]"#);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn append_json_path_key_matches_serde_json_escape_behavior() {
        let key = "quote\" slash\\ line\ncarriage\rtab\tbackspace\u{08}formfeed\u{0c}control\u{1f}";
        let expected = format!("$[{}]", serde_json::to_string(key).unwrap());
        assert_eq!(render_key(key), expected);
    }
}
