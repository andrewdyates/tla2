// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constant value parsing from TLC config files
//!
//! Handles parsing constant value strings (integers, booleans, strings,
//! sets, tuples, records, model values) into runtime `Value`s.

use crate::value::{SetBuilder, Value};

/// Errors from parsing TLC config constant values.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ConstantParseError {
    /// Input does not match any supported constant syntax.
    #[error("Cannot parse constant value: {input}")]
    InvalidSyntax { input: String },

    /// Identifier is valid but cannot be constructed as a model value.
    #[error("Cannot create model value from constant {input:?}: {reason}")]
    ModelValueCreation { input: String, reason: String },

    /// Record literal body is empty (e.g., `[]` with `|->`).
    #[error("Empty record literal")]
    EmptyRecord,

    /// A record field has an empty name before `|->`.
    #[error("Empty field name in record: {field}")]
    EmptyFieldName { field: String },

    /// A record field is missing the `|->` separator.
    #[error("Invalid record field syntax: {field}")]
    InvalidRecordField { field: String },
}

/// Parse a constant value string and return the runtime value
///
/// # Arguments
/// * `value_str` - The value string from the config file (e.g., "{a, b, c}" or "3")
///
/// # Returns
/// * `Ok(Value)` - The parsed runtime value
/// * `Err(ConstantParseError)` - Typed parse error
///
/// # Supported syntax
///
/// - Integer literals: `3`, `-42`, `100`
/// - String literals: `"hello"`, `"neg"`, `"SAT"`
/// - Boolean literals: `TRUE`, `FALSE`
/// - Set literals: `{a, b, c}`, `{1, 2, 3}`, nested `{{a}, {b}}`
/// - Tuple/sequence literals: `<<1, 2, 3>>`, `<<a, "neg">>`
/// - Record literals: `[field |-> value]`, `[x |-> 1, y |-> 2]`
/// - Model values: identifiers like `a`, `p1`, `server`
pub fn parse_constant_value(value_str: &str) -> Result<Value, ConstantParseError> {
    let trimmed = value_str.trim();

    // Try integer first
    if let Ok(n) = trimmed.parse::<i64>() {
        return Ok(Value::int(n));
    }

    // Try boolean literals
    if trimmed == "TRUE" {
        return Ok(Value::Bool(true));
    }
    if trimmed == "FALSE" {
        return Ok(Value::Bool(false));
    }

    // Try string literals
    if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() >= 2 {
        let inner = &trimmed[1..trimmed.len() - 1];
        return Ok(Value::string(inner));
    }

    // Try parsing as a set literal
    if trimmed.starts_with('{') && trimmed.ends_with('}') {
        return parse_set_literal(trimmed);
    }

    // Try parsing as a sequence/tuple
    if trimmed.starts_with("<<") && trimmed.ends_with(">>") {
        return parse_tuple_literal(trimmed);
    }

    // Try parsing as a record literal
    if trimmed.starts_with('[') && trimmed.ends_with(']') && trimmed.contains("|->") {
        return parse_record_literal(trimmed);
    }

    // Otherwise treat as model value (identifier)
    if is_valid_identifier(trimmed) {
        return Value::try_model_value(trimmed).map_err(|e| {
            ConstantParseError::ModelValueCreation {
                input: trimmed.to_string(),
                reason: e.to_string(),
            }
        });
    }

    Err(ConstantParseError::InvalidSyntax {
        input: value_str.to_string(),
    })
}

/// Parse a set literal like `{a, b, c}` or `{1, 2, 3}`
fn parse_set_literal(s: &str) -> Result<Value, ConstantParseError> {
    let inner = &s[1..s.len() - 1];
    let trimmed = inner.trim();

    if trimmed.is_empty() {
        return Ok(Value::empty_set());
    }

    let elements = split_set_elements(trimmed);
    let mut set = SetBuilder::new();

    for elem in elements {
        let value = parse_constant_value(&elem)?;
        set.insert(value);
    }

    Ok(set.build_value())
}

/// Parse a tuple/sequence literal like `<<a, b, c>>`
fn parse_tuple_literal(s: &str) -> Result<Value, ConstantParseError> {
    let inner = &s[2..s.len() - 2];
    let trimmed = inner.trim();

    if trimmed.is_empty() {
        return Ok(Value::Tuple(Vec::new().into()));
    }

    let elements = split_set_elements(trimmed);
    let mut tuple = Vec::new();

    for elem in elements {
        let value = parse_constant_value(&elem)?;
        tuple.push(value);
    }

    Ok(Value::Tuple(tuple.into()))
}

/// Parse a record literal like `[field |-> value]` or `[x |-> 1, y |-> 2]`
fn parse_record_literal(s: &str) -> Result<Value, ConstantParseError> {
    let inner = &s[1..s.len() - 1];
    let trimmed = inner.trim();

    if trimmed.is_empty() {
        return Err(ConstantParseError::EmptyRecord);
    }

    // Split on commas at the top level
    let field_strs = split_set_elements(trimmed);
    let mut fields = Vec::new();

    for field_str in field_strs {
        // Parse "field |-> value"
        if let Some(pos) = field_str.find("|->") {
            let name = field_str[..pos].trim();
            let value_str = field_str[pos + 3..].trim();

            if name.is_empty() {
                return Err(ConstantParseError::EmptyFieldName { field: field_str });
            }

            let value = parse_constant_value(value_str)?;
            fields.push((name.to_string(), value));
        } else {
            return Err(ConstantParseError::InvalidRecordField { field: field_str });
        }
    }

    Ok(Value::record(fields))
}

/// Split set elements, handling nested braces, brackets, tuples, and strings
fn split_set_elements(s: &str) -> Vec<String> {
    let mut elements = Vec::new();
    let mut current = String::new();
    let mut brace_depth = 0; // {}
    let mut bracket_depth = 0; // []
    let mut angle_depth = 0; // <<>>
    let mut in_string = false;
    let mut prev_char = '\0';

    for c in s.chars() {
        // Handle string state transitions
        if c == '"' && !in_string {
            in_string = true;
            current.push(c);
            prev_char = c;
            continue;
        }
        if c == '"' && in_string && prev_char != '\\' {
            in_string = false;
            current.push(c);
            prev_char = c;
            continue;
        }

        // If inside a string, just accumulate characters
        if in_string {
            current.push(c);
            prev_char = c;
            continue;
        }

        match c {
            '{' => {
                brace_depth += 1;
                current.push(c);
            }
            '}' => {
                brace_depth -= 1;
                current.push(c);
            }
            '[' => {
                bracket_depth += 1;
                current.push(c);
            }
            ']' => {
                bracket_depth -= 1;
                current.push(c);
            }
            '<' => {
                // Check for <<
                if prev_char == '<' {
                    angle_depth += 1;
                }
                current.push(c);
            }
            '>' => {
                // Check for >>
                if prev_char == '>' {
                    angle_depth -= 1;
                }
                current.push(c);
            }
            ',' if brace_depth == 0 && bracket_depth == 0 && angle_depth == 0 => {
                let elem = current.trim().to_string();
                if !elem.is_empty() {
                    elements.push(elem);
                }
                current.clear();
            }
            _ => {
                current.push(c);
            }
        }
        prev_char = c;
    }

    let elem = current.trim().to_string();
    if !elem.is_empty() {
        elements.push(elem);
    }

    elements
}

/// Check if string is a valid TLA+ identifier
fn is_valid_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !first.is_alphabetic() && first != '_' {
        return false;
    }
    chars.all(|c| c.is_alphanumeric() || c == '_')
}
