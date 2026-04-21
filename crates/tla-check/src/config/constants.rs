// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant assignment parsing helpers for .cfg files.

use super::types::{Config, ConfigError, ConstantValue};

/// Parse a constant assignment line
///
/// Formats:
/// - `Name = Value` - direct value assignment
/// - `Name <- [ model value ]` - model value
/// - `Name <- {a, b, c}` - set of model values
/// - `Name <- OtherOp` - replacement operator
/// - `Name <- [Module] OtherOp` - module-scoped replacement (also accepts no-space: `[Module]OtherOp`)
/// - `a1=a1  a2=a2  a3=a3` - multiple space-separated model values (TLC Toolbox format)
pub(super) fn parse_constant_assignment(
    config: &mut Config,
    line: &str,
    line_num: usize,
) -> Result<(), ConfigError> {
    // If line contains `<-`, it's a single replacement-style assignment
    if let Some((name, replacement)) = line.split_once("<-") {
        let name = name.trim().to_string();
        let replacement = replacement.trim();

        // Check for module-scoped substitution: `Name <- [Module] Value` (also accepts `[Module]Value`).
        //
        // TLC parses this as a distinct "module override" entry and applies it only within that
        // module's operator definitions.
        if replacement.starts_with('[')
            && !replacement.starts_with("[ model value")
            && !replacement.starts_with("[model value")
        {
            if let Some(close_bracket) = replacement.find(']') {
                let module_name = replacement[1..close_bracket].trim();
                let after_bracket = replacement[close_bracket + 1..].trim();

                // Only treat as module scope if there is a non-empty rhs after `]`.
                // This preserves the special-case for `[ model value ]` and avoids mis-parsing
                // record/func literals that start with `[` but don't have trailing content.
                if !module_name.is_empty()
                    && !after_bracket.is_empty()
                    && is_valid_cfg_identifier(module_name)
                {
                    if !is_valid_cfg_compound_identifier(&name) {
                        return Err(ConfigError::InvalidSyntax {
                            line: line_num,
                            directive: "CONSTANT",
                            text: line.to_string(),
                        });
                    }
                    config
                        .module_overrides
                        .entry(module_name.to_string())
                        .or_default()
                        .insert(name, after_bracket.to_string());
                    return Ok(());
                }
            }
        }

        if replacement == "[ model value ]" || replacement == "[model value]" {
            config.insert_constant(name, ConstantValue::ModelValue);
        } else if replacement.starts_with('{') && replacement.ends_with('}') {
            // Set of model values
            let inner = &replacement[1..replacement.len() - 1];
            let values: Vec<String> = inner
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            config.insert_constant(name, ConstantValue::ModelValueSet(values));
        } else {
            config.insert_constant(name, ConstantValue::Replacement(replacement.to_string()));
        }
        return Ok(());
    }

    // Check if this is multiple space-separated assignments like "a1=a1  a2=a2  a3=a3"
    // These are model value assignments without spaces around the equals sign
    let parts: Vec<&str> = line.split_whitespace().collect();
    let all_simple_assignments = parts.iter().all(|part| {
        // Each part should be of the form "name=value" without spaces
        if let Some((n, v)) = part.split_once('=') {
            is_valid_cfg_identifier(n.trim()) && !v.is_empty()
        } else {
            false
        }
    });

    if all_simple_assignments && !parts.is_empty() {
        // Parse each simple assignment
        for part in parts {
            if let Some((name, value)) = part.split_once('=') {
                let name = name.trim().to_string();
                let value = value.trim().to_string();
                config.insert_constant(name, ConstantValue::Value(value));
            }
        }
        return Ok(());
    }

    // Single assignment with equals sign and potentially spaces around it
    if let Some((name, value)) = line.split_once('=') {
        let name = name.trim().to_string();
        let value = value.trim();

        // Check for module-scoped assignment: `Name = [Module] Value` (also accepts `[Module]Value`).
        if value.starts_with('[')
            && !value.starts_with("[ model value")
            && !value.starts_with("[model value")
        {
            if let Some(close_bracket) = value.find(']') {
                let module_name = value[1..close_bracket].trim();
                let after_bracket = value[close_bracket + 1..].trim();
                if !module_name.is_empty()
                    && !after_bracket.is_empty()
                    && is_valid_cfg_identifier(module_name)
                {
                    if !is_valid_cfg_compound_identifier(&name) {
                        return Err(ConfigError::InvalidSyntax {
                            line: line_num,
                            directive: "CONSTANT",
                            text: line.to_string(),
                        });
                    }
                    config
                        .module_assignments
                        .entry(module_name.to_string())
                        .or_default()
                        .insert(name, after_bracket.to_string());
                    return Ok(());
                }
            }
        }

        config.insert_constant(name, ConstantValue::Value(value.to_string()));
        Ok(())
    } else {
        Err(ConfigError::InvalidSyntax {
            line: line_num,
            directive: "CONSTANT",
            text: line.to_string(),
        })
    }
}

/// Check if string is a valid TLA+ identifier for config files
pub(super) fn is_valid_cfg_identifier(s: &str) -> bool {
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

/// Check if `s` is a valid CONSTANT(S) LHS identifier in TLC `.cfg` files.
///
/// TLC supports instance-qualified names like `I!X` (Bug44), and also permits numeric
/// segments after `!` for conjunct selection (e.g., `Def!1`).
fn is_valid_cfg_compound_identifier(s: &str) -> bool {
    let mut parts = s.split('!');
    let Some(first) = parts.next() else {
        return false;
    };
    if !is_valid_cfg_identifier(first) {
        return false;
    }
    for part in parts {
        if part.is_empty() {
            return false;
        }
        if is_valid_cfg_identifier(part) {
            continue;
        }
        if part.chars().all(|c| c.is_ascii_digit()) {
            continue;
        }
        return false;
    }
    true
}

/// Strip TLA+ block comments (* ... *) from a line.
/// Handles multiple comments and nested comments are NOT supported (matches TLC behavior).
pub(super) fn strip_block_comments(line: &str) -> String {
    let mut result = String::with_capacity(line.len());
    let mut chars = line.chars().peekable();
    let mut in_comment = false;

    while let Some(c) = chars.next() {
        if in_comment {
            // Look for closing *)
            if c == '*' && chars.peek() == Some(&')') {
                chars.next(); // consume ')'
                in_comment = false;
            }
            // Skip character while in comment
        } else {
            // Look for opening (*
            if c == '(' && chars.peek() == Some(&'*') {
                chars.next(); // consume '*'
                in_comment = true;
            } else {
                result.push(c);
            }
        }
    }

    result
}
