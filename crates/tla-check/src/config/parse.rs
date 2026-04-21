// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Configuration file (.cfg) parser: BlockContext and Config::parse().

use super::constants::{is_valid_cfg_identifier, parse_constant_assignment, strip_block_comments};
use super::types::{Config, ConfigError, TerminalSpec};

/// Strip a directive keyword from the start of a line, only if at a word boundary.
/// The keyword must be followed by whitespace or end-of-string — prevents
/// `"NEXTSTATE"` from matching the `"NEXT"` directive (fixes #2848).
pub(super) fn strip_directive_prefix<'a>(line: &'a str, keyword: &str) -> Option<&'a str> {
    line.strip_prefix(keyword).and_then(|rest| {
        if rest.is_empty() || rest.starts_with(|c: char| c.is_ascii_whitespace()) {
            Some(rest)
        } else {
            None
        }
    })
}

/// Check if a line starts with any known directive keyword at a word boundary.
fn is_directive_line(line: &str) -> bool {
    const DIRECTIVES: &[&str] = &[
        "SPECIFICATION",
        "ACTION_CONSTRAINTS",
        "ACTION_CONSTRAINT",
        "CHECK_DEADLOCK",
        "POSTCONDITION",
        "INVARIANTS",
        "INVARIANT",
        "PROPERTIES",
        "PROPERTY",
        "CONSTRAINTS",
        "CONSTRAINT",
        "CONSTANTS",
        "CONSTANT",
        "SYMMETRY",
        "TERMINAL",
        "ALIAS",
        "INIT",
        "NEXT",
        "VIEW",
    ];
    DIRECTIVES
        .iter()
        .any(|kw| strip_directive_prefix(line, kw).is_some())
}

/// Block directive context for multi-line parsing
#[derive(Debug, Clone, Copy, PartialEq)]
enum BlockContext {
    None,
    Init,
    Next,
    Constants,
    Invariants,
    Properties,
    Specification,
    Symmetry,
    Constraints,
    ActionConstraints,
    Alias,
    CheckDeadlock,
    View,
    Terminal,
    Postcondition,
}

impl Config {
    /// Parse a configuration file from a string
    ///
    /// Supports multi-line block syntax for CONSTANTS:
    /// ```text
    /// CONSTANTS
    ///     Name = Value
    ///     Name2 = Value2
    /// ```
    pub fn parse(input: &str) -> Result<Config, Vec<ConfigError>> {
        let mut config = Config::new();
        let mut errors = Vec::new();
        let mut block_context = BlockContext::None;
        let mut pending_init_line: Option<usize> = None;
        let mut pending_next_line: Option<usize> = None;
        let mut check_deadlock_explicit = false;
        let mut in_block_comment = false;

        for (line_num, raw_line) in input.lines().enumerate() {
            let line_num = line_num + 1; // 1-indexed

            // Strip inline comments (everything after \*)
            let line_without_comment = if let Some(pos) = raw_line.find("\\*") {
                &raw_line[..pos]
            } else {
                raw_line
            };

            // Handle multi-line block comments (* ... *)
            // Track comment state across lines so comments spanning multiple lines
            // are correctly skipped (e.g., MCCRDT.cfg has a multi-line (* ... *) comment).
            let line_content = if in_block_comment {
                // We're inside a multi-line block comment — skip until *)
                if let Some(close_pos) = line_without_comment.find("*)") {
                    in_block_comment = false;
                    &line_without_comment[close_pos + 2..]
                } else {
                    // Entire line is inside the comment
                    ""
                }
            } else {
                line_without_comment
            };

            // Strip any remaining single-line block comments and check for unclosed ones
            let line_without_block_comment = strip_block_comments(line_content);
            // If strip_block_comments consumed an opening (* without finding *),
            // the rest of this line is in a comment that continues to the next line.
            if line_content.contains("(*") && !line_content.contains("*)") {
                in_block_comment = true;
            }
            let line = line_without_block_comment.trim();

            // Skip empty lines and comments
            if line.is_empty() || line.starts_with("(*") {
                continue;
            }

            // Check if line starts with a known directive keyword (this ends any block context).
            // Uses word boundary check to avoid "NEXTSTATE" matching "NEXT" (#2848).
            let is_directive = is_directive_line(line);

            // If we were in a block context that requires a value and we hit a new directive,
            // report a missing value error for the original directive line.
            if is_directive {
                if block_context == BlockContext::Init && config.init.is_none() {
                    errors.push(ConfigError::MissingInit {
                        line: pending_init_line.unwrap_or(line_num),
                    });
                    pending_init_line = None;
                }
                if block_context == BlockContext::Next && config.next.is_none() {
                    errors.push(ConfigError::MissingNext {
                        line: pending_next_line.unwrap_or(line_num),
                    });
                    pending_next_line = None;
                }
            }

            // Handle non-directive lines within a block context
            if !is_directive && block_context != BlockContext::None {
                handle_block_continuation(
                    &mut config,
                    &mut errors,
                    block_context,
                    line,
                    line_num,
                    &mut pending_init_line,
                    &mut pending_next_line,
                );
                continue;
            }

            // Directive line resets block context
            block_context = BlockContext::None;

            // Parse directive
            parse_directive(
                &mut config,
                &mut errors,
                &mut block_context,
                &mut check_deadlock_explicit,
                &mut pending_init_line,
                &mut pending_next_line,
                line,
                line_num,
            );
        }

        // If the file ends while still waiting for a block value, report it.
        if config.init.is_none() {
            if let Some(line) = pending_init_line {
                errors.push(ConfigError::MissingInit { line });
            }
        }
        if config.next.is_none() {
            if let Some(line) = pending_next_line {
                errors.push(ConfigError::MissingNext { line });
            }
        }

        // Store whether CHECK_DEADLOCK was explicitly set in the config.
        config.check_deadlock_explicit = check_deadlock_explicit;

        if errors.is_empty() {
            Ok(config)
        } else {
            Err(errors)
        }
    }
}

/// Handle a non-directive continuation line within a block context.
fn handle_block_continuation(
    config: &mut Config,
    errors: &mut Vec<ConfigError>,
    block_context: BlockContext,
    line: &str,
    line_num: usize,
    pending_init_line: &mut Option<usize>,
    pending_next_line: &mut Option<usize>,
) {
    match block_context {
        BlockContext::Init => {
            if !line.is_empty() && config.init.is_none() {
                config.init = Some(line.to_string());
                *pending_init_line = None;
            }
        }
        BlockContext::Next => {
            if !line.is_empty() && config.next.is_none() {
                config.next = Some(line.to_string());
                *pending_next_line = None;
            }
        }
        BlockContext::Constants => {
            if let Err(e) = parse_constant_assignment(config, line, line_num) {
                errors.push(e);
            }
        }
        BlockContext::Invariants => {
            for name in line.split_whitespace() {
                config.invariants.push(name.to_string());
            }
        }
        BlockContext::Properties => {
            for name in line.split_whitespace() {
                config.properties.push(name.to_string());
            }
        }
        BlockContext::Specification => {
            if !line.is_empty() && config.specification.is_none() {
                config.specification = Some(line.to_string());
            }
        }
        BlockContext::Symmetry => {
            if !line.is_empty() && config.symmetry.is_none() {
                config.symmetry = Some(line.to_string());
            }
        }
        BlockContext::Constraints => {
            for name in line.split_whitespace() {
                config.constraints.push(name.to_string());
            }
        }
        BlockContext::ActionConstraints => {
            for name in line.split_whitespace() {
                config.action_constraints.push(name.to_string());
            }
        }
        BlockContext::Alias => {
            if !line.is_empty() && config.alias.is_none() {
                config.alias = Some(line.to_string());
            }
        }
        BlockContext::CheckDeadlock => {
            let value = line.to_uppercase();
            if value == "FALSE" || value == "OFF" || value == "NO" {
                config.check_deadlock = false;
            } else if value == "TRUE" || value == "ON" || value == "YES" {
                config.check_deadlock = true;
            } else {
                errors.push(ConfigError::InvalidSyntax {
                    line: line_num,
                    directive: "CHECK_DEADLOCK",
                    text: line.to_string(),
                });
            }
        }
        BlockContext::View => {
            if !line.is_empty() && config.view.is_none() {
                config.view = Some(line.to_string());
            }
        }
        BlockContext::Terminal => {
            if let Some((var, val)) = line.split_once('=') {
                let var = var.trim().to_string();
                let val = val.trim().to_string();
                match &mut config.terminal {
                    Some(TerminalSpec::Predicates(preds)) => {
                        preds.push((var, val));
                    }
                    _ => {
                        config.terminal = Some(TerminalSpec::Predicates(vec![(var, val)]));
                    }
                }
            } else if is_valid_cfg_identifier(line) && config.terminal.is_none() {
                config.terminal = Some(TerminalSpec::Operator(line.to_string()));
            }
        }
        BlockContext::Postcondition => {
            if !line.is_empty() && config.postcondition.is_none() {
                config.postcondition = Some(line.to_string());
            }
        }
        BlockContext::None => {
            unreachable!("config parser: continuation with BlockContext::None")
        }
    }
}

/// Parse a single directive line, updating config and block_context.
#[allow(clippy::too_many_arguments)]
fn parse_directive(
    config: &mut Config,
    errors: &mut Vec<ConfigError>,
    block_context: &mut BlockContext,
    check_deadlock_explicit: &mut bool,
    pending_init_line: &mut Option<usize>,
    pending_next_line: &mut Option<usize>,
    line: &str,
    line_num: usize,
) {
    // All directive matching uses word-boundary-aware strip_directive_prefix (#2848).
    // Longer keywords are checked before shorter ones to avoid ambiguity
    // (e.g., INVARIANTS before INVARIANT, CONSTANTS before CONSTANT).
    if let Some(rest) = strip_directive_prefix(line, "SPECIFICATION") {
        let name = rest.trim().to_string();
        if name.is_empty() {
            *block_context = BlockContext::Specification;
        } else {
            config.specification = Some(name);
        }
    } else if let Some(rest) = strip_directive_prefix(line, "ACTION_CONSTRAINTS")
        .or_else(|| strip_directive_prefix(line, "ACTION_CONSTRAINT"))
    {
        let rest = rest.trim();
        if rest.is_empty() {
            *block_context = BlockContext::ActionConstraints;
        } else {
            for name in rest.split(',') {
                let name = name.trim().to_string();
                if !name.is_empty() {
                    config.action_constraints.push(name);
                }
            }
        }
    } else if let Some(rest) = strip_directive_prefix(line, "CHECK_DEADLOCK") {
        *check_deadlock_explicit = true;
        let value = rest.trim().to_uppercase();
        if value == "FALSE" || value == "OFF" || value == "NO" {
            config.check_deadlock = false;
        } else if value == "TRUE" || value == "ON" || value == "YES" {
            config.check_deadlock = true;
        } else if value.is_empty() {
            *block_context = BlockContext::CheckDeadlock;
        } else {
            // TLC rejects invalid CHECK_DEADLOCK values with CFG_EXPECTED_SYMBOL.
            errors.push(ConfigError::InvalidSyntax {
                line: line_num,
                directive: "CHECK_DEADLOCK",
                text: rest.trim().to_string(),
            });
        }
    } else if let Some(rest) = strip_directive_prefix(line, "POSTCONDITION") {
        let name = rest.trim().to_string();
        if name.is_empty() {
            *block_context = BlockContext::Postcondition;
        } else {
            config.postcondition = Some(name);
        }
    } else if let Some(rest) = strip_directive_prefix(line, "INVARIANTS")
        .or_else(|| strip_directive_prefix(line, "INVARIANT"))
    {
        let rest = rest.trim();
        if rest.is_empty() {
            *block_context = BlockContext::Invariants;
        } else {
            for part in rest.split(&[',', ' '][..]) {
                let name = part.trim().to_string();
                if !name.is_empty() {
                    config.invariants.push(name);
                }
            }
        }
    } else if let Some(rest) = strip_directive_prefix(line, "PROPERTIES")
        .or_else(|| strip_directive_prefix(line, "PROPERTY"))
    {
        let rest = rest.trim();
        if rest.is_empty() {
            *block_context = BlockContext::Properties;
        } else {
            for part in rest.split(&[',', ' '][..]) {
                let name = part.trim().to_string();
                if !name.is_empty() {
                    config.properties.push(name);
                }
            }
        }
    } else if let Some(rest) = strip_directive_prefix(line, "CONSTANTS")
        .or_else(|| strip_directive_prefix(line, "CONSTANT"))
    {
        let rest = rest.trim();
        if rest.is_empty() {
            *block_context = BlockContext::Constants;
        } else {
            if let Err(e) = parse_constant_assignment(config, rest, line_num) {
                errors.push(e);
            }
            *block_context = BlockContext::Constants;
        }
    } else if let Some(rest) = strip_directive_prefix(line, "CONSTRAINTS")
        .or_else(|| strip_directive_prefix(line, "CONSTRAINT"))
    {
        let rest = rest.trim();
        if rest.is_empty() {
            *block_context = BlockContext::Constraints;
        } else {
            for name in rest.split(',') {
                let name = name.trim().to_string();
                if !name.is_empty() {
                    config.constraints.push(name);
                }
            }
        }
    } else if let Some(rest) = strip_directive_prefix(line, "SYMMETRY") {
        let name = rest.trim().to_string();
        if name.is_empty() {
            *block_context = BlockContext::Symmetry;
        } else {
            config.symmetry = Some(name);
        }
    } else if let Some(rest) = strip_directive_prefix(line, "TERMINAL") {
        let rest = rest.trim();
        if rest.is_empty() {
            *block_context = BlockContext::Terminal;
        } else if let Some((var, val)) = rest.split_once('=') {
            let var = var.trim().to_string();
            let val = val.trim().to_string();
            config.terminal = Some(TerminalSpec::Predicates(vec![(var, val)]));
            *block_context = BlockContext::Terminal;
        } else if is_valid_cfg_identifier(rest) {
            config.terminal = Some(TerminalSpec::Operator(rest.to_string()));
        } else {
            errors.push(ConfigError::InvalidSyntax {
                line: line_num,
                directive: "TERMINAL",
                text: rest.to_string(),
            });
        }
    } else if let Some(rest) = strip_directive_prefix(line, "ALIAS") {
        let name = rest.trim().to_string();
        if name.is_empty() {
            *block_context = BlockContext::Alias;
        } else {
            config.alias = Some(name);
        }
    } else if let Some(rest) = strip_directive_prefix(line, "INIT") {
        let name = rest.trim().to_string();
        if name.is_empty() {
            *block_context = BlockContext::Init;
            *pending_init_line = Some(line_num);
        } else {
            config.init = Some(name);
            *pending_init_line = None;
        }
    } else if let Some(rest) = strip_directive_prefix(line, "NEXT") {
        let name = rest.trim().to_string();
        if name.is_empty() {
            *block_context = BlockContext::Next;
            *pending_next_line = Some(line_num);
        } else {
            config.next = Some(name);
            *pending_next_line = None;
        }
    } else if let Some(rest) = strip_directive_prefix(line, "VIEW") {
        let name = rest.trim().to_string();
        if name.is_empty() {
            *block_context = BlockContext::View;
        } else {
            config.view = Some(name);
        }
    } else {
        errors.push(ConfigError::UnknownDirective {
            line: line_num,
            text: line.to_string(),
        });
    }
}
