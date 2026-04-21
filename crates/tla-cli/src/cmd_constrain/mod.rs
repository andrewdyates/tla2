// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `constrain` subcommand: generates constrained TLC config files by
//! analyzing a TLA+ specification and its constants.
//!
//! Three strategies are supported:
//!
//! - **Minimize** — suggests the smallest CONSTANT values that exercise all
//!   actions defined in the spec. Analyzes quantifier bounds and set
//!   membership to infer minimum useful sizes.
//!
//! - **Incremental** — generates a sequence of configs with progressively
//!   larger constant values (N=1, N=2, ...) for incremental verification.
//!
//! - **Symmetric** — detects model-value sets that are used symmetrically
//!   (no ordering, no distinguished elements) and emits SYMMETRY declarations.
//!
//! Usage:
//!   tla2 constrain Spec.tla --config Spec.cfg --strategy minimize
//!   tla2 constrain Spec.tla --config Spec.cfg --strategy incremental --output dir/
//!   tla2 constrain Spec.tla --config Spec.cfg --strategy symmetric

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;
use std::path::Path;

use anyhow::{bail, Context, Result};

// ── Strategy enum ───────────────────────────────────────────────────────────

/// Strategy for constraining a TLA+ configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstrainStrategy {
    /// Suggest the smallest CONSTANT values that exercise all actions.
    Minimize,
    /// Generate configs with progressively larger constants (N=1, N=2, ...).
    Incremental,
    /// Detect and add SYMMETRY declarations for model-value sets.
    Symmetric,
}

impl std::fmt::Display for ConstrainStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstrainStrategy::Minimize => write!(f, "minimize"),
            ConstrainStrategy::Incremental => write!(f, "incremental"),
            ConstrainStrategy::Symmetric => write!(f, "symmetric"),
        }
    }
}

// ── Internal analysis types ─────────────────────────────────────────────────

/// Information about a constant extracted from the .tla spec and .cfg file.
#[derive(Debug, Clone)]
struct ConstantInfo {
    /// Name of the constant as declared.
    name: String,
    /// Current value from the config file (if present).
    cfg_value: Option<CfgConstantKind>,
    /// Whether the constant is used as a quantifier bound (`\in 1..N`, `\in S`).
    used_as_bound: bool,
    /// Whether the constant appears inside a Cardinality() or similar size context.
    used_in_cardinality: bool,
    /// Set of action names where this constant appears.
    actions_referencing: BTreeSet<String>,
    /// Whether the constant names a set of model values.
    is_model_value_set: bool,
    /// Number of model values if it is a model-value set.
    model_value_count: Option<usize>,
    /// Whether the constant is used symmetrically (no ordering, no distinguished elements).
    appears_symmetric: bool,
}

/// Parsed constant kind from the .cfg file.
#[derive(Debug, Clone, PartialEq)]
enum CfgConstantKind {
    /// Integer assignment: `N = 3`
    Integer(i64),
    /// Non-integer value expression: `S = {a, b, c}`
    ValueExpr(String),
    /// Model value: `p <- [ model value ]`
    ModelValue,
    /// Set of model values: `Procs <- {p1, p2, p3}`
    ModelValueSet(Vec<String>),
    /// Operator replacement: `Op <- OtherOp`
    Replacement(String),
}

// ── Entry point ─────────────────────────────────────────────────────────────

/// Generate a constrained configuration file for faster model checking.
///
/// Reads both `file` (.tla) and `config` (.cfg), analyzes constant usage, and
/// emits a modified .cfg to `output` (or stdout if `None`).
pub(crate) fn cmd_constrain(
    file: &Path,
    config: &Path,
    strategy: ConstrainStrategy,
    output: Option<&Path>,
) -> Result<()> {
    if !file.exists() {
        bail!("spec file not found: {}", file.display());
    }
    if !config.exists() {
        bail!("config file not found: {}", config.display());
    }

    let tla_source = std::fs::read_to_string(file)
        .with_context(|| format!("read spec {}", file.display()))?;
    let cfg_text = std::fs::read_to_string(config)
        .with_context(|| format!("read config {}", config.display()))?;

    let cfg_lines = parse_cfg_lines(&cfg_text);
    let tla_constants = extract_tla_constants(&tla_source);
    let tla_variables = extract_tla_variables(&tla_source);
    let tla_actions = extract_tla_actions(&tla_source);

    let mut constants = build_constant_info(&tla_constants, &cfg_lines);
    analyze_constant_usage(&tla_source, &tla_actions, &tla_variables, &mut constants);

    match strategy {
        ConstrainStrategy::Minimize => {
            let result = generate_minimized_cfg(&cfg_text, &cfg_lines, &constants);
            emit_output(&result, output)?;
        }
        ConstrainStrategy::Incremental => {
            let configs = generate_incremental_cfgs(&cfg_text, &cfg_lines, &constants);
            if let Some(out_dir) = output {
                std::fs::create_dir_all(out_dir)
                    .with_context(|| format!("create output directory {}", out_dir.display()))?;
                for (i, cfg_content) in configs.iter().enumerate() {
                    let name = format!("step_{}.cfg", i + 1);
                    let path = out_dir.join(&name);
                    std::fs::write(&path, cfg_content)
                        .with_context(|| format!("write {}", path.display()))?;
                    eprintln!("Wrote {}", path.display());
                }
                eprintln!("Generated {} incremental configs in {}", configs.len(), out_dir.display());
            } else {
                // Print all configs separated by a marker line.
                for (i, cfg_content) in configs.iter().enumerate() {
                    if i > 0 {
                        println!("\\---- step {} ----", i + 1);
                    }
                    print!("{cfg_content}");
                }
            }
        }
        ConstrainStrategy::Symmetric => {
            let result = generate_symmetric_cfg(&cfg_text, &cfg_lines, &constants);
            emit_output(&result, output)?;
        }
    }

    Ok(())
}

// ── Output helper ───────────────────────────────────────────────────────────

fn emit_output(content: &str, output: Option<&Path>) -> Result<()> {
    match output {
        Some(path) => {
            std::fs::write(path, content)
                .with_context(|| format!("write output {}", path.display()))?;
            eprintln!("Wrote constrained config to {}", path.display());
        }
        None => {
            print!("{content}");
        }
    }
    Ok(())
}

// ── .cfg parsing (lightweight, line-oriented) ───────────────────────────────

/// A parsed line from the .cfg file.
#[derive(Debug, Clone)]
struct CfgLine {
    /// Original line text.
    text: String,
    /// Line number (0-indexed).
    lineno: usize,
    /// Parsed directive, if recognized.
    directive: Option<CfgDirective>,
}

#[derive(Debug, Clone)]
enum CfgDirective {
    Init(String),
    Next(String),
    Invariant(String),
    Property(String),
    Specification(String),
    Symmetry(String),
    Constraint(String),
    ActionConstraint(String),
    View(String),
    CheckDeadlock(bool),
    Constant { name: String, value: CfgConstantKind },
    Other(String),
}

fn parse_cfg_lines(cfg_text: &str) -> Vec<CfgLine> {
    let mut lines = Vec::new();
    let mut in_constants_block = false;

    for (lineno, raw_line) in cfg_text.lines().enumerate() {
        let trimmed = raw_line.trim();

        // Skip comments and blank lines for directive detection, but keep them.
        if trimmed.is_empty() || trimmed.starts_with("\\*") {
            in_constants_block = false;
            lines.push(CfgLine {
                text: raw_line.to_string(),
                lineno,
                directive: None,
            });
            continue;
        }

        let directive = parse_single_cfg_directive(trimmed, &mut in_constants_block);
        lines.push(CfgLine {
            text: raw_line.to_string(),
            lineno,
            directive,
        });
    }
    lines
}

fn parse_single_cfg_directive(trimmed: &str, in_constants_block: &mut bool) -> Option<CfgDirective> {
    // Section headers that start a constant block.
    if trimmed == "CONSTANT" || trimmed == "CONSTANTS" {
        *in_constants_block = true;
        return None;
    }

    // Inline CONSTANT directives.
    if let Some(rest) = strip_kw(trimmed, "CONSTANT").or_else(|| strip_kw(trimmed, "CONSTANTS")) {
        *in_constants_block = false;
        return parse_constant_directive(rest);
    }

    // Inside a CONSTANT block, bare assignments.
    if *in_constants_block {
        if is_known_directive_start(trimmed) {
            *in_constants_block = false;
            // Fall through to normal directive parsing below.
        } else {
            return parse_constant_directive(trimmed);
        }
    }

    // Non-constant directives.
    if let Some(rest) = strip_kw(trimmed, "INIT") {
        *in_constants_block = false;
        return Some(CfgDirective::Init(rest.to_string()));
    }
    if let Some(rest) = strip_kw(trimmed, "NEXT") {
        *in_constants_block = false;
        return Some(CfgDirective::Next(rest.to_string()));
    }
    if let Some(rest) = strip_kw(trimmed, "INVARIANT").or_else(|| strip_kw(trimmed, "INVARIANTS")) {
        *in_constants_block = false;
        return Some(CfgDirective::Invariant(rest.to_string()));
    }
    if let Some(rest) = strip_kw(trimmed, "PROPERTY").or_else(|| strip_kw(trimmed, "PROPERTIES")) {
        *in_constants_block = false;
        return Some(CfgDirective::Property(rest.to_string()));
    }
    if let Some(rest) = strip_kw(trimmed, "SPECIFICATION") {
        *in_constants_block = false;
        return Some(CfgDirective::Specification(rest.to_string()));
    }
    if let Some(rest) = strip_kw(trimmed, "SYMMETRY") {
        *in_constants_block = false;
        return Some(CfgDirective::Symmetry(rest.to_string()));
    }
    if let Some(rest) = strip_kw(trimmed, "CONSTRAINT").or_else(|| strip_kw(trimmed, "CONSTRAINTS")) {
        *in_constants_block = false;
        return Some(CfgDirective::Constraint(rest.to_string()));
    }
    if let Some(rest) =
        strip_kw(trimmed, "ACTION_CONSTRAINT").or_else(|| strip_kw(trimmed, "ACTION_CONSTRAINTS"))
    {
        *in_constants_block = false;
        return Some(CfgDirective::ActionConstraint(rest.to_string()));
    }
    if let Some(rest) = strip_kw(trimmed, "VIEW") {
        *in_constants_block = false;
        return Some(CfgDirective::View(rest.to_string()));
    }
    if let Some(rest) = strip_kw(trimmed, "CHECK_DEADLOCK") {
        *in_constants_block = false;
        let val = rest.trim().eq_ignore_ascii_case("true");
        return Some(CfgDirective::CheckDeadlock(val));
    }

    *in_constants_block = false;
    Some(CfgDirective::Other(trimmed.to_string()))
}

/// Strip a keyword prefix at a word boundary.
fn strip_kw<'a>(line: &'a str, kw: &str) -> Option<&'a str> {
    line.strip_prefix(kw).and_then(|rest| {
        if rest.is_empty() || rest.starts_with(|c: char| c.is_ascii_whitespace()) {
            Some(rest.trim_start())
        } else {
            None
        }
    })
}

fn is_known_directive_start(line: &str) -> bool {
    const DIRECTIVES: &[&str] = &[
        "INIT", "NEXT", "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES",
        "SPECIFICATION", "SYMMETRY", "CONSTRAINT", "CONSTRAINTS",
        "ACTION_CONSTRAINT", "ACTION_CONSTRAINTS", "CHECK_DEADLOCK", "VIEW",
        "CONSTANT", "CONSTANTS", "ALIAS", "TERMINAL", "POSTCONDITION",
    ];
    DIRECTIVES.iter().any(|kw| strip_kw(line, kw).is_some())
}

fn parse_constant_directive(text: &str) -> Option<CfgDirective> {
    let text = text.trim();
    if text.is_empty() {
        return None;
    }

    // Model value replacement: `Name <- [ model value ]` or `Name <- {v1, v2}`
    if let Some(arrow_pos) = text.find("<-") {
        let name = text[..arrow_pos].trim().to_string();
        let rhs = text[arrow_pos + 2..].trim();

        if rhs.contains("model value") {
            return Some(CfgDirective::Constant {
                name,
                value: CfgConstantKind::ModelValue,
            });
        }
        if rhs.starts_with('{') && rhs.ends_with('}') {
            let inner = &rhs[1..rhs.len() - 1];
            let values: Vec<String> = inner.split(',').map(|s| s.trim().to_string()).collect();
            return Some(CfgDirective::Constant {
                name,
                value: CfgConstantKind::ModelValueSet(values),
            });
        }
        return Some(CfgDirective::Constant {
            name,
            value: CfgConstantKind::Replacement(rhs.to_string()),
        });
    }

    // Value assignment: `Name = <expr>`
    if let Some(eq_pos) = text.find('=') {
        let name = text[..eq_pos].trim().to_string();
        let rhs = text[eq_pos + 1..].trim().to_string();
        let kind = if let Ok(n) = rhs.parse::<i64>() {
            CfgConstantKind::Integer(n)
        } else {
            CfgConstantKind::ValueExpr(rhs)
        };
        return Some(CfgDirective::Constant { name, value: kind });
    }

    None
}

// ── TLA+ source analysis (regex-based, lightweight) ─────────────────────────

/// Extract CONSTANT declarations from the .tla source.
fn extract_tla_constants(source: &str) -> Vec<String> {
    let mut constants = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if let Some(rest) = strip_kw(trimmed, "CONSTANT").or_else(|| strip_kw(trimmed, "CONSTANTS")) {
            for name in rest.split(',') {
                let name = name.trim().trim_end_matches(|c: char| c == '(' || c == '_');
                let name = name.trim();
                if !name.is_empty() && name.chars().next().map_or(false, |c| c.is_alphabetic()) {
                    constants.push(name.to_string());
                }
            }
        }
    }
    constants
}

/// Extract VARIABLE declarations from the .tla source.
fn extract_tla_variables(source: &str) -> Vec<String> {
    let mut variables = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if let Some(rest) = strip_kw(trimmed, "VARIABLE").or_else(|| strip_kw(trimmed, "VARIABLES")) {
            for name in rest.split(',') {
                let name = name.trim();
                if !name.is_empty() && name.chars().next().map_or(false, |c| c.is_alphabetic()) {
                    variables.push(name.to_string());
                }
            }
        }
    }
    variables
}

/// Extract operator definitions that look like actions (contain primed variables).
fn extract_tla_actions(source: &str) -> BTreeMap<String, String> {
    let mut actions = BTreeMap::new();
    let mut current_op: Option<(String, String)> = None;

    for line in source.lines() {
        let trimmed = line.trim();

        // Look for `OpName == ...` or `OpName(params) == ...`
        if let Some(eq_pos) = trimmed.find("==") {
            // Save previous operator.
            if let Some((name, body)) = current_op.take() {
                actions.insert(name, body);
            }

            let lhs = trimmed[..eq_pos].trim();
            let rhs = trimmed[eq_pos + 2..].trim();

            // Extract operator name (strip parameters).
            let op_name = lhs
                .split('(')
                .next()
                .unwrap_or(lhs)
                .trim()
                .to_string();

            if !op_name.is_empty() && op_name.chars().next().map_or(false, |c| c.is_alphabetic()) {
                current_op = Some((op_name, rhs.to_string()));
            }
        } else if let Some((_, ref mut body)) = current_op {
            // Continuation of current operator body.
            body.push('\n');
            body.push_str(trimmed);
        }
    }

    // Save final operator.
    if let Some((name, body)) = current_op {
        actions.insert(name, body);
    }

    actions
}

// ── Constant info construction ──────────────────────────────────────────────

fn build_constant_info(
    tla_constants: &[String],
    cfg_lines: &[CfgLine],
) -> Vec<ConstantInfo> {
    // Gather cfg constant assignments.
    let mut cfg_map: HashMap<String, CfgConstantKind> = HashMap::new();
    for line in cfg_lines {
        if let Some(CfgDirective::Constant { ref name, ref value }) = line.directive {
            cfg_map.insert(name.clone(), value.clone());
        }
    }

    let mut infos = Vec::new();
    // Include all constants from the TLA source.
    let mut seen: HashSet<String> = HashSet::new();
    for name in tla_constants {
        if seen.insert(name.clone()) {
            let cfg_value = cfg_map.remove(name);
            let is_model_value_set = matches!(cfg_value, Some(CfgConstantKind::ModelValueSet(_)));
            let model_value_count = match &cfg_value {
                Some(CfgConstantKind::ModelValueSet(vs)) => Some(vs.len()),
                _ => None,
            };
            infos.push(ConstantInfo {
                name: name.clone(),
                cfg_value,
                used_as_bound: false,
                used_in_cardinality: false,
                actions_referencing: BTreeSet::new(),
                is_model_value_set,
                model_value_count,
                appears_symmetric: false,
            });
        }
    }

    // Include constants from cfg that were not in the TLA source.
    for (name, value) in cfg_map {
        let is_model_value_set = matches!(value, CfgConstantKind::ModelValueSet(_));
        let model_value_count = match &value {
            CfgConstantKind::ModelValueSet(vs) => Some(vs.len()),
            _ => None,
        };
        infos.push(ConstantInfo {
            name,
            cfg_value: Some(value),
            used_as_bound: false,
            used_in_cardinality: false,
            actions_referencing: BTreeSet::new(),
            is_model_value_set,
            model_value_count,
            appears_symmetric: false,
        });
    }

    infos
}

// ── Constant usage analysis ─────────────────────────────────────────────────

fn analyze_constant_usage(
    source: &str,
    actions: &BTreeMap<String, String>,
    _variables: &[String],
    constants: &mut Vec<ConstantInfo>,
) {
    for info in constants.iter_mut() {
        // Check if the constant is used as a quantifier bound.
        // Patterns: `\in 1..N`, `\in S`, `\in SUBSET S`, `Cardinality(S)`
        let name = &info.name;

        // Bound usage: `\in 1..Name` or `\in Name` or `\in SUBSET Name`
        let bound_patterns = [
            format!("\\in 1..{name}"),
            format!("\\in 0..{name}"),
            format!("\\in {name}"),
            format!("\\in SUBSET {name}"),
        ];
        for pattern in &bound_patterns {
            if source.contains(pattern.as_str()) {
                info.used_as_bound = true;
                break;
            }
        }

        // Cardinality usage.
        let card_patterns = [
            format!("Cardinality({name})"),
            format!("Cardinality( {name} )"),
            format!("Len({name})"),
        ];
        for pattern in &card_patterns {
            if source.contains(pattern.as_str()) {
                info.used_in_cardinality = true;
                break;
            }
        }

        // Track which actions reference this constant.
        for (action_name, action_body) in actions {
            if action_body.contains(name.as_str()) {
                info.actions_referencing.insert(action_name.clone());
            }
        }

        // Symmetry detection for model-value sets:
        // A set is symmetric if no element is individually named in the source
        // outside of the set definition itself.
        if info.is_model_value_set {
            info.appears_symmetric = check_symmetry_eligibility(source, &info.cfg_value);
        }
    }
}

/// A model-value set is symmetric if none of its individual elements appear
/// outside the constant assignment context (no distinguished elements).
fn check_symmetry_eligibility(source: &str, cfg_value: &Option<CfgConstantKind>) -> bool {
    let values = match cfg_value {
        Some(CfgConstantKind::ModelValueSet(vs)) => vs,
        _ => return false,
    };

    // If any individual model value is referenced in the TLA+ source,
    // the set is NOT symmetric.
    for val in values {
        // Simple heuristic: check if the value name appears as a standalone
        // identifier in the source (not just inside a set literal).
        // We look for word-boundary occurrences.
        for line in source.lines() {
            let trimmed = line.trim();
            // Skip CONSTANT declarations and comments.
            if trimmed.starts_with("CONSTANT")
                || trimmed.starts_with("\\*")
                || trimmed.starts_with("(*")
            {
                continue;
            }
            if contains_word(trimmed, val) {
                return false;
            }
        }
    }

    true
}

/// Check if `text` contains `word` as a standalone identifier.
fn contains_word(text: &str, word: &str) -> bool {
    let mut start = 0;
    while let Some(pos) = text[start..].find(word) {
        let abs_pos = start + pos;
        let before_ok = abs_pos == 0
            || !text.as_bytes()[abs_pos - 1].is_ascii_alphanumeric()
                && text.as_bytes()[abs_pos - 1] != b'_';
        let after_pos = abs_pos + word.len();
        let after_ok = after_pos >= text.len()
            || !text.as_bytes()[after_pos].is_ascii_alphanumeric()
                && text.as_bytes()[after_pos] != b'_';
        if before_ok && after_ok {
            return true;
        }
        start = abs_pos + 1;
    }
    false
}

// ── Strategy: Minimize ──────────────────────────────────────────────────────

fn generate_minimized_cfg(
    cfg_text: &str,
    _cfg_lines: &[CfgLine],
    constants: &[ConstantInfo],
) -> String {
    let mut overrides: HashMap<String, String> = HashMap::new();
    let mut comments = Vec::new();

    for info in constants {
        match &info.cfg_value {
            Some(CfgConstantKind::Integer(n)) => {
                // For integer constants used as bounds, suggest minimum that
                // exercises all referencing actions. Heuristic: at least 2 if
                // used as a bound (need non-trivial range), at least 1 otherwise.
                let min_val = if info.used_as_bound {
                    // If the constant appears in multiple actions, we need at
                    // least 2 to exercise non-trivial interleaving.
                    if info.actions_referencing.len() > 1 { 2 } else { 2 }
                } else if info.used_in_cardinality {
                    1
                } else {
                    // Default: keep at 1 for minimal checking.
                    1
                };

                if *n > min_val {
                    overrides.insert(info.name.clone(), min_val.to_string());
                    comments.push(format!(
                        "\\* {} reduced from {} to {} ({})",
                        info.name,
                        n,
                        min_val,
                        if info.used_as_bound {
                            "bound variable"
                        } else if info.used_in_cardinality {
                            "cardinality context"
                        } else {
                            "minimal exercise"
                        },
                    ));
                }
            }
            Some(CfgConstantKind::ModelValueSet(vs)) if vs.len() > 2 => {
                // For model-value sets, 2 elements is usually the minimum
                // to exercise pair-wise interactions.
                let min_count = if info.used_as_bound { 2 } else { 2 };
                if vs.len() > min_count {
                    let reduced: Vec<String> = vs[..min_count].to_vec();
                    let set_str = format!("{{{}}}", reduced.join(", "));
                    overrides.insert(info.name.clone(), set_str);
                    comments.push(format!(
                        "\\* {} reduced from {} to {} model values",
                        info.name,
                        vs.len(),
                        min_count,
                    ));
                }
            }
            _ => {}
        }
    }

    if overrides.is_empty() {
        comments.push("\\* No reductions possible: constants already minimal.".to_string());
        return format!(
            "\\* Generated by: tla2 constrain --strategy minimize\n{}\n{}",
            comments.join("\n"),
            cfg_text,
        );
    }

    let mut result = String::new();
    let _ = writeln!(result, "\\* Generated by: tla2 constrain --strategy minimize");
    for c in &comments {
        let _ = writeln!(result, "{c}");
    }
    let _ = writeln!(result);

    // Rewrite the cfg with overrides applied.
    result.push_str(&apply_constant_overrides(cfg_text, &overrides));
    result
}

// ── Strategy: Incremental ───────────────────────────────────────────────────

fn generate_incremental_cfgs(
    cfg_text: &str,
    _cfg_lines: &[CfgLine],
    constants: &[ConstantInfo],
) -> Vec<String> {
    // Find integer constants and model-value-set constants that can scale.
    let scalable: Vec<&ConstantInfo> = constants
        .iter()
        .filter(|c| {
            matches!(
                c.cfg_value,
                Some(CfgConstantKind::Integer(_)) | Some(CfgConstantKind::ModelValueSet(_))
            )
        })
        .collect();

    if scalable.is_empty() {
        // Nothing to scale; return the original config.
        return vec![cfg_text.to_string()];
    }

    // Determine max value for each scalable constant.
    let max_steps: usize = scalable
        .iter()
        .map(|c| match &c.cfg_value {
            Some(CfgConstantKind::Integer(n)) => (*n).max(1) as usize,
            Some(CfgConstantKind::ModelValueSet(vs)) => vs.len(),
            _ => 1,
        })
        .max()
        .unwrap_or(1);

    // Generate configs for steps 1..=max_steps.
    let step_count = max_steps.min(10); // Cap at 10 incremental steps.
    let mut configs = Vec::with_capacity(step_count);

    for step in 1..=step_count {
        let mut overrides: HashMap<String, String> = HashMap::new();

        for info in &scalable {
            match &info.cfg_value {
                Some(CfgConstantKind::Integer(max_n)) => {
                    // Scale linearly: at step i out of N, use ceil(max * i / N).
                    let scaled = (((*max_n as f64) * (step as f64)) / (step_count as f64))
                        .ceil() as i64;
                    let scaled = scaled.max(1);
                    overrides.insert(info.name.clone(), scaled.to_string());
                }
                Some(CfgConstantKind::ModelValueSet(vs)) => {
                    // Use first `step` elements (capped at set size).
                    let count = step.min(vs.len()).max(1);
                    let subset: Vec<String> = vs[..count].to_vec();
                    let set_str = format!("{{{}}}", subset.join(", "));
                    overrides.insert(info.name.clone(), set_str);
                }
                _ => {}
            }
        }

        let mut result = String::new();
        let _ = writeln!(
            result,
            "\\* Generated by: tla2 constrain --strategy incremental (step {}/{})",
            step, step_count,
        );
        result.push_str(&apply_constant_overrides(cfg_text, &overrides));
        configs.push(result);
    }

    configs
}

// ── Strategy: Symmetric ─────────────────────────────────────────────────────

fn generate_symmetric_cfg(
    cfg_text: &str,
    cfg_lines: &[CfgLine],
    constants: &[ConstantInfo],
) -> String {
    // Find existing SYMMETRY declaration.
    let has_symmetry = cfg_lines
        .iter()
        .any(|l| matches!(l.directive, Some(CfgDirective::Symmetry(_))));

    // Find model-value sets eligible for symmetry.
    let symmetric_sets: Vec<&ConstantInfo> = constants
        .iter()
        .filter(|c| c.is_model_value_set && c.appears_symmetric)
        .collect();

    if symmetric_sets.is_empty() {
        let mut result = String::new();
        let _ = writeln!(result, "\\* Generated by: tla2 constrain --strategy symmetric");
        let _ = writeln!(result, "\\* No model-value sets eligible for SYMMETRY detected.");
        let _ = writeln!(result);
        result.push_str(cfg_text);
        return result;
    }

    let mut result = String::new();
    let _ = writeln!(result, "\\* Generated by: tla2 constrain --strategy symmetric");

    for info in &symmetric_sets {
        let _ = writeln!(
            result,
            "\\* {} ({} elements) detected as symmetric",
            info.name,
            info.model_value_count.unwrap_or(0),
        );
    }
    let _ = writeln!(result);

    // Emit the original config.
    result.push_str(cfg_text);
    if !result.ends_with('\n') {
        result.push('\n');
    }

    // Add SYMMETRY declarations for eligible sets (if not already present).
    if !has_symmetry {
        let _ = writeln!(result);
        for info in &symmetric_sets {
            // TLC convention: SYMMETRY Perms_<SetName>
            // The user must define `Perms_X == Permutations(X)` in the spec.
            let sym_name = format!("Perms_{}", info.name);
            let _ = writeln!(result, "\\* Add to spec: {} == Permutations({})", sym_name, info.name);
            let _ = writeln!(result, "SYMMETRY {sym_name}");
        }
    }

    result
}

// ── .cfg rewriting ──────────────────────────────────────────────────────────

/// Apply a map of constant name -> new value string to a .cfg file.
///
/// For model-value-set overrides, the value string should be `{v1, v2}`.
/// For integer overrides, a bare number.
fn apply_constant_overrides(cfg_text: &str, overrides: &HashMap<String, String>) -> String {
    if overrides.is_empty() {
        return cfg_text.to_string();
    }

    let mut result = cfg_text.to_string();
    for (name, new_value) in overrides {
        result = override_single_constant(&result, name, new_value);
    }

    if !result.ends_with('\n') {
        result.push('\n');
    }
    result
}

/// Replace a single constant assignment in a .cfg text.
fn override_single_constant(cfg_text: &str, name: &str, new_value: &str) -> String {
    let mut lines: Vec<String> = cfg_text.lines().map(String::from).collect();
    let mut found = false;

    for line in &mut lines {
        let trimmed = line.trim();

        // Handle `CONSTANT Name = <old>` or `CONSTANTS Name = <old>`.
        if trimmed.starts_with("CONSTANT") {
            let rest = trimmed
                .strip_prefix("CONSTANTS")
                .or_else(|| trimmed.strip_prefix("CONSTANT"));
            if let Some(rest) = rest {
                let rest = rest.trim();
                if let Some(after_name) = rest.strip_prefix(name) {
                    let after_name = after_name.trim_start();
                    if after_name.starts_with('=') {
                        *line = format!("CONSTANT {} = {}", name, new_value);
                        found = true;
                        continue;
                    }
                    if after_name.starts_with("<-") && new_value.starts_with('{') {
                        *line = format!("CONSTANT {} <- {}", name, new_value);
                        found = true;
                        continue;
                    }
                }
            }
        } else {
            // Bare `Name = <old>` inside a CONSTANT block.
            if let Some(after_name) = trimmed.strip_prefix(name) {
                let after_name = after_name.trim_start();
                if after_name.starts_with('=') {
                    *line = format!("{} = {}", name, new_value);
                    found = true;
                } else if after_name.starts_with("<-") && new_value.starts_with('{') {
                    *line = format!("{} <- {}", name, new_value);
                    found = true;
                }
            }
        }
    }

    if !found {
        // Append a new CONSTANT line.
        lines.push(format!("CONSTANT {} = {}", name, new_value));
    }

    let mut out = lines.join("\n");
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

// ── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // -- ConstrainStrategy Display -----------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_strategy_display() {
        assert_eq!(ConstrainStrategy::Minimize.to_string(), "minimize");
        assert_eq!(ConstrainStrategy::Incremental.to_string(), "incremental");
        assert_eq!(ConstrainStrategy::Symmetric.to_string(), "symmetric");
    }

    // -- cfg parsing -------------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parse_cfg_inline_constant() {
        let cfg = "INIT Init\nNEXT Next\nCONSTANT N = 3\nINVARIANT TypeOK\n";
        let lines = parse_cfg_lines(cfg);
        let constants: Vec<_> = lines
            .iter()
            .filter_map(|l| match &l.directive {
                Some(CfgDirective::Constant { name, value }) => Some((name.clone(), value.clone())),
                _ => None,
            })
            .collect();
        assert_eq!(constants.len(), 1);
        assert_eq!(constants[0].0, "N");
        assert_eq!(constants[0].1, CfgConstantKind::Integer(3));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parse_cfg_block_constants() {
        let cfg = "CONSTANT\nN = 5\nM = 10\nINVARIANT TypeOK\n";
        let lines = parse_cfg_lines(cfg);
        let constants: Vec<_> = lines
            .iter()
            .filter_map(|l| match &l.directive {
                Some(CfgDirective::Constant { name, .. }) => Some(name.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(constants, vec!["N", "M"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parse_cfg_model_value_set() {
        let cfg = "CONSTANT Procs <- {p1, p2, p3}\n";
        let lines = parse_cfg_lines(cfg);
        let constants: Vec<_> = lines
            .iter()
            .filter_map(|l| match &l.directive {
                Some(CfgDirective::Constant { name, value }) => Some((name.clone(), value.clone())),
                _ => None,
            })
            .collect();
        assert_eq!(constants.len(), 1);
        assert_eq!(constants[0].0, "Procs");
        assert!(matches!(constants[0].1, CfgConstantKind::ModelValueSet(ref vs) if vs.len() == 3));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_parse_cfg_model_value() {
        let cfg = "CONSTANT p <- [ model value ]\n";
        let lines = parse_cfg_lines(cfg);
        let constants: Vec<_> = lines
            .iter()
            .filter_map(|l| match &l.directive {
                Some(CfgDirective::Constant { name, value }) => Some((name.clone(), value.clone())),
                _ => None,
            })
            .collect();
        assert_eq!(constants.len(), 1);
        assert_eq!(constants[0].0, "p");
        assert_eq!(constants[0].1, CfgConstantKind::ModelValue);
    }

    // -- TLA+ extraction ---------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_extract_tla_constants() {
        let src = "CONSTANT N, M\nVARIABLE x\nCONSTANTS Procs\n";
        let consts = extract_tla_constants(src);
        assert_eq!(consts, vec!["N", "M", "Procs"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_extract_tla_variables() {
        let src = "VARIABLE x, y\nVARIABLES z\n";
        let vars = extract_tla_variables(src);
        assert_eq!(vars, vec!["x", "y", "z"]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_extract_tla_actions() {
        let src = "Init == x = 0\nNext == x' = x + 1\n";
        let actions = extract_tla_actions(src);
        assert!(actions.contains_key("Init"));
        assert!(actions.contains_key("Next"));
        assert!(actions["Next"].contains("x'"));
    }

    // -- contains_word -----------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_contains_word_basic() {
        assert!(contains_word("foo bar baz", "bar"));
        assert!(!contains_word("foobar baz", "bar"));
        assert!(!contains_word("foo barbaz", "bar"));
        assert!(contains_word("bar", "bar"));
        assert!(contains_word("bar baz", "bar"));
        assert!(contains_word("foo bar", "bar"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_contains_word_with_operators() {
        assert!(contains_word("x \\in S", "S"));
        assert!(!contains_word("x \\in SUBSET", "S"));
        assert!(contains_word("Cardinality(S)", "S"));
    }

    // -- Symmetry detection ------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symmetry_eligible_no_individual_refs() {
        let source = "VARIABLE x\nInit == x \\in Procs\n";
        let cfg_val = Some(CfgConstantKind::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
        ]));
        assert!(check_symmetry_eligibility(source, &cfg_val));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symmetry_not_eligible_individual_ref() {
        let source = "VARIABLE x\nInit == x = p1\n";
        let cfg_val = Some(CfgConstantKind::ModelValueSet(vec![
            "p1".to_string(),
            "p2".to_string(),
        ]));
        assert!(!check_symmetry_eligibility(source, &cfg_val));
    }

    // -- override_single_constant ------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_override_inline_constant() {
        let cfg = "INIT Init\nCONSTANT N = 5\nNEXT Next\n";
        let result = override_single_constant(cfg, "N", "2");
        assert!(result.contains("CONSTANT N = 2"), "got: {result}");
        assert!(!result.contains("N = 5"), "old value remains: {result}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_override_block_constant() {
        let cfg = "CONSTANT\nN = 10\nM = 5\n";
        let result = override_single_constant(cfg, "N", "3");
        assert!(result.contains("N = 3"), "got: {result}");
        assert!(result.contains("M = 5"), "M untouched: {result}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_override_absent_constant_appends() {
        let cfg = "INIT Init\nNEXT Next\n";
        let result = override_single_constant(cfg, "K", "7");
        assert!(result.contains("CONSTANT K = 7"), "got: {result}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_override_model_value_set() {
        let cfg = "CONSTANT Procs <- {p1, p2, p3}\n";
        let result = override_single_constant(cfg, "Procs", "{p1, p2}");
        assert!(result.contains("Procs <- {p1, p2}"), "got: {result}");
        assert!(!result.contains("p3"), "p3 should be removed: {result}");
    }

    // -- Minimize strategy -------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_minimize_reduces_integer() {
        let cfg_text = "INIT Init\nNEXT Next\nCONSTANT N = 10\n";
        let tla_source = "CONSTANT N\nVARIABLE x\nInit == x \\in 1..N\n";
        let cfg_lines = parse_cfg_lines(cfg_text);
        let tla_constants = extract_tla_constants(tla_source);
        let tla_variables = extract_tla_variables(tla_source);
        let tla_actions = extract_tla_actions(tla_source);
        let mut constants = build_constant_info(&tla_constants, &cfg_lines);
        analyze_constant_usage(tla_source, &tla_actions, &tla_variables, &mut constants);

        let result = generate_minimized_cfg(cfg_text, &cfg_lines, &constants);
        assert!(result.contains("N = 2"), "should reduce N to 2: {result}");
        assert!(!result.contains("N = 10"), "old value gone: {result}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_minimize_no_reduction_when_already_small() {
        let cfg_text = "CONSTANT N = 1\n";
        let tla_source = "CONSTANT N\n";
        let cfg_lines = parse_cfg_lines(cfg_text);
        let tla_constants = extract_tla_constants(tla_source);
        let tla_variables = extract_tla_variables(tla_source);
        let tla_actions = extract_tla_actions(tla_source);
        let mut constants = build_constant_info(&tla_constants, &cfg_lines);
        analyze_constant_usage(tla_source, &tla_actions, &tla_variables, &mut constants);

        let result = generate_minimized_cfg(cfg_text, &cfg_lines, &constants);
        assert!(
            result.contains("No reductions possible"),
            "should report no reductions: {result}"
        );
    }

    // -- Incremental strategy ----------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_incremental_generates_steps() {
        let cfg_text = "INIT Init\nNEXT Next\nCONSTANT N = 4\n";
        let tla_source = "CONSTANT N\n";
        let cfg_lines = parse_cfg_lines(cfg_text);
        let tla_constants = extract_tla_constants(tla_source);
        let tla_variables = extract_tla_variables(tla_source);
        let tla_actions = extract_tla_actions(tla_source);
        let mut constants = build_constant_info(&tla_constants, &cfg_lines);
        analyze_constant_usage(tla_source, &tla_actions, &tla_variables, &mut constants);

        let configs = generate_incremental_cfgs(cfg_text, &cfg_lines, &constants);
        assert_eq!(configs.len(), 4, "should generate 4 steps");
        // First step should have N=1, last should have N=4.
        assert!(configs[0].contains("N = 1"), "step 1: {}", configs[0]);
        assert!(configs[3].contains("N = 4"), "step 4: {}", configs[3]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_incremental_no_scalable_constants() {
        let cfg_text = "INIT Init\nNEXT Next\n";
        let tla_source = "";
        let cfg_lines = parse_cfg_lines(cfg_text);
        let tla_constants = extract_tla_constants(tla_source);
        let tla_variables = extract_tla_variables(tla_source);
        let tla_actions = extract_tla_actions(tla_source);
        let mut constants = build_constant_info(&tla_constants, &cfg_lines);
        analyze_constant_usage(tla_source, &tla_actions, &tla_variables, &mut constants);

        let configs = generate_incremental_cfgs(cfg_text, &cfg_lines, &constants);
        assert_eq!(configs.len(), 1, "fallback to single config");
    }

    // -- Symmetric strategy ------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symmetric_detects_eligible_set() {
        let cfg_text = "CONSTANT Procs <- {p1, p2, p3}\nINIT Init\nNEXT Next\n";
        let tla_source = "CONSTANT Procs\nVARIABLE x\nInit == x \\in Procs\n";
        let cfg_lines = parse_cfg_lines(cfg_text);
        let tla_constants = extract_tla_constants(tla_source);
        let tla_variables = extract_tla_variables(tla_source);
        let tla_actions = extract_tla_actions(tla_source);
        let mut constants = build_constant_info(&tla_constants, &cfg_lines);
        analyze_constant_usage(tla_source, &tla_actions, &tla_variables, &mut constants);

        let result = generate_symmetric_cfg(cfg_text, &cfg_lines, &constants);
        assert!(result.contains("SYMMETRY"), "should add SYMMETRY: {result}");
        assert!(result.contains("Perms_Procs"), "should suggest Perms_Procs: {result}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symmetric_skips_asymmetric_set() {
        let cfg_text = "CONSTANT Procs <- {p1, p2, p3}\nINIT Init\nNEXT Next\n";
        // p1 is referenced individually, breaking symmetry.
        let tla_source = "CONSTANT Procs\nVARIABLE x\nInit == x = p1\n";
        let cfg_lines = parse_cfg_lines(cfg_text);
        let tla_constants = extract_tla_constants(tla_source);
        let tla_variables = extract_tla_variables(tla_source);
        let tla_actions = extract_tla_actions(tla_source);
        let mut constants = build_constant_info(&tla_constants, &cfg_lines);
        analyze_constant_usage(tla_source, &tla_actions, &tla_variables, &mut constants);

        let result = generate_symmetric_cfg(cfg_text, &cfg_lines, &constants);
        assert!(
            result.contains("No model-value sets eligible"),
            "should report no eligible sets: {result}"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_symmetric_preserves_existing_symmetry() {
        let cfg_text = "CONSTANT S <- {s1, s2}\nSYMMETRY Perms_S\nINIT Init\nNEXT Next\n";
        let tla_source = "CONSTANT S\nVARIABLE x\nInit == x \\in S\n";
        let cfg_lines = parse_cfg_lines(cfg_text);
        let tla_constants = extract_tla_constants(tla_source);
        let tla_variables = extract_tla_variables(tla_source);
        let tla_actions = extract_tla_actions(tla_source);
        let mut constants = build_constant_info(&tla_constants, &cfg_lines);
        analyze_constant_usage(tla_source, &tla_actions, &tla_variables, &mut constants);

        let result = generate_symmetric_cfg(cfg_text, &cfg_lines, &constants);
        // Should not add a duplicate SYMMETRY line.
        let symmetry_count = result.matches("SYMMETRY").count();
        // The original line + generated comment both contain "SYMMETRY"; the
        // key invariant is that no *new* SYMMETRY directive line is added.
        let directive_lines: Vec<_> = result
            .lines()
            .filter(|l| {
                let t = l.trim();
                t.starts_with("SYMMETRY") && !t.starts_with("\\*")
            })
            .collect();
        assert_eq!(
            directive_lines.len(),
            1,
            "should have exactly one SYMMETRY directive, got: {directive_lines:?}\nfull:\n{result}"
        );
    }

    // -- apply_constant_overrides ------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_apply_multiple_overrides() {
        let cfg = "CONSTANT\nN = 10\nM = 5\n";
        let mut overrides = HashMap::new();
        overrides.insert("N".to_string(), "2".to_string());
        overrides.insert("M".to_string(), "1".to_string());
        let result = apply_constant_overrides(cfg, &overrides);
        assert!(result.contains("N = 2"), "N override: {result}");
        assert!(result.contains("M = 1"), "M override: {result}");
    }

    // -- strip_kw ----------------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_strip_kw_word_boundary() {
        assert_eq!(strip_kw("CONSTANT N = 3", "CONSTANT"), Some("N = 3"));
        assert_eq!(strip_kw("CONSTANTS", "CONSTANT"), None);
        assert_eq!(strip_kw("CONSTANTS N", "CONSTANTS"), Some("N"));
        assert_eq!(strip_kw("INIT Init", "INIT"), Some("Init"));
        assert_eq!(strip_kw("INITIAL", "INIT"), None);
    }

    // -- analyze_constant_usage --------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_analyze_usage_detects_bound() {
        let source = "CONSTANT N\nVARIABLE x\nInit == x \\in 1..N\n";
        let actions = extract_tla_actions(source);
        let variables = extract_tla_variables(source);
        let cfg_lines = parse_cfg_lines("CONSTANT N = 5\n");
        let tla_consts = extract_tla_constants(source);
        let mut constants = build_constant_info(&tla_consts, &cfg_lines);
        analyze_constant_usage(source, &actions, &variables, &mut constants);

        let n = constants.iter().find(|c| c.name == "N").expect("N");
        assert!(n.used_as_bound, "N should be detected as bound variable");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_analyze_usage_detects_cardinality() {
        let source = "CONSTANT S\nInv == Cardinality(S) > 0\n";
        let actions = extract_tla_actions(source);
        let variables = extract_tla_variables(source);
        let cfg_lines = parse_cfg_lines("CONSTANT S = {1, 2}\n");
        let tla_consts = extract_tla_constants(source);
        let mut constants = build_constant_info(&tla_consts, &cfg_lines);
        analyze_constant_usage(source, &actions, &variables, &mut constants);

        let s = constants.iter().find(|c| c.name == "S").expect("S");
        assert!(s.used_in_cardinality, "S should be detected in cardinality context");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_analyze_usage_tracks_action_references() {
        let source = "CONSTANT N\nInit == x = N\nNext == x' = x + N\n";
        let actions = extract_tla_actions(source);
        let variables = extract_tla_variables(source);
        let cfg_lines = parse_cfg_lines("CONSTANT N = 3\n");
        let tla_consts = extract_tla_constants(source);
        let mut constants = build_constant_info(&tla_consts, &cfg_lines);
        analyze_constant_usage(source, &actions, &variables, &mut constants);

        let n = constants.iter().find(|c| c.name == "N").expect("N");
        assert!(
            n.actions_referencing.contains("Init"),
            "N should be referenced in Init"
        );
        assert!(
            n.actions_referencing.contains("Next"),
            "N should be referenced in Next"
        );
    }
}
