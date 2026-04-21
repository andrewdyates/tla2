// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 refactor` -- automated TLA+ spec refactoring.
//!
//! Performs semantic-preserving transformations on TLA+ specs at the AST level:
//!
//! - **extract-operator**: Extract an expression into a new named operator.
//! - **rename**: Rename an operator/variable/constant throughout the spec.
//! - **inline**: Replace all uses of a simple operator with its definition, then remove it.
//! - **cleanup**: Remove all unused operators (those not reachable from Init, Next, or invariants).

use std::collections::{HashMap, HashSet};
use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower_main_module, parse, parse_error_diagnostic, FileId, SyntaxNode};

use crate::cli_schema::RefactorAction;
use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub(crate) fn cmd_refactor(action: RefactorAction) -> Result<()> {
    match action {
        RefactorAction::ExtractOperator {
            file,
            expr,
            name,
            output,
            in_place,
            no_preview,
        } => {
            let result = refactor_extract_operator(&file, &expr, &name)?;
            emit_result(&file, &result, output.as_deref(), in_place, no_preview)
        }
        RefactorAction::Rename {
            file,
            from,
            to,
            output,
            in_place,
            no_preview,
        } => {
            let result = refactor_rename(&file, &from, &to)?;
            emit_result(&file, &result, output.as_deref(), in_place, no_preview)
        }
        RefactorAction::Inline {
            file,
            name,
            output,
            in_place,
            no_preview,
        } => {
            let result = refactor_inline(&file, &name)?;
            emit_result(&file, &result, output.as_deref(), in_place, no_preview)
        }
        RefactorAction::Cleanup {
            file,
            config,
            output,
            in_place,
            no_preview,
        } => {
            let result = refactor_cleanup(&file, config.as_deref())?;
            emit_result(&file, &result, output.as_deref(), in_place, no_preview)
        }
    }
}

// ---------------------------------------------------------------------------
// Output emission
// ---------------------------------------------------------------------------

/// Emit the refactored source: preview diff, write to stdout/file/in-place.
fn emit_result(
    original_file: &Path,
    new_source: &str,
    output_path: Option<&Path>,
    in_place: bool,
    no_preview: bool,
) -> Result<()> {
    let original_source = read_source(original_file)?;

    if !no_preview && original_source != new_source {
        print_diff(&original_source, new_source, original_file);
    }

    if in_place {
        std::fs::write(original_file, new_source)
            .with_context(|| format!("write {}", original_file.display()))?;
        eprintln!("Wrote {}", original_file.display());
    } else if let Some(out) = output_path {
        std::fs::write(out, new_source)
            .with_context(|| format!("write {}", out.display()))?;
        eprintln!("Wrote {}", out.display());
    } else if no_preview {
        // If --no-preview and no --output/--in-place, dump to stdout
        print!("{new_source}");
    }

    Ok(())
}

/// Print a simple unified diff between old and new source.
fn print_diff(old: &str, new: &str, file: &Path) {
    let old_lines: Vec<&str> = old.lines().collect();
    let new_lines: Vec<&str> = new.lines().collect();

    eprintln!("--- {}", file.display());
    eprintln!("+++ {} (refactored)", file.display());

    // Simple line-by-line diff: find contiguous changed regions
    let max_len = old_lines.len().max(new_lines.len());
    let mut i = 0;
    while i < max_len {
        let old_line = old_lines.get(i).copied().unwrap_or("");
        let new_line = new_lines.get(i).copied().unwrap_or("");
        if old_line != new_line {
            // Found a difference, print context
            let ctx_start = i.saturating_sub(2);
            let ctx_end = (i + 3).min(max_len);
            eprintln!(
                "@@ -{},{} +{},{} @@",
                ctx_start + 1,
                ctx_end - ctx_start,
                ctx_start + 1,
                ctx_end - ctx_start,
            );
            for j in ctx_start..ctx_end {
                let ol = old_lines.get(j).copied().unwrap_or("");
                let nl = new_lines.get(j).copied().unwrap_or("");
                if ol == nl {
                    eprintln!(" {ol}");
                } else {
                    if j < old_lines.len() {
                        eprintln!("-{ol}");
                    }
                    if j < new_lines.len() {
                        eprintln!("+{nl}");
                    }
                }
            }
            // Skip past this hunk
            i = ctx_end;
        } else {
            i += 1;
        }
    }
}

// ---------------------------------------------------------------------------
// Parsing helper
// ---------------------------------------------------------------------------

/// Parse a TLA+ file into source text + lowered module.
fn parse_and_lower(file: &Path) -> Result<(String, Module)> {
    let source = read_source(file)?;
    let parse_result = parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diag =
                parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diag.eprint(&file_path, &source);
        }
        bail!("parse failed with {} error(s)", parse_result.errors.len());
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let lower_result = lower_main_module(FileId(0), &tree, hint_name);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diag = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diag.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("lowering produced no module")?;
    Ok((source, module))
}

// ---------------------------------------------------------------------------
// Extract operator
// ---------------------------------------------------------------------------

/// Extract an expression string into a new named operator.
///
/// Finds all occurrences of `expr_text` in the source and replaces them
/// with a reference to a new operator `NewName == <expr>` inserted before
/// the first operator in the module.
fn refactor_extract_operator(file: &Path, expr_text: &str, new_name: &str) -> Result<String> {
    let (source, module) = parse_and_lower(file)?;

    // Validate new_name is not already defined
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            if op.name.node == new_name {
                bail!(
                    "operator `{new_name}` already exists at line {}",
                    line_of_offset(&source, op.name.span.start)
                );
            }
        }
    }

    // Find occurrences of the expression text in the source
    let trimmed = expr_text.trim();
    if trimmed.is_empty() {
        bail!("--expr must be a non-empty expression string");
    }

    let occurrences: Vec<usize> = source
        .match_indices(trimmed)
        .map(|(idx, _)| idx)
        .collect();

    if occurrences.is_empty() {
        bail!(
            "expression `{trimmed}` not found in {}",
            file.display()
        );
    }

    // Find insertion point: just before the first operator definition
    let insert_offset = find_operator_insert_point(&source, &module);

    // Build the new operator definition line
    let new_op_line = format!("{new_name} == {trimmed}\n\n");

    // Perform replacements from end to start to preserve offsets
    let mut result = source.clone();

    // First replace all occurrences of the expression with the new name
    let mut sorted_occurrences = occurrences;
    sorted_occurrences.sort_unstable();
    sorted_occurrences.reverse();
    for offset in &sorted_occurrences {
        let start = *offset;
        let end = start + trimmed.len();
        result.replace_range(start..end, new_name);
    }

    // Now insert the new operator definition. Adjust insert_offset for
    // replacements that occurred before it.
    let mut adjusted_insert = insert_offset;
    for offset in sorted_occurrences.iter().rev() {
        if *offset < insert_offset {
            // This replacement happened before the insert point
            let len_diff = new_name.len() as isize - trimmed.len() as isize;
            adjusted_insert = (adjusted_insert as isize + len_diff) as usize;
        }
    }
    result.insert_str(adjusted_insert, &new_op_line);

    Ok(result)
}

/// Find a good insertion point for a new operator definition.
/// Returns the byte offset just before the first operator definition,
/// or just before the `====` module end marker.
fn find_operator_insert_point(source: &str, module: &Module) -> usize {
    // Find the first operator definition
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            // Go to the start of the line containing this operator
            let offset = op.name.span.start as usize;
            return line_start_of(source, offset);
        }
    }
    // No operators found; insert before the module end marker
    if let Some(end_pos) = source.find("====") {
        return end_pos;
    }
    source.len()
}

// ---------------------------------------------------------------------------
// Rename
// ---------------------------------------------------------------------------

/// Rename an operator, variable, or constant throughout the spec.
///
/// Uses AST analysis to find the definition and all references, then performs
/// text-level replacement at each identified span.
fn refactor_rename(file: &Path, from: &str, to: &str) -> Result<String> {
    let (source, module) = parse_and_lower(file)?;

    if from == to {
        bail!("--from and --to are the same: `{from}`");
    }

    // Check that `to` doesn't already exist
    for unit in &module.units {
        match &unit.node {
            Unit::Operator(op) if op.name.node == to => {
                bail!("target name `{to}` already exists as an operator");
            }
            Unit::Variable(names) => {
                for n in names {
                    if n.node == to {
                        bail!("target name `{to}` already exists as a variable");
                    }
                }
            }
            Unit::Constant(decls) => {
                for d in decls {
                    if d.name.node == to {
                        bail!("target name `{to}` already exists as a constant");
                    }
                }
            }
            _ => {}
        }
    }

    // Check that `from` exists somewhere
    let exists = module.units.iter().any(|u| match &u.node {
        Unit::Operator(op) => op.name.node == from,
        Unit::Variable(names) => names.iter().any(|n| n.node == from),
        Unit::Constant(decls) => decls.iter().any(|d| d.name.node == from),
        _ => false,
    });
    if !exists {
        bail!("name `{from}` not found in the specification");
    }

    // Collect all spans where `from` appears as an identifier.
    // We do whole-word replacement in the source text, guided by AST knowledge.
    //
    // Strategy: find all occurrences of `from` as a whole word (bounded by
    // non-identifier characters) and replace with `to`.
    let result = replace_identifier_whole_word(&source, from, to);

    Ok(result)
}

/// Replace all whole-word occurrences of `from` with `to` in source text.
///
/// A "whole word" boundary means the character before and after the match
/// is not an identifier character (alphanumeric or underscore).
fn replace_identifier_whole_word(source: &str, from: &str, to: &str) -> String {
    let mut result = String::with_capacity(source.len());
    let bytes = source.as_bytes();
    let from_bytes = from.as_bytes();
    let from_len = from_bytes.len();
    let mut i = 0;

    while i < bytes.len() {
        if i + from_len <= bytes.len() && &bytes[i..i + from_len] == from_bytes {
            // Check word boundary before
            let before_ok = i == 0 || !is_ident_char(bytes[i - 1]);
            // Check word boundary after
            let after_ok =
                i + from_len >= bytes.len() || !is_ident_char(bytes[i + from_len]);
            if before_ok && after_ok {
                result.push_str(to);
                i += from_len;
                continue;
            }
        }
        result.push(bytes[i] as char);
        i += 1;
    }

    result
}

/// Check if a byte is a valid TLA+ identifier character.
fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

// ---------------------------------------------------------------------------
// Inline operator
// ---------------------------------------------------------------------------

/// Inline a simple (zero-parameter) operator: replace all uses with its body,
/// then remove the definition.
fn refactor_inline(file: &Path, name: &str) -> Result<String> {
    let (source, module) = parse_and_lower(file)?;

    // Find the operator definition
    let op_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(op) if op.name.node == name => Some(op),
            _ => None,
        })
        .ok_or_else(|| anyhow::anyhow!("operator `{name}` not found"))?;

    // Only inline zero-parameter operators
    if !op_def.params.is_empty() {
        bail!(
            "operator `{name}` has {} parameter(s); only zero-parameter operators can be inlined",
            op_def.params.len()
        );
    }

    // Extract the body text from the source using the body span
    let body_start = op_def.body.span.start as usize;
    let body_end = op_def.body.span.end as usize;
    let body_text = &source[body_start..body_end];

    // Determine the full span of the operator definition line(s).
    // The unit span covers the full `Name == body` text.
    let def_unit_span = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(op) if op.name.node == name => Some(u.span),
            _ => None,
        })
        .expect("already found the operator");

    let def_start = line_start_of(&source, def_unit_span.start as usize);
    let def_end = line_end_of(&source, def_unit_span.end as usize);

    // Check if the body is complex enough to need parenthesization when substituted
    let needs_parens = body_needs_parens(&op_def.body.node);
    let replacement = if needs_parens {
        format!("({body_text})")
    } else {
        body_text.to_string()
    };

    // Collect replacement sites: all places where the operator name is used
    // as a standalone identifier reference (not its own definition).
    // We use whole-word matching but exclude the definition site itself.
    let mut result = String::with_capacity(source.len());
    let bytes = source.as_bytes();
    let name_bytes = name.as_bytes();
    let name_len = name_bytes.len();
    let mut i = 0;

    while i < bytes.len() {
        // Skip the definition region entirely
        if i == def_start {
            i = def_end;
            // Skip trailing blank lines after the removed definition
            while i < bytes.len() && (bytes[i] == b'\n' || bytes[i] == b'\r') {
                i += 1;
                // Only eat one blank line
                break;
            }
            continue;
        }

        if i + name_len <= bytes.len() && &bytes[i..i + name_len] == name_bytes {
            let before_ok = i == 0 || !is_ident_char(bytes[i - 1]);
            let after_ok =
                i + name_len >= bytes.len() || !is_ident_char(bytes[i + name_len]);
            if before_ok && after_ok {
                result.push_str(&replacement);
                i += name_len;
                continue;
            }
        }
        result.push(bytes[i] as char);
        i += 1;
    }

    Ok(result)
}

/// Determine if an expression body needs parenthesization when inlined.
///
/// Simple expressions (idents, literals, function applications) do not need
/// parens. Compound expressions (and, or, implies, etc.) do.
fn body_needs_parens(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::And(_, _)
            | Expr::Or(_, _)
            | Expr::Implies(_, _)
            | Expr::Equiv(_, _)
            | Expr::In(_, _)
            | Expr::NotIn(_, _)
            | Expr::Subseteq(_, _)
            | Expr::Eq(_, _)
            | Expr::Neq(_, _)
            | Expr::Lt(_, _)
            | Expr::Leq(_, _)
            | Expr::Gt(_, _)
            | Expr::Geq(_, _)
            | Expr::Add(_, _)
            | Expr::Sub(_, _)
            | Expr::Mul(_, _)
            | Expr::Div(_, _)
            | Expr::IntDiv(_, _)
            | Expr::Mod(_, _)
            | Expr::If(_, _, _)
            | Expr::Forall(_, _)
            | Expr::Exists(_, _)
            | Expr::Let(_, _)
    )
}

// ---------------------------------------------------------------------------
// Cleanup (remove unused operators)
// ---------------------------------------------------------------------------

/// Remove all operators not reachable from Init, Next, invariants, or properties.
fn refactor_cleanup(file: &Path, config_path: Option<&Path>) -> Result<String> {
    let (source, module) = parse_and_lower(file)?;

    let cfg_info = load_config_info(file, config_path);

    // Build operator map
    let mut all_ops: HashMap<&str, &OperatorDef> = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            all_ops.insert(op.name.node.as_str(), op);
        }
    }

    // Determine root operators from config
    let mut roots: Vec<String> = Vec::new();
    if let Some(init) = &cfg_info.init {
        roots.push(init.clone());
    }
    if let Some(next) = &cfg_info.next {
        roots.push(next.clone());
    }
    for inv in &cfg_info.invariants {
        roots.push(inv.clone());
    }
    for prop in &cfg_info.properties {
        roots.push(prop.clone());
    }

    // If no roots, we cannot determine unused -- bail
    if roots.is_empty() {
        bail!("no Init/Next/invariants/properties found; cannot determine unused operators");
    }

    // Compute reachable set via transitive closure
    let mut reachable: HashSet<String> = HashSet::new();
    let mut worklist = roots;
    while let Some(name) = worklist.pop() {
        if !reachable.insert(name.clone()) {
            continue;
        }
        if let Some(op) = all_ops.get(name.as_str()) {
            let refs = collect_ident_refs(&op.body.node);
            for r in refs {
                if all_ops.contains_key(r.as_str()) && !reachable.contains(&r) {
                    worklist.push(r);
                }
            }
        }
    }

    // Collect spans of unreachable operator definitions to remove.
    // We remove entire lines for each unused operator.
    let mut remove_ranges: Vec<(usize, usize)> = Vec::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            let name = op.name.node.as_str();
            // Keep LOCAL operators (they may be intentional)
            if op.local {
                continue;
            }
            if !reachable.contains(name) {
                let start = line_start_of(&source, unit.span.start as usize);
                let mut end = line_end_of(&source, unit.span.end as usize);
                // Also remove one trailing blank line if present
                if end < source.len() && source.as_bytes()[end] == b'\n' {
                    end += 1;
                }
                remove_ranges.push((start, end));
            }
        }
    }

    if remove_ranges.is_empty() {
        eprintln!("No unused operators found.");
        return Ok(source);
    }

    // Report what we are removing
    for (start, _end) in &remove_ranges {
        let line = line_of_offset(&source, *start as u32);
        // Extract the operator name from the start of the range
        let line_text = source[*start..]
            .lines()
            .next()
            .unwrap_or("")
            .trim();
        eprintln!("Removing unused operator at line {line}: {line_text}");
    }

    // Sort ranges in reverse order and remove them
    remove_ranges.sort_by(|a, b| b.0.cmp(&a.0));
    let mut result = source.clone();
    for (start, end) in &remove_ranges {
        result.replace_range(*start..*end, "");
    }

    Ok(result)
}

// ---------------------------------------------------------------------------
// Config loading (mirrors cmd_lint pattern)
// ---------------------------------------------------------------------------

/// Extracted config info for determining reachable operators.
#[derive(Default)]
struct ConfigInfo {
    init: Option<String>,
    next: Option<String>,
    invariants: Vec<String>,
    properties: Vec<String>,
}

fn load_config_info(file: &Path, config_path: Option<&Path>) -> ConfigInfo {
    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    if !config_path_buf.exists() {
        return ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
    }

    let source = match std::fs::read_to_string(&config_path_buf) {
        Ok(s) => s,
        Err(_) => return ConfigInfo::default(),
    };

    match tla_check::Config::parse(&source) {
        Ok(config) => ConfigInfo {
            init: config.init.clone(),
            next: config.next.clone(),
            invariants: config.invariants.clone(),
            properties: config.properties.clone(),
        },
        Err(_) => ConfigInfo {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        },
    }
}

// ---------------------------------------------------------------------------
// Expression analysis helpers (reused from cmd_lint pattern)
// ---------------------------------------------------------------------------

/// Collect all identifier references in an expression tree.
fn collect_ident_refs(expr: &Expr) -> HashSet<String> {
    let mut refs = HashSet::new();
    collect_ident_refs_inner(expr, &mut refs);
    refs
}

fn collect_ident_refs_inner(expr: &Expr, refs: &mut HashSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            refs.insert(name.clone());
        }
        Expr::Apply(func, args) => {
            collect_ident_refs_inner(&func.node, refs);
            for arg in args {
                collect_ident_refs_inner(&arg.node, refs);
            }
        }
        _ => visit_expr_children(expr, |child| {
            collect_ident_refs_inner(child, refs);
        }),
    }
}

/// Visit all direct child expressions of an Expr node, calling `f` on each.
fn visit_expr_children(expr: &Expr, mut f: impl FnMut(&Expr)) {
    match expr {
        // Leaves
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_)
        | Expr::InstanceExpr(_, _) => {}

        // Unary
        Expr::Not(e)
        | Expr::Prime(e)
        | Expr::Always(e)
        | Expr::Eventually(e)
        | Expr::Enabled(e)
        | Expr::Unchanged(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Domain(e)
        | Expr::Neg(e) => {
            f(&e.node);
        }

        // Binary
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b) => {
            f(&a.node);
            f(&b.node);
        }

        // Apply
        Expr::Apply(func, args) => {
            f(&func.node);
            for arg in args {
                f(&arg.node);
            }
        }

        // Lambda
        Expr::Lambda(_, body) => {
            f(&body.node);
        }

        // Label
        Expr::Label(label) => {
            f(&label.body.node);
        }

        // ModuleRef
        Expr::ModuleRef(target, _, args) => {
            if let tla_core::ast::ModuleTarget::Parameterized(_, params) = target {
                for p in params {
                    f(&p.node);
                }
            }
            if let tla_core::ast::ModuleTarget::Chained(base) = target {
                f(&base.node);
            }
            for arg in args {
                f(&arg.node);
            }
        }

        // Quantifiers
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    f(&d.node);
                }
            }
            f(&body.node);
        }

        Expr::Choose(bv, body) => {
            if let Some(d) = &bv.domain {
                f(&d.node);
            }
            f(&body.node);
        }

        // Sets / Tuples
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for elem in elems {
                f(&elem.node);
            }
        }

        Expr::SetBuilder(body, bounds) | Expr::FuncDef(bounds, body) => {
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    f(&d.node);
                }
            }
            f(&body.node);
        }

        Expr::SetFilter(bv, body) => {
            if let Some(d) = &bv.domain {
                f(&d.node);
            }
            f(&body.node);
        }

        // Records
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, val) in fields {
                f(&val.node);
            }
        }

        Expr::RecordAccess(base, _) => {
            f(&base.node);
        }

        // Except
        Expr::Except(base, specs) => {
            f(&base.node);
            for spec in specs {
                f(&spec.value.node);
                for path_elem in &spec.path {
                    if let tla_core::ast::ExceptPathElement::Index(idx) = path_elem {
                        f(&idx.node);
                    }
                }
            }
        }

        // Control
        Expr::If(cond, then_, else_) => {
            f(&cond.node);
            f(&then_.node);
            f(&else_.node);
        }

        Expr::Case(arms, other) => {
            for arm in arms {
                f(&arm.guard.node);
                f(&arm.body.node);
            }
            if let Some(o) = other {
                f(&o.node);
            }
        }

        Expr::Let(defs, body) => {
            for def in defs {
                f(&def.body.node);
            }
            f(&body.node);
        }

        Expr::SubstIn(_, body) => {
            f(&body.node);
        }
    }
}

// ---------------------------------------------------------------------------
// Text utility helpers
// ---------------------------------------------------------------------------

/// Find the byte offset of the start of the line containing `offset`.
fn line_start_of(source: &str, offset: usize) -> usize {
    let offset = offset.min(source.len());
    source[..offset]
        .rfind('\n')
        .map(|pos| pos + 1)
        .unwrap_or(0)
}

/// Find the byte offset just past the end of the line containing `offset`
/// (after the newline, or end of string).
fn line_end_of(source: &str, offset: usize) -> usize {
    let offset = offset.min(source.len());
    source[offset..]
        .find('\n')
        .map(|pos| offset + pos + 1)
        .unwrap_or(source.len())
}

/// Get the 1-based line number for a byte offset.
fn line_of_offset(source: &str, offset: u32) -> usize {
    let offset = (offset as usize).min(source.len());
    source[..offset].chars().filter(|&c| c == '\n').count() + 1
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_ident_char() {
        assert!(is_ident_char(b'a'));
        assert!(is_ident_char(b'Z'));
        assert!(is_ident_char(b'0'));
        assert!(is_ident_char(b'_'));
        assert!(!is_ident_char(b' '));
        assert!(!is_ident_char(b'+'));
        assert!(!is_ident_char(b'='));
    }

    #[test]
    fn test_replace_identifier_whole_word() {
        let source = "x + xy + x_y + x";
        let result = replace_identifier_whole_word(source, "x", "newX");
        assert_eq!(result, "newX + xy + x_y + newX");
    }

    #[test]
    fn test_replace_identifier_whole_word_no_match() {
        let source = "abc def";
        let result = replace_identifier_whole_word(source, "xyz", "new");
        assert_eq!(result, "abc def");
    }

    #[test]
    fn test_line_start_of() {
        let source = "line1\nline2\nline3";
        assert_eq!(line_start_of(source, 0), 0);
        assert_eq!(line_start_of(source, 3), 0);
        assert_eq!(line_start_of(source, 6), 6);
        assert_eq!(line_start_of(source, 8), 6);
        assert_eq!(line_start_of(source, 12), 12);
    }

    #[test]
    fn test_line_end_of() {
        let source = "line1\nline2\nline3";
        assert_eq!(line_end_of(source, 0), 6);
        assert_eq!(line_end_of(source, 6), 12);
        assert_eq!(line_end_of(source, 12), source.len());
    }

    #[test]
    fn test_line_of_offset() {
        let source = "line1\nline2\nline3";
        assert_eq!(line_of_offset(source, 0), 1);
        assert_eq!(line_of_offset(source, 6), 2);
        assert_eq!(line_of_offset(source, 12), 3);
    }

    #[test]
    fn test_body_needs_parens_simple() {
        assert!(!body_needs_parens(&Expr::Bool(true)));
        assert!(!body_needs_parens(&Expr::Int(num_bigint::BigInt::from(42))));
    }
}
