// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 codegen` command: generate Rust code from TLA+ specifications.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use serde::Deserialize;
use tla_codegen::{
    generate_rust_from_tir_with_modules, generate_rust_with_context, CheckerMapConfig,
    CheckerMapImpl, CodeGenContext, CodeGenOptions, TirCodeGenOptions,
};
use tla_core::ast::Unit;
use tla_core::{lower_error_diagnostic, lower_main_module, FileId, ModuleLoader};
use tla_tir::{lower_module_for_codegen, TirLoweringEnv};

use crate::{parse_or_report, read_source};

pub(crate) fn cmd_codegen(
    file: &Path,
    output: Option<&Path>,
    checker: bool,
    checker_map: Option<&Path>,
    kani: bool,
    proptest: bool,
    emit_source_map: bool,
) -> Result<()> {
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);
    loader
        .load_extends(&module)
        .with_context(|| format!("load EXTENDS dependencies for `{}`", module.name.node))?;
    loader
        .load_instances(&module)
        .with_context(|| format!("load INSTANCE dependencies for `{}`", module.name.node))?;

    let checker_map = match checker_map {
        Some(path) => Some(read_checker_map_config(path)?),
        None => None,
    };

    let options = CodeGenOptions {
        module_name: None,
        generate_kani: kani,
        generate_proptest: proptest,
        generate_checker: checker || checker_map.is_some(),
        checker_map,
    };

    let context = CodeGenContext {
        modules: loader.modules_for_model_checking(&module),
    };

    if emit_source_map && output.is_some() {
        let output_path = output.expect("output is Some");
        let generated_file = output_path.display().to_string();
        let tla_source = file.display().to_string();
        let (rust_code, source_map) = tla_codegen::generate_rust_with_source_map(
            &module,
            &context,
            &options,
            &generated_file,
            &tla_source,
        )
        .map_err(|e| anyhow::anyhow!("{}", e))?;

        std::fs::write(output_path, &rust_code)
            .with_context(|| format!("write {}", output_path.display()))?;
        eprintln!("Generated Rust code written to: {}", output_path.display());

        // Write source map alongside the generated file
        let sm_path = PathBuf::from(format!("{}.source_map.json", output_path.display()));
        let sm_json = serde_json::to_string_pretty(&source_map)
            .context("serialize source map")?;
        std::fs::write(&sm_path, &sm_json)
            .with_context(|| format!("write {}", sm_path.display()))?;
        eprintln!("Source map written to: {}", sm_path.display());
    } else {
        let rust_code = generate_rust_with_context(&module, &context, &options)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        match output {
            Some(path) => {
                std::fs::write(path, &rust_code)
                    .with_context(|| format!("write {}", path.display()))?;
                eprintln!("Generated Rust code written to: {}", path.display());
            }
            None => {
                print!("{}", rust_code);
            }
        }
    }

    Ok(())
}

/// TIR-based code generation command.
///
/// Parses the spec, lowers to TIR, and generates Rust code using type
/// information from the TIR lowering pass. Part of #3729.
pub(crate) fn cmd_codegen_tir(
    file: &Path,
    config_path: Option<&Path>,
    output: Option<&Path>,
) -> Result<()> {
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    // Load dependencies
    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);
    loader
        .load_extends(&module)
        .with_context(|| format!("load EXTENDS dependencies for `{}`", module.name.node))?;
    loader
        .load_instances(&module)
        .with_context(|| format!("load INSTANCE dependencies for `{}`", module.name.node))?;

    // Build TIR lowering environment
    let dep_modules = loader.modules_for_model_checking(&module);
    let mut env = TirLoweringEnv::new(&module);
    for dep in &dep_modules {
        env.add_module(dep);
    }

    // Lower to TIR (permissive mode: allow stdlib builtins like Append, Len,
    // Cardinality through as generic Apply nodes for codegen translation)
    let tir_module = lower_module_for_codegen(&env, &module)
        .map_err(|e| anyhow::anyhow!("TIR lowering failed: {e}"))?;

    // Extract state variables from main module AND dependency modules
    // (EXTENDS can bring in VARIABLE declarations from other modules)
    let mut state_vars: Vec<String> = Vec::new();
    let mut seen_vars: HashSet<String> = HashSet::new();
    for m in std::iter::once(&module).chain(dep_modules.iter().copied()) {
        for unit in &m.units {
            if let Unit::Variable(vars) = &unit.node {
                for v in vars {
                    if seen_vars.insert(v.node.clone()) {
                        state_vars.push(v.node.clone());
                    }
                }
            }
        }
    }

    // Parse config for constants, invariants, and init/next operator names
    let parsed_cfg = match config_path {
        Some(path) => parse_simple_config(path)?,
        None => {
            // Try default config path
            let mut cfg_path = file.to_path_buf();
            cfg_path.set_extension("cfg");
            if cfg_path.exists() {
                parse_simple_config(&cfg_path)?
            } else {
                ParsedConfig {
                    constants: HashMap::new(),
                    invariants: Vec::new(),
                    specification: None,
                    init: None,
                    next: None,
                }
            }
        }
    };
    let mut constants = parsed_cfg.constants;
    let invariant_names = parsed_cfg.invariants;

    // Resolve `<-` constant references from model files
    let spec_dir = file.parent().unwrap_or(Path::new("."));
    resolve_constant_refs(&mut constants, config_path, spec_dir);

    // Resolve init/next operator names from config
    let init_name = resolve_init_name(&parsed_cfg.init, &parsed_cfg.specification, &tir_module);
    let next_name = resolve_next_name(&parsed_cfg.next, &parsed_cfg.specification, &tir_module);

    let options = TirCodeGenOptions {
        module_name: None,
        init_name: Some(init_name),
        next_name: Some(next_name),
    };
    let rust_code = generate_rust_from_tir_with_modules(
        &tir_module,
        &module,
        &env,
        &state_vars,
        &constants,
        &invariant_names,
        &options,
    )
    .map_err(|e| anyhow::anyhow!("{e}"))?;

    match output {
        Some(path) => {
            std::fs::write(path, &rust_code)
                .with_context(|| format!("write {}", path.display()))?;
            eprintln!(
                "Generated Rust code (TIR path) written to: {}",
                path.display()
            );
        }
        None => {
            print!("{rust_code}");
        }
    }

    Ok(())
}

/// Parsed result from a TLA+ .cfg file.
struct ParsedConfig {
    constants: HashMap<String, String>,
    invariants: Vec<String>,
    /// SPECIFICATION operator name (e.g., "Spec"), if present.
    specification: Option<String>,
    /// INIT operator name (e.g., "Init"), if present.
    init: Option<String>,
    /// NEXT operator name (e.g., "Next"), if present.
    next: Option<String>,
}

/// Minimal .cfg parser for CONSTANTS, INVARIANTS, INIT, NEXT, SPECIFICATION.
fn parse_simple_config(path: &Path) -> Result<ParsedConfig> {
    let content =
        std::fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;

    let mut constants = HashMap::new();
    let mut invariants = Vec::new();
    let mut specification = None;
    let mut init = None;
    let mut next = None;

    enum Section {
        None,
        Constants,
        Invariants,
    }

    let mut section = Section::None;

    // Strip TLA+ block comments (* ... *) before parsing
    let content = strip_tla_block_comments(&content);

    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("\\*") {
            continue;
        }

        if let Some(rest) = line.strip_prefix("SPECIFICATION") {
            let name = rest.trim();
            if !name.is_empty() {
                specification = Some(name.to_string());
            }
            section = Section::None;
            continue;
        }
        if let Some(rest) = line.strip_prefix("INIT") {
            let name = rest.trim();
            if !name.is_empty() {
                init = Some(name.to_string());
            }
            section = Section::None;
            continue;
        }
        if let Some(rest) = line.strip_prefix("NEXT") {
            let name = rest.trim();
            if !name.is_empty() {
                next = Some(name.to_string());
            }
            section = Section::None;
            continue;
        }
        if line.starts_with("CONSTANTS") || line.starts_with("CONSTANT") {
            section = Section::Constants;
            let rest = line
                .strip_prefix("CONSTANTS")
                .or_else(|| line.strip_prefix("CONSTANT"))
                .unwrap_or("")
                .trim();
            if !rest.is_empty() {
                parse_constant_line(rest, &mut constants);
            }
            continue;
        }
        if line.starts_with("INVARIANTS") || line.starts_with("INVARIANT") {
            section = Section::Invariants;
            let rest = line
                .strip_prefix("INVARIANTS")
                .or_else(|| line.strip_prefix("INVARIANT"))
                .unwrap_or("")
                .trim();
            if !rest.is_empty() {
                // Multiple invariant names can appear on the same line
                for name in rest.split_whitespace() {
                    let name = strip_tla_line_comment(name);
                    let name = name.trim();
                    if !name.is_empty() {
                        invariants.push(name.to_string());
                    }
                }
            }
            continue;
        }
        if line.starts_with("PROPERTIES")
            || line.starts_with("PROPERTY")
            || line.starts_with("SYMMETRY")
            || line.starts_with("VIEW")
            || line.starts_with("ALIAS")
            || line.starts_with("CONSTRAINTS")
            || line.starts_with("CONSTRAINT")
            || line.starts_with("ACTION_CONSTRAINT")
            || line.starts_with("CHECK_DEADLOCK")
            || line.starts_with("TERMINAL")
            || line.starts_with("POSTCONDITION")
        {
            section = Section::None;
            continue;
        }

        match section {
            Section::None => {}
            Section::Constants => {
                parse_constant_line(line, &mut constants);
            }
            Section::Invariants => {
                // Multiple invariant names can appear on one line
                for name in line.split_whitespace() {
                    let name = strip_tla_line_comment(name);
                    let name = name.trim();
                    if !name.is_empty() {
                        invariants.push(name.to_string());
                    }
                }
            }
        }
    }

    Ok(ParsedConfig {
        constants,
        invariants,
        specification,
        init,
        next,
    })
}

/// Strip TLA+ line comment `\* ...` from a line (outside of string literals).
fn strip_tla_line_comment(line: &str) -> String {
    // Find \* that is not inside a string literal
    let mut in_string = false;
    let chars: Vec<char> = line.chars().collect();
    for i in 0..chars.len() {
        if chars[i] == '"' {
            in_string = !in_string;
        }
        if !in_string && i + 1 < chars.len() && chars[i] == '\\' && chars[i + 1] == '*' {
            return line[..i].trim_end().to_string();
        }
    }
    line.to_string()
}

/// Strip TLA+ block comments `(* ... *)` (possibly nested or multi-line).
fn strip_tla_block_comments(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;
    let mut depth = 0;
    while i < chars.len() {
        if i + 1 < chars.len() && chars[i] == '(' && chars[i + 1] == '*' {
            depth += 1;
            i += 2;
            continue;
        }
        if depth > 0 && i + 1 < chars.len() && chars[i] == '*' && chars[i + 1] == ')' {
            depth -= 1;
            i += 2;
            continue;
        }
        if depth == 0 {
            out.push(chars[i]);
        } else if chars[i] == '\n' {
            // Preserve line breaks inside comments so line-oriented parsing still works
            out.push('\n');
        }
        i += 1;
    }
    out
}

fn parse_constant_line(line: &str, constants: &mut HashMap<String, String>) {
    // Strip TLA+ line comments (\* ...) before parsing values
    let line = strip_tla_line_comment(line);
    let line = line.as_str();
    if let Some((name, value)) = line.split_once('=') {
        let name = name.trim().to_string();
        let value = value.trim().to_string();
        if !name.is_empty() && !value.is_empty() {
            constants.insert(name, value);
        }
    } else if let Some((name, value)) = line.split_once("<-") {
        let name = name.trim().to_string();
        let value = value.trim().to_string();
        if !name.is_empty() && !value.is_empty() {
            // Mark `<-` references with a prefix so codegen can resolve them
            constants.insert(name, format!("@ref:{value}"));
        }
    }
}

/// Resolve `<-` constant references by finding operator definitions in model files.
///
/// When a config has `NumVars <- MCNumVars`, we need to find the operator
/// `MCNumVars` (typically defined in a model-checking wrapper like MCBCP.tla)
/// and extract its value expression as a string.
fn resolve_constant_refs(
    constants: &mut HashMap<String, String>,
    config_path: Option<&Path>,
    spec_dir: &Path,
) {
    let refs_to_resolve: Vec<(String, String)> = constants
        .iter()
        .filter_map(|(k, v)| {
            v.strip_prefix("@ref:")
                .map(|op_name| (k.clone(), op_name.to_string()))
        })
        .collect();

    if refs_to_resolve.is_empty() {
        return;
    }

    // Try to find model file: derive from config filename or scan spec_dir
    let model_files = find_model_files(config_path, spec_dir);
    let mut op_defs: HashMap<String, String> = HashMap::new();

    for model_path in &model_files {
        if let Ok(content) = std::fs::read_to_string(model_path) {
            extract_operator_defs(&content, &refs_to_resolve, &mut op_defs);
        }
    }

    // Collect model values: constants where name == value (e.g., `a = a`)
    let model_values: Vec<String> = constants
        .iter()
        .filter(|(k, v)| {
            k == v && !v.starts_with("@ref:")
        })
        .map(|(k, _)| k.clone())
        .collect();

    // Replace @ref: entries with resolved values
    for (const_name, op_name) in &refs_to_resolve {
        if let Some(resolved) = op_defs.get(op_name) {
            constants.insert(const_name.clone(), resolved.clone());
        } else if op_name.starts_with("const_") && !model_values.is_empty() {
            // TLC model value set pattern: `Value <- const_NNNNN` with model values
            // like `a = a, b = b, c = c`. Build the set from all model values.
            let mut mvs: Vec<String> = model_values.clone();
            mvs.sort();
            let set_str = format!("{{{}}}", mvs.join(", "));
            constants.insert(const_name.clone(), set_str);
        } else {
            // Fallback: remove @ref: prefix, leave the operator name as-is
            // (this will still be wrong but less confusing than having @ref: in output)
            constants.insert(const_name.clone(), op_name.clone());
            eprintln!(
                "warning: could not resolve constant reference `{op_name}` for `{const_name}`"
            );
        }
    }
}

/// Find model TLA files that might define the referenced operators.
fn find_model_files(config_path: Option<&Path>, spec_dir: &Path) -> Vec<std::path::PathBuf> {
    let mut candidates = Vec::new();

    if let Some(cfg) = config_path {
        // Derive model filename from config: MCBCP_noDeadlock.cfg -> MCBCP.tla
        let stem = cfg.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        // Try exact match first
        let exact = cfg.with_file_name(format!("{stem}.tla"));
        if exact.exists() {
            candidates.push(exact);
        }
        // Try stripping common suffixes
        for suffix in &["_noDeadlock", "_small", "_large", "_Pigeon"] {
            if let Some(base) = stem.strip_suffix(suffix) {
                let p = cfg.with_file_name(format!("{base}.tla"));
                if p.exists() {
                    candidates.push(p);
                }
            }
        }
    }

    // Also scan the directory for MC*.tla files
    if let Ok(entries) = std::fs::read_dir(spec_dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                if name.starts_with("MC") && name.ends_with(".tla") && !candidates.contains(&path) {
                    candidates.push(path);
                }
            }
        }
    }

    candidates
}

/// Extract simple operator definitions (Op == value) from TLA+ source text.
fn extract_operator_defs(
    content: &str,
    refs: &[(String, String)],
    defs: &mut HashMap<String, String>,
) {
    let op_names: std::collections::HashSet<&str> =
        refs.iter().map(|(_, name)| name.as_str()).collect();

    for line in content.lines() {
        let trimmed = line.trim();
        // Match patterns like: MCNumVars == 3  or  MCClauses == {{1,2}, ...}
        if let Some((left, right)) = trimmed.split_once("==") {
            let name = left.trim();
            if op_names.contains(name) && !defs.contains_key(name) {
                let value = right.trim().to_string();
                if !value.is_empty() {
                    defs.insert(name.to_string(), value);
                }
            }
        }
    }
}

/// Resolve the Init operator name from config and TIR module.
///
/// Priority: explicit INIT in config > analysis of SPECIFICATION operator > default "Init".
fn resolve_init_name(
    explicit_init: &Option<String>,
    specification: &Option<String>,
    tir_module: &tla_tir::TirModule,
) -> String {
    if let Some(name) = explicit_init {
        return name.clone();
    }
    // If SPECIFICATION is given, analyze the Spec operator body for Init references
    if let Some(spec_name) = specification {
        if let Some(init) = find_init_in_spec_operator(spec_name, tir_module) {
            return init;
        }
    }
    "Init".to_string()
}

/// Resolve the Next operator name from config and TIR module.
///
/// Priority: explicit NEXT in config > analysis of SPECIFICATION operator > default "Next".
fn resolve_next_name(
    explicit_next: &Option<String>,
    specification: &Option<String>,
    tir_module: &tla_tir::TirModule,
) -> String {
    if let Some(name) = explicit_next {
        return name.clone();
    }
    if let Some(spec_name) = specification {
        if let Some(next) = find_next_in_spec_operator(spec_name, tir_module) {
            return next;
        }
    }
    "Next".to_string()
}

/// Find the Init operator name referenced in a Spec operator body.
///
/// The typical TLA+ pattern is `Spec == Init /\ [][Next]_vars /\ ...`.
/// The Init part is typically a non-action, non-temporal operator reference
/// in a conjunction at the top level of Spec's body. We look for `Name`
/// references to operators that exist in the module and don't contain primes.
fn find_init_in_spec_operator(spec_name: &str, tir_module: &tla_tir::TirModule) -> Option<String> {
    let spec_op = tir_module.operators.iter().find(|op| op.name == spec_name)?;
    let op_names: HashSet<&str> = tir_module.operators.iter().map(|op| op.name.as_str()).collect();

    // Collect top-level Name references from the Spec body
    let candidates = collect_top_level_names(&spec_op.body.node);
    for name in &candidates {
        if op_names.contains(name.as_str()) && name != "Next" && name != spec_name {
            // Check if this operator does NOT contain primes (i.e., it's an init predicate)
            if let Some(op) = tir_module.operators.iter().find(|o| o.name == *name) {
                if !tla_codegen::expr_contains_prime_pub(&op.body.node) {
                    return Some(name.clone());
                }
            }
        }
    }
    None
}

/// Find the Next operator name referenced in a Spec operator body.
///
/// Looks for operators referenced within `[][...]_vars` (ActionSubscript/Always)
/// patterns, or failing that, operators that contain prime references.
fn find_next_in_spec_operator(spec_name: &str, tir_module: &tla_tir::TirModule) -> Option<String> {
    let spec_op = tir_module.operators.iter().find(|op| op.name == spec_name)?;
    let op_names: HashSet<&str> = tir_module.operators.iter().map(|op| op.name.as_str()).collect();

    // Look for Name references inside temporal/action operators in the Spec body
    let temporal_names = collect_names_inside_temporal(&spec_op.body.node);
    for name in &temporal_names {
        if op_names.contains(name.as_str()) && name != spec_name {
            return Some(name.clone());
        }
    }

    // Fallback: look at top-level Name references that are action operators (contain primes)
    let candidates = collect_top_level_names(&spec_op.body.node);
    for name in &candidates {
        if op_names.contains(name.as_str()) && name != spec_name {
            if let Some(op) = tir_module.operators.iter().find(|o| o.name == *name) {
                if tla_codegen::expr_contains_prime_pub(&op.body.node) {
                    return Some(name.clone());
                }
            }
        }
    }
    None
}

/// Collect operator names referenced at the top level of a conjunction.
fn collect_top_level_names(expr: &tla_tir::TirExpr) -> Vec<String> {
    let mut names = Vec::new();
    match expr {
        tla_tir::TirExpr::BoolBinOp {
            left,
            op: tla_tir::TirBoolOp::And,
            right,
        } => {
            collect_top_level_names_inner(&left.node, &mut names);
            collect_top_level_names_inner(&right.node, &mut names);
        }
        _ => collect_top_level_names_inner(expr, &mut names),
    }
    names
}

fn collect_top_level_names_inner(expr: &tla_tir::TirExpr, names: &mut Vec<String>) {
    match expr {
        tla_tir::TirExpr::Name(name_ref) => {
            names.push(name_ref.name.clone());
        }
        tla_tir::TirExpr::Apply { op, .. } => {
            if let tla_tir::TirExpr::Name(name_ref) = &op.node {
                names.push(name_ref.name.clone());
            }
        }
        // Recurse into nested conjunctions
        tla_tir::TirExpr::BoolBinOp {
            left,
            op: tla_tir::TirBoolOp::And,
            right,
        } => {
            collect_top_level_names_inner(&left.node, names);
            collect_top_level_names_inner(&right.node, names);
        }
        _ => {}
    }
}

/// Collect operator names referenced inside temporal operators (Always, ActionSubscript, etc.).
fn collect_names_inside_temporal(expr: &tla_tir::TirExpr) -> Vec<String> {
    let mut names = Vec::new();
    collect_names_inside_temporal_inner(expr, false, &mut names);
    names
}

fn collect_names_inside_temporal_inner(
    expr: &tla_tir::TirExpr,
    inside_temporal: bool,
    names: &mut Vec<String>,
) {
    match expr {
        tla_tir::TirExpr::Name(name_ref) if inside_temporal => {
            names.push(name_ref.name.clone());
        }
        tla_tir::TirExpr::Always(inner) | tla_tir::TirExpr::Eventually(inner) => {
            collect_names_inside_temporal_inner(&inner.node, true, names);
        }
        tla_tir::TirExpr::ActionSubscript {
            action, ..
        } => {
            collect_names_inside_temporal_inner(&action.node, true, names);
        }
        tla_tir::TirExpr::BoolBinOp { left, right, .. } => {
            collect_names_inside_temporal_inner(&left.node, inside_temporal, names);
            collect_names_inside_temporal_inner(&right.node, inside_temporal, names);
        }
        _ => {}
    }
}

#[derive(Debug, Default, Deserialize)]
struct CliCheckerMapSpec {
    #[serde(default)]
    module: Option<String>,
}

#[derive(Debug, Default, Deserialize)]
struct CliCheckerMapImplToml {
    rust_type: String,
    #[serde(default)]
    fields: BTreeMap<String, String>,
}

#[derive(Debug, Default, Deserialize)]
struct CliCheckerMapConfigToml {
    #[serde(default)]
    spec: CliCheckerMapSpec,
    #[serde(default)]
    impls: Vec<CliCheckerMapImplToml>,
}

fn read_checker_map_config(path: &Path) -> Result<CheckerMapConfig> {
    let toml_str =
        std::fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    let cfg: CliCheckerMapConfigToml =
        toml::from_str(&toml_str).with_context(|| format!("parse TOML {}", path.display()))?;

    Ok(CheckerMapConfig {
        spec_module: cfg.spec.module,
        impls: cfg
            .impls
            .into_iter()
            .map(|imp| CheckerMapImpl {
                rust_type: imp.rust_type,
                fields: imp.fields,
            })
            .collect(),
    })
}

/// Generate a complete runnable Cargo project from a TLA+ spec.
///
/// Creates an output directory containing:
/// - `Cargo.toml` with tla-runtime dependency
/// - `src/lib.rs` re-exporting the generated module
/// - `src/<spec>.rs` with the generated StateMachine impl
/// - `src/main.rs` that runs BFS and reports state counts
/// - Optionally `src/kani_harness.rs` with zani/Kani verification harnesses
///
/// Part of #3929.
pub(crate) fn cmd_codegen_scaffold(
    file: &Path,
    config_path: Option<&Path>,
    output: Option<&Path>,
    kani: bool,
    tir: bool,
) -> Result<()> {
    let output_dir = output.context(
        "--output is required with --scaffold (specifies the output directory)",
    )?;

    // Derive module name from spec filename
    let spec_stem = file
        .file_stem()
        .and_then(|s| s.to_str())
        .context("could not extract spec name from file path")?;

    let mod_name = to_scaffold_snake_case(spec_stem);
    let machine_type = to_scaffold_pascal_case(spec_stem);
    let state_type = format!("{machine_type}State");

    // Generate the Rust code
    let rust_code = if tir {
        generate_tir_code(file, config_path)?
    } else {
        generate_ast_code(file)?
    };

    // Create the output directory structure
    let src_dir = output_dir.join("src");
    std::fs::create_dir_all(&src_dir)
        .with_context(|| format!("create directory {}", src_dir.display()))?;

    // Find tla-runtime path relative to the repo
    let runtime_dep = find_tla_runtime_dep();

    // Write Cargo.toml
    // Include [workspace] to prevent Cargo workspace auto-discovery issues
    // when the scaffold is generated inside or near an existing workspace.
    let cargo_toml = format!(
        "[package]\n\
         name = \"{mod_name}-codegen\"\n\
         version = \"0.1.0\"\n\
         edition = \"2021\"\n\
         \n\
         [workspace]\n\
         \n\
         [[bin]]\n\
         name = \"check\"\n\
         path = \"src/main.rs\"\n\
         \n\
         [dependencies]\n\
         {runtime_dep}\n"
    );
    std::fs::write(output_dir.join("Cargo.toml"), &cargo_toml)
        .with_context(|| format!("write {}/Cargo.toml", output_dir.display()))?;

    // Write the generated module
    std::fs::write(src_dir.join(format!("{mod_name}.rs")), &rust_code)
        .with_context(|| format!("write src/{mod_name}.rs"))?;

    // Write lib.rs
    let lib_rs = format!("pub mod {mod_name};\n");
    std::fs::write(src_dir.join("lib.rs"), &lib_rs)
        .context("write src/lib.rs")?;

    // Write main.rs with BFS model checker
    let main_rs = format!(
        "//! BFS model checker for {machine_type} (generated by tla2 codegen --scaffold).\n\
         \n\
         mod {mod_name};\n\
         \n\
         use {mod_name}::{machine_type};\n\
         use tla_runtime::prelude::*;\n\
         \n\
         fn main() {{\n\
         {indent}let machine = {machine_type};\n\
         {indent}let max_states = 10_000_000;\n\
         \n\
         {indent}// Run BFS model check with invariant checking\n\
         {indent}let result = model_check(&machine, max_states);\n\
         \n\
         {indent}println!(\"Distinct states: {{}}\", result.distinct_states);\n\
         {indent}println!(\"States explored: {{}}\", result.states_explored);\n\
         \n\
         {indent}if let Some(ref violation) = result.violation {{\n\
         {indent}    eprintln!(\"INVARIANT VIOLATION: {{:?}}\", violation.state);\n\
         {indent}    std::process::exit(1);\n\
         {indent}}}\n\
         \n\
         {indent}if let Some(ref deadlock) = result.deadlock {{\n\
         {indent}    println!(\"Deadlock detected at state: {{:?}}\", deadlock);\n\
         {indent}}}\n\
         \n\
         {indent}if result.is_ok() || result.deadlock.is_some() {{\n\
         {indent}    println!(\"Model check complete.\");\n\
         {indent}}} else {{\n\
         {indent}    std::process::exit(1);\n\
         {indent}}}\n\
         }}\n",
        indent = "    ",
    );
    std::fs::write(src_dir.join("main.rs"), &main_rs)
        .context("write src/main.rs")?;

    // Optionally write Kani/zani harness
    if kani {
        let harness = generate_scaffold_kani_harness(&mod_name, &machine_type, &state_type);
        std::fs::write(src_dir.join("kani_harness.rs"), &harness)
            .context("write src/kani_harness.rs")?;
        eprintln!(
            "Kani/zani harness written to {}/src/kani_harness.rs",
            output_dir.display()
        );
        eprintln!("Run with: cargo kani --harness prove_init_satisfies_inv");
    }

    eprintln!("Scaffold project generated at: {}", output_dir.display());
    eprintln!("Build: cd {} && cargo build --release", output_dir.display());
    eprintln!("Run:   cd {} && cargo run --release", output_dir.display());

    Ok(())
}

/// Generate Rust code via the AST path (no config needed).
fn generate_ast_code(file: &Path) -> Result<String> {
    let source = crate::read_source(file)?;
    let tree = crate::parse_or_report(file, &source)?;

    let hint_name = file.file_stem().and_then(|s| s.to_str()).filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);
    loader.load_extends(&module)?;
    loader.load_instances(&module)?;

    let options = tla_codegen::CodeGenOptions::default();
    let context = tla_codegen::CodeGenContext {
        modules: loader.modules_for_model_checking(&module),
    };
    generate_rust_with_context(&module, &context, &options)
        .map_err(|e| anyhow::anyhow!("{e}"))
}

/// Generate Rust code via the TIR path (uses config for constants).
fn generate_tir_code(file: &Path, config_path: Option<&Path>) -> Result<String> {
    let source = crate::read_source(file)?;
    let tree = crate::parse_or_report(file, &source)?;

    let hint_name = file.file_stem().and_then(|s| s.to_str()).filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    let mut loader = ModuleLoader::new(file);
    loader.seed_from_syntax_tree(&tree, file);
    loader.load_extends(&module)?;
    loader.load_instances(&module)?;

    let dep_modules = loader.modules_for_model_checking(&module);
    let mut env = TirLoweringEnv::new(&module);
    for dep in &dep_modules {
        env.add_module(dep);
    }

    let tir_module = lower_module_for_codegen(&env, &module)
        .map_err(|e| anyhow::anyhow!("TIR lowering failed: {e}"))?;

    let mut state_vars: Vec<String> = Vec::new();
    {
        let mut seen_vars: HashSet<String> = HashSet::new();
        for m in std::iter::once(&module).chain(dep_modules.iter().copied()) {
            for unit in &m.units {
                if let tla_core::ast::Unit::Variable(vars) = &unit.node {
                    for v in vars {
                        if seen_vars.insert(v.node.clone()) {
                            state_vars.push(v.node.clone());
                        }
                    }
                }
            }
        }
    }

    let parsed_cfg = match config_path {
        Some(path) => parse_simple_config(path)?,
        None => {
            let mut cfg_path = file.to_path_buf();
            cfg_path.set_extension("cfg");
            if cfg_path.exists() {
                parse_simple_config(&cfg_path)?
            } else {
                ParsedConfig {
                    constants: HashMap::new(),
                    invariants: Vec::new(),
                    specification: None,
                    init: None,
                    next: None,
                }
            }
        }
    };
    let mut constants = parsed_cfg.constants;
    let invariant_names = parsed_cfg.invariants;

    let spec_dir = file.parent().unwrap_or(Path::new("."));
    resolve_constant_refs(&mut constants, config_path, spec_dir);

    let init_name = resolve_init_name(&parsed_cfg.init, &parsed_cfg.specification, &tir_module);
    let next_name = resolve_next_name(&parsed_cfg.next, &parsed_cfg.specification, &tir_module);

    let options = TirCodeGenOptions {
        module_name: None,
        init_name: Some(init_name),
        next_name: Some(next_name),
    };
    generate_rust_from_tir_with_modules(
        &tir_module, &module, &env, &state_vars, &constants, &invariant_names, &options,
    )
    .map_err(|e| anyhow::anyhow!("{e}"))
}

/// Locate tla-runtime for the Cargo.toml dependency line.
fn find_tla_runtime_dep() -> String {
    // Look for the runtime crate relative to the current binary's location
    if let Ok(exe) = std::env::current_exe() {
        // Walk up to find the repo root
        let mut dir = exe.parent().map(PathBuf::from);
        for _ in 0..10 {
            if let Some(ref d) = dir {
                let candidate = d.join("crates/tla-runtime");
                if candidate.exists() {
                    return format!(
                        "tla-runtime = {{ path = \"{}\" }}",
                        candidate.display()
                    );
                }
                dir = d.parent().map(PathBuf::from);
            }
        }
    }
    // Fallback: use a path that will work from a standard checkout
    "tla-runtime = { path = \"../../crates/tla-runtime\" }".to_string()
}

/// Generate a Kani/zani verification harness for the scaffold project.
fn generate_scaffold_kani_harness(
    mod_name: &str,
    machine_type: &str,
    state_type: &str,
) -> String {
    format!(
        "//! Kani/zani verification harness for {machine_type}.\n\
         //!\n\
         //! Generated by `tla2 codegen --scaffold --kani`.\n\
         //!\n\
         //! Run with:\n\
         //!   cargo kani --harness prove_init_satisfies_inv\n\
         //!   cargo kani --harness prove_next_preserves_inv\n\
         //!   cargo kani --harness prove_bounded_k_steps\n\
         //!\n\
         //! Without Kani, the same logic runs as standard tests:\n\
         //!   cargo test\n\
         \n\
         #[allow(unused_imports)]\n\
         use super::{mod_name}::{{self, {machine_type}, {state_type}}};\n\
         #[allow(unused_imports)]\n\
         use tla_runtime::prelude::*;\n\
         \n\
         // ---------------------------------------------------------------------------\n\
         // Kani/zani proofs\n\
         // ---------------------------------------------------------------------------\n\
         \n\
         /// Base case: every initial state satisfies all invariants.\n\
         #[cfg(kani)]\n\
         #[kani::proof]\n\
         fn prove_init_satisfies_inv() {{\n\
         {indent}let sm = {machine_type};\n\
         {indent}let init_states = sm.init();\n\
         {indent}for state in &init_states {{\n\
         {indent}    if let Some(holds) = sm.check_invariant(state) {{\n\
         {indent}        kani::assert(holds, \"invariant violated in initial state\");\n\
         {indent}    }}\n\
         {indent}}}\n\
         }}\n\
         \n\
         /// Inductive step: for each init state, every one-step successor also\n\
         /// satisfies the invariant.\n\
         #[cfg(kani)]\n\
         #[kani::proof]\n\
         fn prove_next_preserves_inv() {{\n\
         {indent}let sm = {machine_type};\n\
         {indent}let init_states = sm.init();\n\
         {indent}for s in &init_states {{\n\
         {indent}    if let Some(false) = sm.check_invariant(s) {{\n\
         {indent}        continue; // skip states that don't satisfy the invariant\n\
         {indent}    }}\n\
         {indent}    let next_states = sm.next(s);\n\
         {indent}    for ns in &next_states {{\n\
         {indent}        if let Some(holds) = sm.check_invariant(ns) {{\n\
         {indent}            kani::assert(holds, \"invariant violated after transition\");\n\
         {indent}        }}\n\
         {indent}    }}\n\
         {indent}}}\n\
         }}\n\
         \n\
         /// Bounded model check: explore all states reachable within 20 steps.\n\
         #[cfg(kani)]\n\
         #[kani::proof]\n\
         #[kani::unwind(21)]\n\
         fn prove_bounded_k_steps() {{\n\
         {indent}let sm = {machine_type};\n\
         {indent}let init_states = sm.init();\n\
         {indent}if init_states.is_empty() {{\n\
         {indent}    return;\n\
         {indent}}}\n\
         {indent}let idx: usize = kani::any();\n\
         {indent}kani::assume(idx < init_states.len());\n\
         {indent}let mut state = init_states[idx].clone();\n\
         {indent}if let Some(holds) = sm.check_invariant(&state) {{\n\
         {indent}    kani::assert(holds, \"invariant violated at step 0\");\n\
         {indent}}}\n\
         {indent}let k: usize = kani::any();\n\
         {indent}kani::assume(k <= 20);\n\
         {indent}let mut i = 0;\n\
         {indent}while i < k {{\n\
         {indent}    let succs = sm.next(&state);\n\
         {indent}    if succs.is_empty() {{\n\
         {indent}        break;\n\
         {indent}    }}\n\
         {indent}    state = succs[0].clone();\n\
         {indent}    if let Some(holds) = sm.check_invariant(&state) {{\n\
         {indent}        kani::assert(holds, \"invariant violated after step\");\n\
         {indent}    }}\n\
         {indent}    i += 1;\n\
         {indent}}}\n\
         }}\n\
         \n\
         // ---------------------------------------------------------------------------\n\
         // Standard test fallbacks (run without Kani via `cargo test`)\n\
         // ---------------------------------------------------------------------------\n\
         \n\
         #[cfg(test)]\n\
         mod tests {{\n\
         {indent}use super::*;\n\
         \n\
         {indent}#[test]\n\
         {indent}fn test_init_satisfies_inv() {{\n\
         {indent}    let sm = {machine_type};\n\
         {indent}    let states = sm.init();\n\
         {indent}    assert!(!states.is_empty(), \"Init must produce at least one state\");\n\
         {indent}    for state in &states {{\n\
         {indent}        if let Some(holds) = sm.check_invariant(state) {{\n\
         {indent}            assert!(holds, \"Invariant violated in init state: {{:?}}\", state);\n\
         {indent}        }}\n\
         {indent}    }}\n\
         {indent}}}\n\
         \n\
         {indent}#[test]\n\
         {indent}fn test_bounded_exploration() {{\n\
         {indent}    let sm = {machine_type};\n\
         {indent}    let result = model_check(&sm, 10_000);\n\
         {indent}    if let Some(ref v) = result.violation {{\n\
         {indent}        panic!(\"Invariant violated at state: {{:?}}\", v.state);\n\
         {indent}    }}\n\
         {indent}    println!(\"Explored {{}} distinct states\", result.distinct_states);\n\
         {indent}}}\n\
         }}\n",
        indent = "    ",
    )
}

/// Simple snake_case for scaffold use.
fn to_scaffold_snake_case(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            result.push('_');
        }
        result.push(c.to_ascii_lowercase());
    }
    result
}

/// Simple PascalCase for scaffold use.
fn to_scaffold_pascal_case(s: &str) -> String {
    let mut result = String::new();
    let mut capitalize = true;
    for c in s.chars() {
        if c == '_' || c == '-' {
            capitalize = true;
        } else if capitalize {
            result.push(c.to_ascii_uppercase());
            capitalize = false;
        } else {
            result.push(c);
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Public wrappers for compiled check module (Part of --compiled pipeline)
// ---------------------------------------------------------------------------

/// Parsed .cfg result exposed for compiled check module.
pub(crate) struct ParsedConfigPub {
    pub(crate) constants: HashMap<String, String>,
    pub(crate) invariants: Vec<String>,
    pub(crate) specification: Option<String>,
    pub(crate) init: Option<String>,
    pub(crate) next: Option<String>,
}

/// Parse a .cfg file, exposed for compiled check module.
pub(crate) fn parse_simple_config_pub(
    file: &Path,
    config_path: Option<&Path>,
) -> Result<ParsedConfigPub> {
    let cfg_path = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut p = file.to_path_buf();
            p.set_extension("cfg");
            p
        }
    };
    if !cfg_path.exists() {
        return Ok(ParsedConfigPub {
            constants: HashMap::new(),
            invariants: Vec::new(),
            specification: None,
            init: None,
            next: None,
        });
    }
    let parsed = parse_simple_config(&cfg_path)?;
    Ok(ParsedConfigPub {
        constants: parsed.constants,
        invariants: parsed.invariants,
        specification: parsed.specification,
        init: parsed.init,
        next: parsed.next,
    })
}

/// Public wrapper for `resolve_constant_refs` used by compiled check.
pub(crate) fn resolve_constant_refs_pub(
    constants: &mut HashMap<String, String>,
    config_path: Option<&Path>,
    spec_dir: &Path,
) {
    resolve_constant_refs(constants, config_path, spec_dir);
}

/// Resolve Init operator name, exposed for compiled check module.
pub(crate) fn resolve_init_name_pub(
    explicit_init: &Option<String>,
    specification: &Option<String>,
    tir_module: &tla_tir::TirModule,
) -> String {
    resolve_init_name(explicit_init, specification, tir_module)
}

/// Resolve Next operator name, exposed for compiled check module.
pub(crate) fn resolve_next_name_pub(
    explicit_next: &Option<String>,
    specification: &Option<String>,
    tir_module: &tla_tir::TirModule,
) -> String {
    resolve_next_name(explicit_next, specification, tir_module)
}
