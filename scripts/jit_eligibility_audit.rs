// Copyright 2026 Dropbox.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet, HashMap as StdHashMap};
use std::error::Error;
use std::path::{Path, PathBuf};
use tla_check::{bind_constants_from_config, resolve_spec_from_config_with_extends, Config};
use tla_core::ast::{Module, Unit};
use tla_core::{
    intern_name, lower_main_module, parse, FileId, ModuleLoader, SyntaxNode, VarRegistry,
};
use tla_eval::bytecode_vm::{
    collect_bytecode_namespace_callees, compile_operators_to_bytecode_full,
};
use tla_jit::{check_eligibility_with_constants, check_opcode_eligibility_with_constants};
use tla_tir::bytecode::Opcode;
use tla_value::Value;

const DEFAULT_BASELINE_PATH: &str = "tests/tlc_comparison/spec_baseline.json";

#[derive(Debug, Deserialize)]
struct Baseline {
    inputs: BaselineInputs,
    specs: BTreeMap<String, BaselineSpec>,
}

#[derive(Debug, Deserialize)]
struct BaselineInputs {
    examples_dir: String,
}

#[derive(Debug, Deserialize)]
struct BaselineSpec {
    source: Option<BaselineSource>,
}

#[derive(Debug, Deserialize)]
struct BaselineSource {
    tla_path: String,
    cfg_path: String,
}

#[derive(Debug, Default)]
struct AuditTotals {
    specs_seen: usize,
    specs_audited: usize,
    specs_with_blockers: usize,
    requested_ops: usize,
    compiled_target_ops: usize,
    bytecode_compile_failures: usize,
    compiled_functions: usize,
    eligible_functions: usize,
    inline_next_actions_skipped: usize,
    action_resolution_failures: usize,
    spec_failures: usize,
}

#[derive(Debug, Default)]
struct BlockerStats {
    specs: BTreeSet<String>,
    functions: usize,
    occurrences: usize,
}

#[derive(Debug, Default)]
struct SpecAudit {
    blockers: BTreeSet<String>,
    blocker_functions: StdHashMap<String, usize>,
    blocker_occurrences: StdHashMap<String, usize>,
    requested_ops: usize,
    compiled_target_ops: usize,
    bytecode_compile_failures: usize,
    compiled_functions: usize,
    eligible_functions: usize,
    inline_next_action_skipped: bool,
    action_resolution_failed: bool,
}

fn main() -> Result<(), Box<dyn Error>> {
    let baseline_path = parse_args()?;
    let baseline_text = std::fs::read_to_string(&baseline_path)?;
    let baseline: Baseline = serde_json::from_str(&baseline_text)?;
    let examples_dir = PathBuf::from(&baseline.inputs.examples_dir);

    if !examples_dir.is_dir() {
        return Err(format!("examples directory not found: {}", examples_dir.display()).into());
    }

    let mut totals = AuditTotals {
        specs_seen: baseline.specs.len(),
        ..AuditTotals::default()
    };
    let mut blockers: BTreeMap<String, BlockerStats> = BTreeMap::new();
    let mut failures = Vec::new();

    for (index, (spec_name, spec)) in baseline.specs.iter().enumerate() {
        if (index + 1) % 25 == 0 || index == 0 {
            eprintln!("[jit-audit] {}/{} specs", index + 1, baseline.specs.len());
        }

        let Some(source) = &spec.source else {
            continue;
        };

        let tla_path = examples_dir.join(&source.tla_path);
        let cfg_path = examples_dir.join(&source.cfg_path);
        match audit_spec(spec_name, &tla_path, &cfg_path) {
            Ok(spec_audit) => {
                totals.specs_audited += 1;
                totals.requested_ops += spec_audit.requested_ops;
                totals.compiled_target_ops += spec_audit.compiled_target_ops;
                totals.bytecode_compile_failures += spec_audit.bytecode_compile_failures;
                totals.compiled_functions += spec_audit.compiled_functions;
                totals.eligible_functions += spec_audit.eligible_functions;
                totals.inline_next_actions_skipped +=
                    usize::from(spec_audit.inline_next_action_skipped);
                totals.action_resolution_failures +=
                    usize::from(spec_audit.action_resolution_failed);
                if !spec_audit.blockers.is_empty() {
                    totals.specs_with_blockers += 1;
                }

                for blocker in &spec_audit.blockers {
                    blockers
                        .entry(blocker.clone())
                        .or_default()
                        .specs
                        .insert(spec_name.clone());
                }
                for (blocker, count) in spec_audit.blocker_functions {
                    blockers.entry(blocker).or_default().functions += count;
                }
                for (blocker, count) in spec_audit.blocker_occurrences {
                    blockers.entry(blocker).or_default().occurrences += count;
                }
            }
            Err(error) => {
                totals.spec_failures += 1;
                failures.push((spec_name.clone(), error));
            }
        }
    }

    print_report(&baseline_path, &examples_dir, &totals, &blockers, &failures);
    Ok(())
}

fn parse_args() -> Result<PathBuf, Box<dyn Error>> {
    let mut args = std::env::args_os();
    let _program = args.next();
    let baseline = args.next();
    if args.next().is_some() {
        return Err(format!(
            "usage: cargo run --bin jit_eligibility_audit [baseline.json]\n\
             default baseline: {DEFAULT_BASELINE_PATH}"
        )
        .into());
    }

    Ok(baseline
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_BASELINE_PATH)))
}

fn audit_spec(spec_name: &str, tla_path: &Path, cfg_path: &Path) -> Result<SpecAudit, String> {
    let (main_tree, main_module) = load_main_module(tla_path)?;
    let mut loader = ModuleLoader::new(tla_path);
    loader.seed_from_syntax_tree(&main_tree, tla_path);
    loader
        .load_extends(&main_module)
        .map_err(|error| format!("load EXTENDS: {error}"))?;
    loader
        .load_instances(&main_module)
        .map_err(|error| format!("load INSTANCE: {error}"))?;

    let cfg_text = std::fs::read_to_string(cfg_path)
        .map_err(|error| format!("read {}: {error}", cfg_path.display()))?;
    let config =
        Config::parse(&cfg_text).map_err(|errors| format_config_errors(cfg_path, &errors))?;

    let dep_modules = loader.modules_for_model_checking(&main_module);
    let dep_trees: Vec<SyntaxNode> = dep_modules
        .iter()
        .filter_map(|module| {
            loader
                .get(&module.name.node)
                .map(|loaded| loaded.syntax_tree.clone())
        })
        .collect();
    let extended_trees: Vec<&SyntaxNode> = dep_trees.iter().collect();

    let (action_name, inline_next_action_skipped, action_resolution_failed) =
        resolve_action_name(&config, &main_tree, &extended_trees);

    let mut op_names: BTreeSet<String> = config.invariants.iter().cloned().collect();
    if let Some(action_name) = action_name {
        op_names.insert(action_name);
    }
    if op_names.is_empty() {
        return Ok(SpecAudit {
            inline_next_action_skipped,
            action_resolution_failed,
            ..SpecAudit::default()
        });
    }

    let (extended_modules, _) = loader.modules_for_semantic_resolution(&main_module);
    let registry =
        VarRegistry::from_names(collect_state_var_names(&main_module, &extended_modules));

    let mut root = main_module.clone();
    let mut deps: Vec<Module> = dep_modules.into_iter().cloned().collect();
    resolve_state_vars(&mut root, &registry);
    for dep in &mut deps {
        resolve_state_vars(dep, &registry);
    }

    let mut ctx = tla_eval::EvalCtx::new();
    ctx.register_vars(registry.names().iter().map(|name| name.clone()));
    bind_constants_from_config(&mut ctx, &config)
        .map_err(|error| format!("bind config constants for {spec_name}: {error}"))?;

    let resolved_constants = env_to_resolved_constants(ctx.env());
    let dep_refs: Vec<&Module> = deps.iter().collect();
    let tir_callees = collect_bytecode_namespace_callees(&root, &dep_refs);
    let requested_ops: Vec<String> = op_names.into_iter().collect();
    let compiled = compile_operators_to_bytecode_full(
        &root,
        &dep_refs,
        &requested_ops,
        &resolved_constants,
        Some(ctx.op_replacements()),
        Some(&tir_callees),
    );

    let mut spec_audit = SpecAudit {
        requested_ops: requested_ops.len(),
        compiled_target_ops: compiled.op_indices.len(),
        bytecode_compile_failures: compiled.failed.len(),
        compiled_functions: compiled.chunk.functions.len(),
        inline_next_action_skipped,
        action_resolution_failed,
        ..SpecAudit::default()
    };

    for func in &compiled.chunk.functions {
        if check_eligibility_with_constants(func, Some(&compiled.chunk.constants)).is_ok() {
            spec_audit.eligible_functions += 1;
        }

        let mut function_blockers = BTreeSet::new();
        for (pc, opcode) in func.instructions.iter().enumerate() {
            let Err(reason) =
                check_opcode_eligibility_with_constants(func, pc, Some(&compiled.chunk.constants))
            else {
                continue;
            };

            let blocker = blocker_label(opcode, &reason);
            *spec_audit
                .blocker_occurrences
                .entry(blocker.clone())
                .or_insert(0) += 1;
            function_blockers.insert(blocker.clone());
            spec_audit.blockers.insert(blocker);
        }

        for blocker in function_blockers {
            *spec_audit.blocker_functions.entry(blocker).or_insert(0) += 1;
        }
    }

    Ok(spec_audit)
}

fn load_main_module(path: &Path) -> Result<(SyntaxNode, Module), String> {
    let source = std::fs::read_to_string(path)
        .map_err(|error| format!("read {}: {error}", path.display()))?;
    let parsed = parse(&source);
    if !parsed.errors.is_empty() {
        let messages = parsed
            .errors
            .iter()
            .map(|error| error.message.as_str())
            .collect::<Vec<_>>()
            .join("; ");
        return Err(format!("parse {}: {messages}", path.display()));
    }

    let tree = SyntaxNode::new_root(parsed.green_node);
    let hint_name = path.file_stem().and_then(std::ffi::OsStr::to_str);
    let lowered = lower_main_module(FileId(0), &tree, hint_name);
    if !lowered.errors.is_empty() {
        let messages = lowered
            .errors
            .iter()
            .map(|error| error.message.as_str())
            .collect::<Vec<_>>()
            .join("; ");
        return Err(format!("lower {}: {messages}", path.display()));
    }

    let module = lowered
        .module
        .ok_or_else(|| format!("lower {}: no main module found", path.display()))?;
    Ok((tree, module))
}

fn resolve_action_name(
    config: &Config,
    main_tree: &SyntaxNode,
    extended_trees: &[&SyntaxNode],
) -> (Option<String>, bool, bool) {
    if config.next.is_none() && config.specification.is_none() {
        return (None, false, false);
    }

    match resolve_spec_from_config_with_extends(config, main_tree, extended_trees) {
        Ok(resolved) => {
            if resolved.next_node.is_some() {
                (None, true, false)
            } else {
                (Some(resolved.next), false, false)
            }
        }
        Err(_) => (None, false, true),
    }
}

fn collect_state_var_names(main_module: &Module, extended_modules: &[&Module]) -> Vec<String> {
    let mut names = BTreeSet::new();
    for module in extended_modules
        .iter()
        .copied()
        .chain(std::iter::once(main_module))
    {
        for unit in &module.units {
            if let Unit::Variable(vars) = &unit.node {
                for var in vars {
                    names.insert(var.node.clone());
                }
            }
        }
    }
    names.into_iter().collect()
}

fn resolve_state_vars(module: &mut Module, registry: &VarRegistry) {
    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            tla_eval::state_var::resolve_state_vars_in_op_def(def, registry);
        }
    }
}

fn env_to_resolved_constants(
    env: &tla_eval::Env,
) -> tla_core::kani_types::HashMap<tla_core::NameId, Value> {
    env.iter()
        .map(|(name, value)| (intern_name(name), value.clone()))
        .collect()
}

fn blocker_label(opcode: &Opcode, _reason: &str) -> String {
    let variant = opcode_variant_name(opcode);
    match opcode {
        Opcode::SetUnion { .. }
        | Opcode::SetIntersect { .. }
        | Opcode::SetDiff { .. }
        | Opcode::Powerset { .. }
        | Opcode::BigUnion { .. } => format!("set operation: {variant}"),
        Opcode::SetBuilderBegin { .. }
        | Opcode::SetFilterBegin { .. }
        | Opcode::FuncDefBegin { .. }
        | Opcode::LoopNext { .. } => format!("loop/quantifier: {variant}"),
        Opcode::RecordNew { .. }
        | Opcode::RecordSet { .. }
        | Opcode::Domain { .. }
        | Opcode::FuncExcept { .. }
        | Opcode::FuncDef { .. }
        | Opcode::FuncSet { .. }
        | Opcode::TupleNew { .. }
        | Opcode::Times { .. }
        | Opcode::SeqNew { .. }
        | Opcode::StrConcat { .. } => format!("compound value: {variant}"),
        _ => variant.to_string(),
    }
}

fn opcode_variant_name(opcode: &Opcode) -> String {
    let debug = format!("{opcode:?}");
    debug
        .split([' ', '{'])
        .next()
        .unwrap_or("UnknownOpcode")
        .to_string()
}

fn format_config_errors(path: &Path, errors: &[tla_check::ConfigError]) -> String {
    errors
        .iter()
        .map(|error| format!("{}:{}: {}", path.display(), error.line(), error))
        .collect::<Vec<_>>()
        .join("; ")
}

fn print_report(
    baseline_path: &Path,
    examples_dir: &Path,
    totals: &AuditTotals,
    blockers: &BTreeMap<String, BlockerStats>,
    failures: &[(String, String)],
) {
    println!("JIT Eligibility Audit");
    println!("baseline: {}", baseline_path.display());
    println!("examples_dir: {}", examples_dir.display());
    println!("specs_seen: {}", totals.specs_seen);
    println!("specs_audited: {}", totals.specs_audited);
    println!("specs_with_blockers: {}", totals.specs_with_blockers);
    println!("requested_ops: {}", totals.requested_ops);
    println!("compiled_target_ops: {}", totals.compiled_target_ops);
    println!(
        "bytecode_compile_failures: {}",
        totals.bytecode_compile_failures
    );
    println!("compiled_functions: {}", totals.compiled_functions);
    println!("eligible_functions: {}", totals.eligible_functions);
    println!(
        "inline_next_actions_skipped: {}",
        totals.inline_next_actions_skipped
    );
    println!(
        "action_resolution_failures: {}",
        totals.action_resolution_failures
    );
    println!("spec_failures: {}", totals.spec_failures);
    println!();

    let mut rows: Vec<(&String, &BlockerStats)> = blockers.iter().collect();
    rows.sort_by(|(left_name, left), (right_name, right)| {
        right
            .specs
            .len()
            .cmp(&left.specs.len())
            .then_with(|| right.functions.cmp(&left.functions))
            .then_with(|| right.occurrences.cmp(&left.occurrences))
            .then_with(|| left_name.cmp(right_name))
    });

    let blocker_width = rows
        .iter()
        .map(|(name, _)| name.len())
        .max()
        .unwrap_or(7)
        .clamp(7, 48);

    println!(
        "{:<4}  {:<width$}  {:>13}  {:>10}  {:>11}",
        "rank",
        "blocker",
        "specs_blocked",
        "functions",
        "occurrences",
        width = blocker_width,
    );
    for (index, (name, stats)) in rows.iter().enumerate() {
        println!(
            "{:<4}  {:<width$}  {:>13}  {:>10}  {:>11}",
            index + 1,
            name,
            stats.specs.len(),
            stats.functions,
            stats.occurrences,
            width = blocker_width,
        );
    }

    if !failures.is_empty() {
        println!();
        println!("Spec Failures");
        for (name, error) in failures.iter().take(10) {
            println!("{name}: {error}");
        }
        if failures.len() > 10 {
            println!("... {} more failures", failures.len() - 10);
        }
    }
}
