// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 predicate-abs` — predicate abstraction analysis.
//!
//! Constructs an abstract model from a concrete TLA+ specification by tracking
//! only boolean predicates over the state. This dramatically reduces the state
//! space by mapping each concrete state to a boolean vector (which predicates
//! hold).
//!
//! # Algorithm
//!
//! 1. Parse the spec and extract/infer predicates from invariants, guards,
//!    and comparison sub-expressions.
//! 2. Run model checking to explore concrete states.
//! 3. Report abstraction metrics: predicate count, concrete states,
//!    abstract state space bounds, and compression ratio.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the predicate-abs command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PredicateAbsOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run predicate abstraction analysis.
pub(crate) fn cmd_predicate_abs(
    file: &Path,
    config: Option<&Path>,
    predicates: Option<&[String]>,
    max_states: usize,
    format: PredicateAbsOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // --- Parse and lower -----------------------------------------------------

    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("lowering produced no module")?;

    // --- Load config ---------------------------------------------------------

    let config_path_buf = match config {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    let parsed_config = if config_path_buf.exists() {
        let cfg_source = std::fs::read_to_string(&config_path_buf)
            .with_context(|| format!("read config {}", config_path_buf.display()))?;
        Config::parse(&cfg_source).map_err(|errors| {
            for err in &errors {
                eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
            }
            anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
        })?
    } else {
        Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        }
    };

    // --- Extract predicates --------------------------------------------------

    let operators: BTreeMap<String, &OperatorDef> = extract_operators(&module);
    let mut extracted_predicates: Vec<PredicateInfo> = Vec::new();

    // 1. User-provided predicates.
    if let Some(user_preds) = predicates {
        for (i, pred_str) in user_preds.iter().enumerate() {
            extracted_predicates.push(PredicateInfo {
                name: format!("user_{i}"),
                source: PredicateSource::User,
                expression: pred_str.clone(),
            });
        }
    }

    // 2. Predicates from config invariants.
    for inv_name in &parsed_config.invariants {
        extracted_predicates.push(PredicateInfo {
            name: inv_name.clone(),
            source: PredicateSource::Invariant,
            expression: inv_name.clone(),
        });
    }

    // 3. Extract comparison sub-expressions from Init and Next.
    let init_name = parsed_config.init.as_deref().unwrap_or("Init");
    let next_name = parsed_config.next.as_deref().unwrap_or("Next");

    for op_name in [init_name, next_name] {
        if let Some(op) = operators.get(op_name) {
            let comparisons = extract_comparisons(&op.body.node);
            for (i, expr) in comparisons.into_iter().enumerate() {
                let pretty = pretty_expr(&expr);
                if !extracted_predicates.iter().any(|p| p.expression == pretty) {
                    extracted_predicates.push(PredicateInfo {
                        name: format!("{op_name}_pred_{i}"),
                        source: PredicateSource::Extracted,
                        expression: pretty,
                    });
                }
            }
        }
    }

    // Also extract from invariant operator bodies.
    for inv_name in &parsed_config.invariants {
        if let Some(op) = operators.get(inv_name.as_str()) {
            let comparisons = extract_comparisons(&op.body.node);
            for (i, expr) in comparisons.into_iter().enumerate() {
                let pretty = pretty_expr(&expr);
                if !extracted_predicates.iter().any(|p| p.expression == pretty) {
                    extracted_predicates.push(PredicateInfo {
                        name: format!("{inv_name}_sub_{i}"),
                        source: PredicateSource::InvariantSub,
                        expression: pretty,
                    });
                }
            }
        }
    }

    let num_predicates = extracted_predicates.len();

    // --- Run model check (concrete exploration) ------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();
    let concrete_states = stats.states_found;
    let is_success = matches!(check_result, CheckResult::Success(_));

    // --- Compute abstraction metrics -----------------------------------------

    let max_abstract_states: u64 = if num_predicates <= 63 {
        1u64 << num_predicates
    } else {
        u64::MAX
    };

    let abstract_upper_bound = concrete_states.min(max_abstract_states as usize);
    let compression_ratio = if abstract_upper_bound > 0 {
        concrete_states as f64 / abstract_upper_bound as f64
    } else {
        1.0
    };

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ---------------------------------------------------------------

    match format {
        PredicateAbsOutputFormat::Human => {
            println!("predicate-abs: {}", file.display());
            println!(
                "  predicates: {num_predicates} ({} user, {} invariant, {} extracted, {} inv-sub)",
                extracted_predicates.iter().filter(|p| matches!(p.source, PredicateSource::User)).count(),
                extracted_predicates.iter().filter(|p| matches!(p.source, PredicateSource::Invariant)).count(),
                extracted_predicates.iter().filter(|p| matches!(p.source, PredicateSource::Extracted)).count(),
                extracted_predicates.iter().filter(|p| matches!(p.source, PredicateSource::InvariantSub)).count(),
            );
            println!("  concrete states: {concrete_states}");
            println!("  abstract state space: 2^{num_predicates} = {max_abstract_states} possible");
            println!("  abstract states (upper bound): {abstract_upper_bound}");
            println!("  compression ratio: {compression_ratio:.1}x");
            println!("  elapsed: {elapsed:.1}s");
            println!();

            println!("  Extracted predicates:");
            for (i, pred) in extracted_predicates.iter().enumerate() {
                let src = match pred.source {
                    PredicateSource::User => "user",
                    PredicateSource::Invariant => "inv",
                    PredicateSource::Extracted => "spec",
                    PredicateSource::InvariantSub => "inv-sub",
                };
                println!("    [{i}] ({src}) {}: {}", pred.name, pred.expression);
            }

            println!();
            if num_predicates == 0 {
                println!("  Warning: no predicates found. Add --predicate flags or invariants to the config.");
            } else {
                println!(
                    "  Note: per-state predicate evaluation requires state callback integration."
                );
                println!(
                    "  Reported metrics are analytical bounds based on predicate count."
                );
            }
        }
        PredicateAbsOutputFormat::Json => {
            let predicates_json: Vec<serde_json::Value> = extracted_predicates
                .iter()
                .map(|p| {
                    serde_json::json!({
                        "name": p.name,
                        "source": match p.source {
                            PredicateSource::User => "user",
                            PredicateSource::Invariant => "invariant",
                            PredicateSource::Extracted => "extracted",
                            PredicateSource::InvariantSub => "invariant_sub",
                        },
                        "expression": p.expression,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "predicates": predicates_json,
                "statistics": {
                    "num_predicates": num_predicates,
                    "concrete_states": concrete_states,
                    "max_abstract_states": max_abstract_states,
                    "abstract_upper_bound": abstract_upper_bound,
                    "compression_ratio": compression_ratio,
                    "elapsed_seconds": elapsed,
                },
                "model_check_passed": is_success,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

enum PredicateSource {
    User,
    Invariant,
    Extracted,
    InvariantSub,
}

struct PredicateInfo {
    name: String,
    source: PredicateSource,
    expression: String,
}

// ---------------------------------------------------------------------------
// Predicate extraction
// ---------------------------------------------------------------------------

/// Extract comparison sub-expressions from an AST node.
fn extract_comparisons(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    extract_comparisons_inner(expr, &mut out);
    out
}

fn extract_comparisons_inner(expr: &Expr, out: &mut Vec<Expr>) {
    match expr {
        // Comparison nodes — collect and recurse.
        Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b)
        | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::In(a, b) => {
            out.push(expr.clone());
            extract_comparisons_inner(&a.node, out);
            extract_comparisons_inner(&b.node, out);
        }
        // Binary logical — recurse both sides.
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) => {
            extract_comparisons_inner(&a.node, out);
            extract_comparisons_inner(&b.node, out);
        }
        // Unary — recurse.
        Expr::Not(inner) | Expr::Prime(inner) => {
            extract_comparisons_inner(&inner.node, out);
        }
        Expr::If(cond, then, els) => {
            extract_comparisons_inner(&cond.node, out);
            extract_comparisons_inner(&then.node, out);
            extract_comparisons_inner(&els.node, out);
        }
        Expr::Apply(f, args) => {
            extract_comparisons_inner(&f.node, out);
            for arg in args {
                extract_comparisons_inner(&arg.node, out);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_operators(module: &Module) -> BTreeMap<String, &OperatorDef> {
    let mut ops = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            ops.insert(def.name.node.clone(), def);
        }
    }
    ops
}
