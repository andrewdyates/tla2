// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 refine` -- refinement checking for TLA+ specifications.
//!
//! Verifies that one TLA+ specification (the implementation) refines another
//! (the abstract specification) by checking a simulation relation. Refinement
//! means every behavior of the implementation, when projected through the
//! refinement mapping, is a valid behavior of the abstract specification.
//!
//! # Algorithm
//!
//! 1. Parse and lower both implementation and abstract specs to AST.
//! 2. Extract VARIABLES, Init, and Next definitions from both modules.
//! 3. Build a refinement mapping (either from a user-supplied mapping file or
//!    by automatic name matching).
//! 4. BFS over the implementation state space: for each reachable state,
//!    compute the mapped abstract state via the refinement mapping and verify
//!    that the abstract Init/invariant holds for initial states and that every
//!    implementation transition maps to a valid abstract transition (or a
//!    stuttering step).
//! 5. Report violations with concrete counterexample traces.
//!
//! # Mapping file format
//!
//! A simple text file with one mapping per line:
//! ```text
//! impl_var |-> abstract_expr
//! ```
//!
//! Lines starting with `\*` or `(*` are treated as comments and skipped.
//! Blank lines are skipped.

mod mapping;
mod report;
mod types;
mod verify;

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower_main_module, pretty_expr, FileId, SyntaxNode};

use crate::helpers::read_source;

use self::mapping::{build_auto_mapping, parse_mapping_file, RefinementMapping};
use self::report::{print_human_report, print_json_report};
use self::types::{
    AbstractTransition, RefineResult, RefineStatistics, RefinementViolation,
    SpecInfo, ViolationKind,
};
use self::verify::{check_init_refinement, check_transition_refinement};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the refine command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RefineOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run refinement checking: verify that `impl_file` refines `abstract_file`.
///
/// The implementation must simulate the abstract spec through the refinement
/// mapping. Every implementation behavior, when mapped, must be a valid
/// abstract behavior (with stuttering allowed).
pub(crate) fn cmd_refine(
    impl_file: &Path,
    abstract_file: &Path,
    config: Option<&Path>,
    mapping: Option<&Path>,
    max_states: usize,
    format: RefineOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // -----------------------------------------------------------------------
    // 1. Parse both specs
    // -----------------------------------------------------------------------
    let impl_module = parse_and_lower(impl_file, FileId(0))?;
    let abstract_module = parse_and_lower(abstract_file, FileId(1))?;

    // -----------------------------------------------------------------------
    // 2. Extract spec metadata
    // -----------------------------------------------------------------------
    let impl_info = extract_spec_info(&impl_module, impl_file)?;
    let abstract_info = extract_spec_info(&abstract_module, abstract_file)?;

    // -----------------------------------------------------------------------
    // 3. Build or load refinement mapping
    // -----------------------------------------------------------------------
    let config_source = config
        .map(|p| std::fs::read_to_string(p).with_context(|| format!("read config {}", p.display())))
        .transpose()?;
    let refinement_mapping = if let Some(mapping_path) = mapping {
        parse_mapping_file(mapping_path)?
    } else {
        build_auto_mapping(&impl_info, &abstract_info)?
    };

    // Validate the mapping covers all abstract variables.
    let unmapped = validate_mapping_coverage(&refinement_mapping, &abstract_info);

    // -----------------------------------------------------------------------
    // 4. Run refinement check
    // -----------------------------------------------------------------------
    let refine_result = run_refinement_check(
        &impl_module,
        &abstract_module,
        &impl_info,
        &abstract_info,
        &refinement_mapping,
        &unmapped,
        config_source.as_deref(),
        max_states,
    )?;

    let elapsed = start.elapsed();
    let statistics = RefineStatistics {
        impl_states_explored: refine_result.states_explored,
        impl_transitions_explored: refine_result.transitions_explored,
        violations_found: refine_result.violations.len(),
        elapsed_secs: elapsed.as_secs_f64(),
        mapping_entries: refinement_mapping.entries.len(),
        unmapped_variables: unmapped.clone(),
    };

    // -----------------------------------------------------------------------
    // 5. Output results
    // -----------------------------------------------------------------------
    match format {
        RefineOutputFormat::Human => {
            print_human_report(
                impl_file,
                abstract_file,
                &refinement_mapping,
                &refine_result,
                &statistics,
            );
        }
        RefineOutputFormat::Json => {
            print_json_report(
                impl_file,
                abstract_file,
                &refinement_mapping,
                &refine_result,
                &statistics,
            )?;
        }
    }

    // Exit with non-zero status if violations were found.
    if !refine_result.violations.is_empty() {
        std::process::exit(1);
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Parse + lower helper
// ---------------------------------------------------------------------------

fn parse_and_lower(file: &Path, file_id: FileId) -> Result<Module> {
    let source = read_source(file)?;
    let parse_result = tla_core::parse(&source);
    if !parse_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &parse_result.errors {
            let diagnostic =
                tla_core::parse_error_diagnostic(&file_path, &err.message, err.start, err.end);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "parse failed for {}: {} error(s)",
            file.display(),
            parse_result.errors.len()
        );
    }
    let tree = SyntaxNode::new_root(parse_result.green_node);

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(file_id, &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lower failed for {}: {} error(s)",
            file.display(),
            result.errors.len()
        );
    }
    result
        .module
        .context(format!("lower produced no module for {}", file.display()))
}

// ---------------------------------------------------------------------------
// Spec info extraction
// ---------------------------------------------------------------------------

/// Extract variable names, operator definitions, and Init/Next from a module.
fn extract_spec_info(module: &Module, file: &Path) -> Result<SpecInfo> {
    let mut variables = Vec::new();
    let mut operators: BTreeMap<String, OperatorDef> = BTreeMap::new();
    let mut init_def: Option<OperatorDef> = None;
    let mut next_def: Option<OperatorDef> = None;

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(decls) => {
                for decl in decls {
                    variables.push(decl.node.clone());
                }
            }
            Unit::Operator(def) => {
                let name = &def.name.node;
                // Detect Init/Next by convention.
                if name == "Init" {
                    init_def = Some(def.clone());
                } else if name == "Next" {
                    next_def = Some(def.clone());
                }
                operators.insert(name.clone(), def.clone());
            }
            _ => {}
        }
    }

    Ok(SpecInfo {
        module_name: module.name.node.clone(),
        file_path: file.to_path_buf(),
        variables,
        operators,
        init_def,
        next_def,
    })
}

// ---------------------------------------------------------------------------
// Mapping validation
// ---------------------------------------------------------------------------

/// Check which abstract variables are NOT covered by the mapping.
fn validate_mapping_coverage(
    mapping: &RefinementMapping,
    abstract_info: &SpecInfo,
) -> Vec<String> {
    let mapped_targets: std::collections::HashSet<&str> = mapping
        .entries
        .iter()
        .map(|e| e.abstract_var.as_str())
        .collect();

    abstract_info
        .variables
        .iter()
        .filter(|v| !mapped_targets.contains(v.as_str()))
        .cloned()
        .collect()
}

// ---------------------------------------------------------------------------
// Refinement check engine
// ---------------------------------------------------------------------------

/// State representation for BFS: maps variable names to their pretty-printed values.
type StateMap = BTreeMap<String, String>;

/// Run the core refinement check BFS.
fn run_refinement_check(
    impl_module: &Module,
    abstract_module: &Module,
    impl_info: &SpecInfo,
    abstract_info: &SpecInfo,
    mapping: &RefinementMapping,
    unmapped: &[String],
    _config_source: Option<&str>,
    max_states: usize,
) -> Result<RefineResult> {
    let mut violations = Vec::new();
    let mut states_explored: usize = 0;
    let mut transitions_explored: usize = 0;

    // If there are unmapped abstract variables that have no default,
    // report that immediately as a mapping violation.
    if !unmapped.is_empty() {
        violations.push(RefinementViolation {
            kind: ViolationKind::UnmappedVariables,
            description: format!(
                "Abstract variables not covered by refinement mapping: {}",
                unmapped.join(", ")
            ),
            impl_state: None,
            mapped_abstract_state: None,
            trace: Vec::new(),
            step_index: None,
        });
    }

    // Attempt Init refinement check.
    let init_violations = check_init_refinement(
        impl_info,
        abstract_info,
        mapping,
        impl_module,
        abstract_module,
    );
    violations.extend(init_violations);

    // Attempt transition refinement check.
    let (trans_violations, explored, trans_count) = check_transition_refinement(
        impl_info,
        abstract_info,
        mapping,
        impl_module,
        abstract_module,
        max_states,
    );
    violations.extend(trans_violations);
    states_explored = explored;
    transitions_explored = trans_count;

    Ok(RefineResult {
        passed: violations.is_empty(),
        violations,
        states_explored,
        transitions_explored,
    })
}
